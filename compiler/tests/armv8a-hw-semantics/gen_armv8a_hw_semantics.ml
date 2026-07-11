(* Differential test generator: ARMv8-A instruction semantics vs. hardware.

   This program enumerates every mnemonic modeled in
   proofs/compiler/armv8a_instr_decl.v (through its extraction,
   src/CIL/armv8a_instr_decl.ml), evaluates the Coq semantics ([id_semi])
   of each instruction form on a set of edge-case and pseudo-random
   operand vectors, and emits a self-contained C program (on stdout) that
   executes the very same instructions natively with inline assembly and
   compares the results (values and NZCV flags) against the model's
   predictions. The C program prints every mismatch and exits nonzero if
   any is found.

   The generated program must be compiled and run on an AArch64 machine
   (see the Makefile in this directory).

   Coverage:
   - Every mnemonic of [armv8a_mnemonics] is instantiated at both operand
     sizes (U32/W form and U64/X form) and tested whenever [id_valid]
     holds; forms with [id_valid = false] (e.g. UMULL at U32) do not
     exist and are skipped silently.
   - For the mnemonics of [has_shift_mnemonics], the shifted-register
     variants ([has_shift = Some _]) are also tested, for every shift
     kind that A64 can encode for that instruction class (LSL/LSR/ASR for
     the add/sub class, LSL/LSR/ASR/ROR for the logical class) and
     several shift amounts in [0, size).
   - Flag-setting instructions have their NZCV outputs read back with
     [mrs] and compared; flag-consuming instructions (ADC/ADCS/SBC/SBCS,
     CSEL family) have their inputs driven through [msr nzcv].
   - Loads and stores run against a scratch buffer; the model only
     specifies the extension of the transferred value (the addressing is
     the framework's business), which is exactly what is compared.

   Documented skips (see [skips] in the emitted C header as well):
   - ADR: forms a PC-relative address; its [id_semi] is the identity on
     an address already computed by the assembly-semantics framework, so
     there is no hardware-observable semantic content to test in user
     mode.
   - MOV/ADD/SUB/CMP/... immediate forms: the semantics of an instruction
     does not depend on whether an operand comes from a register or an
     immediate ([id_semi] is shared); register forms are tested.
     Immediate *operands* that are part of the semantics itself (shift
     amounts, bitfield lsb/width, MOVZ/MOVN/MOVK immediates) ARE tested,
     over their encodable ranges only.
   - MOVZ/MOVN/MOVK at U32 with shifts 32/48: the model's argument
     checker [CAimmC_armv8a_0_16_32_48] accepts them, but the W form of
     the hardware instructions cannot encode them, so they cannot be
     executed (the assembler rejects them); shifts 0/16 are tested at
     U32, 0/16/32/48 at U64.
   - Shifted-register variants with shift kinds the encoding does not
     have (e.g. ADD with ROR): the model accepts any [shift_kind] in
     [armv8a_options], but such combinations cannot be assembled, hence
     cannot be compared against hardware.
   - Condition-code decoding (NE, LT, ...) happens in [arm_eval_cond]
     (armv8a_decl / arm_common), outside the instruction descriptions
     under test; the CSEL/CSET families are tested with a fixed condition
     (NE) driven both ways through the Z flag, which exercises their
     [id_semi] on both boolean values. *)

open Jasmin
open Arch_decl
module A = Armv8a_instr_decl

(* -------------------------------------------------------------------- *)
(* Small utilities. *)

let z_of_hex s = Z.of_string s

(* splitmix64: reproducible pseudo-random 64-bit values, independent of
   the OCaml stdlib Random implementation. *)
let rnd_state = ref 0x9e3779b97f4a7c15L

let rnd64 () : Z.t =
  let open Int64 in
  rnd_state := add !rnd_state 0x9e3779b97f4a7c15L;
  let z = !rnd_state in
  let z = mul (logxor z (shift_right_logical z 30)) 0xbf58476d1ce4e5b9L in
  let z = mul (logxor z (shift_right_logical z 27)) 0x94d049bb133111ebL in
  let z = logxor z (shift_right_logical z 31) in
  Z.of_int64_unsigned z

let bits = function Wsize.U32 -> 32 | Wsize.U64 -> 64 | _ -> assert false

(* Register-operand modifier for the inline-asm template. *)
let rc = function Wsize.U64 -> "x" | _ -> "w"

let sz_suffix = function Wsize.U64 -> "x" | _ -> "w"

let opts_at ?shift sz = { A.has_shift = shift; A.opts_size = sz }

let desc mn opts = A.armv8a_instr_desc (A.ARMv8A_op (mn, opts))

let string_of_mn = A.string_of_armv8a_mnemonic

(* -------------------------------------------------------------------- *)
(* Evaluation of the extracted Coq semantics. *)

let vword ws z = Values.Vword (ws, Conv.word_of_z ws z)
let vbool b = Values.Vbool b

let eval_semi descr (idt : (_, _, _, _, _) instr_desc_t)
    (args : Values.value list) : Values.value list =
  let tins = List.map Type.eval_ltype idt.id_tin in
  let touts = List.map Type.eval_ltype idt.id_tout in
  match Values.app_sopn tins idt.id_semi args with
  | Utils0.Ok t -> Values.list_ltuple touts t
  | Utils0.Error _ ->
      failwith
        (Printf.sprintf
           "the model rejected the arguments generated for %s (generator bug \
            or unexpected safety condition)"
           descr)

let as_word = function
  | Values.Vword (ws, w) -> Conv.z_unsigned_of_word ws w
  | _ -> assert false

let as_bool = function Values.Vbool b -> b | _ -> assert false

(* Evaluations by output shape. *)
let eval_w descr idt args =
  match eval_semi descr idt args with [ w ] -> as_word w | _ -> assert false

let nzcv_bits fl =
  match fl with
  | [ n; z; c; v ] ->
      let b x = if as_bool x then 1 else 0 in
      (b n lsl 3) lor (b z lsl 2) lor (b c lsl 1) lor b v
  | _ -> assert false

let eval_nzcv descr idt args =
  match eval_semi descr idt args with
  | [ _; _; _; _ ] as fl -> nzcv_bits fl
  | _ -> assert false

let eval_nzcv_w descr idt args =
  match eval_semi descr idt args with
  | [ n; z; c; v; w ] -> (nzcv_bits [ n; z; c; v ], as_word w)
  | _ -> assert false

(* -------------------------------------------------------------------- *)
(* Test units: one C test function each, with a table of operand rows. *)

type row = {
  in0 : Z.t;
  in1 : Z.t;
  in2 : Z.t;
  fin : Z.t; (* NZCV value written with [msr nzcv] before the instruction *)
  out : Z.t; (* expected output (64-bit register/memory contents) *)
  fout : int; (* expected NZCV[31:28] after the instruction *)
}

let row ?(in0 = Z.zero) ?(in1 = Z.zero) ?(in2 = Z.zero) ?(fin = Z.zero)
    ?(out = Z.zero) ?(fout = 0) () =
  { in0; in1; in2; fin; out; fout }

(* How the C harness around the asm statement is shaped. *)
type harness =
  | Out (* fresh register output [out] *)
  | Out_in0 (* [out] is preloaded with in0 (read-modify-write dest) *)
  | No_out (* no register output (CMP/CMN/TST) *)
  | Load (* [out] loaded from a buffer preinitialized with in0 *)
  | Store (* buffer preloaded with in1 (canary); compared with out *)

type unit_t = {
  name : string; (* C identifier suffix; unique *)
  descr : string; (* human-readable instruction description *)
  template : string; (* asm text: %[out] %[in0] %[in1] %[in2] %[fin] %[fout] *)
  harness : harness;
  ins : int list; (* which of in0..in2 are bound as asm inputs *)
  has_fin : bool;
  has_fout : bool;
  rows : row list;
}

let units : unit_t list ref = ref []
let skips : string list ref = ref []

let add_unit u = units := u :: !units
let add_skip s = skips := s :: !skips

(* -------------------------------------------------------------------- *)
(* Operand pools. *)

let edges64 =
  List.map z_of_hex
    [
      "0x0"; "0x1"; "0x2"; "0x7f"; "0x80"; "0xff"; "0x7fff"; "0x8000";
      "0xffff"; "0x7fffffff"; "0x80000000"; "0xffffffff"; "0x100000000";
      "0x7fffffffffffffff"; "0x8000000000000000"; "0xfffffffffffffffe";
      "0xffffffffffffffff"; "0x5555555555555555"; "0xaaaaaaaaaaaaaaaa";
      "0x0123456789abcdef";
    ]

(* For the W forms we keep full 64-bit patterns on purpose: the upper 32
   bits must be ignored identically by the hardware (W register read) and
   by the model (truncation of the input value). *)
let edges32 =
  List.map z_of_hex
    [
      "0x0"; "0x1"; "0x2"; "0x7f"; "0xff"; "0x7fff"; "0x8000"; "0xffff";
      "0x7fffffff"; "0x80000000"; "0xfffffffe"; "0xffffffff"; "0x55555555";
      "0xaaaaaaaa"; "0xdeadbeef00000012"; "0xffffffff80000000";
    ]

let edges sz = match sz with Wsize.U64 -> edges64 | _ -> edges32

(* Smaller per-size sets used for cross products. *)
let sub_edges64 =
  List.map z_of_hex
    [
      "0x0"; "0x1"; "0x2"; "0xff"; "0x7fffffff"; "0x80000000"; "0xffffffff";
      "0x7fffffffffffffff"; "0x8000000000000000"; "0xffffffffffffffff";
      "0xaaaaaaaaaaaaaaaa"; "0x0123456789abcdef";
    ]

let sub_edges32 =
  List.map z_of_hex
    [
      "0x0"; "0x1"; "0x2"; "0xff"; "0x7fff"; "0x8000"; "0x7fffffff";
      "0x80000000"; "0xffffffff"; "0xaaaaaaaa"; "0xdeadbeef00000012";
    ]

let sub_edges sz = match sz with Wsize.U64 -> sub_edges64 | _ -> sub_edges32

let rnds n = List.init n (fun _ -> rnd64 ())

let pool1 sz = edges sz @ rnds 12

let pairs sz =
  let es = sub_edges sz in
  List.concat_map (fun a -> List.map (fun b -> (a, b)) es) es
  @ List.init 24 (fun _ -> (rnd64 (), rnd64 ()))

(* Reduced set of pairs for units that multiply the rows by another
   dimension (carry-in, condition, shift amounts, ...). *)
let small_pairs sz =
  let es =
    match sz with
    | Wsize.U64 ->
        List.map z_of_hex
          [
            "0x0"; "0x1"; "0xffffffffffffffff"; "0x8000000000000000";
            "0x7fffffffffffffff"; "0xaaaaaaaaaaaaaaaa";
          ]
    | _ ->
        List.map z_of_hex
          [ "0x0"; "0x1"; "0xffffffff"; "0x80000000"; "0x7fffffff";
            "0xdeadbeef0000000a" ]
  in
  List.concat_map (fun a -> List.map (fun b -> (a, b)) es) es
  @ List.init 12 (fun _ -> (rnd64 (), rnd64 ()))

let triples _sz =
  let structured =
    List.map
      (fun (a, b, c) -> (z_of_hex a, z_of_hex b, z_of_hex c))
      [
        ("0x0", "0x0", "0x0");
        ("0x1", "0x1", "0x1");
        ("0xffffffffffffffff", "0xffffffffffffffff", "0xffffffffffffffff");
        ("0x8000000000000000", "0xffffffffffffffff", "0x0");
        ("0xffffffffffffffff", "0x2", "0x1");
        ("0x80000000", "0x80000000", "0x7fffffffffffffff");
        ("0xaaaaaaaaaaaaaaaa", "0x5555555555555555", "0x123456789abcdef");
        ("0xffffffff", "0xffffffff", "0xffffffffffffffff");
      ]
  in
  structured @ List.init 32 (fun _ -> (rnd64 (), rnd64 (), rnd64 ()))

(* Shift amounts fed through a register: the hardware reduces the whole
   64-bit register modulo the operand size; the model truncates to a byte
   first (the input is [lword U8]) and then reduces. These agree because
   the operand size divides 256; values above 255 are included to
   exercise exactly that. *)
let reg_shift_amounts sz =
  let b = bits sz in
  List.map Z.of_int
    [ 0; 1; 2; 7; b - 1; b; b + 1; (2 * b) - 1; 2 * b; 100; 127; 128; 255 ]
  @ List.map z_of_hex [ "0x140"; "0x123456789" ]

let imm_shift_amounts sz =
  let b = bits sz in
  [ 0; 1; 7; b / 2; b - 1 ]

(* (lsb, width) pairs, valid for the bitfield instructions:
   0 <= lsb < bits, 1 <= width <= bits - lsb. *)
let bf_pairs sz =
  let b = bits sz in
  [ (0, 1); (0, b); (1, 1); (7, 9); (b / 2, b / 2); (b - 1, 1); (3, b - 3) ]

let extr_lsbs sz =
  let b = bits sz in
  [ 0; 1; 7; b / 2; b - 1 ]

let movw_imms = [ 0x0; 0x1; 0x8000; 0xabcd; 0xffff ]

(* Halfword shifts encodable by the hardware MOVZ/MOVN/MOVK: hw in {0,1}
   for the W form, {0,1,2,3} for the X form. The model checker also
   accepts 32/48 at U32 but those cannot be encoded (documented skip). *)
let movw_shifts sz =
  match sz with Wsize.U64 -> [ 0; 16; 32; 48 ] | _ -> [ 0; 16 ]

let store_canaries =
  List.map z_of_hex [ "0xa5a5a5a5a5a5a5a5"; "0x0"; "0xffffffffffffffff" ]

(* -------------------------------------------------------------------- *)
(* NZCV helpers. *)

let fin_of_carry c = if c then Z.shift_left Z.one 29 else Z.zero

(* The CSEL family is tested with the fixed condition NE, which holds iff
   Z = 0. *)
let fin_of_ne_bool b = if b then Z.zero else Z.shift_left Z.one 30

(* -------------------------------------------------------------------- *)
(* Unit builders, one per instruction family. *)

let lmn mn = String.lowercase_ascii (string_of_mn mn)

let unit_name mn sz variant =
  let v = if variant = "" then "" else "_" ^ variant in
  Printf.sprintf "%s_%s%s" (lmn mn) (sz_suffix sz) v

let unit_descr mn sz variant =
  let v = if variant = "" then "" else " " ^ variant in
  Printf.sprintf "%s (%s form)%s" (string_of_mn mn) (sz_suffix sz) v

(* Fail fast if a form we are about to test is not valid. *)
let check_valid mn opts =
  let idt = desc mn opts in
  if not idt.id_valid then
    failwith
      (Printf.sprintf "form %s is not id_valid but was selected for testing"
         (string_of_mn mn));
  idt

(* --- binary operations: OUT = mn(in0, in1) --------------------------- *)

let mk_binop mn sz =
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz "" in
  let rows =
    List.map
      (fun (a, b) ->
        let out = eval_w descr idt [ vword sz a; vword sz b ] in
        row ~in0:a ~in1:b ~out ())
      (pairs sz)
  in
  add_unit
    {
      name = unit_name mn sz "";
      descr;
      template =
        Printf.sprintf "%s %%%s[out], %%%s[in0], %%%s[in1]" (lmn mn) r r r;
      harness = Out;
      ins = [ 0; 1 ];
      has_fin = false;
      has_fout = false;
      rows;
    }

(* --- flag-setting binary operations ---------------------------------- *)

let mk_binop_s mn sz =
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz "" in
  let rows =
    List.map
      (fun (a, b) ->
        let fout, out = eval_nzcv_w descr idt [ vword sz a; vword sz b ] in
        row ~in0:a ~in1:b ~out ~fout ())
      (pairs sz)
  in
  add_unit
    {
      name = unit_name mn sz "";
      descr;
      template =
        Printf.sprintf "%s %%%s[out], %%%s[in0], %%%s[in1]\\n\\tmrs %%x[fout], nzcv"
          (lmn mn) r r r;
      harness = Out;
      ins = [ 0; 1 ];
      has_fin = false;
      has_fout = true;
      rows;
    }

(* --- carry-consuming operations (ADC/SBC and flag-setting variants) --- *)

let mk_carry mn sz ~set_flags =
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz "" in
  let rows =
    List.concat_map
      (fun (a, b) ->
        List.map
          (fun cf ->
            let args = [ vword sz a; vword sz b; vbool cf ] in
            let fin = fin_of_carry cf in
            if set_flags then
              let fout, out = eval_nzcv_w descr idt args in
              row ~in0:a ~in1:b ~fin ~out ~fout ()
            else
              let out = eval_w descr idt args in
              row ~in0:a ~in1:b ~fin ~out ())
          [ false; true ])
      (small_pairs sz)
  in
  add_unit
    {
      name = unit_name mn sz "";
      descr;
      template =
        Printf.sprintf "msr nzcv, %%x[fin]\\n\\t%s %%%s[out], %%%s[in0], %%%s[in1]%s"
          (lmn mn) r r r
          (if set_flags then "\\n\\tmrs %x[fout], nzcv" else "");
      harness = Out;
      ins = [ 0; 1 ];
      has_fin = true;
      has_fout = set_flags;
      rows;
    }

(* --- unary operations: OUT = mn(in0) --------------------------------- *)

let mk_unop mn sz =
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz "" in
  let rows =
    List.map
      (fun a ->
        let out = eval_w descr idt [ vword sz a ] in
        row ~in0:a ~out ())
      (pool1 sz)
  in
  add_unit
    {
      name = unit_name mn sz "";
      descr;
      template = Printf.sprintf "%s %%%s[out], %%%s[in0]" (lmn mn) r r;
      harness = Out;
      ins = [ 0 ];
      has_fin = false;
      has_fout = false;
      rows;
    }

(* --- MADD/MSUB: OUT = mn(in0, in1, in2) ------------------------------ *)

let mk_madd mn sz =
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz "" in
  let rows =
    List.map
      (fun (a, b, c) ->
        let out = eval_w descr idt [ vword sz a; vword sz b; vword sz c ] in
        row ~in0:a ~in1:b ~in2:c ~out ())
      (triples sz)
  in
  add_unit
    {
      name = unit_name mn sz "";
      descr;
      template =
        Printf.sprintf "%s %%%s[out], %%%s[in0], %%%s[in1], %%%s[in2]"
          (lmn mn) r r r r;
      harness = Out;
      ins = [ 0; 1; 2 ];
      has_fin = false;
      has_fout = false;
      rows;
    }

(* --- UMULL/SMULL: X-only, W sources ---------------------------------- *)

let mk_mull mn =
  let sz = Wsize.U64 in
  let idt = check_valid mn (opts_at sz) in
  let descr = unit_descr mn sz "" in
  let rows =
    List.map
      (fun (a, b) ->
        let out = eval_w descr idt [ vword Wsize.U32 a; vword Wsize.U32 b ] in
        row ~in0:a ~in1:b ~out ())
      (pairs Wsize.U32)
  in
  add_unit
    {
      name = unit_name mn sz "";
      descr;
      template = Printf.sprintf "%s %%x[out], %%w[in0], %%w[in1]" (lmn mn);
      harness = Out;
      ins = [ 0; 1 ];
      has_fin = false;
      has_fout = false;
      rows;
    }

(* --- UMADDL/SMADDL: X-only, W multiply sources, X addend ------------- *)

let mk_maddl mn =
  let sz = Wsize.U64 in
  let idt = check_valid mn (opts_at sz) in
  let descr = unit_descr mn sz "" in
  let rows =
    List.map
      (fun (a, b, c) ->
        let out =
          eval_w descr idt
            [ vword Wsize.U32 a; vword Wsize.U32 b; vword Wsize.U64 c ]
        in
        row ~in0:a ~in1:b ~in2:c ~out ())
      (triples sz)
  in
  add_unit
    {
      name = unit_name mn sz "";
      descr;
      template =
        Printf.sprintf "%s %%x[out], %%w[in0], %%w[in1], %%x[in2]" (lmn mn);
      harness = Out;
      ins = [ 0; 1; 2 ];
      has_fin = false;
      has_fout = false;
      rows;
    }

(* --- variable shifts (register form) --------------------------------- *)

let mk_shift_reg mn sz =
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz "(register)" in
  let rows =
    List.concat_map
      (fun a ->
        List.map
          (fun amt ->
            let out = eval_w descr idt [ vword sz a; vword Wsize.U8 amt ] in
            row ~in0:a ~in1:amt ~out ())
          (reg_shift_amounts sz))
      (sub_edges sz)
  in
  add_unit
    {
      name = unit_name mn sz "reg";
      descr;
      template =
        Printf.sprintf "%s %%%s[out], %%%s[in0], %%%s[in1]" (lmn mn) r r r;
      harness = Out;
      ins = [ 0; 1 ];
      has_fin = false;
      has_fout = false;
      rows;
    }

(* --- immediate shifts (aliases of UBFM/SBFM/EXTR) --------------------- *)

let mk_shift_imm mn sz amt =
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz (Printf.sprintf "#%d" amt) in
  let rows =
    List.map
      (fun a ->
        let out =
          eval_w descr idt [ vword sz a; vword Wsize.U8 (Z.of_int amt) ]
        in
        row ~in0:a ~out ())
      (pool1 sz)
  in
  add_unit
    {
      name = unit_name mn sz (Printf.sprintf "imm%d" amt);
      descr;
      template =
        Printf.sprintf "%s %%%s[out], %%%s[in0], #%d" (lmn mn) r r amt;
      harness = Out;
      ins = [ 0 ];
      has_fin = false;
      has_fout = false;
      rows;
    }

(* --- SBFX/UBFX -------------------------------------------------------- *)

let mk_bfx mn sz (lsb, width) =
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz (Printf.sprintf "#%d, #%d" lsb width) in
  let rows =
    List.map
      (fun a ->
        let out =
          eval_w descr idt
            [
              vword sz a;
              vword Wsize.U8 (Z.of_int lsb);
              vword Wsize.U8 (Z.of_int width);
            ]
        in
        row ~in0:a ~out ())
      (pool1 sz)
  in
  add_unit
    {
      name = unit_name mn sz (Printf.sprintf "l%d_w%d" lsb width);
      descr;
      template =
        Printf.sprintf "%s %%%s[out], %%%s[in0], #%d, #%d" (lmn mn) r r lsb
          width;
      harness = Out;
      ins = [ 0 ];
      has_fin = false;
      has_fout = false;
      rows;
    }

(* --- BFC: read-modify-write destination ------------------------------- *)

let mk_bfc sz (lsb, width) =
  let mn = A.BFC in
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz (Printf.sprintf "#%d, #%d" lsb width) in
  let rows =
    List.map
      (fun x ->
        let out =
          eval_w descr idt
            [
              vword sz x;
              vword Wsize.U8 (Z.of_int lsb);
              vword Wsize.U8 (Z.of_int width);
            ]
        in
        row ~in0:x ~out ())
      (pool1 sz)
  in
  add_unit
    {
      name = unit_name mn sz (Printf.sprintf "l%d_w%d" lsb width);
      descr;
      template = Printf.sprintf "%s %%%s[out], #%d, #%d" (lmn mn) r lsb width;
      harness = Out_in0;
      ins = [];
      has_fin = false;
      has_fout = false;
      rows;
    }

(* --- BFI/BFXIL: read-modify-write destination plus a source ----------- *)

let mk_bfi mn sz (lsb, width) =
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz (Printf.sprintf "#%d, #%d" lsb width) in
  let rows =
    List.map
      (fun (x, y) ->
        let out =
          eval_w descr idt
            [
              vword sz x;
              vword sz y;
              vword Wsize.U8 (Z.of_int lsb);
              vword Wsize.U8 (Z.of_int width);
            ]
        in
        row ~in0:x ~in1:y ~out ())
      (small_pairs sz)
  in
  add_unit
    {
      name = unit_name mn sz (Printf.sprintf "l%d_w%d" lsb width);
      descr;
      template =
        Printf.sprintf "%s %%%s[out], %%%s[in1], #%d, #%d" (lmn mn) r r lsb
          width;
      harness = Out_in0;
      ins = [ 1 ];
      has_fin = false;
      has_fout = false;
      rows;
    }

(* --- EXTR -------------------------------------------------------------- *)

let mk_extr sz lsb =
  let mn = A.EXTR in
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz (Printf.sprintf "#%d" lsb) in
  let rows =
    List.map
      (fun (a, b) ->
        let out =
          eval_w descr idt
            [ vword sz a; vword sz b; vword Wsize.U8 (Z.of_int lsb) ]
        in
        row ~in0:a ~in1:b ~out ())
      (small_pairs sz)
  in
  add_unit
    {
      name = unit_name mn sz (Printf.sprintf "l%d" lsb);
      descr;
      template =
        Printf.sprintf "%s %%%s[out], %%%s[in0], %%%s[in1], #%d" (lmn mn) r r
          r lsb;
      harness = Out;
      ins = [ 0; 1 ];
      has_fin = false;
      has_fout = false;
      rows;
    }

(* --- MOVZ/MOVN: pure immediates ---------------------------------------- *)

let mk_movw mn sz imm sh =
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz (Printf.sprintf "#%d, lsl #%d" imm sh) in
  let out =
    eval_w descr idt
      [ vword Wsize.U16 (Z.of_int imm); vword Wsize.U8 (Z.of_int sh) ]
  in
  let shift_txt = if sh = 0 then "" else Printf.sprintf ", lsl #%d" sh in
  add_unit
    {
      name = unit_name mn sz (Printf.sprintf "i%x_s%d" imm sh);
      descr;
      template = Printf.sprintf "%s %%%s[out], #%d%s" (lmn mn) r imm shift_txt;
      harness = Out;
      ins = [];
      has_fin = false;
      has_fout = false;
      rows = [ row ~out () ];
    }

(* --- MOVK: immediate into a preserved destination ----------------------- *)

let mk_movk sz imm sh =
  let mn = A.MOVK in
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz (Printf.sprintf "#%d, lsl #%d" imm sh) in
  let rows =
    List.map
      (fun old ->
        let out =
          eval_w descr idt
            [
              vword sz old;
              vword Wsize.U16 (Z.of_int imm);
              vword Wsize.U8 (Z.of_int sh);
            ]
        in
        row ~in0:old ~out ())
      (sub_edges sz)
  in
  let shift_txt = if sh = 0 then "" else Printf.sprintf ", lsl #%d" sh in
  add_unit
    {
      name = unit_name mn sz (Printf.sprintf "i%x_s%d" imm sh);
      descr;
      template = Printf.sprintf "%s %%%s[out], #%d%s" (lmn mn) r imm shift_txt;
      harness = Out_in0;
      ins = [];
      has_fin = false;
      has_fout = false;
      rows;
    }

(* --- comparisons: flags only ------------------------------------------- *)

let mk_cmp mn sz =
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz "" in
  let rows =
    List.map
      (fun (a, b) ->
        let fout = eval_nzcv descr idt [ vword sz a; vword sz b ] in
        row ~in0:a ~in1:b ~fout ())
      (pairs sz)
  in
  add_unit
    {
      name = unit_name mn sz "";
      descr;
      template =
        Printf.sprintf "%s %%%s[in0], %%%s[in1]\\n\\tmrs %%x[fout], nzcv"
          (lmn mn) r r;
      harness = No_out;
      ins = [ 0; 1 ];
      has_fin = false;
      has_fout = true;
      rows;
    }

(* --- conditional selection (fixed condition NE, both boolean values) --- *)

let mk_csel mn sz =
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz "(cond NE)" in
  let rows =
    List.concat_map
      (fun (a, b) ->
        List.map
          (fun cond ->
            let out =
              eval_w descr idt [ vword sz a; vword sz b; vbool cond ]
            in
            row ~in0:a ~in1:b ~fin:(fin_of_ne_bool cond) ~out ())
          [ false; true ])
      (small_pairs sz)
  in
  add_unit
    {
      name = unit_name mn sz "";
      descr;
      template =
        Printf.sprintf "msr nzcv, %%x[fin]\\n\\t%s %%%s[out], %%%s[in0], %%%s[in1], ne"
          (lmn mn) r r r;
      harness = Out;
      ins = [ 0; 1 ];
      has_fin = true;
      has_fout = false;
      rows;
    }

let mk_cset mn sz =
  let idt = check_valid mn (opts_at sz) in
  let r = rc sz in
  let descr = unit_descr mn sz "(cond NE)" in
  let rows =
    List.map
      (fun cond ->
        let out = eval_w descr idt [ vbool cond ] in
        row ~fin:(fin_of_ne_bool cond) ~out ())
      [ false; true ]
  in
  add_unit
    {
      name = unit_name mn sz "";
      descr;
      template =
        Printf.sprintf "msr nzcv, %%x[fin]\\n\\t%s %%%s[out], ne" (lmn mn) r;
      harness = Out;
      ins = [];
      has_fin = true;
      has_fout = false;
      rows;
    }

(* --- extensions --------------------------------------------------------- *)

(* [in_ws] is the width of the extracted low bits; the source register is
   always printed W; the destination is X only for the sign extensions of
   the X form. UXTW has no mnemonic of its own: it is [MOV <Wd>, <Wn>]
   (see pp_arm_v8a.ml). *)
let mk_extend mn sz ~in_ws ~signed =
  let idt = check_valid mn (opts_at sz) in
  let dst = if signed then rc sz else "w" in
  let name = if mn = A.UXTW then "mov" else lmn mn in
  let descr = unit_descr mn sz "" in
  let rows =
    List.map
      (fun a ->
        let out = eval_w descr idt [ vword in_ws a ] in
        row ~in0:a ~out ())
      (pool1 sz)
  in
  add_unit
    {
      name = unit_name mn sz "";
      descr;
      template = Printf.sprintf "%s %%%s[out], %%w[in0]" name dst;
      harness = Out;
      ins = [ 0 ];
      has_fin = false;
      has_fout = false;
      rows;
    }

(* --- loads --------------------------------------------------------------- *)

let mk_load mn sz ~wacc ~dst_w =
  let idt = check_valid mn (opts_at sz) in
  let dst = if dst_w then "w" else rc sz in
  let descr = unit_descr mn sz "" in
  let rows =
    List.map
      (fun pat ->
        let out = eval_w descr idt [ vword wacc pat ] in
        row ~in0:pat ~out ())
      (pool1 Wsize.U64)
  in
  add_unit
    {
      name = unit_name mn sz "";
      descr;
      template = Printf.sprintf "%s %%%s[out], [%%x[p]]" (lmn mn) dst;
      harness = Load;
      ins = [];
      has_fin = false;
      has_fout = false;
      rows;
    }

(* --- stores -------------------------------------------------------------- *)

let mk_store mn sz ~wacc ~src_w =
  let idt = check_valid mn (opts_at sz) in
  let src = if src_w then "w" else rc sz in
  let descr = unit_descr mn sz "" in
  let nbytes =
    match wacc with
    | Wsize.U8 -> 1
    | Wsize.U16 -> 2
    | Wsize.U32 -> 4
    | Wsize.U64 -> 8
    | _ -> assert false
  in
  let mask = Z.sub (Z.shift_left Z.one (8 * nbytes)) Z.one in
  let unmask = Z.extract (Z.lognot mask) 0 64 in
  let rows =
    List.concat_map
      (fun v ->
        List.map
          (fun canary ->
            let stored = eval_w descr idt [ vword wacc v ] in
            let out = Z.logor (Z.logand canary unmask) stored in
            row ~in0:v ~in1:canary ~out ())
          store_canaries)
      (pool1 Wsize.U64)
  in
  add_unit
    {
      name = unit_name mn sz "";
      descr;
      template = Printf.sprintf "%s %%%s[in0], [%%x[p]]" (lmn mn) src;
      harness = Store;
      ins = [ 0 ];
      has_fin = false;
      has_fout = false;
      rows;
    }

(* -------------------------------------------------------------------- *)
(* Shifted-register variants. *)

(* Shift kinds each instruction class can encode. The model accepts any
   [shift_kind] for any mnemonic of [has_shift_mnemonics]; the
   combinations the encoding does not have (ROR for the add/sub class)
   cannot be run on hardware and are skipped (see the C header). *)
let encodable_shift_kinds mn =
  let open Shift_kind in
  match mn with
  | A.ADD | A.ADDS | A.SUB | A.SUBS | A.NEG | A.CMP | A.CMN ->
      [ SLSL; SLSR; SASR ]
  | A.AND | A.ANDS | A.BIC | A.BICS | A.ORR | A.EOR | A.MVN | A.TST ->
      [ SLSL; SLSR; SASR; SROR ]
  | _ -> assert false

let shift_kind_txt =
  let open Shift_kind in
  function SLSL -> "lsl" | SLSR -> "lsr" | SASR -> "asr" | SROR -> "ror"

(* Shifted binary operations (with or without flag outputs). *)
let mk_shifted_binop mn sz sk amt =
  let idt = check_valid mn (opts_at ~shift:sk sz) in
  let r = rc sz in
  let sk_txt = shift_kind_txt sk in
  let with_flags =
    match idt.id_tout with _ :: _ :: _ -> true | _ -> false
  in
  let descr = unit_descr mn sz (Printf.sprintf "(%s #%d)" sk_txt amt) in
  let rows =
    List.map
      (fun (a, b) ->
        let args = [ vword sz a; vword sz b; vword Wsize.U8 (Z.of_int amt) ] in
        if with_flags then
          let fout, out = eval_nzcv_w descr idt args in
          row ~in0:a ~in1:b ~out ~fout ()
        else
          let out = eval_w descr idt args in
          row ~in0:a ~in1:b ~out ())
      (small_pairs sz)
  in
  add_unit
    {
      name = unit_name mn sz (Printf.sprintf "%s%d" sk_txt amt);
      descr;
      template =
        Printf.sprintf "%s %%%s[out], %%%s[in0], %%%s[in1], %s #%d%s"
          (lmn mn) r r r sk_txt amt
          (if with_flags then "\\n\\tmrs %x[fout], nzcv" else "");
      harness = Out;
      ins = [ 0; 1 ];
      has_fin = false;
      has_fout = with_flags;
      rows;
    }

(* Shifted comparisons: flags only. *)
let mk_shifted_cmp mn sz sk amt =
  let idt = check_valid mn (opts_at ~shift:sk sz) in
  let r = rc sz in
  let sk_txt = shift_kind_txt sk in
  let descr = unit_descr mn sz (Printf.sprintf "(%s #%d)" sk_txt amt) in
  let rows =
    List.map
      (fun (a, b) ->
        let fout =
          eval_nzcv descr idt
            [ vword sz a; vword sz b; vword Wsize.U8 (Z.of_int amt) ]
        in
        row ~in0:a ~in1:b ~fout ())
      (small_pairs sz)
  in
  add_unit
    {
      name = unit_name mn sz (Printf.sprintf "%s%d" sk_txt amt);
      descr;
      template =
        Printf.sprintf "%s %%%s[in0], %%%s[in1], %s #%d\\n\\tmrs %%x[fout], nzcv"
          (lmn mn) r r sk_txt amt;
      harness = No_out;
      ins = [ 0; 1 ];
      has_fin = false;
      has_fout = true;
      rows;
    }

(* Shifted unary operations (NEG, MVN). *)
let mk_shifted_unop mn sz sk amt =
  let idt = check_valid mn (opts_at ~shift:sk sz) in
  let r = rc sz in
  let sk_txt = shift_kind_txt sk in
  let descr = unit_descr mn sz (Printf.sprintf "(%s #%d)" sk_txt amt) in
  let rows =
    List.map
      (fun a ->
        let out =
          eval_w descr idt [ vword sz a; vword Wsize.U8 (Z.of_int amt) ]
        in
        row ~in0:a ~out ())
      (sub_edges sz)
  in
  add_unit
    {
      name = unit_name mn sz (Printf.sprintf "%s%d" sk_txt amt);
      descr;
      template =
        Printf.sprintf "%s %%%s[out], %%%s[in0], %s #%d" (lmn mn) r r sk_txt
          amt;
      harness = Out;
      ins = [ 0 ];
      has_fin = false;
      has_fout = false;
      rows;
    }

let shifted_amounts sz =
  let b = bits sz in
  [ 0; 1; b / 2; b - 1 ]

let mk_shifted_variants mn sz =
  List.iter
    (fun sk ->
      List.iter
        (fun amt ->
          match mn with
          | A.CMP | A.CMN | A.TST -> mk_shifted_cmp mn sz sk amt
          | A.NEG | A.MVN -> mk_shifted_unop mn sz sk amt
          | _ -> mk_shifted_binop mn sz sk amt)
        (shifted_amounts sz))
    (encodable_shift_kinds mn)

(* -------------------------------------------------------------------- *)
(* Dispatch: build the units of one (mnemonic, size) form. *)

let build_units mn sz =
  match mn with
  (* Arithmetic *)
  | A.ADD | A.SUB -> mk_binop mn sz
  | A.ADDS | A.SUBS -> mk_binop_s mn sz
  | A.ADC | A.SBC -> mk_carry mn sz ~set_flags:false
  | A.ADCS | A.SBCS -> mk_carry mn sz ~set_flags:true
  | A.NEG -> mk_unop mn sz
  | A.MUL | A.SDIV | A.UDIV -> mk_binop mn sz
  | A.MADD | A.MSUB -> mk_madd mn sz
  | A.UMULL | A.SMULL -> mk_mull mn
  | A.UMADDL | A.SMADDL -> mk_maddl mn
  | A.UMULH | A.SMULH -> mk_binop mn sz
  (* Logical *)
  | A.AND | A.BIC | A.ORR | A.EOR -> mk_binop mn sz
  | A.ANDS | A.BICS -> mk_binop_s mn sz
  | A.MVN -> mk_unop mn sz
  (* Shifts *)
  | A.ASR | A.LSL | A.LSR | A.ROR ->
      mk_shift_reg mn sz;
      List.iter (fun amt -> mk_shift_imm mn sz amt) (imm_shift_amounts sz)
  (* Bit fields *)
  | A.BFC -> List.iter (fun p -> mk_bfc sz p) (bf_pairs sz)
  | A.BFI | A.BFXIL -> List.iter (fun p -> mk_bfi mn sz p) (bf_pairs sz)
  | A.SBFX | A.UBFX -> List.iter (fun p -> mk_bfx mn sz p) (bf_pairs sz)
  | A.EXTR -> List.iter (fun l -> mk_extr sz l) (extr_lsbs sz)
  (* Moves *)
  | A.MOV -> mk_unop mn sz
  | A.MOVZ | A.MOVN ->
      List.iter
        (fun imm -> List.iter (fun sh -> mk_movw mn sz imm sh) (movw_shifts sz))
        movw_imms
  | A.MOVK ->
      List.iter
        (fun imm -> List.iter (fun sh -> mk_movk sz imm sh) (movw_shifts sz))
        movw_imms
  | A.ADR ->
      add_skip
        (Printf.sprintf
           "%s (%s form): PC-relative address formation; its id_semi is the \
            identity on an address computed by the assembly-semantics \
            framework, so there is nothing hardware-differential to test in \
            user mode"
           (string_of_mn mn) (sz_suffix sz))
  (* Extensions *)
  | A.SXTB -> mk_extend mn sz ~in_ws:Wsize.U8 ~signed:true
  | A.SXTH -> mk_extend mn sz ~in_ws:Wsize.U16 ~signed:true
  | A.SXTW -> mk_extend mn sz ~in_ws:Wsize.U32 ~signed:true
  | A.UXTB -> mk_extend mn sz ~in_ws:Wsize.U8 ~signed:false
  | A.UXTH -> mk_extend mn sz ~in_ws:Wsize.U16 ~signed:false
  | A.UXTW -> mk_extend mn sz ~in_ws:Wsize.U32 ~signed:false
  (* Bit manipulation *)
  | A.RBIT | A.REV | A.REV16 | A.REV32 | A.CLZ | A.CLS -> mk_unop mn sz
  (* Comparisons *)
  | A.CMP | A.CMN | A.TST -> mk_cmp mn sz
  (* Conditional selection *)
  | A.CSEL | A.CSINC | A.CSINV | A.CSNEG -> mk_csel mn sz
  | A.CSET | A.CSETM -> mk_cset mn sz
  (* Loads *)
  | A.LDR -> mk_load mn sz ~wacc:sz ~dst_w:(sz = Wsize.U32)
  | A.LDRB -> mk_load mn sz ~wacc:Wsize.U8 ~dst_w:true
  | A.LDRH -> mk_load mn sz ~wacc:Wsize.U16 ~dst_w:true
  | A.LDRSB -> mk_load mn sz ~wacc:Wsize.U8 ~dst_w:(sz = Wsize.U32)
  | A.LDRSH -> mk_load mn sz ~wacc:Wsize.U16 ~dst_w:(sz = Wsize.U32)
  | A.LDRSW -> mk_load mn sz ~wacc:Wsize.U32 ~dst_w:false
  (* Stores *)
  | A.STR -> mk_store mn sz ~wacc:sz ~src_w:(sz = Wsize.U32)
  | A.STRB -> mk_store mn sz ~wacc:Wsize.U8 ~src_w:true
  | A.STRH -> mk_store mn sz ~wacc:Wsize.U16 ~src_w:true

(* -------------------------------------------------------------------- *)
(* C emission. *)

let pp_z_ull z = Printf.sprintf "0x%sULL" (Z.format "x" z)

let emit_unit oc u =
  let n_rows = List.length u.rows in
  Printf.fprintf oc "/* %s */\n" u.descr;
  Printf.fprintf oc "static const row_t rows_%s[%d] = {\n" u.name n_rows;
  List.iter
    (fun r ->
      Printf.fprintf oc "  { %s, %s, %s, %s, %s, %s },\n" (pp_z_ull r.in0)
        (pp_z_ull r.in1) (pp_z_ull r.in2) (pp_z_ull r.fin) (pp_z_ull r.out)
        (pp_z_ull (Z.of_int r.fout)))
    u.rows;
  Printf.fprintf oc "};\n";
  Printf.fprintf oc "static void test_%s(void) {\n" u.name;
  Printf.fprintf oc "  for (unsigned i = 0; i < %d; i++) {\n" n_rows;
  Printf.fprintf oc "    const row_t r = rows_%s[i];\n" u.name;
  let out_decl =
    match u.harness with
    | Out | Load -> "    unsigned long long out = 0;\n"
    | Out_in0 -> "    unsigned long long out = r.in0;\n"
    | No_out -> ""
    | Store -> "    unsigned long long out = 0;\n"
  in
  output_string oc out_decl;
  if u.has_fout then output_string oc "    unsigned long long fout = 0;\n";
  (match u.harness with
  | Load -> output_string oc "    unsigned long long buf = r.in0;\n"
  | Store -> output_string oc "    unsigned long long buf = r.in1;\n"
  | _ -> ());
  (* Asm statement. *)
  let outputs =
    List.filter_map
      (fun x -> x)
      [
        (match u.harness with
        | Out | Load -> Some "[out] \"=&r\" (out)"
        | Out_in0 -> Some "[out] \"+&r\" (out)"
        | No_out | Store -> None);
        (if u.has_fout then Some "[fout] \"=&r\" (fout)" else None);
      ]
  in
  let inputs =
    List.map (fun i -> Printf.sprintf "[in%d] \"r\" (r.in%d)" i i) u.ins
    @ (if u.has_fin then [ "[fin] \"r\" (r.fin)" ] else [])
    @
    match u.harness with
    | Load | Store -> [ "[p] \"r\" (&buf)" ]
    | _ -> []
  in
  let clobbers =
    [ "\"cc\"" ]
    @ match u.harness with Load | Store -> [ "\"memory\"" ] | _ -> []
  in
  Printf.fprintf oc "    __asm__ volatile (\"%s\"\n" u.template;
  Printf.fprintf oc "      : %s\n" (String.concat ", " outputs);
  Printf.fprintf oc "      : %s\n" (String.concat ", " inputs);
  Printf.fprintf oc "      : %s);\n" (String.concat ", " clobbers);
  (if u.harness = Store then output_string oc "    out = buf;\n");
  let has_out = u.harness <> No_out in
  Printf.fprintf oc
    "    check(\"%s\", i, &r, %d, %s, %d, %s);\n" u.descr
    (if has_out then 1 else 0)
    (if has_out then "out" else "0ULL")
    (if u.has_fout then 1 else 0)
    (if u.has_fout then "(fout >> 28) & 0xf" else "0ULL");
  Printf.fprintf oc "  }\n}\n\n"

let emit_c oc =
  let us = List.rev !units in
  let n_rows =
    List.fold_left (fun acc u -> acc + List.length u.rows) 0 us
  in
  Printf.fprintf oc
    "/* Generated by gen_armv8a_hw_semantics.ml -- DO NOT EDIT.\n\n\
    \   Differential test of the Jasmin ARMv8-A instruction semantics\n\
    \   (proofs/compiler/armv8a_instr_decl.v, evaluated through its OCaml\n\
    \   extraction) against the hardware. Must be compiled and executed on\n\
    \   an AArch64 (ARMv8-A) machine.\n\n\
    \   %d instruction forms, %d test cases.\n\n\
    \   Documented skips:\n%s\n*/\n\n"
    (List.length us) n_rows
    (String.concat "\n"
       (List.map (fun s -> "   - " ^ s) (List.rev !skips)));
  output_string oc "#include <stdio.h>\n\n";
  output_string oc "#if !defined(__aarch64__)\n#error \"this test must run on an AArch64 (ARMv8-A) host\"\n#endif\n\n";
  output_string oc
    "typedef struct {\n\
    \  unsigned long long in0, in1, in2; /* register / buffer inputs */\n\
    \  unsigned long long fin;           /* NZCV written before the insn */\n\
    \  unsigned long long out;           /* expected output */\n\
    \  unsigned long long fout;          /* expected NZCV[31:28] */\n\
     } row_t;\n\n\
     static unsigned long long n_checks, n_failures;\n\n\
     static void check(const char *descr, unsigned i, const row_t *r,\n\
    \                  int has_out, unsigned long long got_out,\n\
    \                  int has_fout, unsigned long long got_fout) {\n\
    \  int ok = 1;\n\
    \  if (has_out && got_out != r->out) ok = 0;\n\
    \  if (has_fout && got_fout != r->fout) ok = 0;\n\
    \  n_checks++;\n\
    \  if (ok) return;\n\
    \  n_failures++;\n\
    \  printf(\"FAIL %s [row %u]: in0=%#llx in1=%#llx in2=%#llx fin=%#llx\\n\",\n\
    \         descr, i, r->in0, r->in1, r->in2, r->fin);\n\
    \  if (has_out)\n\
    \    printf(\"     value: expected %#llx got %#llx\\n\", r->out, got_out);\n\
    \  if (has_fout)\n\
    \    printf(\"     nzcv:  expected %#llx got %#llx\\n\", r->fout, got_fout);\n\
     }\n\n";
  List.iter (emit_unit oc) us;
  output_string oc "int main(void) {\n";
  List.iter (fun u -> Printf.fprintf oc "  test_%s();\n" u.name) us;
  output_string oc
    "  printf(\"armv8a hardware-semantics test: %llu checks, %llu failures\\n\",\n\
    \         n_checks, n_failures);\n\
    \  return n_failures != 0;\n\
     }\n"

(* -------------------------------------------------------------------- *)
(* Driver. *)

let () =
  (* Sanity check: the shifted-variant table must cover exactly the
     mnemonics the model declares shiftable, so that a future extension
     of [has_shift_mnemonics] cannot silently escape testing. *)
  let shiftable = A.has_shift_mnemonics in
  List.iter
    (fun mn ->
      match encodable_shift_kinds mn with
      | _ -> ()
      | exception _ ->
          failwith
            (Printf.sprintf
               "mnemonic %s is in has_shift_mnemonics but has no entry in \
                encodable_shift_kinds"
               (string_of_mn mn)))
    shiftable;
  List.iter
    (fun mn ->
      List.iter
        (fun sz ->
          let idt = desc mn (opts_at sz) in
          if idt.id_valid then begin
            let n_units = List.length !units in
            let n_skips = List.length !skips in
            build_units mn sz;
            if List.mem mn shiftable then mk_shifted_variants mn sz;
            (* Completeness: every existing (mnemonic, size) form must
               produce at least one test unit or a documented skip. *)
            if List.length !units = n_units && List.length !skips = n_skips
            then
              failwith
                (Printf.sprintf
                   "form %s (%s) is id_valid but produced neither tests nor \
                    a documented skip"
                   (string_of_mn mn) (sz_suffix sz))
          end)
        [ Wsize.U32; Wsize.U64 ])
    A.armv8a_mnemonics;
  (* Skips that are not tied to a single form (kept next to the per-form
     ones in the emitted C header). *)
  add_skip
    "immediate forms of MOV/ADD/SUB/CMP/... operands: id_semi does not \
     depend on whether an operand comes from a register or an immediate; \
     register forms are tested (immediates that are part of the semantics \
     itself -- shift amounts, bitfield lsb/width, MOVZ/MOVN/MOVK -- are \
     tested)";
  add_skip
    "MOVZ/MOVN/MOVK at U32 with halfword shifts 32/48: accepted by the \
     model's CAimmC_armv8a_0_16_32_48 checker but not encodable in the W \
     form, hence not executable";
  add_skip
    "shifted-register variants with shift kinds A64 cannot encode (ROR on \
     the ADD/SUB/CMP/CMN/NEG class): accepted by armv8a_options but not \
     assemblable";
  add_skip
    "condition codes other than NE for CSEL/CSINC/CSINV/CSNEG/CSET/CSETM: \
     condition decoding happens in arm_eval_cond outside \
     armv8a_instr_decl.v; their id_semi booleans are driven both ways \
     through the Z flag";
  emit_c stdout;
  let us = !units in
  Printf.eprintf
    "generated %d instruction forms, %d test cases (%d skips)\n"
    (List.length us)
    (List.fold_left (fun acc u -> acc + List.length u.rows) 0 us)
    (List.length !skips)
