(* Differential test generator: Armv8-M instruction semantics vs. hardware.

   This program enumerates the instructions of the Arm M-profile model
   (proofs/compiler/arm_instr_decl.v, through its extraction in
   src/CIL/arm_instr_decl.ml) at the Armv8-M version, with their options
   (flag setting, shifted operand, conditional execution) and with every
   kind of operands that the model accepts (registers, immediates, memory
   operands, conditions).

   Each instruction form becomes a one-instruction assembly function, printed
   by the assembly printer of the compiler (Pp_arm_m4): what runs on the
   processor is what jasminc emits. Expected results are computed by the model,
   following the semantics of assembly programs (proofs/arch/arch_sem.v,
   [eval_instr_op] and [mem_write_vals]): the operands are read as described
   by [id_in], the semantics [id_semi] is applied, and the results are written
   as described by [id_out].

   The program writes two files in the directory given as first argument:
   - stubs.s: the functions under test;
   - tables.c: for each function, its description and rows of inputs
     (registers, NZCV flags, memory) and expected outputs.

   The model may accept instructions that do not exist. They are found by
   running the assembler on stubs.s: given the messages of the assembler as
   second argument, the program leaves out the instructions that the
   assembler rejects, and lists them.

   The runner (runner.c) executes every row on the processor and compares the
   whole state: the thirteen registers r0-r12 (the registers that are not
   written by the instruction must be unchanged), the flags that the model
   defines, and the memory.

   Documented skips (they are also listed in tables.c):
   - ADR computes an address relative to the program counter; the model takes
     the address from the assembly semantics, there is nothing to compare.
   - The operands LR and SP: the functions under test return through LR, and
     run on the stack of the runner. *)

open Jasmin
open Arch_decl
open Arm_common
open Arm_decl
module A = Arm_instr_decl

let version = ARMv8M
let op_decl = A.arm_op_decl version

(* -------------------------------------------------------------------- *)
(* Pseudo-random values: splitmix64, independent of the OCaml library. *)

let rnd_state = ref 0x9e3779b97f4a7c15L

let rnd64 () : Z.t =
  let open Int64 in
  rnd_state := add !rnd_state 0x9e3779b97f4a7c15L;
  let z = !rnd_state in
  let z = mul (logxor z (shift_right_logical z 30)) 0xbf58476d1ce4e5b9L in
  let z = mul (logxor z (shift_right_logical z 27)) 0x94d049bb133111ebL in
  let z = logxor z (shift_right_logical z 31) in
  Z.of_int64_unsigned z

let mask32 = Z.of_string "0xffffffff"
let rnd32 () = Z.logand (rnd64 ()) mask32
let rnd_int n = Z.to_int (Z.rem (rnd64 ()) (Z.of_int n))

(* -------------------------------------------------------------------- *)
(* Machine states. *)

let nb_regs = 13 (* r0 to r12 *)
let scratch_size = 32 (* bytes *)

(* Value of the base register of the memory operands, relative to the
   beginning of the scratch buffer. *)
let scratch_base = 8

type state = {
  regs : Z.t array; (* r0 to r12 *)
  flags : bool option array; (* N, Z, C, V; [None] is undefined *)
  mem : Bytes.t; (* scratch buffer *)
}

let copy_state s =
  { regs = Array.copy s.regs; flags = Array.copy s.flags; mem = Bytes.copy s.mem }

let reg_index (r : register) =
  match r with
  | R00 -> 0 | R01 -> 1 | R02 -> 2 | R03 -> 3 | R04 -> 4 | R05 -> 5
  | R06 -> 6 | R07 -> 7 | R08 -> 8 | R09 -> 9 | R10 -> 10 | R11 -> 11
  | R12 -> 12
  | LR | SP -> failwith "LR and SP are not operands of the tests"

let reg_of_index i = List.nth registers i
let flag_index = function NF -> 0 | ZF -> 1 | CF -> 2 | VF -> 3

exception Model_error of string

let get_flag s f =
  match s.flags.(flag_index f) with
  | Some b -> Utils0.Ok b
  | None -> Utils0.Error Utils0.ErrAddrUndef

let eval_cond s c =
  match arm_eval_cond (get_flag s) c with
  | Utils0.Ok b -> b
  | Utils0.Error _ -> raise (Model_error "condition")

let wrap32 z = Z.logand z mask32

let decode_addr s (a : _ address) : int =
  match a with
  | Arip _ -> raise (Model_error "PC-relative address")
  | Areg ra ->
      let reg = function
        | None -> Z.zero
        | Some r -> s.regs.(reg_index r)
      in
      let disp = Conv.z_unsigned_of_word U32 ra.ad_disp in
      let scale = Z.shift_left Z.one (Conv.int_of_nat ra.ad_scale) in
      let a =
        wrap32
          (Z.add (Z.add disp (reg ra.ad_base)) (Z.mul scale (reg ra.ad_offset)))
      in
      Z.to_int a

let bytes_of_ws ws = Z.to_int (Conv.z_of_cz (Wsize.wsize_size ws))

let mem_read s a ws =
  let n = bytes_of_ws ws in
  if a < 0 || a + n > scratch_size then
    raise (Model_error "memory access out of the scratch buffer");
  let r = ref Z.zero in
  for i = n - 1 downto 0 do
    let b = Z.of_int (Char.code (Bytes.get s.mem (a + i))) in
    r := Z.add (Z.shift_left !r 8) b
  done;
  !r

let mem_write s a ws z =
  let n = bytes_of_ws ws in
  if a < 0 || a + n > scratch_size then
    raise (Model_error "memory access out of the scratch buffer");
  for i = 0 to n - 1 do
    let b = Z.to_int (Z.logand (Z.shift_right z (8 * i)) (Z.of_int 0xff)) in
    Bytes.set s.mem (a + i) (Char.chr b)
  done

let vword ws z = Values.Vword (ws, Conv.word_of_z ws z)

(* See [eval_asm_arg] in arch_sem.v. *)
let eval_asm_arg k s (a : _ asm_arg) (ty : Type.ltype) : Values.value =
  match a with
  | Condt c -> Values.Vbool (eval_cond s c)
  | Imm (sz', w) -> (
      match ty with
      | Coq_lword sz -> Values.Vword (sz, Word0.sign_extend sz sz' w)
      | _ -> raise (Model_error "type of an immediate"))
  | Reg r -> vword U32 s.regs.(reg_index r)
  | Addr addr -> (
      let a = decode_addr s addr in
      match ty with
      | Coq_lword sz -> (
          match k with
          | AK_compute -> raise (Model_error "computed address")
          | AK_mem _ -> vword sz (mem_read s a sz))
      | _ -> raise (Model_error "type of a memory operand"))
  | Regx _ | XReg _ -> raise (Model_error "kind of register")

(* See [eval_arg_in_v] in arch_sem.v. *)
let eval_arg_in s args (a : _ arg_desc) ty : Values.value =
  match a with
  | ADImplicit (IAreg r) -> vword U32 s.regs.(reg_index r)
  | ADImplicit (IArflag f) -> (
      match s.flags.(flag_index f) with
      | Some b -> Values.Vbool b
      | None -> raise (Model_error "undefined flag"))
  | ADExplicit (k, i, o) ->
      let a = List.nth args (Conv.int_of_nat i) in
      if not (check_oreg arm_decl o a) then
        raise (Model_error "constrained register");
      eval_asm_arg k s a ty

(* See [mem_write_val] in arch_sem.v. The registers are 32-bit wide, as all
   the values that the instructions write to registers. *)
let write_val s args (a : _ arg_desc) (ty : Type.ltype) (v : Values.value) =
  match v, ty with
  | Values.Vbool b, Coq_lbool -> (
      match a with
      | ADImplicit (IArflag f) -> s.flags.(flag_index f) <- Some b
      | _ -> raise (Model_error "boolean destination"))
  | Values.Vundef _, Coq_lbool -> (
      match a with
      | ADImplicit (IArflag f) -> s.flags.(flag_index f) <- None
      | _ -> raise (Model_error "boolean destination"))
  | Values.Vword (ws, w), Coq_lword _ -> (
      let z = Conv.z_unsigned_of_word ws w in
      let write_reg r =
        if ws <> Wsize.U32 then raise (Model_error "size of a register value");
        s.regs.(reg_index r) <- z
      in
      match a with
      | ADImplicit (IAreg r) -> write_reg r
      | ADImplicit (IArflag _) -> raise (Model_error "word destination")
      | ADExplicit (_, i, _) -> (
          match List.nth args (Conv.int_of_nat i) with
          | Reg r -> write_reg r
          | Addr addr -> mem_write s (decode_addr s addr) ws z
          | _ -> raise (Model_error "destination")))
  | _, _ -> raise (Model_error "type of a result")

(* One step of the model: [None] when the model gives no semantics to the
   instruction in this state. *)
let step (idt : _ instr_desc_t) args (s : state) : state option =
  if not idt.id_valid then raise (Model_error "invalid instruction");
  if not (check_i_args_kinds arm_decl idt.id_args_kinds args) then
    raise (Model_error "arguments rejected by the model");
  let vs = List.map2 (eval_arg_in s args) idt.id_in idt.id_tin in
  let tins = List.map Type.eval_ltype idt.id_tin in
  let touts = List.map Type.eval_ltype idt.id_tout in
  match Values.app_sopn tins idt.id_semi vs with
  | Utils0.Error _ -> None
  | Utils0.Ok t ->
      let res = Values.list_ltuple touts t in
      let s' = copy_state s in
      (* The addresses of the destinations are computed in the initial
         state. *)
      let write_val' a ty v =
        match a with
        | ADExplicit (_, i, _) -> (
            match List.nth args (Conv.int_of_nat i), v with
            | Addr addr, Values.Vword (ws, w) ->
                mem_write s' (decode_addr s addr) ws
                  (Conv.z_unsigned_of_word ws w)
            | _, _ -> write_val s' args a ty v)
        | _ -> write_val s' args a ty v
      in
      List.iter2
        (fun (a, ty) v -> write_val' a ty v)
        (List.combine idt.id_out idt.id_tout)
        res;
      Some s'

(* -------------------------------------------------------------------- *)
(* Printing of the instructions, by the assembly printer of the compiler. *)

let () = Utils.set_target_system "linux"

let fundef body : _ asm_fundef =
  {
    asm_fd_align = Wsize.U32;
    asm_fd_arg = [];
    asm_fd_body = body;
    asm_fd_res = [];
    asm_fd_export = true;
    asm_fd_total_stack = Conv.cz_of_int 0;
    asm_fd_align_args = [];
  }

let asm_i op args : _ asm_i =
  { asmi_ii = IInfo.dummy; asmi_i = AsmOp (op, args) }

let prog funcs : A.arm_prog =
  { asm_globs = []; asm_glob_names = []; asm_funcs = funcs }

let print_prog funcs =
  Format.asprintf "%a" (Pp_arm_m4.print_prog version) (prog funcs)

(* The text of one instruction (with its IT instruction, if any). *)
let print_instr op args =
  let fn = CoreIdent.F.mk "f" in
  let txt = print_prog [ (fn, fundef [ asm_i op args ]) ] in
  let lines = String.split_on_char '\n' txt in
  let rec body acc = function
    | [] -> List.rev acc
    | l :: ls ->
        let l' = String.trim l in
        if String.length l' >= 3 && String.sub l' 0 3 = "pop" then List.rev acc
        else body (l' :: acc) ls
  in
  let rec skip = function
    | [] -> []
    | l :: ls ->
        let l' = String.trim l in
        if String.length l' >= 4 && String.sub l' 0 4 = "push" then body [] ls
        else skip ls
  in
  let squeeze s =
    String.concat " "
      (List.filter (fun x -> x <> "")
         (String.split_on_char ' '
            (String.map (fun c -> if c = '\t' then ' ' else c) s)))
  in
  String.concat "; " (List.map squeeze (skip lines))

(* -------------------------------------------------------------------- *)
(* Instruction forms. *)

type form = {
  op : A.arm_op;
  args : (register, Arch_utils.empty, Arch_utils.empty, rflag, condt) asm_arg list;
  idt : (register, Arch_utils.empty, Arch_utils.empty, rflag, condt) instr_desc_t;
  text : string;
  mutable rows : (state * state) list;
}

let forms : form list ref = ref []
(* Skipped forms, by reason. *)
let skips : (string * string list ref) list ref = ref []

let add_skip ?form reason =
  let l =
    match List.assoc_opt reason !skips with
    | Some l -> l
    | None ->
        let l = ref [] in
        skips := !skips @ [ (reason, l) ];
        l
  in
  match form with
  | Some f when not (List.mem f !l) -> l := f :: !l
  | _ -> ()

let pp_skips pr =
  List.iter
    (fun (reason, l) ->
      let l = List.rev !l in
      let n = List.length l in
      if n = 0 then pr (Printf.sprintf "%s" reason)
      else
        pr
          (Printf.sprintf "%s: %d forms (%s%s)" reason n
             (String.concat ", " (List.filteri (fun i _ -> i < 4) l))
             (if n > 4 then ", ..." else "")))
    !skips

let z = Z.of_string

(* Candidate immediates; they are filtered by the conditions of the model. *)
let imm_pool ws =
  match ws with
  | Wsize.U8 ->
      List.map Z.of_int [ 0; 1; 2; 3; 7; 8; 15; 16; 17; 24; 30; 31; 32; 33; 255 ]
  | _ ->
      List.map z
        [
          "0"; "1"; "2"; "4"; "7"; "8"; "16"; "24"; "31"; "32"; "0xff";
          "0x100"; "0x101"; "0x3fc"; "0xfff"; "0x1000"; "0xabc"; "0x7fff";
          "0x8000"; "0xabcd"; "0xffff"; "0x10000"; "0x12345"; "0xff00";
          "0xff0000"; "0xff000000"; "0x00ab00ab"; "0xab00ab00"; "0xabababab";
          "0x80000000"; "0xc0000003"; "0x7fffffff"; "0xfffffffe";
          "0xffffffff"; "0xffffff00";
        ]

(* Number of immediates per operand: every form for the plain instructions,
   fewer for their variants (shifted operand, conditional execution). *)
let max_imms = ref 6

(* Keep at most [n] elements, spread over the list. *)
let sample n l =
  let len = List.length l in
  if len <= n then l
  else if n = 1 then [ List.nth l (len / 2) ]
  else
    List.filteri
      (fun i _ -> List.mem i (List.init n (fun k -> k * (len - 1) / (n - 1))))
      l

let conds_all = condts
let conds_few = [ EQ_ct; CS_ct; HI_ct; LT_ct ]

(* Registers of the operands, by position. *)
let regs_lo = [ R00; R01; R02; R03; R04; R05 ]
let regs_hi = [ R08; R09; R10; R11; R12; R07 ]

let word32 v = Conv.word_of_z U32 v

let mem_args regs i =
  let base = List.nth regs i in
  let off = List.nth regs ((i + 2) mod List.length regs) in
  let addr disp offset scale =
    Addr
      (Areg
         {
           ad_disp = word32 (wrap32 (Z.of_int disp));
           ad_base = Some base;
           ad_scale = Conv.nat_of_int scale;
           ad_offset = offset;
         })
  in
  [
    addr 0 None 0; addr 4 None 0; addr 12 None 0; addr (-8) None 0;
    addr 0 (Some off) 0; addr 0 (Some off) 2;
  ]

let choices all_conds regs i (k : _ arg_kind) =
  match k with
  | CAreg -> [ Reg (List.nth regs i) ]
  | CAcond ->
      List.map (fun c -> Condt c) (if all_conds then conds_all else conds_few)
  | CAmem _ -> mem_args regs i
  | CAimm (chk, ws) ->
      let ok v =
        match chk with
        | None -> true
        | Some c -> check_CAimm arm_decl c ws (Conv.word_of_z ws v)
      in
      let l = List.filter ok (imm_pool ws) in
      List.map (fun v -> Imm (ws, Conv.word_of_z ws v)) (sample !max_imms l)
  | CAregx | CAxmm -> []

let rec product = function
  | [] -> [ [] ]
  | cs :: rest ->
      let tl = product rest in
      List.concat_map (fun c -> List.map (fun t -> c :: t) tl) cs

let has_addr args = List.exists (function Addr _ -> true | _ -> false) args

let add_form op idt args =
  let text = print_instr op args in
  forms := { op; args; idt; text; rows = [] } :: !forms

let enumerate_op ~all_conds ~both_regs ~imms (op : A.arm_op) =
  let idt = A.arm_instr_desc version op in
  max_imms := imms;
  if idt.id_valid then
    List.iter
      (fun (ak : _ args_kinds) ->
        List.iter
          (fun regs ->
            let cs =
              List.mapi
                (fun i kinds ->
                  List.concat_map (choices all_conds regs i) kinds)
                ak
            in
            List.iter
              (fun args ->
                if check_i_args_kinds arm_decl idt.id_args_kinds args then
                  add_form op idt args)
              (product cs))
          (if both_regs then [ regs_lo; regs_hi ] else [ regs_lo ]))
      idt.id_args_kinds

let shift_of mn = List.assoc_opt mn A.always_has_shift_mnemonics

let enumerate () =
  List.iter
    (fun mn ->
      match mn with
      | A.ADR ->
          add_skip
            "ADR: the address is relative to the program counter, the model \
             takes it from the semantics of assembly programs"
      | _ ->
          let sfs =
            if List.mem mn A.set_flags_mnemonics then [ false; true ]
            else [ false ]
          in
          let shifts =
            match shift_of mn with
            | Some sk -> [ Some sk ]
            | None ->
                None
                ::
                (if List.mem mn A.has_shift_mnemonics then
                   List.map (fun sk -> Some sk) shift_kinds
                 else [])
          in
          List.iter
            (fun set_flags ->
              List.iter
                (fun has_shift ->
                  List.iter
                    (fun is_conditional ->
                      let opts = { A.set_flags; is_conditional; has_shift } in
                      let plain = has_shift = shift_of mn in
                      (* Every condition is tested on two instructions. *)
                      let all_conds =
                        plain && (not set_flags) && (mn = A.MOV || mn = A.ADD)
                      in
                      if (not is_conditional) || plain then
                        enumerate_op ~all_conds
                          ~both_regs:(plain && not is_conditional)
                          ~imms:
                            (if is_conditional then 1
                             else if plain then 6
                             else 3)
                          (A.ARM_op (mn, opts)))
                    [ false; true ])
                shifts)
            sfs)
    A.arm_mnemonics;
  forms := List.rev !forms

(* -------------------------------------------------------------------- *)
(* Rows. *)

let edges =
  List.map z
    [
      "0x0"; "0x1"; "0x2"; "0x7f"; "0x80"; "0xff"; "0x7fff"; "0x8000";
      "0xffff"; "0x10000"; "0x7fffffff"; "0x80000000"; "0x80000001";
      "0xfffffffe"; "0xffffffff"; "0x55555555"; "0xaaaaaaaa"; "0x01234567";
      "0x89abcdef"; "0x00000020"; "0x0000001f"; "0x00000021"; "0x00000100";
    ]

let small_edges =
  List.map z [ "0x0"; "0x1"; "0xffffffff"; "0x80000000"; "0x7fffffff" ]

let arg_regs args =
  let add acc r = if List.mem r acc then acc else r :: acc in
  List.rev
    (List.fold_left
       (fun acc a ->
         match a with
         | Reg r -> add acc r
         | Addr (Areg ra) ->
             let acc = match ra.ad_base with Some r -> add acc r | None -> acc in
             (match ra.ad_offset with Some r -> add acc r | None -> acc)
         | _ -> acc)
       [] args)

(* Registers that hold addresses or offsets: their values are not random. *)
let addr_regs args =
  List.fold_left
    (fun (bases, offs) a ->
      match a with
      | Addr (Areg ra) ->
          ( (match ra.ad_base with Some r -> r :: bases | None -> bases),
            match ra.ad_offset with Some r -> r :: offs | None -> offs )
      | _ -> (bases, offs))
    ([], []) args

(* Value of the offset register of a memory operand. *)
let offset_value args j =
  let scale =
    List.fold_left
      (fun acc a ->
        match a with
        | Addr (Areg ra) -> Conv.int_of_nat ra.ad_scale
        | _ -> acc)
      0 args
  in
  (4 * (j mod 3)) lsr scale

let canary i = Z.of_int (0xa5a50000 + (i * 0x0101))

let fresh_state () =
  {
    regs = Array.init nb_regs canary;
    flags = Array.init 4 (fun _ -> Some false);
    mem = Bytes.init scratch_size (fun _ -> Char.chr (rnd_int 256));
  }

let set_flags_bits s bits =
  for i = 0 to 3 do
    (* bit 3 is N, bit 0 is V *)
    s.flags.(i) <- Some (bits land (1 lsl (3 - i)) <> 0)
  done

let is_conditional (A.ARM_op (_, opts)) = opts.A.is_conditional

let has_imm args = List.exists (function Imm _ -> true | _ -> false) args

let nb_rows (f : form) =
  let (A.ARM_op (mn, opts)) = f.op in
  if has_addr f.args then 4
  else if opts.A.is_conditional then
    if (mn = A.MOV || mn = A.ADD) && not opts.A.set_flags then 16 else 4
  else if opts.A.has_shift <> shift_of mn then 6
  else if has_imm f.args then 10
  else 24

let gen_rows (f : form) =
  let regs = arg_regs f.args in
  let bases, offs = addr_regs f.args in
  let n = nb_rows f in
  let nregs = List.length regs in
  let rows = ref [] in
  for j = 0 to n - 1 do
    let s = fresh_state () in
    List.iteri
      (fun i r ->
        let v =
          if List.mem r bases then Z.of_int scratch_base
          else if List.mem r offs then Z.of_int (offset_value f.args j)
          else if j < 5 then List.nth small_edges ((j + (i * (j + 1))) mod 5)
          else if 2 * j < n + 5 then
            List.nth edges (((j * (2 * i + 1)) + (7 * i)) mod List.length edges)
          else rnd32 ()
        in
        s.regs.(reg_index r) <- v)
      regs;
    ignore nregs;
    let bits =
      if is_conditional f.op && n = 16 then j (* every value of NZCV *)
      else rnd_int 16
    in
    set_flags_bits s bits;
    match step f.idt f.args s with
    | None -> ()
    | Some s' -> rows := (s, s') :: !rows
    | exception Model_error msg ->
        add_skip ~form:f.text
          (Printf.sprintf "the model rejects the operands (%s)" msg)
  done;
  f.rows <- List.rev !rows

(* -------------------------------------------------------------------- *)
(* Output. *)

let reg_mask rs =
  List.fold_left (fun m r -> m lor (1 lsl reg_index r)) 0 rs

let flags_bits fl =
  let b = ref 0 and m = ref 0 in
  Array.iteri
    (fun i f ->
      match f with
      | Some v ->
          m := !m lor (1 lsl (3 - i));
          if v then b := !b lor (1 lsl (3 - i))
      | None -> ())
    fl;
  (!b, !m)

let words_of_bytes b =
  List.init (Bytes.length b / 4) (fun i ->
      let g k =
        Z.shift_left (Z.of_int (Char.code (Bytes.get b ((4 * i) + k)))) (8 * k)
      in
      Z.add (Z.add (g 0) (g 1)) (Z.add (g 2) (g 3)))

let c_string s =
  let b = Buffer.create (String.length s + 2) in
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | c -> Buffer.add_char b c)
    s;
  Buffer.contents b

let name i = Printf.sprintf "f%d" i

let funcs_of forms =
  List.mapi
    (fun i f -> (CoreIdent.F.mk (name i), fundef [ asm_i f.op f.args ]))
    forms

(* The forms that the assembler rejects: [log] holds the messages of the
   assembler on the file made of all the forms. *)
let rejected_by_assembler forms log =
  let text = String.split_on_char '\n' (print_prog (funcs_of forms)) in
  let text = Array.of_list text in
  let form_of_line n =
    (* The label of the function is above the line. *)
    let rec up k =
      if k < 0 then None
      else
        let l = String.trim text.(k) in
        let len = String.length l in
        if len > 2 && l.[0] = 'f' && l.[len - 1] = ':' then
          int_of_string_opt (String.sub l 1 (len - 2))
        else up (k - 1)
    in
    up (n - 1)
  in
  let ic = open_in log in
  let rejected = ref [] in
  (try
     while true do
       let l = input_line ic in
       (* file:line: Error: message -- `instruction' *)
       match String.split_on_char ':' l with
       | _ :: n :: kind :: msg when String.trim kind = "Error" -> (
           match int_of_string_opt (String.trim n) with
           | Some n -> (
               match form_of_line n with
               | Some i ->
                   let msg = String.trim (String.concat ":" msg) in
                   let msg =
                     match String.index_opt msg '`' with
                     | Some k when k > 4 -> String.sub msg 0 (k - 4)
                     | _ -> msg
                   in
                   rejected := (i, msg) :: !rejected
               | None -> ())
           | None -> ())
       | _ -> ()
     done
   with End_of_file -> close_in ic);
  List.rev !rejected

let output dir log =
  let forms = List.filter (fun f -> f.rows <> []) !forms in
  let forms =
    match log with
    | None -> forms
    | Some log ->
        let rejected = rejected_by_assembler forms log in
        List.iter
          (fun (i, msg) ->
            add_skip ~form:(List.nth forms i).text
              (Printf.sprintf
                 "the model accepts, the assembler rejects (%s)" msg))
          rejected;
        List.filteri (fun i _ -> not (List.mem_assoc i rejected)) forms
  in
  (* stubs.s *)
  let funcs = funcs_of forms in
  let oc = open_out (Filename.concat dir "stubs.s") in
  output_string oc (print_prog funcs);
  close_out oc;
  (* tables.c *)
  let oc = open_out (Filename.concat dir "tables.c") in
  let pr fmt = Printf.fprintf oc fmt in
  pr "/* Generated by gen_armv8m_hw_semantics.ml: do not edit.\n\n";
  pr "   Skipped:\n";
  pp_skips (fun s -> pr "   - %s\n" s);
  pr "*/\n\n#include \"runner.h\"\n\n";
  let data = Buffer.create (1 lsl 20) in
  let nwords = ref 0 in
  let word v =
    Buffer.add_string data (Printf.sprintf "0x%sU," (Z.format "%08x" v));
    incr nwords;
    if !nwords mod 8 = 0 then Buffer.add_char data '\n'
  in
  let nrows = ref 0 in
  let descrs =
    List.mapi
      (fun i f ->
        let regs = arg_regs f.args in
        let bases, _ = addr_regs f.args in
        let s0, s0' = List.hd f.rows in
        (* Registers that the instruction writes: the registers of the
           operands that are destinations. *)
        let outs =
          List.filter_map
            (fun (a : _ arg_desc) ->
              match a with
              | ADExplicit (_, k, _) -> (
                  match List.nth f.args (Conv.int_of_nat k) with
                  | Reg r -> Some r
                  | _ -> None)
              | ADImplicit (IAreg r) -> Some r
              | ADImplicit (IArflag _) -> None)
            f.idt.id_out
        in
        ignore s0;
        ignore s0';
        let mem = if has_addr f.args then 1 else 0 in
        let first = !nwords in
        List.iter
          (fun (s, s') ->
            incr nrows;
            List.iter (fun r -> word s.regs.(reg_index r)) regs;
            let fin, _ = flags_bits s.flags in
            let fout, fmask = flags_bits s'.flags in
            word (Z.of_int (fin lor (fout lsl 4) lor (fmask lsl 8)));
            List.iter (fun r -> word s'.regs.(reg_index r)) outs;
            if mem = 1 then (
              List.iter word (words_of_bytes s.mem);
              List.iter word (words_of_bytes s'.mem));
            (* The other registers must be unchanged. *)
            Array.iteri
              (fun k v ->
                let r = reg_of_index k in
                if (not (List.mem r outs)) && not (Z.equal v s'.regs.(k)) then
                  failwith
                    (Printf.sprintf "%s: the model writes r%d" f.text k))
              s.regs)
          f.rows;
        Printf.sprintf
          "  { %s, \"%s\", %d, 0x%04x, 0x%04x, 0x%04x, %d, %d },\n" (name i)
          (c_string f.text) (List.length f.rows) (reg_mask regs)
          (reg_mask outs) (reg_mask bases) mem first)
      forms
  in
  List.iteri (fun i _ -> pr "extern void %s(void);\n" (name i)) forms;
  pr "\nconst uint32_t test_data[] = {\n%s\n};\n\n" (Buffer.contents data);
  pr "const struct form test_forms[] = {\n";
  List.iter (pr "%s") descrs;
  pr "};\n\n";
  pr "const uint32_t test_nb_forms = %d;\n" (List.length forms);
  pr "const uint32_t test_nb_rows = %d;\n" !nrows;
  close_out oc;
  Printf.printf "%d instruction forms, %d rows, %d words of data\n"
    (List.length forms) !nrows !nwords;
  let mns =
    List.sort_uniq compare
      (List.map
         (fun f ->
           let (A.ARM_op (mn, _)) = f.op in
           A.string_of_arm_mnemonic mn)
         forms)
  in
  Printf.printf "%d mnemonics: %s\n" (List.length mns) (String.concat " " mns);
  pp_skips (Printf.printf "skipped: %s\n")

let () =
  let dir = if Array.length Sys.argv > 1 then Sys.argv.(1) else "gen" in
  let log = if Array.length Sys.argv > 2 then Some Sys.argv.(2) else None in
  ignore op_decl;
  enumerate ();
  List.iter gen_rows !forms;
  let rejected = List.filter (fun f -> f.rows = []) !forms in
  List.iter
    (fun f ->
      if not (List.exists (fun (_, l) -> List.mem f.text !l) !skips) then
        add_skip ~form:f.text
          "the semantics of the model is undefined for these operands")
    rejected;
  output dir log
