open Allocation
open Arch_extra
open Arch_params
open Array_copy
open Array_expansion
open Array_init
open Compiler_util
open Dead_calls
open Dead_code
open Eqtype
open Expr
open Inline
open Lowering
open MakeReferenceArguments
open Propagate_inline
open Remove_globals
open Utils0
open Compiler
open Utils
open Prog
open Glob_options
open Utils

let unsharp = String.map (fun c -> if c = '#' then '_' else c)

module CL = struct

  type const = Z.t

  let pp_const fmt c = Format.fprintf fmt "%s" (Z.to_string c)

  type var = Prog.var

  let pp_var fmt x =
    Format.fprintf fmt "%s_%s" (unsharp x.v_name) (string_of_uid x.v_id)

  (* Expression over z *)

  module I = struct

    type eexp =
      | Iconst of const
      | Ivar   of var
      | Iunop  of string * eexp
      | Ibinop of eexp * string * eexp
      | Ilimbs of const * eexp list

    let (!-) e1 = Iunop ("-", e1)
    let (-) e1 e2 = Ibinop (e1, "-", e2)
    let (+) e1 e2 = Ibinop (e1, "+", e2)
    let mull e1 e2 = Ibinop (e1, "*", e2)
    let power e1 e2 = Ibinop (e1, "**", e2)

    let rec pp_eexp fmt e =
      match e with
      | Iconst c    -> pp_const fmt c
      | Ivar   x    -> pp_var   fmt x
      | Iunop(s, e) -> Format.fprintf fmt "(%s %a)" s pp_eexp e
      | Ibinop (e1, s, e2) -> Format.fprintf fmt "(%a %s %a)" pp_eexp e1 s pp_eexp e2
      | Ilimbs (c, es) ->
        Format.fprintf fmt  "(limbs %a [%a])"
          pp_const c
          (pp_list ",@ " pp_eexp) es

    type epred =
      | Eeq of eexp * eexp
      | Eeqmod of eexp * eexp * eexp list

    let pp_epred fmt ep =
      match ep with
      | Eeq(e1, e2) -> Format.fprintf fmt "(%a = %a)" pp_eexp e1 pp_eexp e2
      | Eeqmod(e1,e2, es) ->
        Format.fprintf fmt "(%a = %a (mod [%a]))"
          pp_eexp e1
          pp_eexp e2
          (pp_list ",@ " pp_eexp) es

    let pp_epreds fmt eps =
      if eps = [] then Format.fprintf fmt "true"
      else Format.fprintf fmt "/\\[@[%a@]]" (pp_list ",@ " pp_epred) eps

  end

  type ty = Uint of int | Sint of int (* Should be bigger than 1 *)

  let pp_ty fmt ty =
    match ty with
    | Uint i -> Format.fprintf fmt "uint%i" i
    | Sint i -> Format.fprintf fmt "sint%i" i

  let ty_ws ty =
    match ty with
    | Uint i -> i
    | Sint i -> i

  let pp_cast fmt ty = Format.fprintf fmt "@@%a" pp_ty ty

  type tyvar = var * ty

  let pp_tyvar fmt (x, ty) =
    Format.fprintf fmt "%a%a" pp_var x pp_cast ty

  let pp_tyvars fmt xs =
    Format.fprintf fmt "%a" (pp_list ",@ " pp_tyvar) xs

  (* Range expression *)
  module R = struct

    type rexp =
      | Rvar   of tyvar
      | Rconst of int * const
      | Ruext of rexp * int
      | Rsext of rexp * int
      | Runop  of string * rexp
      | Rbinop of rexp * string * rexp
      | Rpreop of string * rexp * rexp
      | Rlimbs of const * rexp list

    let const z1 z2 = Rconst(z1, z2)
    let (!-) e1 = Runop ("-", e1)
    let minu e1 e2 = Rbinop (e1, "-", e2)
    let add e1 e2 = Rbinop (e1, "+", e2)
    let mull e1 e2 = Rbinop (e1, "*", e2)
    let neg e1 = Runop ("neg", e1)
    let not e1 = Runop ("not", e1)
    let rand e1 e2 = Rbinop (e1, "and", e2)
    let ror e1 e2 = Rbinop (e1, "or", e2)
    let xor e1 e2 = Rbinop (e1, "xor", e2)
    let umod e1 e2 = Rpreop ("umod", e1, e2)
    let smod e1 e2 = Rpreop ("smod", e1, e2)
    let srem e1 e2 = Rpreop ("srem", e1, e2)
    let shl e1 e2 = Rpreop ("shl", e1, e2)
    let shr e1 e2 = Rpreop ("shr", e1, e2)
    let udiv e1 e2 = Rpreop ("udiv", e1, e2)

    let rec pp_rexp fmt r =
      match r with
      | Rvar x -> pp_tyvar fmt x
      | Rconst (c1, c2) -> Format.fprintf fmt "(const %i %a)" c1 pp_const c2
      | Ruext (e, c) -> Format.fprintf fmt "(uext %a %i)" pp_rexp e c
      | Rsext (e, c) -> Format.fprintf fmt "(sext %a %i)" pp_rexp e c
      | Runop(s, e) -> Format.fprintf fmt "(%s %a)" s pp_rexp e
      | Rbinop(e1, s, e2) ->  Format.fprintf fmt "(%a %s %a)" pp_rexp e1 s pp_rexp e2
      | Rpreop(s, e1, e2) -> Format.fprintf fmt "(%s %a %a)" s pp_rexp e1 pp_rexp e2
      | Rlimbs(c, es) ->
        Format.fprintf fmt  "(limbs %a [%a])"
          pp_const c
          (pp_list ",@ " pp_rexp) es

    type rpred =
      | RPcmp   of rexp * string * rexp
      | RPeqmod of rexp * rexp * string * rexp
      | RPnot   of rpred
      | RPand   of rpred list
      | RPor    of rpred list

    let eq e1 e2 = RPcmp (e1, "=", e2)
    let equmod e1 e2 e3 = RPeqmod (e1, e2, "umod", e3)
    let eqsmod e1 e2 e3 = RPeqmod (e1, e2, "smod", e3)
    let ult e1 e2 = RPcmp (e1, "<", e2)
    let ule e1 e2 = RPcmp (e1, "<=", e2)
    let ugt e1 e2 = RPcmp (e1, ">", e2)
    let uge e1 e2 = RPcmp (e1, ">=", e2)
    let slt e1 e2 = RPcmp (e1, "<s", e2)
    let sle e1 e2 = RPcmp (e1, "<=s", e2)
    let sgt e1 e2 = RPcmp (e1, ">s", e2)
    let sge e1 e2 = RPcmp (e1, ">=s", e2)

    let rec pp_rpred fmt rp =
      match rp with
      | RPcmp(e1, s, e2) -> Format.fprintf fmt "(%a %s %a)" pp_rexp e1 s pp_rexp e2
      | RPeqmod(e1, e2, s, e3) -> Format.fprintf fmt "(%a = %a (%s %a))" pp_rexp e1 pp_rexp e2 s pp_rexp e3
      | RPnot e -> Format.fprintf fmt "(~ %a)" pp_rpred e
      | RPand rps ->
        begin
          match rps with
          | [] -> Format.fprintf fmt "true"
          | [h] -> pp_rpred fmt h
          | h :: q -> Format.fprintf fmt "/\\[%a]" (pp_list ",@ " pp_rpred) rps
        end
      | RPor  rps -> Format.fprintf fmt "\\/[%a]" (pp_list ",@ " pp_rpred) rps

    let pp_rpreds fmt rps = pp_rpred fmt (RPand rps)

  end

  type clause = I.epred list * R.rpred list

  let pp_clause fmt (ep,rp) =
    Format.fprintf fmt "@[<hov 2>@[%a@] &&@ @[%a@]@]"
      I.pp_epreds ep
      R.pp_rpreds rp

  module Instr = struct

    type atom =
      | Aconst of const * ty
      | Avar of tyvar

    let pp_atom fmt a =
      match a with
      | Aconst (c, ty) -> Format.fprintf fmt "%a%a" pp_const c pp_cast ty
      | Avar tv -> pp_tyvar fmt tv

    let atome_ws a =
      match a with
      | Aconst (_, ty) -> ty_ws ty
      | Avar (_, ty ) -> ty_ws ty

    type lval = tyvar

    let lval_ws ((_,ty): lval) = ty_ws ty

    type arg =
      | Atom of atom
      | Lval of lval
      | Const of const
      | Ty    of ty
      | Pred of clause

    type args = arg list

    let pp_arg fmt a =
      match a with
      | Atom a  -> pp_atom fmt a
      | Lval tv -> pp_tyvar fmt tv
      | Const c -> pp_const fmt c
      | Ty ty   -> pp_ty fmt ty
      | Pred cl -> pp_clause fmt cl

    type instr =
      { iname : string;
        iargs : args; }

    let pp_instr fmt (i : instr) =
      Format.fprintf fmt "%s %a;"
        i.iname (pp_list " " pp_arg) i.iargs

    let pp_instrs fmt (is : instr list) =
      Format.fprintf fmt "%a" (pp_list "@ " pp_instr) is

    module Op1 = struct

      let op1 iname (d : lval) (s : atom) =
        { iname; iargs = [Lval d; Atom s] }

      let mov  = op1 "mov"
      let not  = op1 "not"

    end

    module Op2 = struct

      let op2 iname (d : lval) (s1 : atom) (s2 : atom) =
        { iname; iargs = [Lval d; Atom s1; Atom s2] }

      let add  = op2  "add"
      let sub  = op2  "sub"
      let mul  = op2  "mul"
      let seteq = op2 "seteq"
      let and_  = op2 "and"
      let xor  = op2  "xor"
      let mulj = op2  "mulj"
      let setne = op2 "setne"
      let or_   = op2 "or"
      let join = op2 "join"

    end

    module Op2c = struct

      let op2c iname (d : lval) (s1 : atom) (s2 : atom) (c : tyvar) =
        { iname; iargs = [Lval d; Atom s1; Atom s2; Atom (Avar c)] }

      let adc  = op2c  "adc"
      let sbc  = op2c  "sbc"
      let sbb  = op2c  "sbb"

    end

    module Op2_2 = struct

      let op2_2 iname (d1 : lval) (d2: lval) (s1 : atom) (s2 : atom) =
        { iname; iargs = [Lval d1; Lval d2; Atom s1; Atom s2] }

      let subc = op2_2 "subc"
      let mull = op2_2 "mull"
      let cmov = op2_2  "cmov"
      let adds = op2_2  "adds"
      let subb = op2_2  "subb"
      let muls = op2_2  "muls"

    end

    module Op2_2c = struct

      let op2_2c iname (d1 : lval) (d2: lval) (s1 : atom) (s2 : atom) (c : tyvar) =
        { iname; iargs = [Lval d1; Lval d2; Atom s1; Atom s2; Atom (Avar c)] }

      let adcs = op2_2c "adcs"
      let sbcs = op2_2c "sbcs"
      let sbbs = op2_2c "sbbs"

    end

    module Shift = struct

      let shift iname (d : lval) (s : atom) (c : const) =
        { iname; iargs = [Lval d; Atom s; Const c] }

      let shl  = shift "shl"
      let shr  = shift "shr"
      let sar  = shift "sar"

    end

    module Cshift = struct

      let cshift iname (d1 : lval) (d2 : lval) (s1 : atom) (s2 : atom) (c : const) =
        { iname; iargs = [Lval d1; Lval d2; Atom s1; Atom s2; Const c] }

      let cshl = cshift "cshl"
      let cshr = cshift "cshr"

    end

    module Shifts =  struct

      let shifts iname (d1 : lval) (d2 : lval) (s : atom) (c : const) =
        { iname; iargs = [Lval d1; Lval d2; Atom s; Const c] }

      let shls = shifts "shls"
      let shrs = shifts "shrs"
      let sars = shifts "sars"
      let spl = shifts "spl"
      let split = shifts "split"
      let ssplit = shifts "ssplit"

    end

    module Shift2s = struct

      let shift2s iname (d1 : lval) (d2 : lval) (d3 : lval) (s1 : atom) (s2 : atom) (c : const) =
        { iname; iargs = [Lval d1; Lval d2; Lval d3; Atom s1; Atom s2; Const c] }

      let cshls = shift2s "cshls"
      let cshrs = shift2s "cshrs"

    end

    let cast _ty (d : lval) (s : atom) =
      { iname = "cast"; iargs = [Lval d; Atom s] }

    let assert_ cl =
      { iname = "assert"; iargs = [Pred cl] }

    let cut ep rp =
      { iname = "cut"; iargs = [Pred(ep, rp)] }

    let vpc ty (d : lval) (s : atom) =
      { iname = "vpc"; iargs = [Ty ty; Lval d; Atom s] }

    let assume cl =
      { iname = "assume"; iargs  = [Pred cl] }

    (* nondet set rcut clear ecut ghost *)

  end

  module Proc = struct

    type proc =
      { id : string;
        formals : tyvar list;
        pre : clause;
        prog : Instr.instr list;
        post : clause;
      }

    let pp_proc fmt (proc : proc) =
      Format.fprintf fmt
        "@[<v>proc %s(@[<hov>%a@]) = @ {@[<v>@ %a@]@ }@ %a@ {@[<v>@ %a@]@ }@ @] "
        proc.id
        pp_tyvars proc.formals
        pp_clause proc.pre
        Instr.pp_instrs proc.prog
        pp_clause proc.post
  end
end

module I = struct

  let int_of_typ = function
    | Bty (U ws) -> int_of_ws ws
    | Bty (Bool) -> 1
    | Bty (Abstract ('/'::'*':: q)) -> String.to_int (String.of_list q)
    | _ -> assert false

  let rec gexp_to_rexp e : CL.R.rexp =
    let open CL.R in
    let to_rvar x =
      let var = L.unloc x.gv in
      Rvar (var, Uint (int_of_typ var.v_ty))
    in
    let (!>) e = gexp_to_rexp e in
    match e with
    | Papp1 (Oword_of_int ws, Pconst z) -> Rconst(int_of_ws ws, z)
    | Papp1 (Oword_of_int ws, Pvar x) -> Rvar (L.unloc x.gv, Uint (int_of_ws ws))
    | Pvar x -> to_rvar x
    | Papp1(Oneg _, e) -> neg !> e
    | Papp1(Olnot _, e) -> not !> e
    | Papp2(Oadd _, e1, e2) -> add !> e1 !> e2
    | Papp2(Osub _, e1, e2) -> minu !> e1 !> e2
    | Papp2(Omul _, e1, e2) -> mull !> e1 !> e2
    | Papp2(Odiv (Cmp_w (Unsigned,_)), e1, e2) -> udiv !> e1 !> e2
    (*   Format.fprintf fmt "udiv (%a) (%a)" *)
    (*     pp_rexp e1 *)
    (*     pp_rexp e2 *)
    (* | Papp2(Odiv (Cmp_w (Signed,_)), e1, e2) -> *)
    (*   Format.fprintf fmt "sdiv (%a) (%a)" *)
    (*     pp_rexp e1 *)
    (*     pp_rexp e2 *)
    | Papp2(Olxor _, e1, e2) -> xor !> e1 !> e2
    | Papp2(Oland _, e1, e2) -> rand !> e1 !> e2
    | Papp2(Olor _, e1, e2) -> ror !> e1 !> e2
    | Papp2(Omod (Cmp_w (Unsigned,_)), e1, e2) -> umod !> e1 !> e2
    | Papp2(Omod (Cmp_w (Signed,_)), e1, e2) -> smod !> e1 !> e2
    | Papp2(Olsl _, e1, e2) ->  shl !> e1 !> e2
    | Papp2(Olsr _, e1, e2) ->  shr !> e1 !> e2
    | Papp1(Ozeroext (osz,isz), e1) -> Ruext (!> e1, (int_of_ws osz) - (int_of_ws isz))
    | Pabstract ({name="se_16_64"}, [v]) -> Rsext (!> v, 48)
    | Pabstract ({name="se_32_64"}, [v]) -> Rsext (!> v, 32)
    | Pabstract ({name="ze_16_64"}, [v]) -> Ruext (!> v, 48)
    | Presult x -> to_rvar x
    | _ -> assert false

  let rec gexp_to_rpred e : CL.R.rpred =
    let open CL.R in
    let (!>) e = gexp_to_rexp e in
    let (!>>) e = gexp_to_rpred e in
    match e with
    | Pbool (true) -> RPand []
    | Papp1(Onot, e) -> RPnot (!>> e)
    | Papp2(Oeq _, e1, e2) -> eq !> e1 !> e2
    | Papp2(Obeq, e1, e2)  -> eq !> e1 !> e2
    | Papp2(Oand, e1, e2)  -> RPand [!>> e1; !>> e2]
    | Papp2(Oor, e1, e2)  -> RPor [!>> e1; !>> e2]
    | Papp2(Ole (Cmp_w (Signed,_)), e1, e2)  -> sle !> e1 !>e2
    | Papp2(Ole (Cmp_w (Unsigned,_)), e1, e2)  -> ule !> e1 !> e2
    | Papp2(Olt (Cmp_w (Signed,_)), e1, e2)  -> slt !> e1 !> e2
    | Papp2(Olt (Cmp_w (Unsigned,_)), e1, e2)  -> ult !> e1 !> e2
    | Papp2(Oge (Cmp_w (Signed,_)), e1, e2)  -> sge !> e1 !> e2
    | Papp2(Oge (Cmp_w (Unsigned,_)), e1, e2)  -> uge !> e1 !> e2
    | Papp2(Ogt (Cmp_w (Signed,_)), e1, e2)  -> sgt !> e1 !> e2
    | Papp2(Ogt (Cmp_w (Unsigned,_)), e1, e2)  -> ugt !> e1 !> e2
    | Pif(_, e1, e2, e3) -> RPand [RPor [RPnot !>> e1; !>> e2];RPor[ !>> e1; !>> e3]]
    | Pabstract ({name="eqsmod64"}, [e1;e2;e3]) -> eqsmod !> e1 !> e2 !> e3
    | Pabstract ({name="equmod64"}, [e1;e2;e3]) -> equmod !> e1 !> e2 !> e3
    | _ ->  assert false

  let rec extract_list e aux =
    match e with
    | Pabstract ({name="couple"}, [h;q]) -> [h;q]
    | Pabstract ({name="word_nil"}, []) -> List.rev aux
    | Pabstract ({name="word_cons"}, [h;q]) -> extract_list q (h :: aux)
    | _ -> assert false

  let rec gexp_to_eexp e : CL.I.eexp =
    let open CL.I in
    let (!>) e = gexp_to_eexp e in
    match e with
    | Pconst z -> Iconst z
    | Pvar x -> Ivar (L.unloc x.gv)
    | Papp1 (Oword_of_int _ws, x) -> !> x
    | Papp1 (Oint_of_word _ws, x) -> !> x
    | Papp1(Oneg _, e) -> !- !> e
    | Papp2(Oadd _, e1, e2) -> !> e1 + !> e2
    | Papp2(Osub _, e1, e2) -> !> e1 - !> e2
    | Papp2(Omul _, e1, e2) -> mull !> e1 !> e2
    | Pabstract ({name="limbs"}, [h;q]) ->
      begin
        match !> h with
        | Iconst c -> Ilimbs (c, (List.map (!>) (extract_list q [])))
        | _ -> assert false
      end
    (* | Pabstract ({name="indetX"}, _) -> *)
    (*   Format.fprintf fmt "X" *)
    | Pabstract ({name="pow"}, [b;e]) -> power !> b !> e
    | Presult x -> Ivar (L.unloc x.gv)
    | _ -> assert false

  let rec gexp_to_epred e : CL.I.epred list =
    let open CL.I in
    let (!>) e = gexp_to_eexp e in
    let (!>>) e = gexp_to_epred e in
    match e with
    | Papp2(Oeq _, e1, e2)  -> [Eeq (!> e1, !> e2)]
    | Papp2(Oand, e1, e2)  -> !>> e1 @ !>> e2
    | Pabstract ({name="eqmod"} as _opa, [h1;h2;h3]) ->
      [Eeqmod (!> h1, !> h2, List.map (!>) (extract_list h3 []))]
    | _ -> assert false

  let var_to_tyvar ?(sign=false) v : CL.tyvar =
    if sign then v, CL.Sint (int_of_typ v.v_ty)
    else v, CL.Uint (int_of_typ v.v_ty)

  let mk_tmp_lval ?(name = "TMP____") ?(l = L._dummy)
      ?(kind = (Wsize.Stack Direct)) ?(sign=false)
      ty : CL.Instr.lval =
    let v = CoreIdent.GV.mk name kind ty l [] in
    var_to_tyvar ~sign v

  let mk_spe_tmp_lval ?(name = "TMP____") ?(l = L._dummy)
      ?(kind = (Wsize.Stack Direct)) ?(sign=false)
      size =
    let size = String.to_list (String.of_int size) in
    mk_tmp_lval ~name ~l ~kind ~sign (Bty(Abstract ('/'::'*':: size)))

  let glval_to_lval x : CL.Instr.lval =
    match x with
    | Lvar v -> var_to_tyvar (L.unloc v)
    | Lnone (l,ty)  ->
      let name = "NONE____" in
      mk_tmp_lval ~name ~l ty
    | Lmem _ | Laset _ | Lasub _ -> assert false

  let gexp_to_var x : CL.tyvar =
    match x with
    | Pvar x -> var_to_tyvar (L.unloc x.gv)
    | _ -> assert false

  let gexp_to_const x : CL.const * CL.ty =
    match x with
    | Papp1 (Oword_of_int ws, Pconst c) -> (c, CL.Uint (int_of_ws ws))
    | _ -> assert false

  let mk_const c : CL.const = Z.of_int c

  let mk_const_atome ws c = CL.Instr.Aconst (c, CL.Uint ws)

  let gexp_to_atome x : CL.Instr.atom =
    match x with
    | Pvar _ -> Avar (gexp_to_var x)
    | Papp1 (Oword_of_int _, Pconst _) ->
      let c,ty = gexp_to_const x in
      Aconst (c,ty)
    | _ -> assert false

  let mk_lval_atome lval = CL.Instr.Avar (lval)

  let rec get_const x =
    match x with
    | Pconst z -> Z.to_int z
    | Papp1 (Oword_of_int _ws, x) -> get_const x
    | _ -> assert false
end

let rec power acc n = match n with | 0 -> acc | n -> power (acc * 2) (n - 1)

module type BaseOp = sig
  type op
  type extra_op

  val op_to_instr :
    Expr.assertion_prover ->
    int Prog.glval list ->
    op -> int Prog.gexpr list -> CL.Instr.instr list

  val assgn_to_instr :
    Expr.assertion_prover ->
    int Prog.glval -> int Prog.gexpr -> CL.Instr.instr list

end

module X86BaseOp : BaseOp
  with type op = X86_instr_decl.x86_op
  with type extra_op = X86_extra.x86_extra_op
= struct

  type op = X86_instr_decl.x86_op
  type extra_op = X86_extra.x86_extra_op

  let cast_atome ws x =
    match x with
    | Pvar va ->
      let ws_x = ws_of_ty (L.unloc va.gv).v_ty in

      if ws = ws_x then I.gexp_to_atome x,[]
      else
        let v = L.unloc va.gv in
        let kind = v.v_kind in
        let e = I.gexp_to_atome x in
        let (_,ty) as x = I.mk_tmp_lval ~kind (CoreIdent.tu ws) in
        CL.Instr.Avar x, [CL.Instr.cast ty x e]
    | Papp1 (Oword_of_int ws_x, Pconst z) ->
      if ws = ws_x then I.gexp_to_atome x,[]
      else
        let e = I.gexp_to_atome x in
        let (_,ty) as x = I.mk_tmp_lval (CoreIdent.tu ws) in
        CL.Instr.Avar x, [CL.Instr.cast ty x e]
    | _ -> assert false

  let assgn_to_instr trans x e =
    let a = I.gexp_to_atome e in
    let l = I.glval_to_lval x in
    [CL.Instr.Op1.mov l a]

  let op_to_instr trans xs o es =

    let (!) e = I.mk_lval_atome e in

    match o with
    | X86_instr_decl.MOV ws ->
      let a,i = cast_atome ws (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 0) in
      i @ [CL.Instr.Op1.mov l a]

    | ADD ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2,i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i1 @ i2 @ [CL.Instr.Op2.add l a1 a2]

    | SUB ws ->
      begin
        let a1, i1 = cast_atome ws (List.nth es 0) in
        let a2, i2 = cast_atome ws (List.nth es 1) in
        let l = I.glval_to_lval (List.nth xs 5) in
        match trans with
        | Smt ->
          i1 @ i2 @ [CL.Instr.Op2.sub l a1 a2]
        | Cas ->
          let l_tmp = I.mk_spe_tmp_lval 1 in
          i1 @ i2 @ [CL.Instr.Op2_2.subb l_tmp l a1 a2]
      end

    | IMULr ws ->
      let a1, i1 = cast_atome ws (List.nth es 0) in
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
      let l_tmp = I.mk_tmp_lval (CoreIdent.tu ws) in
      i1 @ i2 @ [CL.Instr.Op2_2.mull l_tmp l a1 a2]

    | IMULri ws ->
      let a1, i1 = cast_atome ws (List.nth es 0) in
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
      let l_tmp = I.mk_tmp_lval (CoreIdent.tu ws) in
      i1 @ i2 @ [CL.Instr.Op2_2.mull l_tmp l a1 a2]

    | ADC ws ->
      let a1, i1 = cast_atome ws (List.nth es 0) in
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let l1 = I.glval_to_lval (List.nth xs 1) in
      let l2 = I.glval_to_lval (List.nth xs 5) in
      let v = I.gexp_to_var (List.nth es 2) in
      i1 @ i2 @ [CL.Instr.Op2_2c.adcs l1 l2 a1 a2 v]

    | SBB ws ->
      let a1, i1 = cast_atome ws (List.nth es 0) in
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let l1 = I.glval_to_lval (List.nth xs 1) in
      let l2 = I.glval_to_lval (List.nth xs 5) in
      let v = I.gexp_to_var (List.nth es 2) in
      i1 @ i2 @ [CL.Instr.Op2_2c.sbbs l1 l2 a1 a2 v]

    | NEG ws ->
      let a1 = I.mk_const_atome (int_of_ws ws) Z.zero in
      let a2,i2 = cast_atome ws (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 4) in
      i2 @ [CL.Instr.Op2.sub l a1 a2]

    | INC ws ->
      let a1 = I.mk_const_atome (int_of_ws ws) Z.one in
      let a2,i2 = cast_atome ws (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 4) in
      i2 @ [CL.Instr.Op2.add l a1 a2]

    | DEC ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2 = I.mk_const_atome (int_of_ws ws) Z.one in
      let l = I.glval_to_lval (List.nth xs 4) in
      i1 @ [CL.Instr.Op2.sub l a1 a2]

    | AND ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2,i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i1 @ i2 @ [CL.Instr.Op2.and_ l a1 a2]

    | ANDN ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2,i2 = cast_atome ws (List.nth es 1) in
      let l_tmp = I.mk_tmp_lval (CoreIdent.tu ws) in
      let at = I.mk_lval_atome l_tmp in
      let l = I.glval_to_lval (List.nth xs 5) in
      i1 @ i2 @ [CL.Instr.Op1.not l_tmp a1; CL.Instr.Op2.and_ l a2 at]

    | OR ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2,i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i1 @ i2 @ [CL.Instr.Op2.or_ l a1 a2]

    | XOR ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2,i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i1 @ i2 @ [CL.Instr.Op2.xor l a1 a2]

    | NOT ws ->
      let a,i = cast_atome ws (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i @ [CL.Instr.Op1.not l a]

    | SHL ws ->
      begin
        match trans with
        | Smt ->
          let a, i = cast_atome ws (List.nth es 0) in
          let (c,_) = I.gexp_to_const(List.nth es 1) in
          let l = I.glval_to_lval (List.nth xs 5) in
          i @ [CL.Instr.Shift.shl l a c]
        | Cas ->
          let a, i = cast_atome ws (List.nth es 0) in
          let g = (List.nth es 1) in
          let (c,_) = I.gexp_to_const g in
          let l = I.glval_to_lval (List.nth xs 5) in
          let l_tmp = I.mk_spe_tmp_lval (I.get_const g) in
          i @ [CL.Instr.Shifts.shls l_tmp l a c]
      end

    | SHR ws ->
      let a, i = cast_atome ws (List.nth es 0) in
      let (c,_) = I.gexp_to_const(List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i @ [CL.Instr.Shift.shr l a c]

    (* | SAL ws -> *)
    (*   (\* FIXME the type of second argument is wrong *\) *)
    (*   Format.fprintf fmt "shl %a %a %a" *)
    (*     pp_lval (List.nth xs 5, int_of_ws ws) *)
    (*     pp_atome (List.nth es 0, int_of_ws ws) *)
    (*     I.pp_const (List.nth es 1) *)

    | SAR ws ->
      begin
        match trans with
        | Smt ->
          let a,i = cast_atome ws (List.nth es 0) in
          let sign = true in
          let l_tmp1 = I.mk_tmp_lval ~sign (CoreIdent.tu ws) in
          let ty1 = CL.Sint (int_of_ws ws) in
          let (c,_) = I.gexp_to_const(List.nth es 1) in
          let l_tmp2 = I.mk_tmp_lval ~sign (CoreIdent.tu ws) in
          let l_tmp3 = I.mk_tmp_lval (CoreIdent.tu ws) in
          let ty2 = CL.Uint (int_of_ws ws) in
          let l = I.glval_to_lval (List.nth xs 5) in
          i @ [CL.Instr.cast ty1 l_tmp1 a;
               CL.Instr.Shifts.ssplit l_tmp2 l_tmp3 !l_tmp1 c;
               CL.Instr.cast ty2 l !l_tmp2]
        | Cas ->
          let a1,i1 = cast_atome ws (List.nth es 0) in
          let c1 = I.mk_const (int_of_ws ws - 1) in
          let l_tmp1 = I.mk_spe_tmp_lval 1 in
          let l_tmp2 = I.mk_spe_tmp_lval (int_of_ws ws - 1) in
          let c = I.get_const (List.nth es 1) in
          let a2 = I.mk_const_atome (c + 1) Z.zero in
          let l_tmp3 = I.mk_spe_tmp_lval (c + 1) in
          let a3 = I.mk_const_atome (c + 1) (Z.of_int (power 1 (c + 1) - 1)) in
          let l_tmp4 = I.mk_spe_tmp_lval (c + 1) in
          let l_tmp5 = I.mk_spe_tmp_lval (c + int_of_ws ws) in
          let c2 = Z.of_int c in
          let l_tmp6 = I.mk_spe_tmp_lval c in
          let l = I.glval_to_lval (List.nth xs 5) in
          i1 @ [CL.Instr.Shifts.spl l_tmp1 l_tmp2 a1 c1;
                CL.Instr.Op2.join l_tmp3 a2 !l_tmp1;
                CL.Instr.Op2.mul l_tmp4 !l_tmp3 a3;
                CL.Instr.Op2.join l_tmp5 !l_tmp4 !l_tmp2;
                CL.Instr.Shifts.spl l l_tmp6 !l_tmp5 c2
               ]
      end

    | MOVSX (ws1, ws2) ->
      begin
        match trans with
        | Smt ->
          let a,i = cast_atome ws2 (List.nth es 0) in
          let sign = true in
          let l_tmp1 = I.mk_tmp_lval ~sign (CoreIdent.tu ws2) in
          let ty1 = CL.Sint (int_of_ws ws2) in
          let l_tmp2 = I.mk_tmp_lval ~sign (CoreIdent.tu ws1) in
          let ty2 = CL.Sint (int_of_ws ws1) in
          let l = I.glval_to_lval (List.nth xs 0) in
          let ty3 = CL.Uint (int_of_ws ws1) in
          i @ [CL.Instr.cast ty1 l_tmp1 a;
               CL.Instr.cast ty2 l_tmp2 !l_tmp1;
               CL.Instr.cast ty3 l !l_tmp2]
        | Cas ->
          let a,i = cast_atome ws2 (List.nth es 0) in
          let c = Z.of_int (int_of_ws ws2 - 1) in
          let l_tmp1 = I.mk_spe_tmp_lval 1 in
          let l_tmp2 = I.mk_spe_tmp_lval (int_of_ws ws2 - 1) in
          let diff = int_of_ws ws1 - (int_of_ws ws2) in
          let a2 = I.mk_const_atome (diff - 1) Z.zero in
          let l_tmp3 = I.mk_spe_tmp_lval diff in
          let a3 =
            I.mk_const_atome diff (Z.of_int ((power 1 diff) - 1))
          in
          let l_tmp4 = I.mk_spe_tmp_lval diff in
          let l = I.glval_to_lval (List.nth xs 0) in
          i @ [CL.Instr.Shifts.spl l_tmp1 l_tmp2 a c;
               CL.Instr.Op2.join l_tmp3 a2 !l_tmp1;
               CL.Instr.Op2.mul l_tmp4 !l_tmp3 a3;
               CL.Instr.Op2.join l !l_tmp4 a;
              ]
      end
    | MOVZX (ws1, ws2) -> 
          let a,i = cast_atome ws2 (List.nth es 0) in
          let l = I.glval_to_lval (List.nth xs 0) in
          let ty = CL.Uint (int_of_ws ws1) in
          i @ [CL.Instr.cast ty l a]
    | _ -> assert false

end

module ARMBaseOp : BaseOp
  with type op = Arm_instr_decl.arm_op
   and  type extra_op = Arm_extra.__
= struct

  open Arm_instr_decl

  type op = Arm_instr_decl.arm_op
  type extra_op = Arm_extra.__

  let ws = Wsize.U32

  let assgn_to_instr trans x e = assert false

  let op_to_instr trans xs o es =
    let mn, opt = match o with Arm_instr_decl.ARM_op (mn, opt) -> mn, opt in
    match mn with
    | ADD -> assert false
(*
      let v1 = pp_cast fmt (List.nth es 0, ws) in
      let v2 = pp_cast fmt (List.nth es 1, ws) in
      let v2' = pp_shifted fmt opt v2 es in
      Format.fprintf fmt "add %a %a %a"
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_atome (v1, int_of_ws ws)
        pp_atome (v2', int_of_ws ws)
*)

    | ADC
    | MUL
    | MLA
    | MLS
    | SDIV
    | SUB
    | RSB
    | UDIV
    | UMULL
    | UMAAL
    | UMLAL
    | SMULL
    | SMLAL
    | SMMUL
    | SMMULR
    | SMUL_hw _
    | SMLA_hw _
    | SMULW_hw _
    | AND
    | BFC
    | BFI
    | BIC
    | EOR
    | MVN
    | ORR
    | ASR
    | LSL
    | LSR
    | ROR
    | REV
    | REV16
    | REVSH
    | ADR
    | MOV
    | MOVT
    | UBFX
    | UXTB
    | UXTH
    | SBFX
    | CLZ
    | CMP
    | TST
    | CMN
    | LDR
    | LDRB
    | LDRH
    | LDRSB
    | LDRSH
    | STR
    | STRB
    | STRH -> assert false

end

module Mk(O:BaseOp) = struct

  let pp_ext_op xs o es trans =
    match o with
    | Arch_extra.BaseOp (_, o) -> O.op_to_instr trans xs o es
    | Arch_extra.ExtOp o -> assert false

  let pp_sopn xs o es tcas =
    match o with
    | Sopn.Opseudo_op _ -> assert false
    | Sopn.Oslh _ -> assert false
    | Sopn.Oasm o -> pp_ext_op xs o es tcas

  let rec filter_clause cs (cas,smt) =
    match cs with
    | [] -> cas,smt
    | (Expr.Cas,c)::q -> filter_clause q (c::cas,smt)
    | (Expr.Smt,c)::q -> filter_clause q (cas,c::smt)

  let to_clause clause : CL.clause =
    let cas,smt = filter_clause clause ([],[]) in
    match cas,smt with
    | [],[] -> [], []
    | [],smt -> [], List.fold_left (fun acc a -> I.gexp_to_rpred a ::  acc) [] smt
    | cas,[] -> List.fold_left (fun acc a -> I.gexp_to_epred a @ acc) [] cas, []
    | _,_ -> List.fold_left (fun acc a -> I.gexp_to_epred a @ acc) [] cas,
             List.fold_left (fun acc a -> I.gexp_to_rpred a ::  acc) [] smt

  let pp_i fds i =
    let mk_trans = Annot.filter_string_list None ["smt", Smt ; "cas", Cas ] in
    let atran annot =
      match Annot.ensure_uniq1 "tran" mk_trans annot with
      | None -> Smt
      | Some aty -> aty
    in
    let trans = atran i.i_annot in
    match i.i_desc with
    | Cassert (t, p, e) ->
      let cl : CL.clause =
        match p with
        | Expr.Cas -> I.gexp_to_epred  e, []
        | Expr.Smt -> [], [I.gexp_to_rpred  e]
      in
      begin
        match t with
        | Expr.Assert -> [CL.Instr.assert_ cl]
        | Expr.Assume -> [CL.Instr.assume cl]
        | Expr.Cut -> assert false
      end
    | Csyscall _ | Cif _ | Cfor _ | Cwhile _ -> assert false
    | Ccall (r,f,params) ->
      let fd = List.find (fun fd -> fd.f_name.fn_id = f.fn_id) fds in
      let aux f =
        List.map (fun (prover,clause) -> prover, f clause)
      in
      let check v vi=
        (L.unloc v.gv).v_name = vi.v_name && (L.unloc v.gv).v_id = vi.v_id
      in
      let aux1 v =
        match List.findi (fun _ vi -> check v vi) fd.f_args with
        | i,_ ->  let _,e = List.findi (fun ii _ -> ii = i) params in
          e
        | exception _ ->
          begin
            match List.findi (fun _ vi -> check v (L.unloc vi)) fd.f_ret with
            | i,_ ->  let _,e = List.findi (fun ii _ -> ii = i) r in
              begin
                match e with
                | Lvar v ->  Pvar({gv = v; gs = Expr.Slocal})
                | _ ->  Pvar v
              end
            | exception _ ->  Pvar v
          end
      in
      let aux2 = Subst.gsubst_e (fun x -> x) aux1 in
      let pre = aux aux2 fd.f_contra.f_pre in
      let post = aux aux2  fd.f_contra.f_post in
      let pre_cl = to_clause pre in
      let post_cl = to_clause post in
      [CL.Instr.assert_ pre_cl;CL.Instr.assume post_cl]

    | Cassgn (a, _, _, e) ->
      begin
        match a with
        | Lvar x -> O.assgn_to_instr trans a e
        | Lnone _ | Lmem _ | Laset _ |Lasub _ -> assert false
      end
    | Copn(xs, _, o, es) -> pp_sopn xs o es trans

  let pp_c fds c =
    List.fold_left (fun acc a -> acc @ pp_i fds a) [] c

  let fun_to_proc fds fd =
    let ret = List.map L.unloc fd.f_ret in
    let args = List.fold_left (
        fun l a ->
          if List.exists (fun x -> (x.v_name = a.v_name) && (x.v_id = a.v_id)) l
          then l else a :: l
      ) fd.f_args ret in
    let formals = List.map I.var_to_tyvar args in
    let pre = to_clause fd.f_contra.f_pre in
    let prog = pp_c fds fd.f_body in
    let post = to_clause fd.f_contra.f_post in
    CL.Proc.{id = fd.f_name.fn_name;
             formals;
             pre;
             prog;
             post}
end
