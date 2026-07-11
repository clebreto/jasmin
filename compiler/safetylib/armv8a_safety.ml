open Jasmin
open Utils
open Prog
open Apron
open Wsize
open Operators

open SafetyUtils
open SafetyExpr
open SafetyVar
open SafetyConstr
open SafetyArch
open SafetyAbsExpr

(** ARMv8-A (AArch64) architecture implementation.

    The precise cases below mirror [x86_safety.ml] and follow the Coq
    semantics of the instructions (armv8a_instr_decl.v). Whenever a
    hook or an operation is not listed, we keep the sound conservative
    default (the outputs are unknown, i.e. Top). *)
module Armv8a_safety
  (A: Arch_full.Arch
      with type reg = Armv8a_decl.register
       and type regx = Arch_utils.empty
       and type xreg = Arch_utils.empty
       and type rflag = Arm_common.rflag
       and type cond = Arm_common.condt
       and type asm_op = Armv8a_instr_decl.armv8a_asm_op
       and type extra_op = Armv8a_extra.armv8a_extra_op)
  : SafetyArch
    with type reg = Armv8a_decl.register
     and type regx = Arch_utils.empty
     and type xreg = Arch_utils.empty
     and type rflag = Arm_common.rflag
     and type cond = Arm_common.condt
     and type asm_op = Armv8a_instr_decl.armv8a_asm_op
     and type extra_op = Armv8a_extra.armv8a_extra_op
  = struct

  include A

  (* Beware: [Armv8a_instr_decl] shadows [Prog.E] (the [Expr] alias), so
     below we refer to [Expr] explicitly. *)
  open Armv8a_instr_decl

  (* -------------------------------------------------------------------- *)
  (* Return flags of the flag-setting operations, in the ARMv8-A output
     order [NF; ZF; CF; VF] (see [ad_nzcv] in armv8a_instr_decl.v).
     NF (result is negative) and VF (signed overflow) are not expressible
     as Jasmin expressions, so they are soundly set to Top. *)

  let zf_of_word sz w =
    Some (Papp2 (Oeq (Op_w sz),
                 w,
                 pcast sz (Pconst (Z.of_int 0))))

  (* Carry flag of an addition: set iff the truncated result differs from
     the unsigned integer result (a carry-out occurred). *)
  let cf_of_add sz w vu =
    Some (Papp2 (Oneq (Op_int),
                 Papp1 (Expr.uint_of_word sz, w),
                 vu))

  (* NZCV flags of ADDS and CMN ([nzcv_of_aluop] on an addition). *)
  let nzcv_of_add sz w vu =
    [ None;                     (* NF *)
      zf_of_word sz w;          (* ZF *)
      cf_of_add sz w vu;        (* CF *)
      None ]                    (* VF *)

  (* NZCV flags of SUBS and CMP. As on x86, we manually set the flags to
     have simpler and more precise expressions for the carry and zero
     flags. Beware: on ARM, the carry flag of a subtraction is "no
     borrow", i.e. [w1 >=u w2] (the opposite of the x86 convention). *)
  let nzcv_of_sub sz w1 w2 =
    [ None;                                                 (* NF *)
      Some (Papp2 (Oeq (Op_w sz), w1, w2));                 (* ZF *)
      Some (Papp2 (Oge (Cmp_w (Unsigned, sz)), w1, w2));    (* CF *)
      None ]                                                (* VF *)

  (* NZCV flags of the flag-setting logical operations (ANDS, BICS, TST):
     N and Z are computed from the result, C and V are cleared
     ([nzcv_of_logop] in armv8a_instr_decl.v). *)
  let nzcv_of_logop sz w =
    [ None;                     (* NF *)
      zf_of_word sz w;          (* ZF *)
      Some (Pbool false);       (* CF *)
      Some (Pbool false) ]      (* VF *)

  let opn_dflt n = List.init n (fun _ -> None)

  let opn_adds sz es =
    let el, er = as_seq2 es in
    let w = Papp2 (Oadd (Op_w sz), el, er) in
    let vu = Papp2 (Oadd Op_int,
                    Papp1 (Expr.uint_of_word sz, el),
                    Papp1 (Expr.uint_of_word sz, er)) in
    nzcv_of_add sz w vu @ [Some w]

  let opn_subs sz es =
    let el, er = as_seq2 es in
    let w = Papp2 (Osub (Op_w sz), el, er) in
    nzcv_of_sub sz el er @ [Some w]

  (* Value of a syntactically constant word expression. *)
  let rec constant_of_expr = function
    | Pconst c -> Some c
    | Papp1 (Oword_of_int _, e) -> constant_of_expr e
    | _ -> None

  (* Shift instructions (LSL, LSR, ASR, ROR) take the shift amount modulo
     the operand size (armv8a_shift_semi), while the Jasmin operators do
     not reduce the amount. We are precise only when the amount is a
     constant smaller than the operand size (where both semantics agree),
     and conservative otherwise. *)
  let opn_shift sz op2 es =
    let e1, e2 = as_seq2 es in
    match constant_of_expr e2 with
    | Some c when Z.leq Z.zero c && Z.lt c (Z.of_int (int_of_ws sz)) ->
      [Some (Papp2 (op2, e1, e2))]
    | _ -> [None]

  (* Zero-extension from [sz_i] to [sz_o] (same pattern as MOVZX on x86). *)
  let zero_ext sz_o sz_i e =
    if sz_o = sz_i then Some e
    else Some (Papp1 (Oword_of_int sz_o, Papp1 (Expr.uint_of_word sz_i, e)))

  (* -------------------------------------------------------------------- *)
  (* CMP, CMN and TST only produce flags: the flags are set from the
     operands, not from a destination register (which these instructions
     do not have). *)
  let is_comparison (opn : extended_op) : bool =
    match opn with
    | Arch_extra.BaseOp (_, ARMv8A_op ((CMP | CMN | TST), _)) -> true
    | _ -> false

  (* CSEL is a conditional move, like CMOVcc on x86. Note the argument
     order: the condition comes last ([mk_csel_instr]). *)
  let is_conditional lvs tag op es =
    match op with
    | Arch_extra.BaseOp (None, ARMv8A_op (CSEL, opts)) ->
      let el, er, c = as_seq3 es in
      let lv = as_seq1 lvs in
      let ty = Bty (U opts.opts_size) in
      let cl = [Cassgn (lv, tag, ty, el)] in
      let cr = [Cassgn (lv, tag, ty, er)] in
      Some (c, cl, cr)
    | _ -> None

  (* -------------------------------------------------------------------- *)
  (* Remark: the assignments must be done in the correct order.
     See armv8a_instr_decl.v for a description of the operators.

     We are only precise for the plain forms of the instructions:
     - [BaseOp (Some _, _)] changes the destination size, and
     - [has_shift = Some _] first shifts the last register operand
       ([mk_shifted]);
     in both cases we keep the conservative default.

     UDIV and SDIV are also left conservative: on ARMv8-A a division by
     zero returns 0, which the Jasmin division operators do not model. *)
  let split_asm_opn n (opn : extended_op) es =
    let dflt () =
      debug (fun () ->
          Format.eprintf "Warning: unknown opn %a, default to ⊤.@."
            (PrintCommon.pp_opn pointer_data msf_size asmOp) (Sopn.Oasm opn));
      opn_dflt n in

    match opn with
    (* swap of two registers *)
    | Arch_extra.ExtOp (Armv8a_extra.Oarmv8a_swap _) ->
      let x, y = as_seq2 es in
      [Some y; Some x]

    (* addition of a large immediate (in two instructions) *)
    | Arch_extra.ExtOp Armv8a_extra.Oarmv8a_add_large_imm ->
      let el, er = as_seq2 es in
      [Some (Papp2 (Oadd (Op_w U64), el, er))]

    (* load of an immediate (as a MOV/MOVZ/MOVN/MOVK sequence);
       the semantics is the identity *)
    | Arch_extra.ExtOp (Armv8a_extra.Oarmv8a_smart_li _) ->
      let e = as_seq1 es in
      [Some e]

    | Arch_extra.BaseOp
        (None, ARMv8A_op (mn, { has_shift = None; opts_size = sz })) ->
      begin match mn with
      (* copies *)
      | MOV ->
        let e = as_seq1 es in
        [Some e]

      (* arithmetic operations *)
      | ADD ->
        let el, er = as_seq2 es in
        [Some (Papp2 (Oadd (Op_w sz), el, er))]

      | SUB ->
        let el, er = as_seq2 es in
        [Some (Papp2 (Osub (Op_w sz), el, er))]

      | NEG ->
        let e = as_seq1 es in
        [Some (Papp1 (Oneg (Op_w sz), e))]

      | MUL ->
        let el, er = as_seq2 es in
        [Some (Papp2 (Omul (Op_w sz), el, er))]

      (* multiply-add and multiply-subtract: es = [wn; wm; wa] and the
         result is wa ± wn * wm *)
      | MADD ->
        let en, em, ea = as_seq3 es in
        [Some (Papp2 (Oadd (Op_w sz), ea, Papp2 (Omul (Op_w sz), en, em)))]

      | MSUB ->
        let en, em, ea = as_seq3 es in
        [Some (Papp2 (Osub (Op_w sz), ea, Papp2 (Omul (Op_w sz), en, em)))]

      (* flag-setting arithmetic operations *)
      | ADDS -> opn_adds sz es

      | SUBS -> opn_subs sz es

      (* comparisons: same flags as ADDS/SUBS/ANDS, without the result *)
      | CMP ->
        let el, er = as_seq2 es in
        nzcv_of_sub sz el er

      | CMN ->
        let el, er = as_seq2 es in
        let w = Papp2 (Oadd (Op_w sz), el, er) in
        let vu = Papp2 (Oadd Op_int,
                        Papp1 (Expr.uint_of_word sz, el),
                        Papp1 (Expr.uint_of_word sz, er)) in
        nzcv_of_add sz w vu

      | TST ->
        let el, er = as_seq2 es in
        nzcv_of_logop sz (Papp2 (Oland sz, el, er))

      (* bitwise operations *)
      | AND ->
        let el, er = as_seq2 es in
        [Some (Papp2 (Oland sz, el, er))]

      | ORR ->
        let el, er = as_seq2 es in
        [Some (Papp2 (Olor sz, el, er))]

      | EOR ->
        let el, er = as_seq2 es in
        [Some (Papp2 (Olxor sz, el, er))]

      | BIC ->
        let el, er = as_seq2 es in
        [Some (Papp2 (Oland sz, el, Papp1 (Olnot sz, er)))]

      | MVN ->
        let e = as_seq1 es in
        [Some (Papp1 (Olnot sz, e))]

      | ANDS ->
        let el, er = as_seq2 es in
        let w = Papp2 (Oland sz, el, er) in
        nzcv_of_logop sz w @ [Some w]

      | BICS ->
        let el, er = as_seq2 es in
        let w = Papp2 (Oland sz, el, Papp1 (Olnot sz, er)) in
        nzcv_of_logop sz w @ [Some w]

      (* shifts and rotation *)
      | LSL -> opn_shift sz (Olsl (Op_w sz)) es
      | LSR -> opn_shift sz (Olsr sz) es
      | ASR -> opn_shift sz (Oasr (Op_w sz)) es
      | ROR -> opn_shift sz (Oror sz) es

      (* conditional operations: es = [wn; wm; cond] resp. [cond] *)
      | CSEL ->
        let el, er, c = as_seq3 es in
        [Some (Pif (Bty (U sz), c, el, er))]

      | CSINC ->
        let el, er, c = as_seq3 es in
        let er1 = Papp2 (Oadd (Op_w sz), er, pcast sz (Pconst (Z.of_int 1))) in
        [Some (Pif (Bty (U sz), c, el, er1))]

      | CSINV ->
        let el, er, c = as_seq3 es in
        [Some (Pif (Bty (U sz), c, el, Papp1 (Olnot sz, er)))]

      | CSNEG ->
        let el, er, c = as_seq3 es in
        [Some (Pif (Bty (U sz), c, el, Papp1 (Oneg (Op_w sz), er)))]

      | CSET ->
        let c = as_seq1 es in
        [Some (Pif (Bty (U sz), c,
                    pcast sz (Pconst (Z.of_int 1)),
                    pcast sz (Pconst (Z.of_int 0))))]

      | CSETM ->
        let c = as_seq1 es in
        [Some (Pif (Bty (U sz), c,
                    pcast sz (Pconst (Z.of_int (-1))),
                    pcast sz (Pconst (Z.of_int 0))))]

      (* zero-extensions (the sign-extensions are left conservative) *)
      | UXTB -> [zero_ext sz U8 (as_seq1 es)]
      | UXTH -> [zero_ext sz U16 (as_seq1 es)]
      | UXTW -> [zero_ext sz U32 (as_seq1 es)]

      (* loads and stores: the memory access itself is performed by the
         surrounding expression or left-value; the instruction semantics
         only (zero-)extends the transferred value (the sign-extending
         loads are left conservative) *)
      | LDR | STR -> [Some (as_seq1 es)]
      | LDRB -> [zero_ext sz U8 (as_seq1 es)]
      | LDRH -> [zero_ext sz U16 (as_seq1 es)]
      | STRB | STRH -> [Some (as_seq1 es)]

      | _ -> dflt ()
      end

    | _ -> dflt ()

  (* Post-conditions of operators, that cannot be precisely expressed as an
     expression of the arguments: the results of the leading-bit counts
     CLZ and CLS are in the interval [0; size]. *)
  let post_opn opn lvs _es : btcons list =
    match opn with
    | Arch_extra.BaseOp (_, ARMv8A_op ((CLZ | CLS), opts)) -> (
        let open Mtexpr in
        match List.last lvs with
        | Lvar x ->
            let x = Mlocal (Avar (L.unloc x)) in
            [ BLeaf
                (Mtcons.make
                   (binop Sub (var x)
                      (cst (Coeff.i_of_int 0 (int_of_ws opts.opts_size))))
                   EQ) ]
        | _ -> [])
    | _ -> []

  (* Heuristic for the flags, used to find candidate decreasing quantities
     for the termination check (the candidates are verified afterwards, so
     this cannot compromise soundness).
     [v] is the variable receiving the assignment. *)
  let opn_heur (opn : extended_op) v es =
    match opn with
    (* flag-setting subtraction: ZF is set iff the result [v] is zero, and
       CF (no borrow) is cleared iff the minuend was smaller than the
       subtrahend, i.e. [v] wrapped around (same shape as DEC on x86) *)
    | Arch_extra.BaseOp (None, ARMv8A_op (SUBS, _)) ->
      Some { fh_zf = Some (Mtexpr.var v);
             fh_cf = Some (Mtexpr.binop Texpr1.Add
                             (Mtexpr.var v)
                             (Mtexpr.cst (Coeff.s_of_int 1))); }

    (* compare (without a shifted operand, so that es = [el; er]) *)
    | Arch_extra.BaseOp (None, ARMv8A_op (CMP, { has_shift = None; _ })) ->
      let exception Opn_heur_failed in
      let rec to_mvar = function
        | Pvar x ->
          check_is_word x;
          Mtexpr.var (mvar_of_var x)
        | Papp1 (Oword_of_int _, e) -> to_mvar e
        | Papp1 (Oint_of_word (s, _), e) ->
          assert (s = Signed); (* FIXME wint2 *)
          to_mvar e
        | _ -> raise Opn_heur_failed in
      let el, er = as_seq2 es in
      begin try
        let el, er = to_mvar el, to_mvar er in
        Some { fh_zf = Some (Mtexpr.binop Texpr1.Sub el er);
               fh_cf = Some (Mtexpr.binop Texpr1.Sub el er); }
      with Opn_heur_failed -> None end

    | _ ->
      debug (fun () ->
          Format.eprintf "No heuristic for the return flags of %a@."
            (PrintCommon.pp_opn pointer_data msf_size asmOp) (Sopn.Oasm opn));
      None

end
