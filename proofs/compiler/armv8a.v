(* ARMv8-A (AArch64) architecture: condition evaluation and [asm] instance. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import utils.
Require Import arch_decl.
Require Import
  armv8a_decl
  armv8a_instr_decl.

(* Evaluation of condition codes on the NZCV flags
   (ARM DDI 0487 M.a, C1.2.4 "Condition code"). *)
Definition armv8a_eval_cond (get : rflag -> result error bool) (c : condt) :
  result error bool :=
  match c with
  | EQ_ct =>
      get ZF
  | NE_ct =>
      Let zf := get ZF in ok (~~ zf)
  | CS_ct =>
      get CF
  | CC_ct =>
      Let cf := get CF in ok (~~ cf)
  | MI_ct =>
      get NF
  | PL_ct =>
      Let nf := get NF in ok (~~ nf)
  | VS_ct =>
      get VF
  | VC_ct =>
      Let vf := get VF in ok (~~ vf)
  | HI_ct =>
      Let cf := get CF in
      Let zf := get ZF in
      ok (cf && ~~ zf)
  | LS_ct =>
      Let cf := get CF in
      Let zf := get ZF in
      ok (~~ cf || zf)
  | GE_ct =>
      Let nf := get NF in
      Let vf := get VF in
      ok (nf == vf)
  | LT_ct =>
      Let nf := get NF in
      Let vf := get VF in
      ok (nf != vf)
  | GT_ct =>
      Let zf := get ZF in
      Let nf := get NF in
      Let vf := get VF in
      ok (~~ zf && (nf == vf))
  | LE_ct =>
      Let zf := get ZF in
      Let nf := get NF in
      Let vf := get VF in
      ok (zf || (nf != vf))
  end.

#[ export ]
Instance armv8a : asm register register_ext xregister rflag condt armv8a_asm_op :=
  {
    eval_cond := fun _ => armv8a_eval_cond;
  }.
