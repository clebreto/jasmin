(* Semantic correctness of the ARMv8-A core operation builders
   ([ARMv8AFopn_core], armv8a_params_core.v), mirroring
   [arm_params_core_proof.v].

   Proven here: the [sem_fopn_args] lemmas for the single-instruction builders
   used by the compiler's stack handling and immediate materialization —
   [add], [addi], [sub], [subi], [mov], [andi] (the AND behind [align]) — and
   the [smart_mov] combinator.

   Deferred: [li] (and the [gen_smart_opi]/[smart_addi]/[smart_subi]
   combinators built on it). Unlike ARMv7-M, which materializes a 32-bit
   immediate with a fixed MOV/MOVT pair (two 16-bit halves, cf.
   [arm_params_core_proof.li_lsem_1]), the AArch64 [li] emits a variable-length
   MOVZ/MOVN/MOVK sequence over up to four 16-bit halves of a 64-bit register.
   Its correctness needs bit-level lemmas about that decomposition that do not
   port from the ARMv7-M proof; it is left as future work. *)

From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.

Require Import
  arch_params
  compiler_util
  expr
  fexpr
  fexpr_sem
  linear
  linear_sem
  linear_facts
  psem.
Require Import
  arch_decl
  arch_sem.

Require Import
  armv8a_decl
  armv8a_instr_decl
  armv8a_params_core.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Module ARMv8AFopn_coreP.

Section Section.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}.

#[local] Existing Instance withsubword.

Definition sem_fopn_args (p : seq lexpr * armv8a_asm_op * seq rexpr) (s : estate) :=
  let: (xs,o,es) := p in
  Let args := sem_rexprs s es in
  let op := instr_desc_op o in
  Let _ := assert (id_valid op) ErrType in
  Let t := app_sopn (map eval_ltype (id_tin op)) (id_semi op) args in
  let res := list_ltuple t in
  write_lexprs xs res s.

Definition sem_fopns_args := foldM sem_fopn_args.

Ltac t_armv8a_op :=
  rewrite /sem_fopn_args /get_gvar /=;
  t_simpl_rewrites;
  rewrite /= /with_vm /=;
  repeat rewrite truncate_word_u /=;
  rewrite ?zero_extend_u ?addn1;
  t_simpl_rewrites.

Lemma add_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} {z} {wz : word Uptr} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  get_var true (evm s) (v_var z) >>= to_word Uptr = ok wz ->
  let: wx' := Vword (wy + wz)in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMv8AFopn_core.add xi y z) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_armv8a_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma addi_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (wy + wrepr reg_size imm)in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMv8AFopn_core.addi xi y imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_armv8a_op.
  by rewrite /= set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma sub_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} {z} {wz : word Uptr} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  get_var true (evm s) (v_var z) >>= to_word Uptr = ok wz ->
  let: wx' := Vword (wy - wz)in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMv8AFopn_core.sub xi y z) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_armv8a_op.
  by rewrite /= /armv8a_SUB_semi sub_wordE set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma subi_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (wy - wrepr reg_size imm)in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMv8AFopn_core.subi xi y imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_armv8a_op.
  by rewrite /= /armv8a_SUB_semi sub_wordE set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma mov_sem_fopn_args {s} {xi:var_i} {y} {wy : word Uptr} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: vm' := (evm s).[xi <- Vword wy] in
  sem_fopn_args (ARMv8AFopn_core.mov xi y) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_armv8a_op.
  by rewrite /= /armv8a_MOV_semi set_var_truncate // (convertible_eval_atype hc).
Qed.

Lemma andi_sem_fopn_args {s} {xi:var_i} {y imm wy} :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  get_var true (evm s) (v_var y) >>= to_word Uptr = ok wy ->
  let: wx' := Vword (wand wy (wrepr reg_size imm)) in
  let: vm' := (evm s).[xi <- wx'] in
  sem_fopn_args (ARMv8AFopn_core.andi xi y imm) s = ok (with_vm s vm').
Proof.
  move=> hc.
  rewrite /=; t_xrbindP => *; t_armv8a_op.
  by rewrite /= /armv8a_bitwise_semi set_var_truncate // (convertible_eval_atype hc).
Qed.

Opaque ARMv8AFopn_core.add.
Opaque ARMv8AFopn_core.addi.
Opaque ARMv8AFopn_core.mov.
Opaque ARMv8AFopn_core.sub.
Opaque ARMv8AFopn_core.subi.
Opaque ARMv8AFopn_core.andi.

Lemma smart_mov_sem_fopns_args s (w : word armv8a_reg_size) (xi:var_i) y :
  convertible xi.(vtype) (aword armv8a_reg_size) ->
  let: lc := ARMv8AFopn_core.smart_mov xi y in
  get_var true (evm s) y >>= to_word Uptr = ok w ->
  exists vm,
    [/\ sem_fopns_args s lc = ok (with_vm s vm)
      , vm =[\ Sv.singleton xi ] evm s
      & get_var true vm xi >>= to_word Uptr = ok w ].
Proof.
  move=> hc hgety.
  rewrite /ARMv8AFopn_core.smart_mov /=.
  case: eqP => heq /=.
  - case : y heq hgety=> y yi /= *; subst y.
    rewrite -{1}(with_vm_same s); eexists; split; eauto.
  rewrite (mov_sem_fopn_args _ hgety) //=.
  eexists; split; first reflexivity.
  + by move=> z /Sv.singleton_spec hz; t_vm_get.
  by rewrite get_var_eq /= (convertible_eval_atype hc) //= truncate_word_u.
Qed.

End Section.

End ARMv8AFopn_coreP.
