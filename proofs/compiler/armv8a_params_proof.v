(* Correctness of the ARMv8-A architecture parameters, mirroring
   [arm_params_proof.v].

   Proven so far: the stack-alloc hypotheses ([armv8a_hsaparams]) and the
   linearization hypotheses ([armv8a_hliparams]), together with the
   scratch-register facts and the (trivial) lower-addressing hypotheses.

   Still missing before the [h_architecture_params] record can be built:
   the lowering proof (armv8a_lowering_proof.v), the assembly-generation
   hypotheses (condition evaluation and the [assemble_extra] lemmas for
   [Oarmv8a_swap], [Oarmv8a_add_large_imm] and [Oarmv8a_smart_li]) and the
   stack-zeroization proof. *)
From Coq Require Import Relations.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat finfun.
From mathcomp Require Import ssralg.
From mathcomp Require Import word_ssrZ.

Require Import oseq.

Require Import
  arch_params_proof
  compiler_util
  expr
  fexpr
  fexpr_sem
  psem
  psem_facts
  sem_one_varmap.
Require Import
  lea_proof
  linearization
  linearization_proof
  lowering
  stack_alloc_params_proof
  stack_zeroization_proof.
Require
  arch_sem.
Require Import
  arch_decl
  arch_extra
  asm_gen
  asm_gen_proof
  sem_params_of_arch_extra.
Require Import
  armv8a_decl
  armv8a_extra
  armv8a_instr_decl
  armv8a
  armv8a_params_core
  armv8a_params_core_proof
  armv8a_params_common_proof.
Require Export armv8a_params.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Section Section.

#[local] Existing Instance withsubword.
#[local] Existing Instance direct_c.

Context
  {atoI  : arch_toIdent}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {call_conv : calling_convention}.

(* ------------------------------------------------------------------------ *)
(* Stack alloc hypotheses. *)

Section STACK_ALLOC.

Lemma shift_of_scaleP scale shift w :
  shift_of_scale scale = Some shift ->
  wshl w (wunsigned (wrepr U8 (Z.of_nat shift))) = (wrepr Uptr scale * w)%R.
Proof.
  by case: scale => // -[|[|[|[]|]|]|] //= [<-]; rewrite wshl_sem /=.
Qed.

Lemma armv8a_mov_ofsP : mov_ofs_correct armv8a_saparams.(sap_mov_ofs).
Proof.
  move=> P' ev s1 e w ofs pofs x tag mk ii ins s2 P'_globs.
  t_xrbindP=> ve ok_ve ok_w vofs ok_vofs ok_pofs.
  rewrite /sap_mov_ofs /= /armv8a_mov_ofs.
  case: mk.
  + move=> [<-] hw; exists (evm s2) => //.
    rewrite with_vm_same.
    rewrite /sem_sopn /= P'_globs /exec_sopn.
    case: is_zeroP.
    + move=> hofs.
      rewrite ok_ve /= ok_w /=.
      move: hofs ok_vofs ok_pofs hw => -> /=.
      rewrite /sem_sop1 /= => -[<-] /=.
      rewrite truncate_word_u wrepr0 => -[<-].
      by rewrite GRing.addr0 => -> /=.
    move=> _ /=.
    rewrite ok_ve ok_vofs /= /sem_sop2 /= ok_w ok_pofs /= truncate_word_u /=.
    by rewrite hw.
  case: x => //.
  + move=> x_; set x := Lvar x_.
    case: ifP => _.
    + case: is_zeroP => // hofs [<-] hw; exists (evm s2) => //.
      rewrite with_vm_same.
      rewrite /sem_sopn /= P'_globs /exec_sopn ok_ve /= ok_w /= zero_extend_u.
      move: hofs ok_vofs ok_pofs hw => -> /=.
      rewrite /sem_sop1 /= => -[<-] /=.
      rewrite truncate_word_u wrepr0 => -[<-].
      by rewrite GRing.addr0 => -> /=.
    case hlea: mk_lea => [[disp base scale offset]|//] /=.
    case: base hlea => [base|//] hlea.
    have lea_sem: sem_pexpr true [::] s1 (add e ofs) = ok (Vword (w + pofs)).
    + by rewrite /= ok_ve ok_vofs /= /sem_sop2 /= ok_w ok_pofs /=.
    have /(_ (cmp_le_refl _)) /(_ (cmp_le_refl _)) := mk_leaP _ _ hlea lea_sem.
    rewrite zero_extend_u /sem_lea /=.
    (* t_xrbindP too aggressive *)
    apply: rbindP => wb.
    apply: rbindP => vb ok_vb ok_wb.
    apply: rbindP => wo ok_wo.
    move=> /ok_inj; rewrite GRing.addrC => {}lea_sem.
    case: offset {hlea} ok_wo => [offset|] /=.
    + t_xrbindP=> vo ok_vo ok_wo.
      case: eqP => // ?; subst disp.
      case hshift: shift_of_scale => [shift|//] /=.
      case: eqP => [heq|_].
      + move=> [<-] hw.
        exists (evm s2) => //.
        rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb ok_vo /=
          /exec_sopn /= ok_wb ok_wo /=.
        have := shift_of_scaleP wo hshift.
        rewrite heq wrepr0 wunsigned0 wshl_sem //= wrepr1 GRing.mul1r => ->.
        rewrite /armv8a_ADD_semi ?add_wordE.
        move: lea_sem; rewrite wrepr0 GRing.addr0 => ->.
        by rewrite hw /= with_vm_same.
      move=> [<-] hw.
      exists (evm s2) => //.
      rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb ok_vo /=
        /exec_sopn /= ok_wb ok_wo truncate_word_u /=.
      rewrite (shift_of_scaleP wo hshift).
      rewrite /armv8a_ADD_semi ?add_wordE.
      move: lea_sem; rewrite wrepr0 GRing.addr0 => ->.
      by rewrite hw /= with_vm_same.
    move=> [?]; subst wo.
    case: eqP => [|_].
    + move=> ?; subst disp.
      move=> [<-] hw.
      exists s2.(evm) => //.
      rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb /=
        /exec_sopn /= ok_wb /=.
      move: lea_sem; rewrite wrepr0 GRing.mulr0 !GRing.addr0 => ->.
      by rewrite hw /= with_vm_same.
    case: ifP => _.
    + move=> [<-] hw.
      exists s2.(evm) => //.
      rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb /=
        /exec_sopn /= ok_wb truncate_word_u /=.
        rewrite /armv8a_ADD_semi ?add_wordE.
      move: lea_sem; rewrite GRing.mulr0 GRing.addr0 => ->.
      by rewrite hw /= with_vm_same.
    move=> [<-] hw.
    exists s2.(evm) => //.
    rewrite /sem_sopn P'_globs /= /get_gvar /= ok_vb /=
      /exec_sopn /= ok_wb truncate_word_u /=.
    rewrite /armv8a_ADD_semi ?add_wordE.
    move: lea_sem; rewrite GRing.mulr0 GRing.addr0 => ->.
    by rewrite hw /= with_vm_same.
  move=> al ws_ x_ e_; move: (Lmem al ws_ x_ e_) => {al ws_ x_ e_} x.
  case: is_zeroP => // hofs [<-] hw; exists (evm s2) => //.
  rewrite with_vm_same.
  rewrite /sem_sopn /= P'_globs /exec_sopn ok_ve /= ok_w /= zero_extend_u.
  move: hofs ok_vofs ok_pofs hw => -> /=.
  rewrite /sem_sop1 /= => -[<-] /=.
  rewrite truncate_word_u wrepr0 => -[<-].
  by rewrite GRing.addr0 => -> /=.
Qed.

Lemma armv8a_immediateP : immediate_correct armv8a_saparams.(sap_immediate).
Proof.
  move=> P' ev s ii x z hty.
  rewrite /= /sem_sopn /= /exec_sopn /= truncate_word_u /=.
  by rewrite /write_var set_var_eq_type ?hty.
Qed.

Lemma armv8a_swapP : swap_correct armv8a_saparams.(sap_swap).
Proof.
  move=> P' ev s ii tag x y z w pz pw hxty hyty hzty hwty hz hw.
  rewrite /= /sem_sopn /= /get_gvar /= /get_var /= hz hw /=.
  rewrite /exec_sopn /= !truncate_word_u /= /write_var /set_var /=.
  rewrite (convertible_eval_atype hxty) (convertible_eval_atype hyty) //=.
Qed.

End STACK_ALLOC.

Definition armv8a_hsaparams :
  h_stack_alloc_params (ap_sap armv8a_params) :=
  {|
    mov_ofsP := armv8a_mov_ofsP;
    sap_immediateP := armv8a_immediateP;
    sap_swapP := armv8a_swapP;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

Lemma convertible_rsp : convertible (aword Uptr) (aword armv8a_reg_size).
Proof. by vm_compute. Qed.

Lemma sem_fopns_args_1 s (a : fopn_args) :
  sem_fopns_args s [:: a ] = sem_fopn_args a s.
Proof. by rewrite /sem_fopns_args /=; case: sem_fopn_args. Qed.

Lemma armv8a_spec_lip_allocate_stack_frame :
  allocate_stack_frame_correct armv8a_liparams.
Proof.
  move=> sp_rsp tmp s ts sz htmp hget /=.
  rewrite /armv8a_allocate_stack_frame.
  case: tmp htmp => [tmp [h1 h2]| _].
  + have [? [-> ? /get_varP [-> _ _]]] := [elaborate
      ARMv8AFopnP.smart_subi_tmp_sem_fopn_args
        (xi := vid sp_rsp) sz convertible_rsp h1 h2 (to_word_get_var hget)
    ].
    by eexists.
  rewrite sem_fopns_args_1
    (ARMv8AFopnP.subi_sem_fopn_args (xi := vid sp_rsp) convertible_rsp
       (to_word_get_var hget)).
  eexists; split; first reflexivity.
  + move=> z hz; rewrite Vm.setP_neq //.
    by apply/eqP => heq; apply: hz; rewrite -heq; apply/Sv.add_spec; left.
  by rewrite Vm.setP_eq vm_truncate_val_eq.
Qed.

Lemma armv8a_spec_lip_free_stack_frame :
  free_stack_frame_correct armv8a_liparams.
Proof.
  move=> sp_rsp tmp s ts sz htmp hget /=.
  rewrite /armv8a_free_stack_frame.
  case: tmp htmp => [tmp [h1 h2]| _].
  + have [? [-> ? /get_varP [-> _ _]]] := [elaborate
      ARMv8AFopnP.smart_addi_tmp_sem_fopn_args
        (xi := vid sp_rsp) sz convertible_rsp h1 h2 (to_word_get_var hget)
    ].
    by eexists.
  rewrite sem_fopns_args_1
    (ARMv8AFopnP.addi_sem_fopn_args (xi := vid sp_rsp) convertible_rsp
       (to_word_get_var hget)).
  eexists; split; first reflexivity.
  + move=> z hz; rewrite Vm.setP_neq //.
    by apply/eqP => heq; apply: hz; rewrite -heq; apply/Sv.add_spec; left.
  by rewrite Vm.setP_eq vm_truncate_val_eq.
Qed.

Lemma armv8a_spec_lip_set_up_sp_register :
  set_up_sp_register_correct armv8a_liparams.
Proof.
  Opaque sem_fopn_args.
  move=> vrsp r tmp ts al sz s hget htyrsp htyr htytmp hnetr hner hnert /=.
  rewrite /armv8a_set_up_sp_register sem_fopns_args_cat /=.
  set ts' := align_word _ _.
  have := ARMv8AFopnP.smart_subi_sem_fopn_args
            (xi := tmp) (y := vrsp) (imm := sz) _ _ (to_word_get_var hget).
  move=> [] //.
  + by rewrite htytmp.
  + by right.
  move=> vm1 [] -> heq1 hget1 /=.
  set s1 := with_vm _ _.
  have -> /= := ARMv8AFopnP.align_sem_fopn_args
                 (xi := tmp) (y := tmp) (al := al) (s := s1)
                 _ (to_word_get_var hget1).
  + set s2 := with_vm _ _.
    have hget2 : get_var true (evm s2) vrsp = ok (Vword ts).
    + rewrite get_var_neq; last by [].
      rewrite (get_var_eq_ex _ _ heq1); first by [].
      by apply: Sv_neq_not_in_singleton.
    have -> /= := ARMv8AFopnP.mov_sem_fopn_args (xi := r) _ (to_word_get_var hget2).
    + set s3 := with_vm _ _.
      have hget3 : get_var true (evm s3) tmp = ok (Vword ts').
      + by t_get_var => /=; rewrite htytmp /=.
      have -> /= := ARMv8AFopnP.mov_sem_fopn_args (xi := vrsp) _ (to_word_get_var hget3).
      + set s4 := with_vm _ _.
        Transparent sem_fopn_args.
        eexists; split => //.
        - move=> x; t_notin_add; t_vm_get; rewrite heq1; first by t_vm_get.
          by apply/Sv_neq_not_in_singleton/nesym.
        - by t_get_var => /=; rewrite htyrsp /=.
        - by t_get_var => /=; rewrite (convertible_eval_atype htyr) /=.
        move=> x hx _.
        move: hx => /vflagsP hxtype.
        have [*] : [/\ v_var vrsp <> x, v_var tmp <> x & v_var r <> x].
        - split; apply/eqP/vtype_diff; rewrite hxtype //.
          + by rewrite htyrsp.
          + by rewrite htytmp.
          by apply /eqP => /= h; move: htyr; rewrite h.
        t_vm_get; rewrite heq1 //.
        by apply: Sv_neq_not_in_singleton.
      by rewrite htyrsp.
    by rewrite htyr.
  by rewrite htytmp.
Qed.

Lemma armv8a_lmove_correct : lmove_correct armv8a_liparams.
Proof.
  move=> xd xs w ws w' s htxd htxs hget htr.
  rewrite /armv8a_liparams /lip_lmove /armv8a_lmove /= hget /=.
  rewrite /exec_sopn /= htr /=.
  by rewrite set_var_eq_type ?htxd.
Qed.

Lemma armv8a_lstore_correct : lstore_correct_aux armv8a_check_ws armv8a_lstore.
Proof.
  move=> xd xs ofs ws w wp s m htxs /eqP hchk; t_xrbindP; subst ws.
  move=> vd hgetd htrd vs hgets htrs hwr.
  rewrite /armv8a_lstore /= hgets hgetd /= /exec_sopn /= htrs /=.
  rewrite /sem_sop2 /= htrd /= !truncate_word_u /= truncate_word_u /=.
  by rewrite zero_extend_u hwr.
Qed.

Lemma armv8a_smart_addi_correct : ladd_imm_correct_aux ARMv8AFopn_smart_addi.
Proof.
  move=> x1 x2 s w ofs hty hne hget.
  apply: ARMv8AFopnP.smart_addi_sem_fopn_args hget => //; last by right.
  by rewrite hty.
Qed.

Lemma armv8a_lstores_correct : lstores_correct armv8a_liparams.
Proof.
  apply/lstores_imm_dfl_correct.
  + by apply armv8a_lstore_correct.
  apply armv8a_smart_addi_correct.
Qed.

Lemma armv8a_lload_correct :
  lload_correct_aux (lip_check_ws armv8a_liparams) armv8a_lload.
Proof.
  move=> xd xs ofs ws top s w vm heq hcheck; t_xrbindP => ? hgets hto hread hset.
  move/eqP: hcheck => ?; subst ws.
  rewrite /armv8a_lload /= hgets /= /sem_sop2 /= hto /= !truncate_word_u /=
    truncate_word_u /= hread /=.
  by rewrite /exec_sopn /= truncate_word_u /= zero_extend_u hset.
Qed.

Lemma armv8a_tmp_correct : lip_tmp armv8a_liparams <> lip_tmp2 armv8a_liparams.
Proof. by move=> h; assert (h1 := inj_to_ident h). Qed.

Lemma armv8a_check_ws_correct : lip_check_ws armv8a_liparams Uptr.
Proof. done. Qed.

(* Missing for [h_linearization_params]: [lloads_correct] for the custom
   [armv8a_lloads] (which restores the saved stack pointer through the
   scratch register X17 and a MOV, since an A64 LDR cannot target SP). *)

End LINEARIZATION.

Lemma armv8a_ok_lip_tmp :
  exists r : reg_t, of_ident (lip_tmp (ap_lip armv8a_params)) = Some r.
Proof. exists R16; exact: to_identK. Qed.

Lemma armv8a_ok_lip_tmp2 :
  exists r : reg_t, of_ident (lip_tmp2 (ap_lip armv8a_params)) = Some r.
Proof. exists R17; exact: to_identK. Qed.

(* ------------------------------------------------------------------------ *)
(* Lowering of complex addressing mode for RISC-V.
   It is the identity on armv8a, so the proof is trivial. *)

Lemma armv8a_hlaparams : h_lower_addressing_params (ap_lap armv8a_params).
Proof.
  split=> /=.
  + by move=> _ ? _ [<-].
  + move=> _ ? _ [<-] _ fd ->; by exists fd.
  + by move=> _ ? _ [<-].
  move=> ???? _ ? _ ?? [<-]; exact: (wiequiv_f_eq (scP := sCP_stack)).
Qed.

End Section.
