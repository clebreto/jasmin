From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.

Require Import
  arch_params
  compiler_util
  expr
  fexpr
  one_varmap.
Require Import
  register_zeroization
  linearization
  lowering
  stack_alloc.
Require Import
  arch_decl
  arch_extra
  asm_gen.
Require Import
  x86_decl
  x86_extra
  x86_instr_decl
  x86_lowering.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Used to set up stack. *)
Definition x86_op_align (x : var_i) (ws : wsize) (al : wsize) : fopn_args :=
  let f_to_lvar x := LLvar (VarI (to_var x) dummy_var_info) in
  let eflags := map f_to_lvar [:: OF; CF; SF; PF; ZF ] in
  let ex := Rexpr (Fvar x) in
  let emask := fconst ws (- wsize_size al) in
  (eflags ++ [:: LLvar x ], Ox86 (AND ws), [:: ex; Rexpr emask ]).

(* ------------------------------------------------------------------------ *)
(* Stack alloc parameters. *)

Definition lea_ptr x y tag ofs : instr_r :=
  Copn [:: x] tag (Ox86 (LEA Uptr)) [:: add y (cast_const ofs)].

Section IS_REGX.

Context (is_regx : var -> bool).

Variant mov_kind :=
  | MK_LEA
  | MK_MOV.

Definition mk_mov vpk :=
  match vpk with
  | VKglob _ | VKptr (Pdirect _ _ _ _ Sglob) => MK_LEA
  | _ => MK_MOV
  end.

Definition x86_mov_ofs x tag vpk y ofs :=
  let addr :=
    if mk_mov vpk is MK_LEA
    then
      lea_ptr x y tag ofs
    else
      if ofs == 0%Z
      then mov_ws is_regx Uptr x y tag
      else lea_ptr x y tag ofs
  in
  Some addr.

End IS_REGX.

Definition x86_saparams is_regx : stack_alloc_params :=
  {|
    sap_mov_ofs := x86_mov_ofs is_regx;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization parameters. *)

Section LINEARIZATION.

Notation vtmpi := {| v_var := to_var RAX; v_info := dummy_var_info; |}.

Definition x86_allocate_stack_frame (rspi: var_i) (sz: Z) :=
  let p := Fapp2 (Osub (Op_w Uptr)) (Fvar rspi) (fconst Uptr sz) in
  ([:: LLvar rspi ], Ox86 (LEA Uptr), [:: Rexpr p ]).

Definition x86_free_stack_frame (rspi: var_i) (sz: Z) :=
  let p := Fapp2 (Oadd (Op_w Uptr)) (Fvar rspi) (fconst Uptr sz) in
  ([:: LLvar rspi ], Ox86 (LEA Uptr), [:: Rexpr p ]).

(* TODO: consider using VMOVDQA when the address is known to be aligned *)
Definition x86_lassign (x: lexpr) (ws: wsize) (e: rexpr) :=
  let op := if (ws <= U64)%CMP
            then MOV ws
            else VMOVDQU ws
  in ([:: x ], Ox86 op, [:: e ]).

Definition x86_set_up_sp_register
  (rspi : var_i) (sf_sz : Z) (al : wsize) (r : var_i) : seq fopn_args :=
  let i0 := x86_lassign (LLvar r) Uptr (Rexpr (Fvar rspi)) in
  let i1 := x86_allocate_stack_frame rspi sf_sz in
  let i2 := x86_op_align rspi Uptr al in
  [:: i0; i1; i2 ].

Definition x86_set_up_sp_stack
  (rspi : var_i) (sf_sz : Z) (al : wsize) (off : Z) : seq fopn_args :=
  let vtmpg := Fvar vtmpi in
  let i := x86_lassign (Store Uptr rspi (fconst Uptr off)) Uptr (Rexpr vtmpg) in
  x86_set_up_sp_register rspi sf_sz al vtmpi ++ [:: i ].

Definition x86_liparams : linearization_params :=
  {|
    lip_tmp := vname (v_var vtmpi);
    lip_not_saved_stack := [::];
    lip_allocate_stack_frame := x86_allocate_stack_frame;
    lip_free_stack_frame := x86_free_stack_frame;
    lip_set_up_sp_register :=
      fun rspi sf_sz al r => Some (x86_set_up_sp_register rspi sf_sz al r);
    lip_set_up_sp_stack :=
      fun rspi sf_sz al off => Some (x86_set_up_sp_stack rspi sf_sz al off);
    lip_lassign := fun x ws e => Some (x86_lassign x ws e);
  |}.

End LINEARIZATION.

(* ------------------------------------------------------------------------ *)
(* Lowering parameters. *)

Definition x86_loparams : lowering_params fresh_vars lowering_options :=
  {|
    lop_lower_i := lower_i;
    lop_fvars_correct := fvars_correct;
  |}.


(* ------------------------------------------------------------------------ *)
(* Assembly generation parameters. *)

Definition not_condt (c : condt) :=
  match c with
  | O_ct => NO_ct
  | NO_ct => O_ct
  | B_ct => NB_ct
  | NB_ct => B_ct
  | E_ct => NE_ct
  | NE_ct => E_ct
  | BE_ct => NBE_ct
  | NBE_ct => BE_ct
  | S_ct => NS_ct
  | NS_ct => S_ct
  | P_ct => NP_ct
  | NP_ct => P_ct
  | L_ct => NL_ct
  | NL_ct => L_ct
  | LE_ct => NLE_ct
  | NLE_ct => LE_ct
  end.

Definition or_condt ii e c1 c2 : cexec condt :=
  match c1, c2 with
  | L_ct, E_ct => ok LE_ct
  | E_ct, L_ct => ok LE_ct
  | B_ct, E_ct => ok BE_ct
  | E_ct, B_ct => ok BE_ct
  | _, _ => Error (E.berror ii e "Invalid condition (OR)")
  end.

Definition and_condt ii e c1 c2 :=
  match c1, c2 with
  | NB_ct, NE_ct => ok NBE_ct
  | NE_ct, NB_ct => ok NBE_ct
  | NE_ct, NL_ct => ok NLE_ct
  | NL_ct, NE_ct => ok NLE_ct
  | _, _ => Error (E.berror ii e "Invalid condition (AND)")
  end.

Definition of_var_e_bool ii (v: var_i) : cexec rflag :=
  match of_var v with
  | Some r => ok r
  | None => Error (asm_gen.E.invalid_flag ii v)
  end.

Fixpoint assemble_cond_r ii (e : fexpr) : cexec condt :=
  match e with
  | Fvar v =>
      Let r := of_var_e_bool ii v in
      match r with
      | OF => ok O_ct
      | CF => ok B_ct
      | ZF => ok E_ct
      | SF => ok S_ct
      | PF => ok P_ct
      end

  | Fapp1 Onot e =>
      Let c := assemble_cond_r ii e in
      ok (not_condt c)

  | Fapp2 Oor e1 e2 =>
      Let c1 := assemble_cond_r ii e1 in
      Let c2 := assemble_cond_r ii e2 in
      or_condt ii e c1 c2

  | Fapp2 Oand e1 e2 =>
      Let c1 := assemble_cond_r ii e1 in
      Let c2 := assemble_cond_r ii e2 in
      and_condt ii e c1 c2

  | Fapp2 Obeq (Fvar x1) (Fvar x2) =>
      Let r1 := of_var_e_bool ii x1 in
      Let r2 := of_var_e_bool ii x2 in
      if ((r1 == SF) && (r2 == OF)) || ((r1 == OF) && (r2 == SF))
      then ok NL_ct
      else Error (E.berror ii e "Invalid condition (NL)")

  | _ => Error (E.berror ii e "don't known how to compile the condition")

  end.

Definition assemble_cond ii (e: fexpr) : cexec condt :=
  assemble_cond_r ii e.

Definition x86_agparams : asm_gen_params :=
  {|
    agp_assemble_cond := assemble_cond;
  |}.


(* ------------------------------------------------------------------------ *)
(* Register zeroization parameters. *)

Section REGISTER_ZEROIZATION.

Context {ovmi : one_varmap_info}.

Definition x86_zeroize_var
  (err_register : var -> pp_error_loc) (x : var) : cexec lopn_args :=
  if vtype x is sword ws
  then
    let op := if (ws <= U64)%CMP then MOV else VMOVDQU in
    let xi := {| v_var := x; v_info := dummy_var_info; |} in
    ok ([:: LLvar xi ], Ox86 (op ws), [:: Rexpr (fconst ws 0) ])
  else
    Error (err_register x).

Definition x86_zeroize_flags
  (err_flags : pp_error_loc) (ox : option var) : cexec (seq lopn_args) :=
  if ox is Some x
  then
    let xi := {| v_var := x; v_info := dummy_var_info; |} in
    let e := Rexpr (Fvar xi) in
    let to_lflag f := LLvar {| v_var := to_var f; v_info := dummy_var_info; |} in
    let lflags := map to_lflag [:: OF; CF; SF; PF; ZF ] in
    ok [:: (lflags, Ox86 (CMP reg_size), [:: e; e ]) ]
  else
    Error (err_flags).

Definition x86_rz_cmd_args
  (rzm : rzmode)
  (xs : seq var)
  (err_flags : pp_error_loc)
  (err_register : var -> pp_error_loc) :
  cexec (seq lopn_args) :=
  let f x := seq_diff x (Sv.elements one_varmap.callee_saved ++ xs) in
  let regs := if rzm_registers rzm then f (map to_var registers) else [::] in
  let xregs := if rzm_xregisters rzm then f (map to_var xregisters) else [::] in
  Let rzvars := mapM (x86_zeroize_var err_register) (regs ++ xregs) in
  Let rzflags :=
    if rzm_flags rzm then x86_zeroize_flags err_flags (ohead regs) else ok [::]
  in
  ok (rzvars ++ rzflags).

Definition x86_rzparams : register_zeroization_params :=
  {|
    rz_cmd_args := x86_rz_cmd_args;
  |}.

End REGISTER_ZEROIZATION.


(* ------------------------------------------------------------------------ *)
(* Shared parameters. *)

Definition x86_is_move_op (o : asm_op_t) :=
  match o with
  | BaseOp (None, MOV _) => true
  | BaseOp (None, VMOVDQA _) => true
  | BaseOp (None, VMOVDQU _) => true
  | _ => false
  end.

(* ------------------------------------------------------------------------ *)

Definition x86_params {ovmi : one_varmap_info} :
  architecture_params fresh_vars lowering_options :=
  {|
    ap_sap := x86_saparams;
    ap_lip := x86_liparams;
    ap_lop := x86_loparams;
    ap_agp := x86_agparams;
    ap_rzp := x86_rzparams;
    ap_is_move_op := x86_is_move_op;
  |}.
