(* ARMv8-A (AArch64) architecture declaration.

 * Description of the A64 base architecture (no SIMD/FP, no extensions).
 * General-purpose registers are modeled at their full 64-bit width (X
 * registers); instructions come in 64-bit (X) and 32-bit (W) forms.
 *)
From elpi.apps Require Import derive.std.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype ssralg.
From mathcomp Require Import word_ssrZ.

Require Import
  expr
  flag_combination
  sem_type
  shift_kind
  strings
  utils
  wsize
  word.

Require Import
  arch_decl
  arch_utils.

(* --------------------------------------------- *)
Definition armv8a_reg_size  := U64.
Definition armv8a_xreg_size := U128.

(* -------------------------------------------------------------------- *)
(* Registers.
   [R0]..[R30] are the general-purpose registers X0..X30.
   [RZR] is the zero register XZR and [RSP] the stack pointer SP; both use
   register encoding 31, the instruction determines which one is meant. *)

#[only(eqbOK)] derive
Variant register : Type :=
| R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7
| R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
| R16 | R17 | R18
| R19 | R20 | R21 | R22 | R23 | R24
| R25 | R26 | R27 | R28
| R29                           (* Frame pointer. *)
| R30                           (* Link register. *)
| RZR                           (* Zero register. *)
| RSP.                          (* Stack pointer. *)

#[ export ]
Instance eqTC_register : eqTypeC register :=
  { ceqP := register_eqb_OK }.

Canonical armv8a_register_eqType := @ceqT_eqType _ eqTC_register.

Definition registers :=
  [:: R0; R1; R2; R3; R4; R5; R6; R7;
      R8; R9; R10; R11; R12; R13; R14; R15;
      R16; R17; R18;
      R19; R20; R21; R22; R23; R24;
      R25; R26; R27; R28;
      R29; R30; RZR; RSP ].

Lemma register_fin_axiom : Finite.axiom registers.
Proof. by case. Qed.

#[ export ]
Instance finTC_register : finTypeC register :=
  {
    cenum  := registers;
    cenumP := register_fin_axiom;
  }.

Canonical register_finType := @cfinT_finType _ finTC_register.

Definition register_to_string (r : register) : string :=
  match r with
  | R0 => "x0"   | R1 => "x1"   | R2 => "x2"   | R3 => "x3"
  | R4 => "x4"   | R5 => "x5"   | R6 => "x6"   | R7 => "x7"
  | R8 => "x8"   | R9 => "x9"   | R10 => "x10" | R11 => "x11"
  | R12 => "x12" | R13 => "x13" | R14 => "x14" | R15 => "x15"
  | R16 => "x16" | R17 => "x17" | R18 => "x18"
  | R19 => "x19" | R20 => "x20" | R21 => "x21" | R22 => "x22"
  | R23 => "x23" | R24 => "x24" | R25 => "x25" | R26 => "x26"
  | R27 => "x27" | R28 => "x28"
  | R29 => "x29" | R30 => "x30"
  | RZR => "xzr"
  | RSP => "sp"
  end.

#[ export ]
Instance reg_toS : ToString (lword armv8a_reg_size) register :=
  {| category  := "register"
   ; to_string := register_to_string
  |}.

(* -------------------------------------------------------------------- *)
(* Flags. *)

#[only(eqbOK)] derive
Variant rflag : Type :=
| NF    (* Negative condition flag. *)
| ZF    (* Zero condition flag. *)
| CF    (* Carry condition flag. *)
| VF.   (* Overflow condition flag. *)

#[ export ]
Instance eqTC_rflag : eqTypeC rflag :=
  { ceqP := rflag_eqb_OK }.

Canonical rflag_eqType := @ceqT_eqType _ eqTC_rflag.

Definition rflags := [:: NF; ZF; CF; VF ].

Lemma rflag_fin_axiom : Finite.axiom rflags.
Proof. by case. Qed.

#[ export ]
Instance finTC_rflag : finTypeC rflag :=
  { cenum := rflags; cenumP := rflag_fin_axiom }.

Canonical rflag_finType := @cfinT_finType _ finTC_rflag.

Definition flag_to_string (f : rflag) : string :=
  match f with
  | NF => "NF"
  | ZF => "ZF"
  | CF => "CF"
  | VF => "VF"
  end.

#[ export ]
Instance rflag_toS : ToString lbool rflag :=
  { category  := "rflag"
  ; to_string := flag_to_string
  }.

(* -------------------------------------------------------------------- *)
(* Conditions.
   Condition codes for conditional instructions (ARM ARM DDI0487 M.a,
   section C1.2.4 "Condition code"). *)

#[only(eqbOK)] derive
Variant condt : Type :=
| EQ_ct    (* Equal (Z == 1). *)
| NE_ct    (* Not equal (Z == 0). *)
| CS_ct    (* Carry set, unsigned higher or same (C == 1). *)
| CC_ct    (* Carry clear, unsigned lower (C == 0). *)
| MI_ct    (* Minus, negative (N == 1). *)
| PL_ct    (* Plus, positive or zero (N == 0). *)
| VS_ct    (* Overflow (V == 1). *)
| VC_ct    (* No overflow (V == 0). *)
| HI_ct    (* Unsigned higher (C == 1 && Z == 0). *)
| LS_ct    (* Unsigned lower or same (C == 0 || Z == 1). *)
| GE_ct    (* Signed greater than or equal (N == V). *)
| LT_ct    (* Signed less than (N != V). *)
| GT_ct    (* Signed greater than (Z == 0 && N == V). *)
| LE_ct.   (* Signed less than or equal (Z == 1 || N != V). *)

#[ export ]
Instance eqTC_condt : eqTypeC condt :=
  { ceqP := condt_eqb_OK }.

Canonical condt_eqType := @ceqT_eqType _ eqTC_condt.

Definition condts : seq condt :=
  [:: EQ_ct; NE_ct; CS_ct; CC_ct; MI_ct; PL_ct; VS_ct; VC_ct; HI_ct; LS_ct
    ; GE_ct; LT_ct; GT_ct; LE_ct
  ].

Lemma condt_fin_axiom : Finite.axiom condts.
Proof. by case. Qed.

#[ export ]
Instance finTC_condt : finTypeC condt :=
  {
    cenum := condts;
    cenumP := condt_fin_axiom;
  }.

Canonical condt_finType := @cfinT_finType _ finTC_condt.

Definition string_of_condt (c : condt) : string :=
  match c with
  | EQ_ct => "eq"
  | NE_ct => "ne"
  | CS_ct => "cs"
  | CC_ct => "cc"
  | MI_ct => "mi"
  | PL_ct => "pl"
  | VS_ct => "vs"
  | VC_ct => "vc"
  | HI_ct => "hi"
  | LS_ct => "ls"
  | GE_ct => "ge"
  | LT_ct => "lt"
  | GT_ct => "gt"
  | LE_ct => "le"
  end.

(* -------------------------------------------------------------------- *)
(* Register shifts.
 * Data-processing (shifted register) instructions can shift a register
 * operand before performing the operation. The shift amount ranges over
 * 0..63 for 64-bit operands and 0..31 for 32-bit operands. *)

#[ export ]
Instance eqTC_shift_kind : eqTypeC shift_kind :=
  { ceqP := shift_kind_eqb_OK }.

Canonical shift_kind_eqType := @ceqT_eqType _ eqTC_shift_kind.

Definition shift_kinds :=
  [:: SLSL; SLSR; SASR; SROR ].

Definition string_of_shift_kind (sk : shift_kind) : string :=
  match sk with
  | SLSL => "lsl"
  | SLSR => "lsr"
  | SASR => "asr"
  | SROR => "ror"
  end.

Definition check_shift_amount (ws : wsize) (z : Z) : bool :=
  (0 <=? z)%Z && (z <? wsize_bits ws)%Z.

Definition shift_op (sk : shift_kind) :
  forall (sz : wsize), word sz -> Z -> word sz :=
  match sk with
  | SLSL => wshl
  | SLSR => wshr
  | SASR => wsar
  | SROR => wror
  end.

Definition shift_of_sop2 (ws : wsize) (op : sop2) : option shift_kind :=
  let%opt _ := oassert ((ws == U64) || (ws == U32)) in
  match op with
  | Olsl (Op_w ws') => if ws' == ws then Some SLSL else None
  | Olsr ws' => if ws' == ws then Some SLSR else None
  | Oasr (Op_w ws') => if ws' == ws then Some SASR else None
  | Oror ws' => if ws' == ws then Some SROR else None
  | _ => None
  end.

(* -------------------------------------------------------------------- *)
(* Flag combinations.
   - [CFC_B] is Carry clear (unsigned lower).
   - [CFC_E] is Equal.
   - [CFC_L] is Signed less than.
   - [CFC_BE] is Unsigned lower or same.
   - [CFC_LE] is Signed less than or equal. *)

Definition armv8a_fc_of_cfc (cfc : combine_flags_core) : flag_combination :=
  let vnf := FCVar0 in
  let vzf := FCVar1 in
  let vcf := FCVar2 in
  let vvf := FCVar3 in
  match cfc with
  | CFC_B => FCNot vcf
  | CFC_E => vzf
  | CFC_L => FCNot (FCEq vnf vvf)
  | CFC_BE => FCOr (FCNot vcf) vzf
  | CFC_LE => FCOr vzf (FCNot (FCEq vnf vvf))
  end.

#[global]
Instance armv8a_fcp : FlagCombinationParams :=
  {
    fc_of_cfc := armv8a_fc_of_cfc;
  }.

(* -------------------------------------------------------------------- *)
(* Architecture declaration. *)

Notation register_ext := empty.
Notation xregister := empty.

Definition armv8a_check_CAimm (checker : caimm_checker_s) ws (w : word ws) : bool :=
  match checker with
  | CAimmC_none => true
  | CAimmC_armv8a_shift_amount ws' => check_shift_amount ws' (wunsigned w)
  | CAimmC_armv8a_0_16_32_48 => let x := wunsigned w in x \in [:: 0; 16; 32; 48 ]%Z
  | CAimmC_arm_shift_amout _ | CAimmC_arm_wencoding _ | CAimmC_arm_0_8_16_24 => false
  | CAimmC_riscv_12bits_signed | CAimmC_riscv_5bits_unsigned => false
  end.

#[ export ]
Instance armv8a_decl : arch_decl register register_ext xregister rflag condt :=
  { reg_size  := armv8a_reg_size
  ; xreg_size := armv8a_xreg_size
  ; cond_eqC  := eqTC_condt
  ; toS_r     := reg_toS
  ; toS_rx    := empty_toS lword64
  ; toS_x     := empty_toS lword128
  ; toS_f     := rflag_toS
  ; reg_size_neq_xreg_size := refl_equal
  ; ad_rsp := RSP
  ; ad_fcp := armv8a_fcp
  ; check_CAimm := armv8a_check_CAimm
  }.

(* -------------------------------------------------------------------- *)
(* Calling convention (AAPCS64). *)

Definition armv8a_linux_call_conv : calling_convention :=
  {| callee_saved :=
      map ARReg [:: R19; R20; R21; R22; R23; R24; R25; R26; R27; R28
                  ; R29; RSP ]
   ; callee_saved_not_bool := erefl true
   ; callee_saved_has_rsp  := erefl true
   ; call_reg_args  := [:: R0; R1; R2; R3; R4; R5; R6; R7 ]
   ; call_xreg_args := [::]
   ; call_reg_ret   := [:: R0; R1 ]
   ; call_xreg_ret  := [::]
   ; call_reg_ret_uniq := erefl true
   |}.

Definition armv8a_internal_call_conv : internal_calling_convention :=
  {| icall_reg   :=
      [:: R0; R1; R2; R3; R4; R5; R6; R7;
          R8; R9; R10; R11; R12; R13; R14; R15;
          R16; R17; R18;
          R19; R20; R21; R22; R23; R24;
          R25; R26; R27; R28; R29 ]
   ; icall_regx  := [::]
   ; icall_xreg  := [::]
   ; icall_rflag := [:: CF; NF; ZF; VF ]
  |}.
