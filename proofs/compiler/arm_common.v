(* Definitions shared by the Arm architectures.

 * AArch32 (arm, ARMv7-M) and AArch64 (armv8a) share the NZCV flag
 * register, the condition codes evaluated on it, and the flag-combination
 * description. This file holds these common definitions; the
 * architecture-specific declarations ([arm_decl], [armv8a_decl]) re-export
 * it.
 *)
From elpi.apps Require Import derive.std.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype.

Require Import
  flag_combination
  strings
  type
  utils.

Require Import arch_decl.

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
  {
    cenum  := rflags;
    cenumP := rflag_fin_axiom;
  }.

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
(* Flag combinations.
   The Arm terminology is different from Intel's (chapter A7.3 from the
   ARMv7-M reference manual; section C1.2.4 from the Arm ARM DDI0487).
   - [CFC_B] is Carry clear (unsigned lower).
   - [CFC_E] is Equal.
   - [CFC_L] is Signed less than.
   - [CFC_BE] is Unsigned lower or same.
   - [CFC_LE] is Signed less than or equal. *)

Definition arm_fc_of_cfc (cfc : combine_flags_core) : flag_combination :=
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
Instance arm_fcp : FlagCombinationParams :=
  {
    fc_of_cfc := arm_fc_of_cfc;
  }.
