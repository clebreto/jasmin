(* ARMv8-A (AArch64) instruction set.

   A64 base instructions. Data-processing instructions come in two forms
   selected by the [opts_size] option: the 64-bit (X registers) form and
   the 32-bit (W registers) form, which zeroes the upper 32 bits of
   destination registers. Instruction documentation is quoted from the ARM
   Architecture Reference Manual for A-profile architecture, ARM DDI 0487
   M.a (the machine-readable extraction lives in
   compiler/doc/armv8a_isa_docs.json). *)

From elpi.apps Require Import derive.std.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype fintype.
From mathcomp Require Import ssralg word_ssrZ.

Require Import
  sem_type
  shift_kind
  strings
  utils
  word.
Require xseq.
Require Import
  values
  sopn
  arch_decl
  arch_utils.
Require Import armv8a_decl.


Module E.
  Definition no_semantics : error := ErrSemUndef.
End E.


(* -------------------------------------------------------------------- *)
(* ARMv8-A instruction options.
   Unlike ARMv7-M, A64 has no conditional execution and flag-setting
   variants are distinct mnemonics (ADDS, SUBS, ...). The options select
   the operand size ([U64] for the X form, [U32] for the W form) and an
   optional shift of the last register operand of data-processing
   instructions. *)

#[only(eqbOK)] derive
Record armv8a_options :=
  {
    has_shift : option shift_kind;
    opts_size : wsize;
  }.

#[ export ]
Instance eqTC_armv8a_options : eqTypeC armv8a_options :=
  { ceqP := armv8a_options_eqb_OK }.

Canonical armv8a_options_eqType := @ceqT_eqType _ eqTC_armv8a_options.

Definition default_opts : armv8a_options :=
  {|
    has_shift := None;
    opts_size := U64;
  |}.

Definition opts_at (ws : wsize) : armv8a_options :=
  {|
    has_shift := None;
    opts_size := ws;
  |}.


(* -------------------------------------------------------------------- *)
(* ARMv8-A instruction mnemonics. *)

#[only(eqbOK)] derive
Variant armv8a_mnemonic : Type :=
(* Arithmetic *)
| ADD                            (* Add without carry *)
| ADDS                           (* Add without carry, setting flags *)
| ADC                            (* Add with carry *)
| ADCS                           (* Add with carry, setting flags *)
| SUB                            (* Subtract without carry *)
| SUBS                           (* Subtract without carry, setting flags *)
| SBC                            (* Subtract with carry *)
| SBCS                           (* Subtract with carry, setting flags *)
| NEG                            (* Negate *)
| MUL                            (* Multiply and write the least significant
                                    bits of the result *)
| MADD                           (* Multiply and add *)
| MSUB                           (* Multiply and subtract *)
| SDIV                           (* Signed division *)
| UDIV                           (* Unsigned division *)
| UMULL                          (* Unsigned multiply 32x32 -> 64 *)
| SMULL                          (* Signed multiply 32x32 -> 64 *)
| UMADDL                         (* Unsigned multiply-add 32x32+64 -> 64 *)
| SMADDL                         (* Signed multiply-add 32x32+64 -> 64 *)
| UMULH                          (* Unsigned multiply, high 64 bits *)
| SMULH                          (* Signed multiply, high 64 bits *)

(* Logical *)
| AND                            (* Bitwise AND *)
| ANDS                           (* Bitwise AND, setting flags *)
| BIC                            (* Bitwise AND with bitwise NOT *)
| BICS                           (* Bitwise AND with bitwise NOT, setting flags *)
| ORR                            (* Bitwise OR *)
| EOR                            (* Bitwise XOR *)
| MVN                            (* Bitwise NOT *)

(* Shifts *)
| ASR                            (* Arithmetic shift right *)
| LSL                            (* Logical shift left *)
| LSR                            (* Logical shift right *)
| ROR                            (* Rotate right *)

(* Bit field operations *)
| BFC                            (* Bitfield clear *)
| BFI                            (* Bitfield insert *)
| BFXIL                          (* Bitfield extract and insert at low end *)
| SBFX                           (* Signed bitfield extract *)
| UBFX                           (* Unsigned bitfield extract *)
| EXTR                           (* Extract register from a register pair *)

(* Other data processing instructions *)
| MOV                            (* Copy operand to destination *)
| MOVN                           (* Move wide with NOT *)
| MOVZ                           (* Move wide with zero *)
| MOVK                           (* Move wide with keep *)
| ADR                            (* Form PC-relative address *)
| SXTB                           (* Sign extend byte *)
| SXTH                           (* Sign extend halfword *)
| SXTW                           (* Sign extend word *)
| UXTB                           (* Zero extend byte *)
| UXTH                           (* Zero extend halfword *)
| UXTW                           (* Zero extend word *)
| RBIT                           (* Reverse bits *)
| REV                            (* Byte-reverse register *)
| REV16                          (* Byte-reverse 16-bit halfwords *)
| REV32                          (* Byte-reverse 32-bit words *)
| CLZ                            (* Count leading zeros *)
| CLS                            (* Count leading sign bits *)

(* Comparisons *)
| CMP                            (* Compare *)
| CMN                            (* Compare negative *)
| TST                            (* Test *)

(* Conditional selection *)
| CSEL                           (* Conditional select *)
| CSINC                          (* Conditional select increment *)
| CSINV                          (* Conditional select invert *)
| CSNEG                          (* Conditional select negate *)
| CSET                           (* Conditional set *)
| CSETM                          (* Conditional set mask *)

(* Loads *)
| LDR                            (* Load a word or doubleword *)
| LDRB                           (* Load a zero extended byte *)
| LDRH                           (* Load a zero extended halfword *)
| LDRSB                          (* Load a sign extended byte *)
| LDRSH                          (* Load a sign extended halfword *)
| LDRSW                          (* Load a sign extended word *)

(* Stores *)
| STR                            (* Store a word or doubleword *)
| STRB                           (* Store a byte *)
| STRH.                          (* Store a halfword *)

#[ export ]
Instance eqTC_armv8a_mnemonic : eqTypeC armv8a_mnemonic :=
  { ceqP := armv8a_mnemonic_eqb_OK }.

Canonical armv8a_mnemonic_eqType := @ceqT_eqType _ eqTC_armv8a_mnemonic.

Definition armv8a_mnemonics : seq armv8a_mnemonic :=
  [:: ADD; ADDS; ADC; ADCS; SUB; SUBS; SBC; SBCS; NEG
    ; MUL; MADD; MSUB; SDIV; UDIV
    ; UMULL; SMULL; UMADDL; SMADDL; UMULH; SMULH
    ; AND; ANDS; BIC; BICS; ORR; EOR; MVN
    ; ASR; LSL; LSR; ROR
    ; BFC; BFI; BFXIL; SBFX; UBFX; EXTR
    ; MOV; MOVN; MOVZ; MOVK; ADR
    ; SXTB; SXTH; SXTW; UXTB; UXTH; UXTW
    ; RBIT; REV; REV16; REV32; CLZ; CLS
    ; CMP; CMN; TST
    ; CSEL; CSINC; CSINV; CSNEG; CSET; CSETM
    ; LDR; LDRB; LDRH; LDRSB; LDRSH; LDRSW
    ; STR; STRB; STRH
  ].

Lemma armv8a_mnemonic_fin_axiom : Finite.axiom armv8a_mnemonics.
Proof. by case. Qed.

#[ export ]
Instance finTC_armv8a_mnemonic : finTypeC armv8a_mnemonic :=
  {
    cenum := armv8a_mnemonics;
    cenumP := armv8a_mnemonic_fin_axiom;
  }.

Canonical armv8a_mnemonic_finType := @cfinT_finType _ finTC_armv8a_mnemonic.

(* Mnemonics whose last register operand can be optionally shifted. *)
Definition has_shift_mnemonics : seq armv8a_mnemonic :=
  [:: ADD; ADDS; SUB; SUBS; NEG
    ; AND; ANDS; BIC; BICS; ORR; EOR; MVN
    ; CMP; CMN; TST
  ].

(* Mnemonics available in both the 32-bit (W) and 64-bit (X) forms; the
   remaining mnemonics are only valid with [opts_size = U64]. *)
Definition sized_mnemonics : seq armv8a_mnemonic :=
  [:: ADD; ADDS; ADC; ADCS; SUB; SUBS; SBC; SBCS; NEG
    ; MUL; MADD; MSUB; SDIV; UDIV
    ; AND; ANDS; BIC; BICS; ORR; EOR; MVN
    ; ASR; LSL; LSR; ROR
    ; BFC; BFI; BFXIL; SBFX; UBFX; EXTR
    ; MOV; MOVN; MOVZ; MOVK
    ; SXTB; SXTH; UXTB; UXTH
    ; RBIT; REV; REV16; CLZ; CLS
    ; CMP; CMN; TST
    ; CSEL; CSINC; CSINV; CSNEG; CSET; CSETM
    ; LDR; LDRB; LDRH; LDRSB; LDRSH
    ; STR; STRB; STRH
  ].

Definition wsize_uload_mn : seq (wsize * armv8a_mnemonic) :=
  [:: (U8, LDRB); (U16, LDRH); (U32, LDR); (U64, LDR) ].

Definition uload_mn_of_wsize (ws : wsize) : option armv8a_mnemonic :=
  xseq.assoc wsize_uload_mn ws.

Definition wsize_sload_mn : seq (wsize * armv8a_mnemonic) :=
  [:: (U8, LDRSB); (U16, LDRSH); (U32, LDRSW) ].

Definition sload_mn_of_wsize (ws : wsize) : option armv8a_mnemonic :=
  xseq.assoc wsize_sload_mn ws.

Definition wsize_of_sload_mn (mn : armv8a_mnemonic) : option wsize :=
  xseq.assoc ([seq (x.2, x.1) | x <- wsize_sload_mn]) mn.

(* Memory access width of narrow loads; [LDR] accesses at the operand
   size. *)
Definition wsize_of_narrow_load_mn (mn : armv8a_mnemonic) : option wsize :=
  match mn with
  | LDRB | LDRSB => Some U8
  | LDRH | LDRSH => Some U16
  | LDRSW => Some U32
  | _ => None
  end.

Definition wsize_store_mn : seq (wsize * armv8a_mnemonic) :=
  [:: (U8, STRB); (U16, STRH); (U32, STR); (U64, STR) ].

Definition store_mn_of_wsize (ws : wsize) : option armv8a_mnemonic :=
  xseq.assoc wsize_store_mn ws.

Definition wsize_of_narrow_store_mn (mn : armv8a_mnemonic) : option wsize :=
  match mn with
  | STRB => Some U8
  | STRH => Some U16
  | _ => None
  end.

Definition string_of_armv8a_mnemonic (mn : armv8a_mnemonic) : string :=
  match mn with
  | ADD => "ADD"
  | ADDS => "ADDS"
  | ADC => "ADC"
  | ADCS => "ADCS"
  | SUB => "SUB"
  | SUBS => "SUBS"
  | SBC => "SBC"
  | SBCS => "SBCS"
  | NEG => "NEG"
  | MUL => "MUL"
  | MADD => "MADD"
  | MSUB => "MSUB"
  | SDIV => "SDIV"
  | UDIV => "UDIV"
  | UMULL => "UMULL"
  | SMULL => "SMULL"
  | UMADDL => "UMADDL"
  | SMADDL => "SMADDL"
  | UMULH => "UMULH"
  | SMULH => "SMULH"
  | AND => "AND"
  | ANDS => "ANDS"
  | BIC => "BIC"
  | BICS => "BICS"
  | ORR => "ORR"
  | EOR => "EOR"
  | MVN => "MVN"
  | ASR => "ASR"
  | LSL => "LSL"
  | LSR => "LSR"
  | ROR => "ROR"
  | BFC => "BFC"
  | BFI => "BFI"
  | BFXIL => "BFXIL"
  | SBFX => "SBFX"
  | UBFX => "UBFX"
  | EXTR => "EXTR"
  | MOV => "MOV"
  | MOVN => "MOVN"
  | MOVZ => "MOVZ"
  | MOVK => "MOVK"
  | ADR => "ADR"
  | SXTB => "SXTB"
  | SXTH => "SXTH"
  | SXTW => "SXTW"
  | UXTB => "UXTB"
  | UXTH => "UXTH"
  | UXTW => "UXTW"
  | RBIT => "RBIT"
  | REV => "REV"
  | REV16 => "REV16"
  | REV32 => "REV32"
  | CLZ => "CLZ"
  | CLS => "CLS"
  | CMP => "CMP"
  | CMN => "CMN"
  | TST => "TST"
  | CSEL => "CSEL"
  | CSINC => "CSINC"
  | CSINV => "CSINV"
  | CSNEG => "CSNEG"
  | CSET => "CSET"
  | CSETM => "CSETM"
  | LDR => "LDR"
  | LDRB => "LDRB"
  | LDRH => "LDRH"
  | LDRSB => "LDRSB"
  | LDRSH => "LDRSH"
  | LDRSW => "LDRSW"
  | STR => "STR"
  | STRB => "STRB"
  | STRH => "STRH"
  end%string.


(* -------------------------------------------------------------------- *)
(* ARMv8-A operators are pairs of mnemonics and options. *)

#[only(eqbOK)] derive
Variant armv8a_asm_op :=
| ARMv8A_op : armv8a_mnemonic -> armv8a_options -> armv8a_asm_op.

#[ export ]
Instance eqTC_armv8a_asm_op : eqTypeC armv8a_asm_op :=
  { ceqP := armv8a_asm_op_eqb_OK }.

Canonical armv8a_asm_op_eqType := @ceqT_eqType _ eqTC_armv8a_asm_op.


(* -------------------------------------------------------------------- *)
(* Common semantic types. *)

Notation sflag := (lbool) (only parsing).
Notation snzcv := ([:: sflag; sflag; sflag; sflag ]) (only parsing).

Notation ty_nzcv := (sem_ltuple snzcv) (only parsing).
Notation ty_r := (sem_ltuple [:: lreg ]) (only parsing).
Notation ty_w ws := (sem_ltuple [:: lword ws ]) (only parsing).

Notation ty_nzcv_w ws := (sem_ltuple (snzcv ++ [:: lword ws ])) (only parsing).


(* -------------------------------------------------------------------- *)
(* Common argument descriptions. *)

Definition ad_nzcv : seq arg_desc := map F [:: NF; ZF; CF; VF ].


(* -------------------------------------------------------------------- *)
(* Common flag definitions. *)

Definition NF_of_word (ws : wsize) (w : word ws) := msb w.
Definition ZF_of_word (ws : wsize) (w : word ws) := w == 0%w.

(* Compute the value of the flags for an arithmetic operation.
   For instance, for <+> a binary operation, this function should be called
   with
     res = w <+> w'
     res_unsigned = wunsigned w Z.<+> wunsigned w'
     res_signed = wsigned w Z.<+> wsigned w'
*)
Definition nzcv_of_aluop
  {ws : wsize}
  (res : word ws)     (* Actual result. *)
  (res_unsigned : Z)  (* Result with unsigned interpretation. *)
  (res_signed : Z)    (* Result with signed interpretation. *)
  : ty_nzcv :=
  (:: Some (NF_of_word res)                 (* NF *)
    , Some (ZF_of_word res)                 (* ZF *)
    , Some (wunsigned res != res_unsigned)  (* CF *)
    & Some (wsigned res != res_signed)      (* VF *)
  ).

(* Flags of A64 flag-setting logical instructions (ANDS, BICS, TST):
   PSTATE.<N,Z,C,V> = result<msb>:IsZeroBit(result):'00'. *)
Definition nzcv_of_logop {ws : wsize} (res : word ws) : ty_nzcv :=
  (:: Some (NF_of_word res)
    , Some (ZF_of_word res)
    , Some false
    & Some false
  ).

Definition nzcv_w_of_aluop {ws : wsize} (w : word ws) (wun wsi : Z) :=
  merge_tuple (nzcv_of_aluop w wun wsi) (w : ty_w ws).

Definition nzcv_w_of_logop {ws : wsize} (w : word ws) :=
  merge_tuple (nzcv_of_logop w) (w : ty_w ws).


(* -------------------------------------------------------------------- *)
(* Instruction semantics.
   Semantics are parametric in the operand size [ws] (U32 for the W form,
   U64 for the X form) unless the instruction exists at a single size. *)

(* [C6.2.6 ADD (shifted register)] ARM DDI 0487 M.a, p. 1798
   Add optionally-shifted register  This instruction adds a register value and
   an optionally-shifted register value, and writes the result to the
   destination register.
   Syntax: ADD <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     bits(datasize) result;
     (result, -) = AddWithCarry(operand1, operand2, '0');
     X[d, datasize] = result;
*)
Definition armv8a_ADD_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  (wn + wm)%w.

(* [C6.2.11 ADDS (shifted register)] ARM DDI 0487 M.a, p. 1807
   Add optionally-shifted register, setting flags  This instruction adds a
   register value and an optionally-shifted register value, and writes the
   result to the destination register. It updates the condition flags based on
   the result.  This instruction is used by the alias CMN (shifted register).
   Syntax: ADDS <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     bits(datasize) result;
     bits(4) nzcv;
     (result, nzcv) = AddWithCarry(operand1, operand2, '0');
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = nzcv;
*)
Definition armv8a_ADDS_semi {ws : wsize} (wn wm : word ws) : ty_nzcv_w ws :=
  nzcv_w_of_aluop
    (wn + wm)%w
    (wunsigned wn + wunsigned wm)%Z
    (wsigned wn + wsigned wm)%Z.

(* [C6.2.2 ADC] ARM DDI 0487 M.a, p. 1789
   Add with carry  This instruction adds two register values and the Carry flag
   value, and writes the result to the destination register.
   Syntax: ADC <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     bits(datasize) result;
     (result, -) = AddWithCarry(operand1, operand2, PSTATE.C);
     X[d, datasize] = result;
*)
Definition armv8a_ADC_semi {ws : wsize} (wn wm : word ws) (cf : bool) : ty_w ws :=
  let c := Z.b2z cf in
  (wn + wm + wrepr ws c)%w.

(* [C6.2.3 ADCS] ARM DDI 0487 M.a, p. 1791
   Add with carry, setting flags  This instruction adds two register values and
   the Carry flag value, and writes the result to the destination register. It
   updates the condition flags based on the result.
   Syntax: ADCS <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     bits(datasize) result;
     bits(4) nzcv;
     (result, nzcv) = AddWithCarry(operand1, operand2, PSTATE.C);
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = nzcv;
*)
Definition armv8a_ADCS_semi {ws : wsize} (wn wm : word ws) (cf : bool) : ty_nzcv_w ws :=
  let c := Z.b2z cf in
  nzcv_w_of_aluop
    (wn + wm + wrepr ws c)%w
    (wunsigned wn + wunsigned wm + c)%Z
    (wsigned wn + wsigned wm + c)%Z.

(* [C6.2.457 SUB (shifted register)] ARM DDI 0487 M.a, p. 2785
   Subtract optionally-shifted register  This instruction subtracts an
   optionally-shifted register value from a register value, and writes the
   result to the destination register.  This instruction is used by the alias
   NEG (shifted register).
   Syntax: SUB <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = NOT(ShiftReg(m, shift_type, shift_amount, datasize));
     bits(datasize) result;
     (result, -) = AddWithCarry(operand1, operand2, '1');
     X[d, datasize] = result;
*)
Definition armv8a_SUB_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  (wn - wm)%w.

(* [C6.2.464 SUBS (shifted register)] ARM DDI 0487 M.a, p. 2797
   Subtract optionally-shifted register, setting flags  This instruction
   subtracts an optionally-shifted register value from a register value, and
   writes the result to the destination register. It updates the condition
   flags based on the result.  This instruction is used by the aliases CMP
   (shifted register) and NEGS.
   Syntax: SUBS <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = NOT(ShiftReg(m, shift_type, shift_amount, datasize));
     bits(datasize) result;
     bits(4) nzcv;
     (result, nzcv) = AddWithCarry(operand1, operand2, '1');
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = nzcv;
*)
Definition armv8a_SUBS_semi {ws : wsize} (wn wm : word ws) : ty_nzcv_w ws :=
  let wmnot := wnot wm in
  nzcv_w_of_aluop
    (wn + wmnot + 1)%w
    (wunsigned wn + wunsigned wmnot + 1)%Z
    (wsigned wn + wsigned wmnot + 1)%Z.

(* [C6.2.351 SBC] ARM DDI 0487 M.a, p. 2548
   Subtract with carry  This instruction subtracts a register value and the
   value of NOT (Carry flag) from a register value, and writes the result to
   the destination register.  This instruction is used by the alias NGC.
   Syntax: SBC <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = NOT(X[m, datasize]);
     bits(datasize) result;
     (result, -) = AddWithCarry(operand1, operand2, PSTATE.C);
     X[d, datasize] = result;
*)
Definition armv8a_SBC_semi {ws : wsize} (wn wm : word ws) (cf : bool) : ty_w ws :=
  armv8a_ADC_semi wn (wnot wm) cf.

(* [C6.2.352 SBCS] ARM DDI 0487 M.a, p. 2550
   Subtract with carry, setting flags  This instruction subtracts a register
   value and the value of NOT (Carry flag) from a register value, and writes
   the result to the destination register. It updates the condition flags based
   on the result.  This instruction is used by the alias NGCS.
   Syntax: SBCS <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = NOT(X[m, datasize]);
     bits(datasize) result;
     bits(4) nzcv;
     (result, nzcv) = AddWithCarry(operand1, operand2, PSTATE.C);
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = nzcv;
*)
Definition armv8a_SBCS_semi {ws : wsize} (wn wm : word ws) (cf : bool) : ty_nzcv_w ws :=
  armv8a_ADCS_semi wn (wnot wm) cf.

(* [C6.2.294 NEG (shifted register)] ARM DDI 0487 M.a, p. 2440
   Negate (shifted register)  This instruction negates an optionally-shifted
   register value, and writes the result to the destination register.  This is
   an alias of SUB (shifted register). This means:  • The encodings in this
   description are named to match the encodings of SUB (shifted register). •
   The description of SUB (shifted register) gives the operational pseudocode,
   any CONSTRAINED UNPREDICTABLE behavior, and any operational information for
   this instruction.
   Note: NEG is an alias of SUB (shifted register) with Rn = ZR; the SUB entry carries the operational pseudocode.
   Syntax: NEG <Xd>, <Xm>{, <shift> #<amount>}  ==  SUB <Xd>, XZR, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     The description of SUB (shifted register) gives the operational pseudocode for this instruction.
   Base instruction [C6.2.457 SUB (shifted register)] p. 2785, Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = NOT(ShiftReg(m, shift_type, shift_amount, datasize));
     bits(datasize) result;
     (result, -) = AddWithCarry(operand1, operand2, '1');
     X[d, datasize] = result;
*)
Definition armv8a_NEG_semi {ws : wsize} (wm : word ws) : ty_w ws :=
  (wnot wm + 1)%w.

(* [C6.2.292 MUL] ARM DDI 0487 M.a, p. 2436
   Multiply  This instruction multiplies two register values and writes the
   result to the destination register.  This is an alias of MADD. This means:
   • The encodings in this description are named to match the encodings of
   MADD. • The description of MADD gives the operational pseudocode, any
   CONSTRAINED UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Note: MUL is an alias of MADD with Ra = ZR (see the MADD entry for the operational pseudocode).
   Syntax: MUL <Xd>, <Xn>, <Xm>  ==  MADD <Xd>, <Xn>, <Xm>, XZR
   Operation (ASL):
     The description of MADD gives the operational pseudocode for this instruction.
*)
Definition armv8a_MUL_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  (wn * wm)%w.

(* [C6.2.274 MADD] ARM DDI 0487 M.a, p. 2401
   Multiply-add  This instruction multiplies two register values, adds a third
   register value, and writes the result to the destination register.  This
   instruction is used by the alias MUL.
   Syntax: MADD <Xd>, <Xn>, <Xm>, <Xa>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     constant bits(datasize) operand3 = X[a, datasize];
     constant integer result = UInt(operand3) + (UInt(operand1) * UInt(operand2));
     X[d, datasize] = result<datasize-1:0>;
*)
Definition armv8a_MADD_semi {ws : wsize} (wn wm wa : word ws) : ty_w ws :=
  (wa + wn * wm)%w.

(* [C6.2.290 MSUB] ARM DDI 0487 M.a, p. 2432
   Multiply-subtract  This instruction multiplies two register values,
   subtracts the product from a third register value, and writes the result to
   the destination register.  This instruction is used by the alias MNEG.
   Syntax: MSUB <Xd>, <Xn>, <Xm>, <Xa>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     constant bits(datasize) operand3 = X[a, datasize];
     constant integer result = UInt(operand3) - (UInt(operand1) * UInt(operand2));
     X[d, datasize] = result<datasize-1:0>;
*)
Definition armv8a_MSUB_semi {ws : wsize} (wn wm wa : word ws) : ty_w ws :=
  (wa - wn * wm)%w.

(* [C6.2.356 SDIV] ARM DDI 0487 M.a, p. 2558
   Signed divide  This instruction divides the first signed source register
   value by the second signed source register value, and writes the result to
   the destination register. Dividing by zero writes the value zero to the
   destination register. The condition flags are not affected.
   Syntax: SDIV <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     constant integer dividend = SInt(operand1);
     constant integer divisor = SInt(operand2);
     integer result;
     if divisor == 0 then
         result = 0;
     elsif (dividend < 0) == (divisor < 0) then
         result = Abs(dividend) DIV Abs(divisor); // same signs - positive result
     else
         result = -(Abs(dividend) DIV Abs(divisor)); // different signs - negative result
     X[d, datasize] = result<datasize-1:0>;
*)
Definition armv8a_SDIV_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  wdivi wn wm.

(* [C6.2.489 UDIV] ARM DDI 0487 M.a, p. 2846
   Unsigned divide  This instruction divides the first unsigned source register
   value by the second unsigned source register value, and writes the result to
   the destination register. Dividing by zero writes the value zero to the
   destination register. The condition flags are not affected.
   Syntax: UDIV <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     constant integer dividend = UInt(operand1);
     constant integer divisor = UInt(operand2);
     integer result;
     if divisor == 0 then
         result = 0;
     else
         result = dividend DIV divisor;
     X[d, datasize] = result<datasize-1:0>;
*)
Definition armv8a_UDIV_semi {ws : wsize} (wn wm : word ws) : ty_w ws :=
  wdiv wn wm.

(* [C6.2.498 UMULL] ARM DDI 0487 M.a, p. 2862
   Unsigned multiply long  This instruction multiplies two 32-bit register
   values, and writes the result to the 64-bit destination register.  This is
   an alias of UMADDL. This means:  • The encodings in this description are
   named to match the encodings of UMADDL. • The description of UMADDL gives
   the operational pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any
   operational information for this instruction.
   Note: UMULL is an alias of UMADDL with Ra = XZR.
   Syntax: UMULL <Xd>, <Wn>, <Wm>  ==  UMADDL <Xd>, <Wn>, <Wm>, XZR
   Operation (ASL):
     The description of UMADDL gives the operational pseudocode for this instruction.
*)
Definition armv8a_UMULL_semi (wn wm : word U32) : ty_r :=
  (zero_extend U64 wn * zero_extend U64 wm)%w.

(* [C6.2.379 SMULL] ARM DDI 0487 M.a, p. 2616
   Signed multiply long  This instruction multiplies two 32-bit register
   values, and writes the result to the 64-bit destination register.  This is
   an alias of SMADDL. This means:  • The encodings in this description are
   named to match the encodings of SMADDL. • The description of SMADDL gives
   the operational pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any
   operational information for this instruction.
   Note: SMULL is an alias of SMADDL with Ra = XZR.
   Syntax: SMULL <Xd>, <Wn>, <Wm>  ==  SMADDL <Xd>, <Wn>, <Wm>, XZR
   Operation (ASL):
     The description of SMADDL gives the operational pseudocode for this instruction.
*)
Definition armv8a_SMULL_semi (wn wm : word U32) : ty_r :=
  (sign_extend U64 wn * sign_extend U64 wm)%w.

(* [C6.2.490 UMADDL] ARM DDI 0487 M.a, p. 2848
   Unsigned multiply-add long  This instruction multiplies two 32-bit register
   values, adds a 64-bit register value, and writes the result to the 64-bit
   destination register.  This instruction is used by the alias UMULL.
   Syntax: UMADDL <Xd>, <Wn>, <Wm>, <Xa>
   Operation (ASL):
     constant bits(32) operand1 = X[n, 32];
     constant bits(32) operand2 = X[m, 32];
     constant bits(64) operand3 = X[a, 64];
     constant integer result = UInt(operand3) + (UInt(operand1) * UInt(operand2));
     X[d, 64] = result<63:0>;
*)
Definition armv8a_UMADDL_semi (wn wm : word U32) (wa : word U64) : ty_r :=
  (wa + zero_extend U64 wn * zero_extend U64 wm)%w.

(* [C6.2.368 SMADDL] ARM DDI 0487 M.a, p. 2599
   Signed multiply-add long  This instruction multiplies two 32-bit register
   values, adds a 64-bit register value, and writes the result to the 64-bit
   destination register.  This instruction is used by the alias SMULL.
   Syntax: SMADDL <Xd>, <Wn>, <Wm>, <Xa>
   Operation (ASL):
     constant bits(32) operand1 = X[n, 32];
     constant bits(32) operand2 = X[m, 32];
     constant bits(64) operand3 = X[a, 64];
     constant integer result = SInt(operand3) + (SInt(operand1) * SInt(operand2));
     X[d, 64] = result<63:0>;
*)
Definition armv8a_SMADDL_semi (wn wm : word U32) (wa : word U64) : ty_r :=
  (wa + sign_extend U64 wn * sign_extend U64 wm)%w.

(* [C6.2.497 UMULH] ARM DDI 0487 M.a, p. 2861
   Unsigned multiply high  This instruction multiplies two 64-bit register
   values, and writes bits[127:64] of the 128-bit result to the 64-bit
   destination register.
   Syntax: UMULH <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(64) operand1 = X[n, 64];
     constant bits(64) operand2 = X[m, 64];
     constant integer result = UInt(operand1) * UInt(operand2);
     X[d, 64] = result<127:64>;
*)
Definition armv8a_UMULH_semi (wn wm : word U64) : ty_r :=
  (wumul wn wm).1.

(* [C6.2.378 SMULH] ARM DDI 0487 M.a, p. 2615
   Signed multiply high  This instruction multiplies two 64-bit register
   values, and writes bits[127:64] of the 128-bit result to the 64-bit
   destination register.
   Syntax: SMULH <Xd>, <Xn>, <Xm>
   Operation (ASL):
     constant bits(64) operand1 = X[n, 64];
     constant bits(64) operand2 = X[m, 64];
     constant integer result = SInt(operand1) * SInt(operand2);
     X[d, 64] = result<127:64>;
*)
Definition armv8a_SMULH_semi (wn wm : word U64) : ty_r :=
  wmulhs wn wm.

Definition armv8a_bitwise_semi
  {ws : wsize}
  (op0 op1 : word ws -> word ws)
  (op : word ws -> word ws -> word ws)
  (wn wm : word ws) :
  ty_w ws :=
  op (op0 wn) (op1 wm).

(* [C6.2.17 ANDS (shifted register)] ARM DDI 0487 M.a, p. 1817
   Bitwise AND (shifted register), setting flags  This instruction performs a
   bitwise AND of a register value and an optionally-shifted register value,
   and writes the result to the destination register. It updates the condition
   flags based on the result.  This instruction is used by the alias TST
   (shifted register).
   Syntax: ANDS <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     constant bits(datasize) result = operand1 AND operand2;
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = result<datasize-1>:IsZeroBit(result):'00';
*)
Definition armv8a_ANDS_semi {ws : wsize} (wn wm : word ws) : ty_nzcv_w ws :=
  nzcv_w_of_logop (wand wn wm).

(* [C6.2.42 BICS (shifted register)] ARM DDI 0487 M.a, p. 1858
   Bitwise bit clear (shifted register), setting flags  This instruction
   performs a bitwise AND of a register value and the complement of an
   optionally-shifted register value, and writes the result to the destination
   register. It updates the condition flags based on the result.
   Syntax: BICS <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     constant bits(datasize) result = operand1 AND NOT(operand2);
     X[d, datasize] = result;
     PSTATE.<N,Z,C,V> = result<datasize-1>:IsZeroBit(result):'00';
*)
Definition armv8a_BICS_semi {ws : wsize} (wn wm : word ws) : ty_nzcv_w ws :=
  nzcv_w_of_logop (wand wn (wnot wm)).

(* [C6.2.293 MVN] ARM DDI 0487 M.a, p. 2438
   Bitwise NOT  This instruction writes the bitwise inverse of a register value
   to the destination register.  This is an alias of ORN (shifted register).
   This means:  • The encodings in this description are named to match the
   encodings of ORN (shifted register). • The description of ORN (shifted
   register) gives the operational pseudocode, any CONSTRAINED UNPREDICTABLE
   behavior, and any operational information for this instruction.
   Syntax: MVN <Xd>, <Xm>{, <shift> #<amount>}  ==  ORN <Xd>, XZR, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     The description of ORN (shifted register) gives the operational pseudocode for this instruction.
*)
Definition armv8a_MVN_semi {ws : wsize} (wm : word ws) : ty_w ws :=
  wnot wm.

(* Shift semantics: the shift amount is the value of the last operand
   modulo the operand size in bits. *)
Definition armv8a_shift_semi
  {ws : wsize} (op : forall sz, word sz -> Z -> word sz)
  (wn : word ws) (wsham : word U8) : ty_w ws :=
  let sham := (wunsigned wsham mod wsize_bits ws)%Z in
  op ws wn sham.

(* [C6.2.281 MOV (register)] ARM DDI 0487 M.a, p. 2413
   Move register value  This instruction copies the value in a source register
   to the destination register.  This is an alias of ORR (shifted register).
   This means:  • The encodings in this description are named to match the
   encodings of ORR (shifted register). • The description of ORR (shifted
   register) gives the operational pseudocode, any CONSTRAINED UNPREDICTABLE
   behavior, and any operational information for this instruction.
   Syntax: MOV <Xd>, <Xm>  ==  ORR <Xd>, XZR, <Xm>
   Operation (ASL):
     The description of ORR (shifted register) gives the operational pseudocode for this instruction.
*)
Definition armv8a_MOV_semi {ws : wsize} (wn : word ws) : ty_w ws :=
  wn.

(* [C6.2.284 MOVZ] ARM DDI 0487 M.a, p. 2418
   Move wide with zero  This instruction moves an optionally-shifted 16-bit
   immediate value to a register.  This instruction is used by the alias MOV
   (wide immediate).
   Syntax: MOVZ <Xd>, #<imm>{, LSL #<shift>}
   Operation (ASL):
     bits(datasize) result = Zeros(datasize);
     result<pos+15:pos> = imm;
     X[d, datasize] = result;
*)
Definition armv8a_MOVZ_semi {ws : wsize} (imm : word U16) (wsh : word U8) : ty_w ws :=
  wshl (zero_extend ws imm) (wunsigned wsh).

(* [C6.2.283 MOVN] ARM DDI 0487 M.a, p. 2416
   Move wide with NOT  This instruction moves the inverse of an optionally-
   shifted 16-bit immediate value to a register.  This instruction is used by
   the alias MOV (inverted wide immediate).
   Syntax: MOVN <Xd>, #<imm>{, LSL #<shift>}
   Operation (ASL):
     bits(datasize) result = Zeros(datasize);
     result<pos+15:pos> = imm;
     X[d, datasize] = NOT(result);
*)
Definition armv8a_MOVN_semi {ws : wsize} (imm : word U16) (wsh : word U8) : ty_w ws :=
  wnot (wshl (zero_extend ws imm) (wunsigned wsh)).

(* [C6.2.282 MOVK] ARM DDI 0487 M.a, p. 2415
   Move wide with keep  This instruction moves an optionally-shifted 16-bit
   immediate value into a register, keeping other bits unchanged.
   Syntax: MOVK <Xd>, #<imm>{, LSL #<shift>}
   Operation (ASL):
     bits(datasize) result = X[d, datasize];
     result<pos+15:pos> = imm;
     X[d, datasize] = result;
*)
Definition armv8a_MOVK_semi {ws : wsize} (old : word ws) (imm : word U16) (wsh : word U8) : ty_w ws :=
  let sh := wunsigned wsh in
  let mask := wshl (zero_extend ws (wrepr U16 (-1))) sh in
  wor (wshl (zero_extend ws imm) sh) (wand old (wnot mask)).

(* [C6.2.12 ADR] ARM DDI 0487 M.a, p. 1809
   Form PC-relative address  This instruction adds an immediate value to the PC
   value to form a PC-relative address, and writes the result to the
   destination register.
   Syntax: ADR <Xd>, <label>
   Operation (ASL):
     X[d, 64] = PC64 + imm;
*)
Definition armv8a_ADR_semi (wn : word U64) : ty_r :=
  wn.

Definition armv8a_extend_semi
  {ws : wsize} (sign : bool) (ws' : wsize) (wn : word ws) : word ws' :=
  let f := if sign then sign_extend else zero_extend in
  (f ws' ws wn).

(* [C6.2.320 RBIT] ARM DDI 0487 M.a, p. 2484
   Reverse bits  This instruction reverses the bit order in a register.
   Syntax: RBIT <Xd>, <Xn>
   Operation (ASL):
     constant bits(datasize) operand = X[n, datasize];
     bits(datasize) result;
     for i = 0 to datasize-1
         result<(datasize-1)-i> = operand<i>;
     X[d, datasize] = result;
*)
Definition armv8a_RBIT_semi {ws : wsize} (w : word ws) : ty_w ws :=
  winit ws (fun i => wbit_n w (Z.to_nat (wsize_bits ws) - 1 - i)).

(* [C6.2.341 REV] ARM DDI 0487 M.a, p. 2532
   Reverse bytes  This instruction reverses the byte order in a register.  This
   instruction is used by the pseudo-instruction REV64.
   Syntax: REV <Xd>, <Xn>
   Operation (ASL):
     constant bits(datasize) operand = X[n, datasize];
     bits(datasize) result;
     constant integer containers = datasize DIV container_size;
     for c = 0 to containers-1
         constant bits(container_size) container = Elem[operand, c, container_size];
         Elem[result, c, container_size] = Reverse(container, 8);
     X[d, datasize] = result;
*)
Definition armv8a_REV_semi {ws : wsize} (w : word ws) : ty_w ws :=
  wbswap w.

(* [C6.2.342 REV16] ARM DDI 0487 M.a, p. 2534
   Reverse bytes in 16-bit halfwords  This instruction reverses the byte order
   in each 16-bit halfword of a register.
   Syntax: REV16 <Xd>, <Xn>
   Operation (ASL):
     constant bits(datasize) operand = X[n, datasize];
     bits(datasize) result;
     constant integer containers = datasize DIV container_size;
     for c = 0 to containers-1
         constant bits(container_size) container = Elem[operand, c, container_size];
         Elem[result, c, container_size] = Reverse(container, 8);
     X[d, datasize] = result;
*)
Definition armv8a_REV16_semi {ws : wsize} (w : word ws) : ty_w ws :=
  lift1_vec U16 (@wbswap U16) ws w.

(* [C6.2.343 REV32] ARM DDI 0487 M.a, p. 2536
   Reverse bytes in 32-bit words  This instruction reverses the byte order in
   each 32-bit word of a register.
   Syntax: REV32 <Xd>, <Xn>
   Operation (ASL):
     constant bits(datasize) operand = X[n, datasize];
     bits(datasize) result;
     constant integer containers = datasize DIV container_size;
     for c = 0 to containers-1
         constant bits(container_size) container = Elem[operand, c, container_size];
         Elem[result, c, container_size] = Reverse(container, 8);
     X[d, datasize] = result;
*)
Definition armv8a_REV32_semi (w : word U64) : ty_r :=
  lift1_vec U32 (@wbswap U32) U64 w.

(* [C6.2.91 CLZ] ARM DDI 0487 M.a, p. 1940
   Count leading zeros  This instruction counts the number of consecutive
   binary zero bits, starting from the most significant bit in the source
   register, and places the count in the destination register.
   Syntax: CLZ <Xd>, <Xn>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant integer result = CountLeadingZeroBits(operand1);
     X[d, datasize] = result<datasize-1:0>;
*)
Definition armv8a_CLZ_semi {ws : wsize} (w : word ws) : ty_w ws :=
  leading_zero w.

(* [C6.2.90 CLS] ARM DDI 0487 M.a, p. 1939
   Count leading sign bits  This instruction counts the number of leading bits
   of the source register that have the same value as the most significant bit
   of the register, and writes the result to the destination register. This
   count does not include the most significant bit of the source register.
   Syntax: CLS <Xd>, <Xn>
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant integer result = CountLeadingSignBits(operand1);
     X[d, datasize] = result<datasize-1:0>;
*)
(* CountLeadingSignBits(x) = CountLeadingZeroBits(x<msb:1> EOR x<msb-1:0>):
   the (N-1)-bit word [x<msb:1> EOR x<msb-1:0>] is computed as the N-bit
   word [(x >> 1) EOR x] with its top bit cleared, whose leading-zero
   count is one more than that of the (N-1)-bit word. *)
Definition armv8a_CLS_semi {ws : wsize} (w : word ws) : ty_w ws :=
  let t := wand (wxor (wshr w 1) w) (wrepr ws (2 ^ (wsize_bits ws - 1) - 1)) in
  (leading_zero t - 1)%w.

(* [C6.2.97 CMP (shifted register)] ARM DDI 0487 M.a, p. 1953
   Compare (shifted register)  This instruction subtracts an optionally-shifted
   register value from a register value. It updates the condition flags based
   on the result, and discards the result.  This is an alias of SUBS (shifted
   register). This means:  • The encodings in this description are named to
   match the encodings of SUBS (shifted register). • The description of SUBS
   (shifted register) gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: CMP <Wn>, <Wm>{, <shift> #<amount>}  ==  CMP <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     The description of SUBS (shifted register) gives the operational pseudocode for this instruction.
*)
Definition armv8a_CMP_semi {ws : wsize} (wn wm : word ws) : ty_nzcv :=
  let wmnot := wnot wm in
  nzcv_of_aluop
    (wn + wmnot + 1)%w
    (wunsigned wn + wunsigned wmnot + 1)%Z
    (wsigned wn + wsigned wmnot + 1)%Z.

(* [C6.2.94 CMN (shifted register)] ARM DDI 0487 M.a, p. 1946
   Compare negative (shifted register)  This instruction adds a register value
   and an optionally-shifted register value. It updates the condition flags
   based on the result, and discards the result.  This is an alias of ADDS
   (shifted register). This means:  • The encodings in this description are
   named to match the encodings of ADDS (shifted register). • The description
   of ADDS (shifted register) gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: CMN <Wn>, <Wm>{, <shift> #<amount>}  ==  CMN <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     The description of ADDS (shifted register) gives the operational pseudocode for this instruction.
*)
Definition armv8a_CMN_semi {ws : wsize} (wn wm : word ws) : ty_nzcv :=
  nzcv_of_aluop
    (wn + wm)%w
    (wunsigned wn + wunsigned wm)%Z
    (wsigned wn + wsigned wm)%Z.

(* [C6.2.484 TST (shifted register)] ARM DDI 0487 M.a, p. 2837
   Test (shifted register)  This instruction performs a bitwise AND operation
   on a register value and an optionally-shifted register value. It updates the
   condition flags based on the result, and discards the result.  This is an
   alias of ANDS (shifted register). This means:  • The encodings in this
   description are named to match the encodings of ANDS (shifted register). •
   The description of ANDS (shifted register) gives the operational pseudocode,
   any CONSTRAINED UNPREDICTABLE behavior, and any operational information for
   this instruction.
   Syntax: TST <Wn>, <Wm>{, <shift> #<amount>}  ==  TST <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     The description of ANDS (shifted register) gives the operational pseudocode for this instruction.
*)
Definition armv8a_TST_semi {ws : wsize} (wn wm : word ws) : ty_nzcv :=
  nzcv_of_logop (wand wn wm).

(* [C6.2.138 CSEL] ARM DDI 0487 M.a, p. 2138
   Conditional select  This instruction writes the value of the first source
   register to the destination register if the condition is TRUE. If the
   condition is FALSE, it writes the value of the second source register to the
   destination register.
   Syntax: CSEL <Xd>, <Xn>, <Xm>, <cond>
   Operation (ASL):
     bits(datasize) result;
     if ConditionHolds(condition) then
         result = X[n, datasize];
     else
         result = X[m, datasize];
     X[d, datasize] = result;
*)
Definition armv8a_CSEL_semi {ws : wsize} (wn wm : word ws) (b : bool) : ty_w ws :=
  if b then wn else wm.

(* [C6.2.141 CSINC] ARM DDI 0487 M.a, p. 2144
   Conditional select increment  This instruction returns, in the destination
   register, the value of the first source register if the condition is TRUE,
   and otherwise returns the value of the second source register incremented by
   1.  This instruction is used by the aliases CINC and CSET.
   Syntax: CSINC <Xd>, <Xn>, <Xm>, <cond>
   Operation (ASL):
     bits(datasize) result;
     if ConditionHolds(condition) then
         result = X[n, datasize];
     else
         result = X[m, datasize] + 1;
     X[d, datasize] = result;
*)
Definition armv8a_CSINC_semi {ws : wsize} (wn wm : word ws) (b : bool) : ty_w ws :=
  if b then wn else (wm + 1)%w.

(* [C6.2.142 CSINV] ARM DDI 0487 M.a, p. 2146
   Conditional select invert  This instruction returns, in the destination
   register, the value of the first source register if the condition is TRUE,
   and otherwise returns the bitwise inversion value of the second source
   register.  This instruction is used by the aliases CINV and CSETM.
   Syntax: CSINV <Xd>, <Xn>, <Xm>, <cond>
   Operation (ASL):
     bits(datasize) result;
     if ConditionHolds(condition) then
         result = X[n, datasize];
     else
         result = NOT(X[m, datasize]);
     X[d, datasize] = result;
*)
Definition armv8a_CSINV_semi {ws : wsize} (wn wm : word ws) (b : bool) : ty_w ws :=
  if b then wn else wnot wm.

(* [C6.2.143 CSNEG] ARM DDI 0487 M.a, p. 2148
   Conditional select negation  This instruction returns, in the destination
   register, the value of the first source register if the condition is TRUE,
   and otherwise returns the negated value of the second source register.  This
   instruction is used by the alias CNEG.
   Syntax: CSNEG <Xd>, <Xn>, <Xm>, <cond>
   Operation (ASL):
     bits(datasize) result;
     if ConditionHolds(condition) then
         result = X[n, datasize];
     else
         result = NOT(X[m, datasize]) + 1;
     X[d, datasize] = result;
*)
Definition armv8a_CSNEG_semi {ws : wsize} (wn wm : word ws) (b : bool) : ty_w ws :=
  if b then wn else (wnot wm + 1)%w.

(* [C6.2.139 CSET] ARM DDI 0487 M.a, p. 2140
   Conditional set  This instruction sets the destination register to 1 if the
   condition is TRUE, and otherwise sets it to 0.  This is an alias of CSINC.
   This means:  • The encodings in this description are named to match the
   encodings of CSINC. • The description of CSINC gives the operational
   pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any operational
   information for this instruction.
   Syntax: CSET <Xd>, <invcond>  ==  CSINC <Xd>, XZR, XZR, <cond>
   Operation (ASL):
     The description of CSINC gives the operational pseudocode for this instruction.
*)
Definition armv8a_CSET_semi {ws : wsize} (b : bool) : ty_w ws :=
  if b then 1%w else 0%w.

(* [C6.2.140 CSETM] ARM DDI 0487 M.a, p. 2142
   Conditional set mask  This instruction sets all bits of the destination
   register to 1 if the condition is TRUE, and otherwise sets all bits to 0.
   This is an alias of CSINV. This means:  • The encodings in this description
   are named to match the encodings of CSINV. • The description of CSINV gives
   the operational pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any
   operational information for this instruction.
   Syntax: CSETM <Xd>, <invcond>  ==  CSINV <Xd>, XZR, XZR, <cond>
   Operation (ASL):
     The description of CSINV gives the operational pseudocode for this instruction.
*)
Definition armv8a_CSETM_semi {ws : wsize} (b : bool) : ty_w ws :=
  if b then wrepr ws (-1) else 0%w.

(* [C6.2.160 EXTR] ARM DDI 0487 M.a, p. 2174
   Extract register  This instruction extracts a register from a pair of
   registers.  This instruction is used by the alias ROR (immediate).
   Syntax: EXTR <Xd>, <Xn>, <Xm>, #<lsb>
   Operation (ASL):
     bits(datasize) result;
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = X[m, datasize];
     constant bits(2*datasize) concat = operand1:operand2;
     result = concat<(lsb+datasize)-1:lsb>;
     X[d, datasize] = result;
*)
Definition armv8a_EXTR_semi {ws : wsize} (wn wm : word ws) (wlsb : word U8) : ty_w ws :=
  let bits := wsize_bits ws in
  let l := (wunsigned wlsb mod bits)%Z in
  if (l =? 0)%Z
  then wm
  else wor (wshr wm l) (wshl wn (bits - l)).


(* -------------------------------------------------------------------- *)
(* Shift transformations.
   Instruction descriptions are defined without optionally shifted registers.
   The following transformation adds a shift argument to an instruction
   and updates the semantics and the rest of the fields accordingly. *)

Definition mk_semi1_shifted
  {A} {ws : wsize} (sk : shift_kind) (semi : sem_lprod [:: lword ws ] (exec A)) :
  sem_lprod [:: lword ws; lword8 ] (exec A) :=
  fun wn shift_amount =>
    let sham := wunsigned shift_amount in
    semi (shift_op sk wn sham).

Definition mk_semi2_2_shifted
  {A} {o : ltype} {ws : wsize} (sk : shift_kind) (semi : sem_lprod [:: o; lword ws ] (exec A)) :
  sem_lprod [:: o; lword ws; lword8 ] (exec A) :=
  fun x wm shift_amount =>
    let sham := wunsigned shift_amount in
    semi x (shift_op sk wm sham).

#[ local ]
Lemma mk_shifted_eq_size {A B} {x y} {xs0 : seq A} {ys0 : seq B} {p} :
  (size xs0 == size ys0) && p
  -> (size (xs0 ++ [:: x ]) == size (ys0 ++ [:: y ])) && p.
Proof.
  move=> /andP [] /eqP H0 Hp.
  rewrite 2!size_cat H0.
  by apply/andP.
Qed.

Lemma mk_semi1_shifted_errty A ws sk (semi : sem_lprod [:: lword ws] (exec A)) :
  sem_lforall (fun r : exec A => r <> Error ErrType) [:: lword ws] semi ->
  sem_lforall (fun r : exec A => r <> Error ErrType)
         ([:: lword ws] ++ [:: lword8]) (mk_semi1_shifted sk semi).
Proof. by rewrite /mk_semi1_shifted /= => h *; apply h. Qed.

Lemma mk_semi2_2_shifted_errty A (t : ltype) ws sk (semi : sem_lprod [:: t; lword ws] (exec A)) :
  sem_lforall (fun r : exec A => r <> Error ErrType) [:: t; lword ws] semi ->
  sem_lforall (fun r : exec A => r <> Error ErrType)
         ([:: t; lword ws] ++ [:: lword8]) (mk_semi2_2_shifted sk semi).
Proof. rewrite /mk_semi2_2_shifted /= => h *; apply h. Qed.

Lemma mk_semi1_shifted_safe A ws sk (semi : sem_lprod [:: lword ws] (exec A)) :
  interp_safe_cond_ty [::] semi ->
  interp_safe_cond_ty [::] (mk_semi1_shifted sk semi).
Proof. move=> h > _; apply h; constructor. Qed.

Lemma mk_semi2_2_shifted_safe A sk (t : ltype) ws (semi : sem_lprod [:: t; lword ws] (exec A)) :
  interp_safe_cond_ty [::] semi ->
  interp_safe_cond_ty [::] (mk_semi2_2_shifted sk semi).
Proof. move=> h > _; apply h; constructor. Qed.

Lemma safe_wf_cat (tin tin' : seq ltype) sc :
  all (fun sc => sc_needed_args sc <= size tin) sc ->
  all (fun sc => sc_needed_args sc <= size (tin ++ tin')) sc.
Proof. apply sub_all => c h; rewrite size_cat; apply: (leq_trans h); apply leq_addr. Qed.

Definition mk_shifted
  (ws : wsize) (sk : shift_kind) (idt : instr_desc_t) semi' semi_errty' semi_safe' : instr_desc_t :=
  {|
    id_msb_flag := idt.(id_msb_flag);
    id_tin := (id_tin idt) ++ [:: lword8 ];
    id_in := (id_in idt) ++ [:: Ea (id_nargs idt) ];
    id_tout := id_tout idt;
    id_out := id_out idt;
    id_semi := semi';
    id_nargs := (id_nargs idt).+1;
    id_args_kinds :=
      map (fun x => x ++ [:: [:: CAimm (CAimmC_armv8a_shift_amount ws) U8] ]) (id_args_kinds idt);
    id_eq_size := mk_shifted_eq_size (id_eq_size idt);
    id_check_dest := id_check_dest idt;
    id_str_jas := id_str_jas idt;
    id_safe := id_safe idt;
    id_pp_asm := id_pp_asm idt;
    id_valid := id_valid idt;
    id_safe_wf := safe_wf_cat _ (id_safe_wf idt);
    id_semi_errty := semi_errty';
    id_semi_safe := semi_safe'
  |}.

Arguments mk_shifted : clear implicits.


(* -------------------------------------------------------------------- *)
(* Printing. *)

Definition pp_armv8a_op
  (mn : armv8a_mnemonic) (opts : armv8a_options) (args : seq asm_arg) : pp_asm_op :=
  {|
    pp_aop_name := string_of_armv8a_mnemonic mn;
    pp_aop_ext := PP_name;
    pp_aop_args := map (fun a => (opts_size opts, a)) args;
  |}.


(* -------------------------------------------------------------------- *)
(* Instruction descriptions.
   Descriptions are parameterized by the options: the operand size [osz]
   selects the W or X form (W-form instructions clear the upper 32 bits of
   their destination registers, [MSB_CLEAR]), and data-processing
   instructions gain a shift operand with [mk_shifted] when [has_shift]
   is set. *)

Section ARMV8A_INSTR.

Context
  (opts : armv8a_options).

Notation osz := (opts_size opts).

Let string_of_armv8a_mnemonic mn :=
  string_of_armv8a_mnemonic mn.

Notation osz_valid := ((osz == U32) || (osz == U64)) (only parsing).
Notation msbf := (if osz == U64 then MSB_MERGE else MSB_CLEAR) (only parsing).

(* Argument kinds.
   Immediate operands are checked against the A64 encoding rules
   (armv8a_decl.v): [CAimmC_armv8a_arith_imm] (imm12, optionally shifted
   by 12) for the arithmetic class, [CAimmC_armv8a_bitmask_imm] for the
   logical class, [CAimmC_armv8a_mov_imm] for the MOV alias. Instructions
   without an immediate form (BIC, MVN, ...) only accept registers, which
   the [option] parameter of [ak_rr_or_imm]/[ak_rrr_or_imm] expresses
   with [None]. The immediate forms are only available without a shifted
   operand. *)

Let ak_rr := ak_reg_reg.
Let ak_rrr := ak_reg_reg_reg.
Let ak_rrrr := ak_reg_reg_reg_reg.

Let ak_rr_or_imm (ick : option caimm_checker_s) :=
  if ick is Some ic
  then
    if has_shift opts
    then ak_reg_reg
    else ak_reg_reg ++ [:: [:: [:: CAreg ]; [:: CAimm ic osz ] ] ]
  else ak_reg_reg.

Let ak_rrr_or_imm (ick : option caimm_checker_s) :=
  if ick is Some ic
  then
    if has_shift opts
    then ak_reg_reg_reg
    else ak_reg_reg_reg ++ [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm ic osz ] ] ]
  else ak_reg_reg_reg.

Let ak_rr_imm_shift :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm (CAimmC_armv8a_shift_amount osz) U8 ] ] ].

Let ak_r_imm16_shift :=
  [:: [:: [:: CAreg ]; [:: CAimm_sz U16 ]; [:: CAimm CAimmC_armv8a_0_16_32_48 U8 ] ] ].

Let ak_rrr_imm_shift :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAreg ]; [:: CAimm (CAimmC_armv8a_shift_amount osz) U8 ] ] ].

Let ak_rrr_cond :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAreg ]; [:: CAcond ] ] ].

Let ak_r_cond :=
  [:: [:: [:: CAreg ]; [:: CAcond ] ] ].

Let ak_rr_imm8_imm8 :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm_sz U8 ]; [:: CAimm_sz U8 ] ] ].

Let ak_r_imm8_imm8 :=
  [:: [:: [:: CAreg ]; [:: CAimm_sz U8 ]; [:: CAimm_sz U8 ] ] ].

Let ak_rr_imm_imm_extr :=
  [:: [:: [:: CAreg ]; [:: CAreg ]; [:: CAimm (CAimmC_armv8a_shift_amount osz) U8 ]; [:: CAimm_sz U8 ] ] ].

(* -------------------------------------------------------------------- *)
(* Arithmetic instructions. *)

(* A binary data-processing instruction without flag outputs, accepting
   an optionally shifted register or an immediate as its last operand. *)
(* [ick] is the immediate-encoding checker for the instruction's immediate
   form ([None] for instructions with no immediate form). *)
Definition mk_arith_instr mn (ick : option caimm_checker_s)
  (semi : word osz -> word osz -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz ] in
  let x :=
    {|
      id_msb_flag := msbf;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := [:: lword osz ];
      id_out := [:: Ea 0 ];
      id_semi := sem_lprod_ok tin semi;
      id_nargs := 3;
      id_args_kinds := ak_rrr_or_imm ick;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_armv8a_op mn opts;
      id_valid := osz_valid;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
      id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted osz sk x (mk_semi2_2_shifted sk (id_semi x))
                       (fun h => mk_semi2_2_shifted_errty (x.(id_semi_errty) h))
                       (fun h => mk_semi2_2_shifted_safe sk (x.(id_semi_safe) h))
  else x.

(* Same as [mk_arith_instr], with the NZCV flags as extra outputs. *)
Definition mk_ariths_instr mn (ick : option caimm_checker_s)
  (semi : word osz -> word osz -> ty_nzcv_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz ] in
  let x :=
    {|
      id_msb_flag := msbf;
      id_tin := tin;
      id_in := [:: Ea 1; Ea 2 ];
      id_tout := snzcv ++ [:: lword osz ];
      id_out := ad_nzcv ++ [:: Ea 0 ];
      id_semi := sem_lprod_ok tin semi;
      id_nargs := 3;
      id_args_kinds := ak_rrr_or_imm ick;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_armv8a_op mn opts;
      id_valid := osz_valid;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
      id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted osz sk x (mk_semi2_2_shifted sk (id_semi x))
                       (fun h => mk_semi2_2_shifted_errty (x.(id_semi_errty) h))
                       (fun h => mk_semi2_2_shifted_safe sk (x.(id_semi_safe) h))
  else x.

Notation arith_imm := (Some CAimmC_armv8a_arith_imm) (only parsing).
Notation bitmask_imm := (Some CAimmC_armv8a_bitmask_imm) (only parsing).
Notation no_imm := (None : option caimm_checker_s) (only parsing).

Definition armv8a_ADD_instr : instr_desc_t :=
  mk_arith_instr ADD arith_imm armv8a_ADD_semi.
Definition armv8a_ADDS_instr : instr_desc_t :=
  mk_ariths_instr ADDS arith_imm armv8a_ADDS_semi.
Definition armv8a_SUB_instr : instr_desc_t :=
  mk_arith_instr SUB arith_imm armv8a_SUB_semi.
Definition armv8a_SUBS_instr : instr_desc_t :=
  mk_ariths_instr SUBS arith_imm armv8a_SUBS_semi.

(* Add/subtract with carry (no shifted or immediate forms in A64). *)
Definition mk_carry_instr mn (semi : word osz -> word osz -> bool -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz; lbool ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; F CF ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_rrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

Definition mk_carrys_instr mn (semi : word osz -> word osz -> bool -> ty_nzcv_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz; lbool ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; F CF ];
    id_tout := snzcv ++ [:: lword osz ];
    id_out := ad_nzcv ++ [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_rrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

Definition armv8a_ADC_instr : instr_desc_t := mk_carry_instr ADC armv8a_ADC_semi.
Definition armv8a_ADCS_instr : instr_desc_t := mk_carrys_instr ADCS armv8a_ADCS_semi.
Definition armv8a_SBC_instr : instr_desc_t := mk_carry_instr SBC armv8a_SBC_semi.
Definition armv8a_SBCS_instr : instr_desc_t := mk_carrys_instr SBCS armv8a_SBCS_semi.

Definition armv8a_NEG_instr : instr_desc_t :=
  let mn := NEG in
  let tin := [:: lword osz ] in
  let semi := armv8a_NEG_semi (ws := osz) in
  let x :=
    {|
      id_msb_flag := msbf;
      id_tin := tin;
      id_in := [:: Ea 1 ];
      id_tout := [:: lword osz ];
      id_out := [:: Ea 0 ];
      id_semi := sem_lprod_ok tin semi;
      id_nargs := 2;
      id_args_kinds := ak_rr;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_armv8a_op mn opts;
      id_valid := osz_valid;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
      id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted osz sk x (mk_semi1_shifted sk (id_semi x))
                       (fun h => mk_semi1_shifted_errty (x.(id_semi_errty) h))
                       (fun h => mk_semi1_shifted_safe sk (x.(id_semi_safe) h))
  else x.

(* A three-register instruction without flags (MUL, SDIV, UDIV, ...). *)
Definition mk_rrr_instr mn (semi : word osz -> word osz -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_rrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

Definition armv8a_MUL_instr : instr_desc_t := mk_rrr_instr MUL armv8a_MUL_semi.
Definition armv8a_SDIV_instr : instr_desc_t := mk_rrr_instr SDIV armv8a_SDIV_semi.
Definition armv8a_UDIV_instr : instr_desc_t := mk_rrr_instr UDIV armv8a_UDIV_semi.

(* Multiply-add and multiply-subtract. *)
Definition mk_madd_instr mn (semi : word osz -> word osz -> word osz -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz; lword osz ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 4;
    id_args_kinds := ak_rrrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

Definition armv8a_MADD_instr : instr_desc_t := mk_madd_instr MADD armv8a_MADD_semi.
Definition armv8a_MSUB_instr : instr_desc_t := mk_madd_instr MSUB armv8a_MSUB_semi.

(* 32x32 -> 64 multiplies (X form only). *)
Definition mk_mull_instr mn (semi : word U32 -> word U32 -> ty_r)
  : instr_desc_t :=
  let tin := [:: lword U32; lword U32 ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_rrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz == U64;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

Definition armv8a_UMULL_instr : instr_desc_t := mk_mull_instr UMULL armv8a_UMULL_semi.
Definition armv8a_SMULL_instr : instr_desc_t := mk_mull_instr SMULL armv8a_SMULL_semi.

Definition mk_maddl_instr mn (semi : word U32 -> word U32 -> word U64 -> ty_r)
  : instr_desc_t :=
  let tin := [:: lword U32; lword U32; lreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 4;
    id_args_kinds := ak_rrrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz == U64;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

Definition armv8a_UMADDL_instr : instr_desc_t := mk_maddl_instr UMADDL armv8a_UMADDL_semi.
Definition armv8a_SMADDL_instr : instr_desc_t := mk_maddl_instr SMADDL armv8a_SMADDL_semi.

(* High 64 bits of a 64x64 multiply (X form only). *)
Definition mk_mulh_instr mn (semi : word U64 -> word U64 -> ty_r)
  : instr_desc_t :=
  let tin := [:: lreg; lreg ] in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_rrr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz == U64;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

Definition armv8a_UMULH_instr : instr_desc_t := mk_mulh_instr UMULH armv8a_UMULH_semi.
Definition armv8a_SMULH_instr : instr_desc_t := mk_mulh_instr SMULH armv8a_SMULH_semi.

(* -------------------------------------------------------------------- *)
(* Bitwise instructions. *)

(* [C6.2.15 AND (shifted register)] ARM DDI 0487 M.a, p. 1813
   Bitwise AND (shifted register)  This instruction performs a bitwise AND of a
   register value and an optionally-shifted register value, and writes the
   result to the destination register.
   Syntax: AND <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     X[d, datasize] = operand1 AND operand2;
*)
Definition armv8a_AND_instr : instr_desc_t :=
  mk_arith_instr AND bitmask_imm (armv8a_bitwise_semi id id wand).

Definition armv8a_ANDS_instr : instr_desc_t :=
  mk_ariths_instr ANDS bitmask_imm armv8a_ANDS_semi.

(* [C6.2.41 BIC (shifted register)] ARM DDI 0487 M.a, p. 1856
   Bitwise bit clear (shifted register)  This instruction performs a bitwise
   AND of a register value and the complement of an optionally-shifted register
   value, and writes the result to the destination register.
   Syntax: BIC <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     X[d, datasize] = operand1 AND NOT(operand2);
*)
(* BIC and BICS have no immediate form in A64 (the assembler does not
   invert bitmask immediates into AND/ANDS). *)
Definition armv8a_BIC_instr : instr_desc_t :=
  mk_arith_instr BIC no_imm (armv8a_bitwise_semi id wnot wand).

Definition armv8a_BICS_instr : instr_desc_t :=
  mk_ariths_instr BICS no_imm armv8a_BICS_semi.

(* [C6.2.301 ORR (shifted register)] ARM DDI 0487 M.a, p. 2453
   Bitwise OR (shifted register)  This instruction performs a bitwise
   (inclusive) OR of a register value and an optionally-shifted register value,
   and writes the result to the destination register.  This instruction is used
   by the alias MOV (register).
   Syntax: ORR <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     X[d, datasize] = operand1 OR operand2;
*)
Definition armv8a_ORR_instr : instr_desc_t :=
  mk_arith_instr ORR bitmask_imm (armv8a_bitwise_semi id id wor).

(* [C6.2.156 EOR (shifted register)] ARM DDI 0487 M.a, p. 2169
   Bitwise exclusive-OR (shifted register)  This instruction performs a bitwise
   exclusive-OR of a register value and an optionally-shifted register value,
   and writes the result to the destination register.
   Syntax: EOR <Xd>, <Xn>, <Xm>{, <shift> #<amount>}
   Operation (ASL):
     constant bits(datasize) operand1 = X[n, datasize];
     constant bits(datasize) operand2 = ShiftReg(m, shift_type, shift_amount, datasize);
     X[d, datasize] = operand1 EOR operand2;
*)
Definition armv8a_EOR_instr : instr_desc_t :=
  mk_arith_instr EOR bitmask_imm (armv8a_bitwise_semi id id wxor).

(* MVN is an alias of ORN (shifted register); it has no immediate form
   (an inverted immediate is a MOV with the complemented value). *)
Definition armv8a_MVN_instr : instr_desc_t :=
  let mn := MVN in
  let tin := [:: lword osz ] in
  let semi := armv8a_MVN_semi (ws := osz) in
  let x :=
    {|
      id_msb_flag := msbf;
      id_tin := tin;
      id_in := [:: Ea 1 ];
      id_tout := [:: lword osz ];
      id_out := [:: Ea 0 ];
      id_semi := sem_lprod_ok tin semi;
      id_nargs := 2;
      id_args_kinds := ak_rr_or_imm no_imm;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_armv8a_op mn opts;
      id_valid := osz_valid;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
      id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted osz sk x (mk_semi1_shifted sk (id_semi x))
                       (fun h => mk_semi1_shifted_errty (x.(id_semi_errty) h))
                       (fun h => mk_semi1_shifted_safe sk (x.(id_semi_safe) h))
  else x.

(* -------------------------------------------------------------------- *)
(* Shift instructions.
   The shift amount is the value of the second operand modulo the operand
   size; the immediate forms are restricted by the argument checker. Only
   the alias mnemonics (ASR, ...) are provided: they accept registers and
   immediates, subsuming the base variable forms (ASRV, ...), which accept
   only registers and are otherwise identical. *)

Definition mk_shift_instr mn (op : forall sz, word sz -> Z -> word sz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword U8 ] in
  let semi := armv8a_shift_semi (ws := osz) op in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_rrr ++ ak_rr_imm_shift;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* [C6.2.19 ASR (register)] ARM DDI 0487 M.a, p. 1820
   Arithmetic shift right (register)  This instruction shifts a register value
   right by a variable number of bits, shifting in copies of its sign bit, and
   writes the result to the destination register. The value of the second
   source register modulo the register size in bits gives the number of bits by
   which the first source register is right-shifted.  This is an alias of ASRV.
   This means:  • The encodings in this description are named to match the
   encodings of ASRV. • The description of ASRV gives the operational
   pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any operational
   information for this instruction.
   Syntax: ASR <Xd>, <Xn>, <Xm>  ==  ASRV <Xd>, <Xn>, <Xm>
   Operation (ASL, from the ASRV description):
     constant bits(datasize) operand2 = X[m, datasize];
     X[d, datasize] = ShiftReg(n, shift_type, UInt(operand2) MOD datasize, datasize);
*)
Definition armv8a_ASR_instr : instr_desc_t := mk_shift_instr ASR (@wsar).
(* [C6.2.268 LSL (register)] ARM DDI 0487 M.a, p. 2389
   Logical shift left (register)  This instruction shifts a register value left
   by a variable number of bits, shifting in zeros, and writes the result to
   the destination register. The value of the second source register modulo the
   register size in bits gives the number of bits by which the first source
   register is left-shifted.  This is an alias of LSLV. This means:  • The
   encodings in this description are named to match the encodings of LSLV. •
   The description of LSLV gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: LSL <Xd>, <Xn>, <Xm>  ==  LSLV <Xd>, <Xn>, <Xm>
   Operation (ASL, from the LSLV description):
     constant bits(datasize) operand2 = X[m, datasize];
     X[d, datasize] = ShiftReg(n, shift_type, UInt(operand2) MOD datasize, datasize);
*)
Definition armv8a_LSL_instr : instr_desc_t := mk_shift_instr LSL (@wshl).
(* [C6.2.271 LSR (register)] ARM DDI 0487 M.a, p. 2395
   Logical shift right (register)  This instruction shifts a register value
   right by a variable number of bits, shifting in zeros, and writes the result
   to the destination register. The value of the second source register modulo
   the register size in bits gives the number of bits by which the first source
   register is right-shifted.  This is an alias of LSRV. This means:  • The
   encodings in this description are named to match the encodings of LSRV. •
   The description of LSRV gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: LSR <Xd>, <Xn>, <Xm>  ==  LSRV <Xd>, <Xn>, <Xm>
   Operation (ASL, from the LSRV description):
     constant bits(datasize) operand2 = X[m, datasize];
     X[d, datasize] = ShiftReg(n, shift_type, UInt(operand2) MOD datasize, datasize);
*)
Definition armv8a_LSR_instr : instr_desc_t := mk_shift_instr LSR (@wshr).
(* [C6.2.347 ROR (register)] ARM DDI 0487 M.a, p. 2541
   Rotate right (register)  This instruction provides the value of the contents
   of a register rotated by a variable number of bits. The bits that are
   rotated off the right end are inserted into the vacated bit positions on the
   left. The value of the second source register modulo the register size in
   bits gives the number of bits by which the first source register is right-
   shifted.  This is an alias of RORV. This means:  • The encodings in this
   description are named to match the encodings of RORV. • The description of
   RORV gives the operational pseudocode, any CONSTRAINED UNPREDICTABLE
   behavior, and any operational information for this instruction.
   Syntax: ROR <Xd>, <Xn>, <Xm>  ==  RORV <Xd>, <Xn>, <Xm>
   Operation (ASL, from the RORV description):
     constant bits(datasize) operand2 = X[m, datasize];
     X[d, datasize] = ShiftReg(n, shift_type, UInt(operand2) MOD datasize, datasize);
*)
Definition armv8a_ROR_instr : instr_desc_t := mk_shift_instr ROR (@wror).

(* -------------------------------------------------------------------- *)
(* Bit field instructions. *)

(* [C6.2.37 BFC] ARM DDI 0487 M.a, p. 1848
   Bitfield clear  This instruction sets a bitfield of <width> bits at bit
   position <lsb> of the destination register to zero, leaving the other
   destination bits unchanged.  This is an alias of BFM. This means:  • The
   encodings in this description are named to match the encodings of BFM. • The
   description of BFM gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: BFC <Xd>, #<lsb>, #<width>  ==  BFM <Xd>, XZR, #(-<lsb> MOD 64), #(<width>-1)
   Operation (ASL):
     The description of BFM gives the operational pseudocode for this instruction.
   Base instruction [C6.2.39 BFM] p. 1852, Operation (ASL):
     constant bits(datasize) dst = X[d, datasize];
     constant bits(datasize) src = X[n, datasize];
     // Perform bitfield move on low bits
     constant bits(datasize) bot = (dst AND NOT(wmask)) OR (ROR(src, r) AND wmask);
     // Combine extension bits and result bits
     X[d, datasize] = (dst AND NOT(tmask)) OR (bot AND tmask);
*)
Definition armv8a_BFC_semi (x : word osz) (lsb width : word U8) : exec (ty_w osz) :=
  let bits := wsize_bits osz in
  let lsbit := wunsigned lsb in
  let nbits := wunsigned width in
  Let _ := assert (lsbit <? bits)%Z E.no_semantics in
  Let _ := assert (1 <=? nbits)%Z E.no_semantics in
  Let _ := assert (nbits <=? bits - lsbit)%Z E.no_semantics in
  let msbit := (lsbit + nbits - 1)%Z in
  let mk i :=
    if [&& Z.to_nat lsbit <=? i & i <=? Z.to_nat msbit ]
    then false
    else wbit_n x i
  in
  ok (winit osz mk).

Definition armv8a_BFC_semi_sc :=
  [:: ULt U8 1 (wsize_bits osz); UGe U8 1%Z 2; UaddLe U8 2 1 (wsize_bits osz)].

Lemma armv8a_BFC_semi_errty :
  sem_lforall (fun r : result error (sem_ltuple [:: lword osz ]) => r <> Error ErrType)
   [:: lword osz; lword8; lword8 ] armv8a_BFC_semi.
Proof.
  rewrite /armv8a_BFC_semi => x lsb width.
  by case: (_ <? _)%Z => //; case: (1 <=? _)%Z => //; case: (_ <=? _)%Z.
Qed.

Lemma armv8a_BFC_semi_safe :
  interp_safe_cond_lty [:: lword osz; lword8; lword8 ] armv8a_BFC_semi_sc armv8a_BFC_semi.
Proof.
  rewrite /interp_safe_cond_ty /= => x lsb width.
  move=> /List.Forall_cons_iff /= [] /[swap] /List.Forall_cons_iff /= [] /[swap] /List.Forall_cons_iff /= [].
  rewrite !truncate_word_u => /(_ _ _ erefl erefl) h3 _ /(_ _ erefl) /ZleP h2 /(_ _ erefl) /ZltP h1.
  have /ZleP {}h3 : (wunsigned width <= wsize_bits osz - wunsigned lsb)%Z by Lia.lia.
  rewrite /armv8a_BFC_semi h1 h2 h3 /=; eauto.
Qed.

Definition armv8a_BFC_instr : instr_desc_t :=
  let mn := BFC in
  {|
    id_msb_flag := msbf;
    id_tin := [:: lword osz; lword8; lword8 ];
    id_in := [:: Ea 0; Ea 1; Ea 2 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := armv8a_BFC_semi;
    id_nargs := 3;
    id_args_kinds := ak_r_imm8_imm8;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := armv8a_BFC_semi_sc;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => armv8a_BFC_semi_errty;
    id_semi_safe := fun _ => armv8a_BFC_semi_safe;
  |}.

(* [C6.2.38 BFI] ARM DDI 0487 M.a, p. 1850
   Bitfield insert  This instruction copies a bitfield of <width> bits from the
   least significant bits of the source register to bit position <lsb> of the
   destination register, leaving the other destination bits unchanged.  This is
   an alias of BFM. This means:  • The encodings in this description are named
   to match the encodings of BFM. • The description of BFM gives the
   operational pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any
   operational information for this instruction.
   Syntax: BFI <Xd>, <Xn>, #<lsb>, #<width>  ==  BFM <Xd>, <Xn>, #(-<lsb> MOD 64), #(<width>-1)
   Operation (ASL):
     The description of BFM gives the operational pseudocode for this instruction.
   Base instruction [C6.2.39 BFM] p. 1852, Operation (ASL):
     constant bits(datasize) dst = X[d, datasize];
     constant bits(datasize) src = X[n, datasize];
     // Perform bitfield move on low bits
     constant bits(datasize) bot = (dst AND NOT(wmask)) OR (ROR(src, r) AND wmask);
     // Combine extension bits and result bits
     X[d, datasize] = (dst AND NOT(tmask)) OR (bot AND tmask);
*)
Definition armv8a_BFI_semi (x y : word osz) (lsb width : word U8) : exec (ty_w osz) :=
  let bits := wsize_bits osz in
  let lsbit := wunsigned lsb in
  let nbits := wunsigned width in
  Let _ := assert (lsbit <? bits)%Z E.no_semantics in
  Let _ := assert (1 <=? nbits)%Z E.no_semantics in
  Let _ := assert (nbits <=? bits - lsbit)%Z E.no_semantics in
  let msbit := (lsbit + nbits - 1)%Z in
  let mk i :=
    if [&& Z.to_nat lsbit <=? i & i <=? Z.to_nat msbit ]
    then wbit_n y (i - Z.to_nat lsbit)
    else wbit_n x i
  in
  ok (winit osz mk).

Definition armv8a_BFI_semi_sc :=
  [:: ULt U8 2 (wsize_bits osz); UGe U8 1%Z 3; UaddLe U8 3 2 (wsize_bits osz)].

Lemma armv8a_BFI_semi_errty :
  sem_lforall (fun r : result error (sem_ltuple [:: lword osz ]) => r <> Error ErrType)
   [:: lword osz; lword osz; lword8; lword8 ] armv8a_BFI_semi.
Proof.
  rewrite /armv8a_BFI_semi => x y lsb width.
  by case: (_ <? _)%Z => //; case: (1 <=? _)%Z => //; case: (_ <=? _)%Z.
Qed.

Lemma armv8a_BFI_semi_safe :
  interp_safe_cond_lty [:: lword osz; lword osz; lword8; lword8 ] armv8a_BFI_semi_sc armv8a_BFI_semi.
Proof.
  rewrite /interp_safe_cond_ty /= => x y lsb width.
  move=> /List.Forall_cons_iff /= [] /[swap] /List.Forall_cons_iff /= [] /[swap] /List.Forall_cons_iff /= [].
  rewrite !truncate_word_u => /(_ _ _ erefl erefl) h3 _ /(_ _ erefl) /ZleP h2 /(_ _ erefl) /ZltP h1.
  have /ZleP {}h3 : (wunsigned width <= wsize_bits osz - wunsigned lsb)%Z by Lia.lia.
  rewrite /armv8a_BFI_semi h1 h2 h3 /=; eauto.
Qed.

Definition armv8a_BFI_instr : instr_desc_t :=
  let mn := BFI in
  {|
    id_msb_flag := msbf;
    id_tin := [:: lword osz; lword osz; lword8; lword8 ];
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := armv8a_BFI_semi;
    id_nargs := 4;
    id_args_kinds := ak_rr_imm8_imm8;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := armv8a_BFI_semi_sc;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => armv8a_BFI_semi_errty;
    id_semi_safe := fun _ => armv8a_BFI_semi_safe;
  |}.

(* [C6.2.40 BFXIL] ARM DDI 0487 M.a, p. 1854
   Bitfield extract and insert at low end  This instruction copies a bitfield
   of <width> bits starting from bit position <lsb> in the source register to
   the least significant bits of the destination register, leaving the other
   destination bits unchanged.  This is an alias of BFM. This means:  • The
   encodings in this description are named to match the encodings of BFM. • The
   description of BFM gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: BFXIL <Xd>, <Xn>, #<lsb>, #<width>  ==  BFM <Xd>, <Xn>, #<lsb>, #(<lsb>+<width>-1)
   Operation (ASL):
     The description of BFM gives the operational pseudocode for this instruction.
   Base instruction [C6.2.39 BFM] p. 1852, Operation (ASL):
     constant bits(datasize) dst = X[d, datasize];
     constant bits(datasize) src = X[n, datasize];
     // Perform bitfield move on low bits
     constant bits(datasize) bot = (dst AND NOT(wmask)) OR (ROR(src, r) AND wmask);
     // Combine extension bits and result bits
     X[d, datasize] = (dst AND NOT(tmask)) OR (bot AND tmask);
*)
Definition armv8a_BFXIL_semi (x y : word osz) (lsb width : word U8) : exec (ty_w osz) :=
  let bits := wsize_bits osz in
  let lsbit := wunsigned lsb in
  let nbits := wunsigned width in
  Let _ := assert (lsbit <? bits)%Z E.no_semantics in
  Let _ := assert (1 <=? nbits)%Z E.no_semantics in
  Let _ := assert (nbits <=? bits - lsbit)%Z E.no_semantics in
  let mk i :=
    if (i <? Z.to_nat nbits)%nat
    then wbit_n y (i + Z.to_nat lsbit)
    else wbit_n x i
  in
  ok (winit osz mk).

Definition armv8a_BFXIL_semi_sc :=
  [:: ULt U8 2 (wsize_bits osz); UGe U8 1%Z 3; UaddLe U8 3 2 (wsize_bits osz)].

Lemma armv8a_BFXIL_semi_errty :
  sem_lforall (fun r : result error (sem_ltuple [:: lword osz ]) => r <> Error ErrType)
   [:: lword osz; lword osz; lword8; lword8 ] armv8a_BFXIL_semi.
Proof.
  rewrite /armv8a_BFXIL_semi => x y lsb width.
  by case: (_ <? _)%Z => //; case: (1 <=? _)%Z => //; case: (_ <=? _)%Z.
Qed.

Lemma armv8a_BFXIL_semi_safe :
  interp_safe_cond_lty [:: lword osz; lword osz; lword8; lword8 ] armv8a_BFXIL_semi_sc armv8a_BFXIL_semi.
Proof.
  rewrite /interp_safe_cond_ty /= => x y lsb width.
  move=> /List.Forall_cons_iff /= [] /[swap] /List.Forall_cons_iff /= [] /[swap] /List.Forall_cons_iff /= [].
  rewrite !truncate_word_u => /(_ _ _ erefl erefl) h3 _ /(_ _ erefl) /ZleP h2 /(_ _ erefl) /ZltP h1.
  have /ZleP {}h3 : (wunsigned width <= wsize_bits osz - wunsigned lsb)%Z by Lia.lia.
  rewrite /armv8a_BFXIL_semi h1 h2 h3 /=; eauto.
Qed.

Definition armv8a_BFXIL_instr : instr_desc_t :=
  let mn := BFXIL in
  {|
    id_msb_flag := msbf;
    id_tin := [:: lword osz; lword osz; lword8; lword8 ];
    id_in := [:: Ea 0; Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := armv8a_BFXIL_semi;
    id_nargs := 4;
    id_args_kinds := ak_rr_imm8_imm8;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := armv8a_BFXIL_semi_sc;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => armv8a_BFXIL_semi_errty;
    id_semi_safe := fun _ => armv8a_BFXIL_semi_safe;
  |}.

Definition bit_field_extract_semi
  (shr : word osz -> Z -> word osz) (wn : word osz) (widx wwidth : word U8) : exec (ty_w osz) :=
  let bits := wsize_bits osz in
  let idx := wunsigned widx in
  let width := wunsigned wwidth in
  Let _ := assert [&& 1 <=? width & width <? bits + 1 - idx]%Z E.no_semantics in
  ok (shr (wshl wn (bits - width - idx)%Z) (bits - width)%Z).

Definition bit_field_extract_semi_sc :=
  [:: UGe U8 1%Z 2; UaddLe U8 2 1 (wsize_bits osz)].

Lemma bit_field_extract_semi_errty shr :
  sem_lforall (fun r : result error (sem_ltuple [:: lword osz ]) => r <> Error ErrType)
   [:: lword osz; lword8; lword8 ] (bit_field_extract_semi shr).
Proof. by rewrite /bit_field_extract_semi => x lsb width; case: andP. Qed.

Lemma bit_field_extract_semi_safe shr :
  interp_safe_cond_lty [:: lword osz; lword8; lword8 ] bit_field_extract_semi_sc (bit_field_extract_semi shr).
Proof.
  rewrite /interp_safe_cond_ty /= => x lsb width.
  move=> /List.Forall_cons_iff /= [] /[swap] /List.Forall_cons_iff /= [].
  rewrite !truncate_word_u => /(_ _ _ erefl erefl) h2 _ /(_ _ erefl) /ZleP h1.
  have /ZltP {}h2 : (wunsigned width < wsize_bits osz + 1 - wunsigned lsb)%Z by Lia.lia.
  rewrite /bit_field_extract_semi h1 h2 /=; eauto.
Qed.

Definition mk_bfx_instr mn (shr : word osz -> Z -> word osz) : instr_desc_t :=
  {|
    id_msb_flag := msbf;
    id_tin := [:: lword osz; lword U8; lword U8 ];
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := bit_field_extract_semi shr;
    id_nargs := 4;
    id_args_kinds := ak_rr_imm_imm_extr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := bit_field_extract_semi_sc;
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => @bit_field_extract_semi_errty shr;
    id_semi_safe := fun _ => @bit_field_extract_semi_safe shr;
  |}.

(* [C6.2.355 SBFX] ARM DDI 0487 M.a, p. 2556
   Signed bitfield extract  This instruction copies a bitfield of <width> bits
   starting from bit position <lsb> in the source register to the least
   significant bits of the destination register, and sets destination bits
   above the bitfield to a copy of the most significant bit of the bitfield.
   This is an alias of SBFM. This means:  • The encodings in this description
   are named to match the encodings of SBFM. • The description of SBFM gives
   the operational pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any
   operational information for this instruction.
   Syntax: SBFX <Xd>, <Xn>, #<lsb>, #<width>  ==  SBFM <Xd>, <Xn>, #<lsb>, #(<lsb>+<width>-1)
   Operation (ASL):
     The description of SBFM gives the operational pseudocode for this instruction.
   Base instruction [C6.2.354 SBFM] p. 2554, Operation (ASL):
     constant bits(datasize) src = X[n, datasize];
     // Perform bitfield move on low bits
     constant bits(datasize) bot = ROR(src, r) AND wmask;
     constant bits(datasize) top = Replicate(src<s>, datasize);
     // Combine extension bits and result bits
     X[d, datasize] = (top AND NOT(tmask)) OR (bot AND tmask);
*)
Definition armv8a_SBFX_instr : instr_desc_t := mk_bfx_instr SBFX (wsar (sz := osz)).
(* [C6.2.487 UBFX] ARM DDI 0487 M.a, p. 2843
   Unsigned bitfield extract  This instruction copies a bitfield of <width>
   bits starting from bit position <lsb> in the source register to the least
   significant bits of the destination register, and sets destination bits
   above the bitfield to zero.  This is an alias of UBFM. This means:  • The
   encodings in this description are named to match the encodings of UBFM. •
   The description of UBFM gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: UBFX <Xd>, <Xn>, #<lsb>, #<width>  ==  UBFM <Xd>, <Xn>, #<lsb>, #(<lsb>+<width>-1)
   Operation (ASL):
     The description of UBFM gives the operational pseudocode for this instruction.
   Base instruction [C6.2.486 UBFM] p. 2841, Operation (ASL):
     constant bits(datasize) src = X[n, datasize];
     // Perform bitfield move on low bits
     constant bits(datasize) bot = ROR(src, r) AND wmask;
     // Combine extension bits and result bits
     X[d, datasize] = bot AND tmask;
*)
Definition armv8a_UBFX_instr : instr_desc_t := mk_bfx_instr UBFX (wshr (sz := osz)).

Definition armv8a_EXTR_instr : instr_desc_t :=
  let mn := EXTR in
  let tin := [:: lword osz; lword osz; lword U8 ] in
  let semi := armv8a_EXTR_semi (ws := osz) in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 4;
    id_args_kinds := ak_rrr_imm_shift;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* -------------------------------------------------------------------- *)
(* Moves. *)

Definition armv8a_MOV_instr : instr_desc_t :=
  let mn := MOV in
  let tin := [:: lword osz ] in
  let semi := armv8a_MOV_semi (ws := osz) in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 2;
    id_args_kinds :=
      ak_reg_reg ++ [:: [:: [:: CAreg ]; [:: CAimm CAimmC_armv8a_mov_imm osz ] ] ];
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

Definition mk_movw_instr mn (semi : word U16 -> word U8 -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword U16; lword U8 ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_r_imm16_shift;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

Definition armv8a_MOVZ_instr : instr_desc_t :=
  mk_movw_instr MOVZ (armv8a_MOVZ_semi (ws := osz)).

Definition armv8a_MOVN_instr : instr_desc_t :=
  mk_movw_instr MOVN (armv8a_MOVN_semi (ws := osz)).

Definition armv8a_MOVK_instr : instr_desc_t :=
  let mn := MOVK in
  let tin := [:: lword osz; lword U16; lword U8 ] in
  let semi := armv8a_MOVK_semi (ws := osz) in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 0; Ea 1; Ea 2 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 3;
    id_args_kinds := ak_r_imm16_shift;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

Definition armv8a_ADR_instr : instr_desc_t :=
  let mn := ADR in
  let tin := [:: lreg ] in
  let semi := armv8a_ADR_semi in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ec 1 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz == U64;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* -------------------------------------------------------------------- *)
(* Extensions.
   [in_ws] is the width of the extracted low bits; the result is extended
   to the operand size. SXTW and UXTW only exist in the X form. *)

Definition mk_extend_instr mn (in_ws : wsize) (sign : bool) (valid : bool)
  : instr_desc_t :=
  let tin := [:: lword in_ws ] in
  let semi := armv8a_extend_semi (ws := in_ws) sign osz in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* [C6.2.471 SXTB] ARM DDI 0487 M.a, p. 2812
   Signed extend byte  This instruction extracts an 8-bit value from a
   register, sign-extends it to the size of the register, and writes the result
   to the destination register.  This is an alias of SBFM. This means:  • The
   encodings in this description are named to match the encodings of SBFM. •
   The description of SBFM gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: SXTB <Xd>, <Wn>  ==  SBFM <Xd>, <Xn>, #0, #7
   Operation (ASL):
     The description of SBFM gives the operational pseudocode for this instruction.
*)
Definition armv8a_SXTB_instr : instr_desc_t := mk_extend_instr SXTB U8 true osz_valid.
(* [C6.2.472 SXTH] ARM DDI 0487 M.a, p. 2813
   Sign extend halfword  This instruction extracts a 16-bit value, sign-extends
   it to the size of the register, and writes the result to the destination
   register.  This is an alias of SBFM. This means:  • The encodings in this
   description are named to match the encodings of SBFM. • The description of
   SBFM gives the operational pseudocode, any CONSTRAINED UNPREDICTABLE
   behavior, and any operational information for this instruction.
   Syntax: SXTH <Xd>, <Wn>  ==  SBFM <Xd>, <Xn>, #0, #15
   Operation (ASL):
     The description of SBFM gives the operational pseudocode for this instruction.
*)
Definition armv8a_SXTH_instr : instr_desc_t := mk_extend_instr SXTH U16 true osz_valid.
(* [C6.2.473 SXTW] ARM DDI 0487 M.a, p. 2814
   Sign extend word  This instruction sign-extends a word to the size of the
   register, and writes the result to the destination register.  This is an
   alias of SBFM. This means:  • The encodings in this description are named to
   match the encodings of SBFM. • The description of SBFM gives the operational
   pseudocode, any CONSTRAINED UNPREDICTABLE behavior, and any operational
   information for this instruction.
   Syntax: SXTW <Xd>, <Wn>  ==  SBFM <Xd>, <Xn>, #0, #31
   Operation (ASL):
     The description of SBFM gives the operational pseudocode for this instruction.
*)
Definition armv8a_SXTW_instr : instr_desc_t := mk_extend_instr SXTW U32 true (osz == U64).
(* [C6.2.499 UXTB] ARM DDI 0487 M.a, p. 2863
   Unsigned extend byte  This instruction extracts an 8-bit value from a
   register, zero-extends it to the size of the register, and writes the result
   to the destination register.  This is an alias of UBFM. This means:  • The
   encodings in this description are named to match the encodings of UBFM. •
   The description of UBFM gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: UXTB <Wd>, <Wn>  ==  UBFM <Wd>, <Wn>, #0, #7
   Operation (ASL):
     The description of UBFM gives the operational pseudocode for this instruction.
*)
Definition armv8a_UXTB_instr : instr_desc_t := mk_extend_instr UXTB U8 false osz_valid.
(* [C6.2.500 UXTH] ARM DDI 0487 M.a, p. 2864
   Unsigned extend halfword  This instruction extracts a 16-bit value from a
   register, zero-extends it to the size of the register, and writes the result
   to the destination register.  This is an alias of UBFM. This means:  • The
   encodings in this description are named to match the encodings of UBFM. •
   The description of UBFM gives the operational pseudocode, any CONSTRAINED
   UNPREDICTABLE behavior, and any operational information for this
   instruction.
   Syntax: UXTH <Wd>, <Wn>  ==  UBFM <Wd>, <Wn>, #0, #15
   Operation (ASL):
     The description of UBFM gives the operational pseudocode for this instruction.
*)
Definition armv8a_UXTH_instr : instr_desc_t := mk_extend_instr UXTH U16 false osz_valid.
(* [C6.2.281 MOV (register)] ARM DDI 0487 M.a, p. 2413
   Move register value  This instruction copies the value in a source register
   to the destination register.  This is an alias of ORR (shifted register).
   This means:  • The encodings in this description are named to match the
   encodings of ORR (shifted register). • The description of ORR (shifted
   register) gives the operational pseudocode, any CONSTRAINED UNPREDICTABLE
   behavior, and any operational information for this instruction.
   Note: The ARM ARM defines no UXTW entry: UXTW #0 is equivalent to a 32-bit register MOV (alias of ORR (shifted register)), whose 32-bit result is zero-extended to 64 bits; the MOV (register) entry is recorded here in its place.
   Syntax: MOV <Xd>, <Xm>  ==  ORR <Xd>, XZR, <Xm>
   Operation (ASL):
     The description of ORR (shifted register) gives the operational pseudocode for this instruction.
*)
Definition armv8a_UXTW_instr : instr_desc_t := mk_extend_instr UXTW U32 false (osz == U64).

(* -------------------------------------------------------------------- *)
(* Bit-manipulation instructions. *)

Definition mk_unary_instr mn (semi : word osz -> ty_w osz) (valid : bool)
  : instr_desc_t :=
  let tin := [:: lword osz ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

Definition armv8a_RBIT_instr := mk_unary_instr RBIT (armv8a_RBIT_semi (ws := osz)) osz_valid.
Definition armv8a_REV_instr := mk_unary_instr REV (armv8a_REV_semi (ws := osz)) osz_valid.
Definition armv8a_REV16_instr := mk_unary_instr REV16 (armv8a_REV16_semi (ws := osz)) osz_valid.
Definition armv8a_CLZ_instr := mk_unary_instr CLZ (armv8a_CLZ_semi (ws := osz)) osz_valid.
Definition armv8a_CLS_instr := mk_unary_instr CLS (armv8a_CLS_semi (ws := osz)) osz_valid.

Definition armv8a_REV32_instr : instr_desc_t :=
  let mn := REV32 in
  let tin := [:: lreg ] in
  let semi := armv8a_REV32_semi in
  {|
    id_msb_flag := MSB_MERGE;
    id_tin := tin;
    id_in := [:: Ea 1 ];
    id_tout := [:: lreg ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_reg;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz == U64;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* -------------------------------------------------------------------- *)
(* Comparisons. *)

Definition mk_cmp_instr mn (ick : option caimm_checker_s)
  (semi : word osz -> word osz -> ty_nzcv)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz ] in
  let x :=
    {|
      id_msb_flag := MSB_MERGE;
      id_tin := tin;
      id_in := [:: Ea 0; Ea 1 ];
      id_tout := snzcv;
      id_out := ad_nzcv;
      id_semi := sem_lprod_ok tin semi;
      id_nargs := 2;
      id_args_kinds := ak_rr_or_imm ick;
      id_eq_size := refl_equal;
      id_check_dest := refl_equal;
      id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
      id_safe := [::];
      id_pp_asm := pp_armv8a_op mn opts;
      id_valid := osz_valid;
      id_safe_wf := refl_equal;
      id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
      id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
    |}
  in
  if has_shift opts is Some sk
  then mk_shifted osz sk x (mk_semi2_2_shifted sk (id_semi x))
                       (fun h => mk_semi2_2_shifted_errty (x.(id_semi_errty) h))
                       (fun h => mk_semi2_2_shifted_safe sk (x.(id_semi_safe) h))
  else x.

Definition armv8a_CMP_instr : instr_desc_t :=
  mk_cmp_instr CMP arith_imm armv8a_CMP_semi.
Definition armv8a_CMN_instr : instr_desc_t :=
  mk_cmp_instr CMN arith_imm armv8a_CMN_semi.
Definition armv8a_TST_instr : instr_desc_t :=
  mk_cmp_instr TST bitmask_imm armv8a_TST_semi.

(* -------------------------------------------------------------------- *)
(* Conditional selection.
   The condition is a first-class operand (the [CAcond] argument kind),
   evaluated by [arm_eval_cond] on the NZCV flags and passed to the
   semantics as a boolean. *)

Definition mk_csel_instr mn (semi : word osz -> word osz -> bool -> ty_w osz)
  : instr_desc_t :=
  let tin := [:: lword osz; lword osz; lbool ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1; Ea 2; Ea 3 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 4;
    id_args_kinds := ak_rrr_cond;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

Definition armv8a_CSEL_instr := mk_csel_instr CSEL (armv8a_CSEL_semi (ws := osz)).
Definition armv8a_CSINC_instr := mk_csel_instr CSINC (armv8a_CSINC_semi (ws := osz)).
Definition armv8a_CSINV_instr := mk_csel_instr CSINV (armv8a_CSINV_semi (ws := osz)).
Definition armv8a_CSNEG_instr := mk_csel_instr CSNEG (armv8a_CSNEG_semi (ws := osz)).

Definition mk_cset_instr mn (semi : bool -> ty_w osz) : instr_desc_t :=
  let tin := [:: lbool ] in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Ea 1 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := ak_r_cond;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

Definition armv8a_CSET_instr := mk_cset_instr CSET (armv8a_CSET_semi (ws := osz)).
Definition armv8a_CSETM_instr := mk_cset_instr CSETM (armv8a_CSETM_semi (ws := osz)).

(* -------------------------------------------------------------------- *)
(* Loads and stores.
   The memory access itself is performed by the framework ([eval_asm_arg]
   reads or writes memory for address arguments); the instruction semantics
   only sign- or zero-extends the transferred value. [LDR] and [STR] access
   memory at the operand size; the narrow loads and stores have their
   access width in the mnemonic. *)

(* [C6.2.217 LDR (register)] ARM DDI 0487 M.a, p. 2275
   Load register (register)  This instruction calculates an address from a base
   register value and an offset register value, loads a word from memory, and
   writes it to a register. The offset register value can optionally be shifted
   and extended. For information about addressing modes, see Load/Store
   addressing modes.
   Syntax: LDR <Wt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Syntax: LDR <Xt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(datasize) data = Mem[address, datasize DIV 8, accdesc];
     X[t, regsize] = ZeroExtend(data, regsize);
*)
Definition armv8a_load_instr mn : instr_desc_t :=
  let wacc :=
    if wsize_of_narrow_load_mn mn is Some ws'
    then ws'
    else osz
  in
  let tin := [:: lword wacc ] in
  let semi := armv8a_extend_semi (ws := wacc) (isSome (wsize_of_sload_mn mn)) osz in
  {|
    id_msb_flag := msbf;
    id_tin := tin;
    id_in := [:: Eu 1 ];
    id_tout := [:: lword osz ];
    id_out := [:: Ea 0 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid && (if mn is LDRSW then osz == U64 else true);
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* [C6.2.220 LDRB (register)] ARM DDI 0487 M.a, p. 2283
   Load register byte (register)  This instruction calculates an address from a
   base register value and an offset register value, loads a byte from memory,
   zero-extends it, and writes it to a register. For information about
   addressing modes, see Load/Store addressing modes.
   Syntax: LDRB <Wt>, [<Xn|SP>, (<Wm>|<Xm>), <extend> {<amount>}]
   Syntax: LDRB <Wt>, [<Xn|SP>, <Xm>{, LSL <amount>}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(8) data = Mem[address, 1, accdesc];
     X[t, 32] = ZeroExtend(data, 32);
*)

(* [C6.2.222 LDRH (register)] ARM DDI 0487 M.a, p. 2288
   Load register halfword (register)  This instruction calculates an address
   from a base register value and an offset register value, loads a halfword
   from memory, zero-extends it, and writes it to a register. For information
   about addressing modes, see Load/Store addressing modes.
   Syntax: LDRH <Wt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(16) data = Mem[address, 2, accdesc];
     X[t, 32] = ZeroExtend(data, 32);
*)

(* [C6.2.224 LDRSB (register)] ARM DDI 0487 M.a, p. 2293
   Load register signed byte (register)  This instruction calculates an address
   from a base register value and an offset register value, loads a byte from
   memory, sign-extends it, and writes it to a register. For information about
   addressing modes, see Load/Store addressing modes.
   Syntax: LDRSB <Wt>, [<Xn|SP>, (<Wm>|<Xm>), <extend> {<amount>}]
   Syntax: LDRSB <Wt>, [<Xn|SP>, <Xm>{, LSL <amount>}]
   Syntax: LDRSB <Xt>, [<Xn|SP>, (<Wm>|<Xm>), <extend> {<amount>}]
   Syntax: LDRSB <Xt>, [<Xn|SP>, <Xm>{, LSL <amount>}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(8) data = Mem[address, 1, accdesc];
     X[t, regsize] = SignExtend(data, regsize);
*)

(* [C6.2.226 LDRSH (register)] ARM DDI 0487 M.a, p. 2298
   Load register signed halfword (register)  This instruction calculates an
   address from a base register value and an offset register value, loads a
   halfword from memory, sign-extends it, and writes it to a register. For
   information about addressing modes, see Load/Store addressing modes.
   Syntax: LDRSH <Wt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Syntax: LDRSH <Xt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(16) data = Mem[address, 2, accdesc];
     X[t, regsize] = SignExtend(data, regsize);
*)

(* [C6.2.229 LDRSW (register)] ARM DDI 0487 M.a, p. 2304
   Load register signed word (register)  This instruction calculates an address
   from a base register value and an offset register value, loads a word from
   memory, sign-extends it to form a 64-bit value, and writes it to a register.
   The offset register value can be shifted left by 0 or 2 bits. For
   information about addressing modes, see Load/Store addressing modes.
   Syntax: LDRSW <Xt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_LOAD, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     constant bits(32) data = Mem[address, 4, accdesc];
     X[t, 64] = SignExtend(data, 64);
*)

(* [C6.2.415 STR (register)] ARM DDI 0487 M.a, p. 2693
   Store register (register)  This instruction calculates an address from a
   base register value and an offset register value, and stores a 32-bit word
   or a 64-bit doubleword to the calculated address, from a register. For
   information about addressing modes, see Load/Store addressing modes.  The
   instruction uses an offset addressing mode, that calculates the address used
   for the memory access from a base register value and an offset register
   value. The offset can be optionally shifted and extended.
   Syntax: STR <Wt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Syntax: STR <Xt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_STORE, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     Mem[address, datasize DIV 8, accdesc] = X[t, datasize];
*)
Definition armv8a_store_instr mn : instr_desc_t :=
  let wacc :=
    if wsize_of_narrow_store_mn mn is Some ws'
    then ws'
    else osz
  in
  let tin := [:: lword wacc ] in
  let semi := armv8a_extend_semi (ws := wacc) false wacc in
  {|
    id_msb_flag := MSB_MERGE;
    (* The input should be an [osz] word and be zero_extended to the output
       size, but this is implicit in Jasmin semantics. *)
    id_tin := tin;
    id_in := [:: Ea 0 ];
    id_tout := [:: lword wacc ];
    id_out := [:: Eu 1 ];
    id_semi := sem_lprod_ok tin semi;
    id_nargs := 2;
    id_args_kinds := ak_reg_addr;
    id_eq_size := refl_equal;
    id_check_dest := refl_equal;
    id_str_jas := pp_s (string_of_armv8a_mnemonic mn);
    id_safe := [::];
    id_pp_asm := pp_armv8a_op mn opts;
    id_valid := osz_valid;
    id_safe_wf := refl_equal;
    id_semi_errty := fun _ => sem_lprod_ok_error tin semi;
    id_semi_safe := fun _ => sem_lprod_ok_safe tin semi;
  |}.

(* [C6.2.417 STRB (register)] ARM DDI 0487 M.a, p. 2699
   Store register byte (register)  This instruction calculates an address from
   a base register value and an offset register value, and stores a byte from a
   32-bit register to the calculated address. For information about addressing
   modes, see Load/Store addressing modes.  The instruction uses an offset
   addressing mode, that calculates the address used for the memory access from
   a base register value and an offset register value. The offset can be
   optionally shifted and extended.
   Syntax: STRB <Wt>, [<Xn|SP>, (<Wm>|<Xm>), <extend> {<amount>}]
   Syntax: STRB <Wt>, [<Xn|SP>, <Xm>{, LSL <amount>}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_STORE, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     Mem[address, 1, accdesc] = X[t, 8];
*)

(* [C6.2.419 STRH (register)] ARM DDI 0487 M.a, p. 2704
   Store register halfword (register)  This instruction calculates an address
   from a base register value and an offset register value, and stores a
   halfword from a 32-bit register to the calculated address. For information
   about addressing modes, see Load/Store addressing modes.  The instruction
   uses an offset addressing mode, that calculates the address used for the
   memory access from a base register value and an offset register value. The
   offset can be optionally shifted and extended.
   Syntax: STRH <Wt>, [<Xn|SP>, (<Wm>|<Xm>){, <extend> {<amount>}}]
   Operation (ASL):
     constant bits(64) offset = ExtendReg(m, extend_type, shift, 64);
     bits(64) address;
     constant boolean privileged = PSTATE.EL != EL0;
     constant AccessDescriptor accdesc = CreateAccDescGPR(MemOp_STORE, nontemporal, privileged,
                                                          tagchecked, t);
     if n == 31 then
         CheckSPAlignment();
         address = SP[64];
     else
         address = X[n, 64];
     address = AddressAdd(address, offset, accdesc);
     Mem[address, 2, accdesc] = X[t, 16];
*)

(* -------------------------------------------------------------------- *)
(* Description of instructions. *)

Definition mn_desc (mn : armv8a_mnemonic) : instr_desc_t :=
  match mn with
  | ADD => armv8a_ADD_instr
  | ADDS => armv8a_ADDS_instr
  | ADC => armv8a_ADC_instr
  | ADCS => armv8a_ADCS_instr
  | SUB => armv8a_SUB_instr
  | SUBS => armv8a_SUBS_instr
  | SBC => armv8a_SBC_instr
  | SBCS => armv8a_SBCS_instr
  | NEG => armv8a_NEG_instr
  | MUL => armv8a_MUL_instr
  | MADD => armv8a_MADD_instr
  | MSUB => armv8a_MSUB_instr
  | SDIV => armv8a_SDIV_instr
  | UDIV => armv8a_UDIV_instr
  | UMULL => armv8a_UMULL_instr
  | SMULL => armv8a_SMULL_instr
  | UMADDL => armv8a_UMADDL_instr
  | SMADDL => armv8a_SMADDL_instr
  | UMULH => armv8a_UMULH_instr
  | SMULH => armv8a_SMULH_instr
  | AND => armv8a_AND_instr
  | ANDS => armv8a_ANDS_instr
  | BIC => armv8a_BIC_instr
  | BICS => armv8a_BICS_instr
  | ORR => armv8a_ORR_instr
  | EOR => armv8a_EOR_instr
  | MVN => armv8a_MVN_instr
  | ASR => armv8a_ASR_instr
  | LSL => armv8a_LSL_instr
  | LSR => armv8a_LSR_instr
  | ROR => armv8a_ROR_instr
  | BFC => armv8a_BFC_instr
  | BFI => armv8a_BFI_instr
  | BFXIL => armv8a_BFXIL_instr
  | SBFX => armv8a_SBFX_instr
  | UBFX => armv8a_UBFX_instr
  | EXTR => armv8a_EXTR_instr
  | MOV => armv8a_MOV_instr
  | MOVN => armv8a_MOVN_instr
  | MOVZ => armv8a_MOVZ_instr
  | MOVK => armv8a_MOVK_instr
  | ADR => armv8a_ADR_instr
  | SXTB => armv8a_SXTB_instr
  | SXTH => armv8a_SXTH_instr
  | SXTW => armv8a_SXTW_instr
  | UXTB => armv8a_UXTB_instr
  | UXTH => armv8a_UXTH_instr
  | UXTW => armv8a_UXTW_instr
  | RBIT => armv8a_RBIT_instr
  | REV => armv8a_REV_instr
  | REV16 => armv8a_REV16_instr
  | REV32 => armv8a_REV32_instr
  | CLZ => armv8a_CLZ_instr
  | CLS => armv8a_CLS_instr
  | CMP => armv8a_CMP_instr
  | CMN => armv8a_CMN_instr
  | TST => armv8a_TST_instr
  | CSEL => armv8a_CSEL_instr
  | CSINC => armv8a_CSINC_instr
  | CSINV => armv8a_CSINV_instr
  | CSNEG => armv8a_CSNEG_instr
  | CSET => armv8a_CSET_instr
  | CSETM => armv8a_CSETM_instr
  | LDR => armv8a_load_instr LDR
  | LDRB => armv8a_load_instr LDRB
  | LDRH => armv8a_load_instr LDRH
  | LDRSB => armv8a_load_instr LDRSB
  | LDRSH => armv8a_load_instr LDRSH
  | LDRSW => armv8a_load_instr LDRSW
  | STR => armv8a_store_instr STR
  | STRB => armv8a_store_instr STRB
  | STRH => armv8a_store_instr STRH
  end.

End ARMV8A_INSTR.

Definition armv8a_instr_desc (o : armv8a_asm_op) : instr_desc_t :=
  let '(ARMv8A_op mn opts) := o in
  mn_desc opts mn.

(* Size-suffixed intrinsic parsing: [#ADD] is the X (64-bit) form and
   [#ADD_32] the W form. Fixed-size mnemonics take no suffix. *)
Definition armv8a_prim_sized (mn : armv8a_mnemonic) : prim_constructor armv8a_asm_op :=
  PrimX86
    [:: PVp U64; PVp U32 ]
    (fun s =>
       if s is PVp sz
       then Some (ARMv8A_op mn (opts_at sz))
       else None).

Definition armv8a_prim_string : seq (string * prim_constructor armv8a_asm_op) :=
  map
    (fun mn =>
       (string_of_armv8a_mnemonic mn,
        if mn \in sized_mnemonics
        then armv8a_prim_sized mn
        else primM (ARMv8A_op mn default_opts)))
    cenum.

#[ export ]
Instance armv8a_op_decl : asm_op_decl armv8a_asm_op :=
  {|
    instr_desc_op := armv8a_instr_desc;
    prim_string := armv8a_prim_string;
  |}.

Definition armv8a_prog := @asm_prog _ _ _ _ _ _ _ armv8a_op_decl.
