(* ARMv8A architecture full integration *)
open Arch_decl

module type Armv8a_input = sig
  val call_conv : (Armv8a_decl.register, Arch_utils.empty, Arch_utils.empty, Armv8a_decl.rflag, Armv8a_decl.condt) calling_convention
end

(* Create arch_toIdent for ARMv8A *)
let atoI armv8a_decl =
  let open Prog in
  let mk_var k t s =
    V.mk s (Reg(k,Direct)) (Conv.ty_of_cty (Type.atype_of_ltype t)) L._dummy [] in
  match Arch_extra.MkAToIdent.mk armv8a_decl mk_var with
  | Utils0.Error e ->
      let e = Conv.error_of_cerror (Printer.pp_err ~debug:true) e in
      raise (Utils.HiError e)
  | Utils0.Ok atoI -> atoI

module Armv8a (Lowering_params : Armv8a_input) = struct
  module AD = Armv8a_decl

  type reg = AD.register
  type regx = Arch_utils.empty
  type xreg = Arch_utils.empty
  type nonrec rflag = AD.rflag
  type cond = AD.condt
  type asm_op = Armv8a_instr_decl.armv8a_asm_op
  type extra_op = Armv8a_extra.armv8a_extra_op
  type lowering_options = unit

  let atoI = atoI AD.armv8a_decl

  let asm_e = Armv8a_extra.armv8a_extra atoI

  let aparams = Armv8a_params.armv8a_params atoI

  let known_implicits = ["NF", "_nf_"; "ZF", "_zf_"; "CF", "_cf_"; "VF", "_vf_"]

  let alloc_stack_need_extra _ = false

  let is_ct_asm_op (o : asm_op) =
    match o with
    | Armv8a_instr_decl.ARMv8A_op (Armv8a_instr_decl.SDIV, _) -> false
    | Armv8a_instr_decl.ARMv8A_op (Armv8a_instr_decl.UDIV, _) -> false
    | _ -> true

  let is_doit_asm_op (o : asm_op) =
    match o with
    | Armv8a_instr_decl.ARMv8A_op ((Armv8a_instr_decl.ADD | Armv8a_instr_decl.SUB | Armv8a_instr_decl.MUL | Armv8a_instr_decl.AND | Armv8a_instr_decl.ORR | Armv8a_instr_decl.EOR | Armv8a_instr_decl.LSL | Armv8a_instr_decl.LSR | Armv8a_instr_decl.ASR | Armv8a_instr_decl.MOV), _) -> true
    | Armv8a_instr_decl.ARMv8A_op ((Armv8a_instr_decl.LDR | Armv8a_instr_decl.STR), _) -> true
    | _ -> false

  let is_ct_asm_extra (_o : extra_op) = true

  let is_doit_asm_extra (o : extra_op) =
    match o with
    | Armv8a_extra.Oarmv8a_swap _ -> true
    | Armv8a_extra.Oarmv8a_add_large_imm -> true
    | Armv8a_extra.Oarmv8a_smart_li _ -> true

  let lowering_opt = ()

  let not_saved_stack = []

  let pp_asm = Pp_arm_v8a.print_prog

  let callstyle = Arch_full.ByReg { call = Some Armv8a_decl.R30; return = true }

  let internal_call_conv = Armv8a_decl.armv8a_internal_call_conv

  include Lowering_params
end
