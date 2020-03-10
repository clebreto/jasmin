(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import x86_gen expr.
Import ZArith.
Require Import compiler_util allocation inline dead_calls unrolling remove_globals
   constant_prop dead_code array_expansion lowering stack_alloc linear x86_sem.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition unroll1 (p:uprog) :=
  let p := unroll_prog p in
  let p := const_prop_prog p in
  dead_code_prog p.

Fixpoint unroll (n:nat) (p:uprog) :=
  match n with
  | O   => cferror Ferr_loop
  | S n =>
    Let p' := unroll1 p in
    if (p_funcs p == p_funcs p') then cfok p
    else unroll n p'
  end.

Definition unroll_loop (p:prog) := unroll Loop.nb p.

Section COMPILER.

Variant compiler_step :=
  | Typing                      : compiler_step
  | ParamsExpansion             : compiler_step
  | Inlining                    : compiler_step
  | RemoveUnusedFunction        : compiler_step
  | Unrolling                   : compiler_step
  | Splitting                   : compiler_step
  | AllocInlineAssgn            : compiler_step
  | DeadCode_AllocInlineAssgn   : compiler_step
  | ShareStackVariable          : compiler_step
  | DeadCode_ShareStackVariable : compiler_step
  | RegArrayExpansion           : compiler_step
  | RemoveArrInit               : compiler_step
  | RemoveGlobal                : compiler_step
  | LowerInstruction            : compiler_step
  | RegAllocation               : compiler_step
  | DeadCode_RegAllocation      : compiler_step
  | StackAllocation             : compiler_step
  | Linearisation               : compiler_step
  | Assembly                    : compiler_step.

Record compiler_params := {
  rename_fd        : instr_info -> funname -> ufundef -> ufundef;
  expand_fd        : funname -> ufundef -> ufundef;
  var_alloc_fd     : funname -> ufundef -> ufundef;
  share_stk_fd     : funname -> ufundef -> ufundef;
  lowering_vars    : fresh_vars;
  inline_var       : var -> bool;
  is_var_in_memory : var_i → bool;
  reg_alloc_fd     : funname -> ufundef -> ufundef; (* Fixme : change this *)
  stk_alloc_gl     : uprog → seq u8 * Ident.ident * seq (var * Z);
  stk_pointer_name : Ident.ident;
  stk_alloc_fd     : ufun_decl → Z * seq (var * Z) * (seq var * expr.saved_stack);
  print_uprog      : compiler_step -> uprog -> uprog;
  print_sprog      : compiler_step -> sprog -> sprog;
  print_linear     : lprog -> lprog;
  warning          : instr_info -> warning_msg -> instr_info;
  lowering_opt     : lowering_options;
  is_glob          : var -> bool;
  fresh_id         : glob_decls -> var -> Ident.ident;
}.

Variable cparams : compiler_params.

Definition expand_prog (p:uprog) := map_prog_name cparams.(expand_fd) p.

Definition var_alloc_prog (p:uprog) := map_prog_name cparams.(var_alloc_fd) p.

Definition share_stack_prog (p:uprog) := map_prog_name cparams.(share_stk_fd) p.

Definition reg_alloc_prog (p:uprog) := map_prog_name cparams.(reg_alloc_fd) p.

Definition compile_prog (entries : seq funname) (p:prog) :=
  Let p := inline_prog_err cparams.(inline_var) cparams.(rename_fd) p in
  let p := cparams.(print_uprog) Inlining p in

  Let p := dead_calls_err_seq entries p in
  let p := cparams.(print_uprog) RemoveUnusedFunction p in

  Let p := unroll Loop.nb p in
  let p := cparams.(print_uprog) Unrolling p in

  let p := const_prop_prog p in
  let p := cparams.(print_uprog) Unrolling p in

  let pv := var_alloc_prog p in
  let pv := cparams.(print_uprog) AllocInlineAssgn pv in
  Let _ := CheckAllocRegU.check_prog p.(p_extra) p.(p_funcs) pv.(p_extra) pv.(p_funcs) in
  Let pv := dead_code_prog pv in
  let pv := cparams.(print_uprog) DeadCode_AllocInlineAssgn pv in

  let ps := share_stack_prog pv in
  let ps := cparams.(print_uprog) ShareStackVariable ps in
  Let _ := CheckAllocRegU.check_prog pv.(p_extra) pv.(p_funcs) ps.(p_extra) ps.(p_funcs) in
  Let ps := dead_code_prog ps in
  let ps := cparams.(print_uprog) DeadCode_ShareStackVariable ps in

  let pr := remove_init_prog ps in
  let pr := cparams.(print_uprog) RemoveArrInit pr in

  let pe := expand_prog pr in
  let pe := cparams.(print_uprog) RegArrayExpansion pe in
  Let _ := CheckExpansion.check_prog pr.(p_extra) pr.(p_funcs) pe.(p_extra) pe.(p_funcs) in

  Let pg := remove_glob_prog cparams.(is_glob) cparams.(fresh_id) pe in
  let pg := cparams.(print_uprog) RemoveGlobal pg in

  if (fvars_correct cparams.(lowering_vars) (p_funcs pg)) then
    let pl := lower_prog cparams.(lowering_opt) cparams.(warning) cparams.(lowering_vars) cparams.(is_var_in_memory) pg in
    let pl := cparams.(print_uprog) LowerInstruction pl in

    let pa := reg_alloc_prog pl in
    let pa := cparams.(print_uprog) RegAllocation pa in
    Let _ := CheckAllocRegU.check_prog pl.(p_extra) pl.(p_funcs) pa.(p_extra) pa.(p_funcs) in
    Let pd := dead_code_prog pa in
    let pd := cparams.(print_uprog) DeadCode_RegAllocation pd in

    (* stack_allocation                    *)
    Let ps := stack_alloc.alloc_prog cparams.(stk_pointer_name) cparams.(stk_alloc_fd) cparams.(stk_alloc_gl) pd in
    let ps := cparams.(print_sprog) StackAllocation ps in
    (* linearisation                     *)
    Let pl := linear_prog ps in
    let pl := cparams.(print_linear) pl in
    (* asm                               *)
    cfok (pl)

  else cferror Ferr_lowering.

Definition check_signature (p: prog) (lp: lprog) (fn: funname) : bool :=
  if get_fundef lp.(lp_funcs) fn is Some fd' then
    if get_fundef (p_funcs p) fn is Some fd then
      signature_of_fundef fd == signature_of_lfundef fd'
    else true
  else true.

Definition compile_prog_to_x86 entries (p: prog): result fun_error xprog :=
  Let lp := compile_prog entries p in
  Let _ := assert (all (check_signature p lp) entries) Ferr_lowering in
  assemble_prog lp.

End COMPILER.
