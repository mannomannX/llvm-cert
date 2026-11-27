(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Layer-1 Kernel Assumption & Theorem Gate ([CertValidator.CheckAssumptions])

    Purpose:
      Re-checks and binds top-level soundness theorems across
      [CertPasses.{Pipeline,ModuleMerge}], IR [CertValidator], and machine-code
      [McValidator] modules for CI axiom and kernel auditing.

    Trust Contract & Fail-Closed Boundary:
      Proof-only CI audit gate; not extracted to OCaml. Evaluated under
      [rocq check -o] and [Print Assumptions] to block unapproved axioms.

    Assumptions:
      Imports [CertPasses.{Pipeline,McfgExport,ModuleMerge}] and [CertValidator]
      modules only to [Check] theorem types; zero definitions and zero axioms.

    Section Outline:
      Single flat [Check @...] audit list across [CertPasses], IR
      [CertValidator], and machine-code [McValidator] soundness theorems. *)

Set Default Goal Selector "!".

From CertPasses Require
  Pipeline
  McfgExport
  ModuleMerge.

From CertValidator Require
  CertFormat
  LratCore
  AigGates
  AigLrat
  AlgRulesNormRefines
  AlgRules
  CertValidator
  Elf64Spec
  McFrameMem
  Rv64DagProof
  Rv64SymOracle
  Rv64Sem
  A64Decode
  A64DagProof
  A64SymOracle
  A64CoreSem
  McFormat
  McLoop
  McCall
  McValidator.

Check @CertPasses.Pipeline.optimize_mcfg_refines_IPZ.
Check @CertPasses.Pipeline.optimize_mcfg_I2F_model_refine.
Check @CertPasses.ModuleMerge.validate_module_merge_parsed_I2F_model_refine.
Check @CertPasses.ModuleMerge.validate_module_merge_tle_refines.
Check @CertPasses.ModuleMerge.validate_module_merge_certified_tle_refines.
Check @CertPasses.ModuleMerge.validate_module_merge_certified_tle_composed_refines.
Check @CertValidator.LratCore.check_lrat_unsat_sound.
Check @CertValidator.AigGates.blast_refinement_cex_unsat_sound.
Check @CertValidator.AlgRulesNormRefines.check_expr_refines_sound.
Check @CertValidator.AlgRules.check_expr_refines_with_lrat_sound.
Check @CertValidator.CertFormat.validate_dimacs_lrat_str_sound.
Check @CertValidator.CertValidator.validate_mcfg_with_cert_sound.
Check @CertValidator.CertValidator.validate_tle_pair_with_cert_str_sound.
Check @CertValidator.Elf64Spec.elf64_extract_func_sound.
Check @CertValidator.Elf64Spec.elf64_extract_func_with_calls_sound.
Check @CertValidator.McFrameMem.mc_stk_load_store_same.
Check @CertValidator.McFrameMem.mc_stk_load_store_disjoint.
Check @CertValidator.McFrameMem.mc_sym_stk_store_agrees.
Check @CertValidator.McFrameMem.mc_sym_stk_load_sound.
Check @CertValidator.McFormat.parse_mc_cert_wf.
Check @CertValidator.Rv64DagProof.summarize_rv64_dag_wf.
Check @CertValidator.Rv64DagProof.summarize_rv64_dag_sound.
Check @CertValidator.Rv64SymOracle.rv_step_sym_oracle_sound.
Check @CertValidator.Rv64SymOracle.sail_divrem_128_width_reduce.
Check @CertValidator.A64Decode.decode_a64_bytes_valid.
Check @CertValidator.A64DagProof.summarize_a64_dag_wf.
Check @CertValidator.A64DagProof.summarize_a64_dag_sound.
Check @CertValidator.A64SymOracle.a64_step_sym_oracle_sound.
Check @CertValidator.McLoop.validate_mc_loop_rv64_sound.
Check @CertValidator.McLoop.validate_mc_loop_a64_sound.
Check @CertValidator.McCall.validate_mc_call_rv64_sound.
Check @CertValidator.McCall.validate_mc_call_a64_sound.
Check @CertValidator.McCall.compose_rv64_caller_callee_sound.
Check @CertValidator.McCall.compose_a64_caller_callee_sound.
Check @CertValidator.McValidator.validate_mc_tle_with_cert_str_sound.
