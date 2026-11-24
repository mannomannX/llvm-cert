(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Layer-1 Kernel Assumption & Top-Level Theorem Gate ([CertValidator.CheckAssumptions])

    Re-checks and binds all top-level soundness theorems across:
    1. [CertPasses.Pipeline] (Safe-Path optimization pipeline & I2F composition),
    2. [CertPasses.ModuleMerge] (Compositional split/merge verification),
    3. [CertValidator.AigLrat] & [CertValidator.AlgRules] (LRAT & 2-rail bitvector soundness),
    4. [CertValidator.CertValidator] (End-to-end string-to-TLE translation validator).

    Evaluated under [rocq check -o] and audited via [Print Assumptions] in CI to
    enforce that zero unapproved axioms enter the proof dependency closure. *)

From CertPasses Require
  Pipeline
  McfgExport
  ModuleMerge.

From CertValidator Require
  CertFormat
  AigLrat
  AlgRules
  CertValidator
  Elf64Spec
  Rv64Sem
  McFormat
  McValidator.

Check @CertPasses.Pipeline.optimize_mcfg_refines_IPZ.
Check @CertPasses.Pipeline.optimize_mcfg_I2F_model_refine.
Check @CertPasses.ModuleMerge.validate_module_merge_parsed_I2F_model_refine.
Check @CertPasses.ModuleMerge.validate_module_merge_tle_refines.
Check @CertPasses.ModuleMerge.validate_module_merge_certified_tle_refines.
Check @CertPasses.ModuleMerge.validate_module_merge_certified_tle_composed_refines.
Check @CertValidator.AigLrat.check_lrat_unsat_sound.
Check @CertValidator.AigLrat.blast_refinement_cex_unsat_sound.
Check @CertValidator.AlgRules.check_expr_refines_sound.
Check @CertValidator.AlgRules.check_expr_refines_with_lrat_sound.
Check @CertValidator.CertFormat.validate_dimacs_lrat_str_sound.
Check @CertValidator.CertValidator.validate_mcfg_with_cert_sound.
Check @CertValidator.CertValidator.validate_tle_pair_with_cert_str_sound.
Check @CertValidator.Elf64Spec.elf64_extract_func_sound.
Check @CertValidator.McFormat.parse_mc_cert_wf.
Check @CertValidator.Rv64Sem.summarize_rv64_dag_wf.
Check @CertValidator.Rv64Sem.summarize_rv64_dag_sound.
Check @CertValidator.McValidator.validate_mc_tle_with_cert_str_sound.
