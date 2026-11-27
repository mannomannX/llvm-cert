(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Umbrella Facade for 2-Rail Bit-Blasting & [LRAT]/DPLL ([CertValidator.AigLrat])

    Purpose:
      Provides a single import target re-exporting [CertValidator.LratCore],
      [CertValidator.AigGates], and [CertValidator.AigArith] together with
      [CertValidator.common.Options] for downstream validator modules.

    Trust Contract & Fail-Closed Boundary:
      Compatibility facade; adds no new runtime checks, definitions, or proof
      obligations beyond the re-exported modules.

    Assumptions:
      Imports [CertValidator.common.Options] and re-exports
      [CertValidator.{LratCore,AigGates,AigArith}]; zero custom axioms.

    Section Outline:
      Single facade module importing [Options] and re-exporting [LratCore],
      [AigGates], and [AigArith]. *)

From CertValidator.common Require Import Options.

From CertValidator Require Export LratCore AigGates AigArith.
