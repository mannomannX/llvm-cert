(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * [CertValidator.AigLrat]: Umbrella Facade for 2-Rail Bit-Blasting & [LRAT]/DPLL UNSAT Checking

    Re-exports [CertValidator.LratCore], [CertValidator.AigGates], and
    [CertValidator.AigArith] for downstream validator modules. *)

From CertValidator Require Export LratCore AigGates AigArith.
