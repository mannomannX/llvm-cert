(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Umbrella Facade for Verified [RV64IM] + [RVC] Semantics & Symbolic Lowering

    Re-exports [CertValidator.McIsaCommon], [CertValidator.Rv64Decode],
    [CertValidator.Rv64ExecSym], [CertValidator.Rv64DagProof],
    [CertValidator.Rv64SymOracle], and [CertValidator.Rv64LoopSeg]
    under [CertValidator.Rv64Sem]. *)

From CertValidator Require Export
  McIsaCommon
  Rv64Decode
  Rv64ExecSym
  Rv64DagProof
  Rv64SymOracle
  Rv64LoopSeg.
