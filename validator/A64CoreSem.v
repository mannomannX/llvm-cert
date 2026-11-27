(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified [AArch64] ([A64]) Core Semantics Umbrella Facade

    Umbrella re-export facade for [CertValidator.A64CoreSem], re-exporting
    [McIsaCommon], [A64Decode], [A64ExecSym], [A64DagProof], [A64SymOracle],
    and [A64LoopSeg]. *)

From CertValidator Require Export
  McIsaCommon
  A64Decode
  A64ExecSym
  A64DagProof
  A64SymOracle
  A64LoopSeg.
