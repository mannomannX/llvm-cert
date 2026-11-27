(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified AArch64 (A64) Core Semantics Umbrella Facade ([CertValidator.A64CoreSem])

    Purpose:
      Re-exports [McIsaCommon], [A64Decode], [A64ExecSym], [A64DagProof], [A64SymOracle],
      and [A64LoopSeg] under [CertValidator.A64CoreSem].

    Trust Contract & Fail-Closed Boundary:
      Compatibility facade; introduces no new definitions or executable checks (re-exports
      underlying AArch64 modules and proof-hygiene [Options]).

    Assumptions:
      [CertValidator.common.Options] plus re-exported [CertValidator.{McIsaCommon,A64Decode,
      A64ExecSym,A64DagProof,A64SymOracle,A64LoopSeg}]; zero custom axioms.

    Section Outline:
      Export-only facade re-exporting the six A64 semantics, proof, oracle, and loop modules. *)

From CertValidator.common Require Import Options.

From CertValidator Require Export
  McIsaCommon
  A64Decode
  A64ExecSym
  A64DagProof
  A64SymOracle
  A64LoopSeg.
