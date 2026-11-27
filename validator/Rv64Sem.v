(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Umbrella Facade for RV64IM+RVC Semantics & Lowering ([CertValidator.Rv64Sem])

    Purpose:
      Re-exports [McIsaCommon], [Rv64Decode], [Rv64ExecSym], [Rv64DagProof], [Rv64SymOracle],
      and [Rv64LoopSeg] under [CertValidator.Rv64Sem].

    Trust Contract & Fail-Closed Boundary:
      Compatibility facade; introduces no new definitions or executable checks (re-exports
      underlying RV64 modules and proof-hygiene [Options]).

    Assumptions:
      [CertValidator.common.Options] plus re-exported [CertValidator.{McIsaCommon,Rv64Decode,
      Rv64ExecSym,Rv64DagProof,Rv64SymOracle,Rv64LoopSeg}]; zero custom axioms.

    Section Outline:
      Export-only facade re-exporting the six RV64 semantics, proof, oracle, and loop modules. *)

From CertValidator.common Require Import Options.

From CertValidator Require Export
  McIsaCommon
  Rv64Decode
  Rv64ExecSym
  Rv64DagProof
  Rv64SymOracle
  Rv64LoopSeg.
