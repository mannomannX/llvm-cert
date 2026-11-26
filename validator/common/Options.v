(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Shared Rocq 9.1 Proof-Hygiene Options ([CertValidator.common.Options])

    Purpose:
      Provides uniform, exported Rocq vernacular flags so refactored and newly
      written modules inherit strict bullet/goal-selector hygiene and parallel
      [-vos]/[-vok] section checking without per-lemma boilerplate.

    Trust Contract & Assumptions:
      Contains vernacular option flags only (zero definitions, zero axioms). *)

#[export] Set Default Goal Selector "!".
#[export] Set Default Proof Using "Type".
