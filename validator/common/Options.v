(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Shared Rocq 9.1 Proof-Hygiene Options ([CertValidator.common.Options])

    Purpose:
      Provides uniform exported vernacular flags ([Default Goal Selector "!"] and
      [Default Proof Using "Type"]) so modules inherit strict goal-selector
      hygiene and parallel [-vos]/[-vok] checking without per-lemma boilerplate.

    Trust Contract & Fail-Closed Boundary:
      Vernacular option flags only; no definitions, runtime code, or extraction
      surface.

    Assumptions:
      Zero dependencies and zero custom axioms.

    Section Outline:
      Single flat file exporting [Default Goal Selector "!"] and
      [Default Proof Using "Type"]. *)

#[export] Set Default Goal Selector "!".
#[export] Set Default Proof Using "Type".
