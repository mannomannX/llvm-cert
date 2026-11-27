(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Pure [EOU] Outcome Tactics ([CertValidator.common.EouTactics])

    Purpose:
      Provides deterministic 1-step eliminators ([eou_inv], [eou_step]) for
      Vellvm's [EOU] outcome monad ([raise_ret], [raise_ub], [raise_error],
      [raise_oom]) in symbolic DAG evaluator and validator proofs.

    Trust Contract & Fail-Closed Boundary:
      Shared tactic library (Ltac only); outside the Rocq trusted kernel and not
      extracted to OCaml.

    Assumptions:
      Depends on [ExtLib.Structures.Monad], [Vellvm.Semantics.EOU], and
      [CertValidator.common.Options]; zero custom axioms.

    Section Outline:
      Single flat library defining [eou_inv] and [eou_step]. *)

From ExtLib Require Import
  Structures.Monad.

From Vellvm Require Import
  Semantics.EOU.

From CertValidator.common Require Import
  Options.

(** Eliminate an [EOU] monadic bind, concrete [EOU] match, or constructor
    equality hypothesis [H], automatically closing impossible error/OOM/UB branches. *)
Ltac eou_inv H :=
  match type of H with
  | @ExtLib.Structures.Monad.bind EOU _ _ _ ?m _ = _ =>
      destruct m;
      cbn [ExtLib.Structures.Monad.bind EOU_monad] in H;
      try discriminate H
  | match ?m with
    | raise_error _ => _
    | raise_oom _ => _
    | raise_ub _ => _
    | raise_ret _ => _
    end = _ =>
      destruct m; try discriminate H
  | raise_ret _ = raise_ret _ =>
      inversion H; subst; clear H
  | _ = raise_ret _ => discriminate H
  | raise_ret _ = _ => discriminate H
  end.

(** Reduce one head [EOU_monad] bind step in the goal. *)
Ltac eou_step :=
  cbn [ExtLib.Structures.Monad.bind EOU_monad].
