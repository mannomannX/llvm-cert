(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Pure [EOU] Outcome Tactics ([CertValidator.common.EouTactics])

    Purpose:
      Deterministic 1-step eliminators for Vellvm's [EOU] monad ([eou_bind],
      [raise_ret], [raise_ub], [raise_error], [raise_oom]) in symbolic DAG
      evaluators and validator proofs ([PS-12]).

    Trust Contract & Guardrails:
      Deterministic 1-step rewriting/inversion only; outside the kernel TCB. *)

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
