(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Core Deterministic Single-Step Proof Tactics ([CertValidator.common.CoreTactics])

    Purpose:
      Stdlib-only (zero Vellvm dependency) deterministic 1-step eliminators
      for option/sum monads, boolean reflections, decidable equalities, and
      nested boolean conditionals. Naming deliberately avoids collisions with
      [Vellvm.Utils.Tactics].

    Trust Contract & Guardrails:
      No backtracking search ([eauto with *], deep [repeat match goal]).
      Tactics lie completely outside the trusted kernel (checked by [rocq check]). *)

From Stdlib Require Import
  Bool
  List
  Strings.String
  PArith
  NArith
  ZArith
  Arith.PeanoNat.

From CertValidator.common Require Import
  Options.

(** Eliminate an option equality hypothesis ([Some _ = Some _] or impossible
    [None = Some _] / [Some _ = None]). *)
Ltac inv_some H :=
  match type of H with
  | Some _ = Some _ => inversion H; subst; clear H
  | None = Some _ => discriminate H
  | Some _ = None => discriminate H
  end.

(** Eliminate an [inr] sum equality hypothesis (useful on fail-closed
    [sum string T] validator acceptance paths). *)
Ltac inv_inr H :=
  match type of H with
  | inr _ = inr _ => inversion H; subst; clear H
  | inl _ = inr _ => discriminate H
  | inr _ = inl _ => discriminate H
  end.

(** Eliminate an [inl] sum equality hypothesis on diagnostic rejection paths. *)
Ltac inv_inl H :=
  match type of H with
  | inl _ = inl _ => inversion H; subst; clear H
  | inr _ = inl _ => discriminate H
  | inl _ = inr _ => discriminate H
  end.

(** Case-split the outermost option/sum/boolean bind in [H], discharging the
    immediate failure branch. *)
Ltac bind_ok H :=
  match type of H with
  | match ?e with Some _ => _ | None => None end = Some _ =>
      let E := fresh "E" in
      destruct e eqn:E; [| discriminate H]
  | match ?e with inr _ => _ | inl _ => inl _ end = inr _ =>
      let E := fresh "E" in
      destruct e eqn:E; [discriminate H |]
  | (if ?b then _ else None) = Some _ =>
      let E := fresh "E" in
      destruct b eqn:E; [| discriminate H]
  | (if ?b then _ else inl _) = inr _ =>
      let E := fresh "E" in
      destruct b eqn:E; [| discriminate H]
  | (if ?b then None else _) = Some _ =>
      let E := fresh "E" in
      destruct b eqn:E; [discriminate H |]
  | (if ?b then inl _ else _) = inr _ =>
      let E := fresh "E" in
      destruct b eqn:E; [discriminate H |]
  end.

(** Recursively split a conjunction of boolean [&&] checks in [H = true]. *)
Ltac split_andb H :=
  match type of H with
  | (?a && ?b)%bool = true =>
      let H1 := fresh in
      let H2 := fresh in
      apply andb_true_iff in H as [H1 H2];
      split_andb H1;
      split_andb H2
  | _ => idtac
  end.

(** Split a boolean [||] disjunction hypothesis in [H = true]. *)
Ltac split_orb H :=
  match type of H with
  | (?a || ?b)%bool = true =>
      apply orb_true_iff in H as [H | H];
      [try split_orb H | try split_orb H]
  | _ => idtac
  end.

(** Case-split atomic boolean expressions inside goal conditionals [if b then _ else _]
    without backtracking search (promoted from [AlgRules.v]). *)
Ltac split_bool_ifs :=
  repeat (cbn [andb orb negb];
          match goal with
          | |- context [if ?b then _ else _] =>
              let rec d_atom e :=
                match e with
                | ?x && _ => d_atom x
                | ?x || _ => d_atom x
                | negb ?x => d_atom x
                | _ => destruct e
                end in
              d_atom b
          end).

(** Perform a single outer case split on a [match] or [if] in the goal. *)
Ltac destruct_match :=
  match goal with
  | |- context [match ?e with _ => _ end] => destruct e
  | |- context [if ?b then _ else _] => destruct b
  end.

(** Perform a single outer case split on a [match] or [if] in hypothesis [H]. *)
Ltac destruct_match_in H :=
  match type of H with
  | context [match ?e with _ => _ end] => destruct e
  | context [if ?b then _ else _] => destruct b
  end.

(** Reflect a standard boolean equality hypothesis into Leibniz equality and substitute. *)
Ltac eqb_eq_in H :=
  first
    [ apply Nat.eqb_eq in H
    | apply Pos.eqb_eq in H
    | apply N.eqb_eq in H
    | apply Z.eqb_eq in H
    | apply String.eqb_eq in H
    | apply Bool.eqb_true_iff in H ];
  try subst.
