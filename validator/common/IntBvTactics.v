(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Machine-Integer [@Integers.bit_int] Tactics ([CertValidator.common.IntBvTactics])

    Purpose:
      Deterministic helpers for Vellvm's width-indexed [@Integers.bit_int]
      type across validator, ISA semantics, and stack-frame proofs ([PS-03]).

    Trust Contract & Guardrails:
      Layered above [BvTactics] and [Vellvm.Numeric.Integers]; outside the kernel TCB. *)

From Vellvm Require Import
  Numeric.Integers.

From CertValidator.common Require Import
  Options.

From CertValidator.common Require Export
  BvTactics.

(** Discharge bitwise identities over [@Integers.bit_int] goals. *)
Ltac int_bit_solve :=
  Integers.bit_solve.

(** Simplify [@Integers.unsigned (@Integers.repr w x)] and solve range side-condition. *)
Ltac int_unsigned_repr :=
  rewrite Integers.unsigned_repr; [| bv_zify].

(** Simplify [@Integers.signed (@Integers.repr w x)] and solve range side-condition. *)
Ltac int_signed_repr :=
  rewrite Integers.signed_repr; [| bv_zify].

(** Reduce machine-integer equality to equality of underlying [intval] projections. *)
Ltac int_mkint_eq :=
  apply Integers.mkint_eq.
