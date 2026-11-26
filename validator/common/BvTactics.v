(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Stdlib Bitvector & Integer-Coercion Tactics ([CertValidator.common.BvTactics])

    Purpose:
      Shared deterministic helpers over Stdlib [N]/[Z]/[Pos] for coercion
      normalization, bitwise extensionality, mask simplification, and closed
      constant evaluation across [AigLrat], [Rv64Sem], [A64CoreSem], and
      future Phase 7 32-bit targets.

    Trust Contract & Guardrails:
      Pure Stdlib only (zero Vellvm dependency). Outside the kernel TCB. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Lia.

From CertValidator.common Require Import
  Options.

(** Push common [N <-> Z] conversions into hypotheses and goal, then invoke [lia]. *)
Ltac bv_zify :=
  rewrite ?N2Z.inj_add, ?N2Z.inj_sub, ?N2Z.inj_mul,
          ?N2Z.inj_min, ?N2Z.inj_max, ?Z2N.id in *;
  lia.

(** Apply bitwise extensionality over [N] or [Z] goals. *)
Ltac bv_testbit_ext :=
  first
    [ apply N.bits_inj_iff; intro
    | apply Z.bits_inj_iff; intros ? ? ].

(** Normalize bitwise-AND with [ones] bitmasks into modulo reductions. *)
Ltac bv_mask_norm :=
  rewrite ?Z.land_ones, ?N.land_ones in *.

(** Pre-evaluate a closed constant term via [vm_compute] before arithmetic solving
    to keep kernel proof terms small ([PS-02]). *)
Ltac bv_compute_const val :=
  let x := fresh in
  set val as x in *;
  vm_compute in x;
  subst x.
