(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Stdlib Bitvector & Integer-Coercion Tactics ([CertValidator.common.BvTactics])

    Purpose:
      Provides deterministic Ltac helpers ([bv_zify], [bv_testbit_ext],
      [bv_mask_norm], [bv_compute_const]) over Stdlib [N]/[Z]/[positive] for
      coercion normalization, bitwise extensionality, and constant evaluation.

    Trust Contract & Fail-Closed Boundary:
      Shared tactic library (Ltac only); outside the Rocq trusted kernel and not
      extracted to OCaml.

    Assumptions:
      Stdlib-only ([ZArith], [NArith], [PArith], [Lia]) plus
      [CertValidator.common.Options]; zero Vellvm dependencies and zero axioms.

    Section Outline:
      Single flat library of coercion, bitwise extensionality, mask
      normalization, and closed-term evaluation tactics. *)

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
