(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Deterministic [ITree] & Event-Sum Tactics ([CertPasses.common.ItreeTactics])

    Purpose:
      Targets the exact [ITree] idioms used across [CertPasses] and validator
      open-world proofs: strong [eq_itree] ([≅]), [paco] stepping, [observe_bind],
      monadic bind normalization, and [subevent]/[ReSum] dispatch.

    Trust Contract & Guardrails:
      No [repeat match goal] sledgehammers, no [eutt]/[tau_eutt] bloat.
      Tactics lie completely outside the kernel TCB. *)

From Paco Require Import paco.

From ITree Require Import
  ITree
  ITreeFacts
  Eq.Eqit.

From CertValidator.common Require Import
  Options.

(** Collapse [subevent] / [ReSum] / [inl_] / [inr_] / [case_] projections
    in pass and handler goals (promoted from [Inline.v]). *)
Ltac norm_subevent :=
  repeat (progress (
    try unfold subevent;
    try unfold resum;
    try unfold ReSum_id;
    try unfold ReSum_sum;
    try unfold ReSum_inl;
    try unfold ReSum_inr;
    try unfold cat;
    try unfold Cat_IFun;
    try unfold inl_;
    try unfold inr_;
    try unfold Inl_sum1;
    try unfold Inr_sum1;
    try unfold id_;
    try unfold Id_IFun;
    cbn [case_ Case_sum1 case_sum1];
    cbv beta iota)).

(** Destruct an n-ary event coproduct value [e : (_ +' _) _] uniformly
    (promoted from [PassCommon.v]). *)
Ltac destruct_sum1 e :=
  repeat (let Te := type of e in
          let Te' := eval hnf in Te in
          match Te' with
          | (_ +' _) _ => destruct e as [e | e]
          end).

(** Normalize top-level monadic [ITree.bind] associativity and left-identity. *)
Ltac itree_step_bind :=
  rewrite ?bind_ret_l, ?bind_bind.

(** Expose one outer observation of [ITree.bind]. *)
Ltac itree_obs_bind :=
  rewrite observe_bind;
  cbn [observe _observe].
