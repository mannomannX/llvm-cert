(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Inlining Caller Pre-Loop & Sync-Step Simulation ([CertPasses.InlineCallerProof])

    Purpose:
      Proves caller-side instruction, code, remapped-phi, and terminator
      simulations under [cfg_inline_sim], synced-iteration preservation,
      unchanged-function simulation ([denote_function_other_sim]), and
      single-step [run_exc] lifting at synced and inlined call sites.

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml.

    Assumptions:
      Depends on Stdlib, Paco, ITree, ExtLib, Vellvm, [CertPasses.PassCommon],
      [CertPasses.common.ItreeTactics], and
      [CertPasses.Inline{Spec,SyntaxProof,FrameGenv,Sim,CalleeProof}]; zero
      custom axioms.

    Section Outline:
      (10A) Caller instruction, code, phi, terminator, & synced-iter
      simulations; (10B) Unchanged-function simulation and single-step [run_exc]
      lifting for synced and inlined blocks. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.String
  Strings.Ascii
  List
  Bool
  Morphisms
  RelationClasses
  Lia.
Import ListNotations.

From Paco Require Import paco.

From ITree Require Import
  ITree
  ITreeFacts
  Events.State
  Events.StateFacts
  Eq.Eqit
  Basics.HeterogeneousRelations
  Interp.Recursion
  Interp.TranslateFacts
  Interp.InterpFacts.

From ExtLib Require Import
  Structures.Maps
  Structures.Monads
  Structures.Functor.

From Vellvm Require Import
  Numeric
  Utils
  Syntax
  Semantics
  ScopeTheory
  Theory.Equational
  Theory.MemoryBytesFacts
  Semantics.Interfaces.IPtr
  Semantics.Interfaces.Params
  Semantics.Interfaces.Memory
  Semantics.Implementations.Provenance
  Semantics.Implementations.Pointer
  Semantics.Implementations.ParamsV
  Semantics.Implementations.Memory
  Semantics.Handlers
  Semantics.InterpretationStack
  Semantics.TopLevel
  Semantics.Libraries.

From CertPasses Require Import PassCommon.
From CertPasses.common Require Import ItreeTactics.
Import Logic.

Set Default Goal Selector "!".
Unset Implicit Arguments.

From CertPasses Require Import InlineSpec InlineSyntaxProof InlineFrameGenv InlineSim InlineCalleeProof.

Section InliningSemantics.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Notation PaV := (@ParamsV IP IPT).
  #[local] Existing Instance MemoryModelStateV.
  #[local] Existing Instance MemoryModelPrimitivesV.
  #[local] Hint Resolve refine_prov__mon : paco.
  #[local] Hint Resolve gen_inline_sim__mon : paco.

  #[local] Ltac try_cfg_raise_h Hact :=
    lazymatch goal with
    | |- cfg_inline_sim _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise, Hact
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise, Hact
    | _ => idtac
    end.

  #[local] Ltac try_cfg_raise :=
    lazymatch goal with
    | |- cfg_inline_sim _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise; reflexivity
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) =>
        apply cfg_inline_sim_raise; reflexivity
    | _ => idtac
    end.

  #[local] Ltac try_cfg_raise_ub_h Hact :=
    lazymatch goal with
    | |- cfg_inline_sim _ _ _ _ _ (@raiseUB _ _ _ _) _ => apply cfg_inline_sim_raiseUB
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raiseUB _ _ _ _) _ => apply cfg_inline_sim_raiseUB
    | |- cfg_inline_sim _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise, Hact
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise, Hact
    | _ => idtac
    end.

  #[local] Ltac try_cfg_raise_ub :=
    lazymatch goal with
    | |- cfg_inline_sim _ _ _ _ _ (@raiseUB _ _ _ _) _ => apply cfg_inline_sim_raiseUB
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raiseUB _ _ _ _) _ => apply cfg_inline_sim_raiseUB
    | |- cfg_inline_sim _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise; reflexivity
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) =>
        apply cfg_inline_sim_raise; reflexivity
    | _ => idtac
    end.

  #[local] Ltac try_mcfg_raise :=
    lazymatch goal with
    | |- mcfg_inline_sim _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply mcfg_inline_sim_raise; reflexivity
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) =>
        apply mcfg_inline_sim_raise; reflexivity
    | _ => idtac
    end.

(** * 10. Caller CFG Simulation, Function/Module Lifting & Top-Level Refinement *)

  (** ** 10A. Caller Instruction, Code, Remapped-Phi, Terminator & Sync-Iter Simulations *)

  Lemma find_option_ann_num_elements_uses
    (anns : list (annotation dtyp)) (t : dtyp) (num_exp : exp dtyp) :
    find_option ann_num_elements anns = Some (t, num_exp) ->
    forall x, In x (full_exp_uses num_exp) -> In x (flat_map full_ann_uses anns).
  Proof.
    induction anns as [| a rest IH]; cbn [find_option flat_map]; [discriminate |].
    destruct a; cbn [ann_num_elements];
      try (intros H x Hx; apply in_or_app; right; eapply IH; eassumption).
    intros H; injection H as ->.
    intros x Hx; apply in_or_app; left; exact Hx.
  Qed.

  Lemma assoc_some_in {B : Type} (k : block_id) (xs : list (block_id * B)) (v : B) :
    assoc k xs = Some v -> In (k, v) xs.
  Proof.
    induction xs as [| [b ex] rest IH]; [cbn; discriminate |].
    destruct (RawIDOrd.eq_dec k b) as [-> | Hne].
    - rewrite assoc_hd; intros H; injection H as <-; left; reflexivity.
    - rewrite assoc_tl by exact Hne; intros H; right; apply IH, H.
  Qed.

  Lemma denote_call_args_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (e1 e2 : @local_env PaV)
    (args : list (texp dtyp * list param_attr)) (msg1 msg2 : string)
    (Huses : forall x,
               In x (flat_map (fun '(te, _) => full_texp_uses te) args) ->
               ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
      (IC_Synced stk e1 e2)
      (denote_call_args args msg1)
      (denote_call_args args msg2).
  Proof.
    unfold denote_call_args.
    induction args as [| [[t op] attrs] rest IH]; cbn [map_monad flat_map] in *.
    - apply gen_inline_sim_ret; split; reflexivity.
    - eapply gen_inline_sim_bind.
      + eapply gen_inline_sim_bind.
        * apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some t) op);
            [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
        * intros ? v _ [-> <-]; apply cfg_inline_sim_apply_attrs; reflexivity.
      + intros ? v1 _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply IH; intros x Hx; apply Huses, in_or_app; right; exact Hx.
        * intros ? vs1 _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma cfg_inline_sim_assume_deref
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (or_null : bool) (loc1 loc2 : string) (vs : list (@dvalue PaV))
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic /\ r1 = tt /\ r2 = tt)
      ic
      (assume_dereferenceable or_null loc1 vs)
      (assume_dereferenceable or_null loc2 vs).
  Proof.
    unfold assume_dereferenceable, assume_violated, assume_malformed.
    destruct vs as [| p [| sz [| ? ?]]]; cbv beta iota zeta;
      try_cfg_raise_h Hact.
    destruct (dvalue_ptr_address p) as [a |], (bundle_uint sz) as [n |];
      cbv beta iota zeta;
      try_cfg_raise_ub_h Hact.
    destruct (n =? 0)%Z; [apply gen_inline_sim_ret; auto | apply cfg_inline_sim_assert_deref, Hact].
  Qed.

  Lemma cfg_inline_sim_bundle_check
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (f : exp dtyp) (tag : string) (loc1 loc2 : string) (vs : list (@dvalue PaV))
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic /\ r1 = tt /\ r2 = tt)
      ic
      (match bundle_check f tag with Some check => check loc1 vs | None => Ret tt end)
      (match bundle_check f tag with Some check => check loc2 vs | None => Ret tt end).
  Proof.
    unfold bundle_check, assume_bundle_checks.
    destruct (is_llvm_assume f); [| apply gen_inline_sim_ret; auto].
    cbn [find].
    destruct (String.eqb "nonnull" tag); [cbn [option_map snd] |
    destruct (String.eqb "noundef" tag); [cbn [option_map snd] |
    destruct (String.eqb "align" tag); [cbn [option_map snd] |
    destruct (String.eqb "dereferenceable" tag); [cbn [option_map snd] |
    destruct (String.eqb "dereferenceable_or_null" tag); cbn [option_map snd]]]]].
    - unfold assume_nonnull, assume_violated, assume_malformed.
      destruct vs as [| p [| ? ?]]; cbv beta iota zeta;
        try_cfg_raise_h Hact.
      destruct (dvalue_ptr_address p) as [a |]; [| apply cfg_inline_sim_raiseUB].
      destruct (a =? 0)%Z; [apply cfg_inline_sim_raiseUB | apply gen_inline_sim_ret; auto].
    - unfold assume_noundef, assume_violated, assume_malformed.
      destruct vs as [| v [| ? ?]]; cbv beta iota zeta;
        try_cfg_raise_h Hact.
      destruct (dvalue_well_defined v);
        [apply gen_inline_sim_ret; auto | apply cfg_inline_sim_raiseUB].
    - unfold assume_align, assume_violated, assume_malformed.
      destruct vs as [| p [| al off]]; cbv beta iota zeta;
        try_cfg_raise_h Hact.
      destruct (dvalue_ptr_address p) as [a |],
               (bundle_uint al) as [n |],
               (match off with [] => Some 0%Z | [o] => bundle_sint o | _ => None end) as [o |];
        cbv beta iota zeta;
        try_cfg_raise_ub_h Hact.
      destruct (if is_power_of_two n then ((a - o) mod n =? 0)%Z else (a =? 0)%Z);
        [apply gen_inline_sim_ret; auto | apply cfg_inline_sim_raiseUB].
    - apply cfg_inline_sim_assume_deref, Hact.
    - apply cfg_inline_sim_assume_deref, Hact.
    - apply gen_inline_sim_ret; auto.
  Qed.

  Lemma denote_operand_bundles_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (e1 e2 : @local_env PaV)
    (loc1 loc2 : string) (f : exp dtyp) (obs : list (@operand_bundle dtyp))
    (Huses : forall x, In x (flat_map full_ob_uses obs) -> ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = tt /\ r2 = tt)
      (IC_Synced stk e1 e2)
      (denote_operand_bundles loc1 f obs)
      (denote_operand_bundles loc2 f obs).
  Proof.
    unfold denote_operand_bundles.
    assert (Hops :
      forall ops,
        (forall x, In x (flat_map full_operand_uses ops) -> ~ In x fresh_set) ->
        cfg_inline_sim opt_call1 g0 false
          (fun ic' vs1 vs2 => ic' = IC_Synced stk e1 e2 /\ vs1 = vs2)
          (IC_Synced stk e1 e2)
          (map_monad (fun o => match o with SSA_value (t, e) => denote_exp' (Some t) e
                                          | Metadata_string _ => ret (DVALUE_Base DVALUE_None) end) ops)
          (map_monad (fun o => match o with SSA_value (t, e) => denote_exp' (Some t) e
                                          | Metadata_string _ => ret (DVALUE_Base DVALUE_None) end) ops)).
    { induction ops as [| o rest IH]; intros Hop_u; cbn [map_monad flat_map] in *.
      - apply gen_inline_sim_ret; split; reflexivity.
      - eapply gen_inline_sim_bind.
        + destruct o as [[t ex] | m].
          * apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some t) ex);
              [intros x Hx; apply Hop_u, in_or_app; left; exact Hx | exact Hagree].
          * apply gen_inline_sim_ret; split; reflexivity.
        + intros ? v1 _ [-> <-].
          eapply gen_inline_sim_bind.
          * apply IH; intros x Hx; apply Hop_u, in_or_app; right; exact Hx.
          * intros ? vs1 _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity. }
    assert (Hobs :
      forall bs,
        (forall x, In x (flat_map full_ob_uses bs) -> ~ In x fresh_set) ->
        cfg_inline_sim opt_call1 g0 false
          (fun ic' u1 u2 => ic' = IC_Synced stk e1 e2 /\ u1 = u2)
          (IC_Synced stk e1 e2)
          (map_monad
             (fun ob =>
                vs <- map_monad
                        (fun o => match o with SSA_value (t, e) => denote_exp' (Some t) e
                                             | Metadata_string _ => ret (DVALUE_Base DVALUE_None) end)
                        (ob_ops ob) ;;
                match bundle_check f (ob_tag ob) with Some check => check loc1 vs | None => ret tt end) bs)
          (map_monad
             (fun ob =>
                vs <- map_monad
                        (fun o => match o with SSA_value (t, e) => denote_exp' (Some t) e
                                             | Metadata_string _ => ret (DVALUE_Base DVALUE_None) end)
                        (ob_ops ob) ;;
                match bundle_check f (ob_tag ob) with Some check => check loc2 vs | None => ret tt end) bs)).
    { induction bs as [| ob rest IH]; intros Hbs_u; cbn [map_monad flat_map] in *.
      - apply gen_inline_sim_ret; split; reflexivity.
      - eapply gen_inline_sim_bind with
          (RA := fun ic' u1 u2 => ic' = IC_Synced stk e1 e2 /\ u1 = u2).
        + eapply gen_inline_sim_bind.
          * apply Hops; intros x Hx; apply Hbs_u, in_or_app; left; exact Hx.
          * intros ? vs1 _ [-> <-].
            eapply gen_inline_sim_weaken;
              [| apply (cfg_inline_sim_bundle_check opt_call1 g0 false (IC_Synced stk e1 e2)
                          f (ob_tag ob) loc1 loc2 vs1 Logic.eq_refl)].
            intros ? ? ? (-> & -> & ->); split; reflexivity.
        + intros ? u1 _ [-> <-].
          eapply gen_inline_sim_bind.
          * apply IH; intros x Hx; apply Hbs_u, in_or_app; right; exact Hx.
          * intros ? us1 _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity. }
    eapply gen_inline_sim_bind; [apply (Hobs obs Huses) |].
    intros ? _ _ [-> _]; apply gen_inline_sim_ret; auto.
  Qed.

  Lemma denote_cmpxchg_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (e1 e2 : @local_env PaV)
    (id : raw_id) (cpx : cmpxchg dtyp)
    (Huses : forall x,
               In x (full_texp_uses (c_ptr cpx) ++ full_texp_uses (c_cmp cpx) ++ full_texp_uses (c_new cpx)) ->
               ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         r1 = tt /\ r2 = tt /\
         exists e1' e2',
           ic' = IC_Synced stk e1' e2' /\
           env_agree_outside fresh_set e1' e2')
      (IC_Synced stk e1 e2)
      (denote_cmpxchg id cpx)
      (denote_cmpxchg id cpx).
  Proof.
    unfold denote_cmpxchg.
    destruct (c_ptr cpx) as [ptr_ty ptr_val],
             (c_cmp cpx) as [cmp_ty cmp_val],
             (c_new cpx) as [new_ty new_val].
    destruct (dtyp_eq_dec cmp_ty new_ty); [| apply cfg_inline_sim_raise; reflexivity].
    eapply gen_inline_sim_bind.
    - apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some ptr_ty) ptr_val);
        [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
    - intros ? ptr_v _ [-> <-].
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some cmp_ty) cmp_val);
          [ intros x Hx; apply Huses, in_or_app;
              right; apply in_or_app; left; exact Hx
          | exact Hagree ].
      + intros ? cmp_v _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some cmp_ty) new_val);
            [ intros x Hx; apply Huses, in_or_app;
                right; apply in_or_app; right; exact Hx
            | exact Hagree ].
        * intros ? new_v _ [-> <-].
          eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
          eapply gen_inline_sim_bind;
            [unfold load; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? loaded_v _ [-> <-]].
          eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? dv _ [-> <-]].
          destruct dv as [db | |]; cbv beta iota zeta;
            try_cfg_raise.
          destruct db; cbv beta iota zeta;
            try_cfg_raise.
          -- destruct sz as [? | ? |]; cbv beta iota zeta;
               try_cfg_raise.
             lazymatch goal with | |- context [VellvmIntegers.equ ?a ?b] => destruct (VellvmIntegers.equ a b) end.
             ++ eapply gen_inline_sim_bind;
                  [unfold store; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? [] _ [-> _]].
                set (ret_v := DVALUE_Struct false [loaded_v; DVALUE_Base (DVALUE_I 1 VellvmIntegers.one)]).
                eapply gen_inline_sim_weaken;
                  [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                              (IC_Synced stk e1 e2)
                              (IC_Synced stk (Maps.add id ret_v e1) e2)
                              (IC_Synced stk (Maps.add id ret_v e1) (Maps.add id ret_v e2))
                              id id ret_v Logic.eq_refl Logic.eq_refl)].
                intros ? [] [] (-> & _ & _).
                split; [reflexivity | split; [reflexivity |]].
                eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
             ++ set (ret_v := DVALUE_Struct false [loaded_v; DVALUE_Base (DVALUE_I 1 VellvmIntegers.zero)]).
                eapply gen_inline_sim_weaken;
                  [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                              (IC_Synced stk e1 e2)
                              (IC_Synced stk (Maps.add id ret_v e1) e2)
                              (IC_Synced stk (Maps.add id ret_v e1) (Maps.add id ret_v e2))
                              id id ret_v Logic.eq_refl Logic.eq_refl)].
                intros ? [] [] (-> & _ & _).
                split; [reflexivity | split; [reflexivity |]].
                eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
          -- apply cfg_inline_sim_raiseUB.
  Qed.

  Lemma denote_atomicrmw_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (e1 e2 : @local_env PaV)
    (id : raw_id) (armw : atomicrmw dtyp)
    (Huses : forall x,
               In x (full_texp_uses (a_ptr armw) ++ full_texp_uses (a_val armw)) ->
               ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         r1 = tt /\ r2 = tt /\
         exists e1' e2',
           ic' = IC_Synced stk e1' e2' /\
           env_agree_outside fresh_set e1' e2')
      (IC_Synced stk e1 e2)
      (denote_atomicrmw id armw)
      (denote_atomicrmw id armw).
  Proof.
    unfold denote_atomicrmw.
    destruct (a_ptr armw) as [ptr_ty ptr_val],
             (a_val armw) as [a_ty a_v_exp].
    eapply gen_inline_sim_bind.
    - apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some ptr_ty) ptr_val);
        [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
    - intros ? ptr_v _ [-> <-].
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some a_ty) a_v_exp);
          [intros x Hx; apply Huses, in_or_app; right; exact Hx | exact Hagree].
      + intros ? a_v _ [-> <-].
        eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
        eapply gen_inline_sim_bind;
          [unfold load; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? loaded_v _ [-> <-]].
        eapply gen_inline_sim_bind with
          (RA := fun ic' sv1 sv2 => ic' = IC_Synced stk e1 e2 /\ sv1 = sv2).
        * unfold denote_atomic_rmw_operation.
          destruct (a_operation armw); cbv beta iota zeta;
            try_cfg_raise;
            try (apply cfg_inline_sim_EOU; reflexivity).
          -- apply gen_inline_sim_ret; split; reflexivity.
          -- destruct a_v as [db | |]; cbv beta iota zeta;
               try_cfg_raise.
             destruct db; cbv beta iota zeta;
               try_cfg_raise.
             apply cfg_inline_sim_EOU; reflexivity.
        * intros ? stored_v _ [-> <-].
          eapply gen_inline_sim_bind;
            [unfold store; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? [] _ [-> _]].
          eapply gen_inline_sim_bind.
          -- apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                      (IC_Synced stk e1 e2)
                      (IC_Synced stk (Maps.add id loaded_v e1) e2)
                      (IC_Synced stk (Maps.add id loaded_v e1) (Maps.add id loaded_v e2))
                      id id loaded_v Logic.eq_refl Logic.eq_refl).
          -- intros ? [] [] (-> & _ & _).
             apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity |]].
             eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
  Qed.

  Lemma denote_instr_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (e1 e2 : @local_env PaV)
    (va : option (@ptr (@PROV PaV) (@PTR PaV)))
    (iid : instr_id) (ins : instr dtyp) (md : list (metadata dtyp))
    (Huses : forall x,
               In x (full_instr_uses ins ++ flat_map full_metadata_uses md) ->
               ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         r1 = tt /\ r2 = tt /\
         exists e1' e2',
           ic' = IC_Synced stk e1' e2' /\
           env_agree_outside fresh_set e1' e2')
      (IC_Synced stk e1 e2)
      (denote_instr (iid, ins, md) va)
      (denote_instr (iid, ins, md) va).
  Proof.
    destruct ins as [s_cmt | op | [dt f] args anns obs | dt annotations
                     | dt [du ptr] anns | [dt val] [du ptr] anns
                     | s_f1 s_f2 | cpx | armw | [t ptr_exp] argty | lp_t lp_b lp_cs].
    - (* INSTR_Comment *)
      destruct iid as [id | vn]; cbn [denote_instr].
      + apply cfg_inline_sim_raise; reflexivity.
      + apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - (* INSTR_Op *)
      destruct iid as [id | vn]; cbn [denote_instr]; [| apply cfg_inline_sim_raise; reflexivity].
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 None op);
          [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
      + intros ? uv _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                   (IC_Synced stk e1 e2)
                   (IC_Synced stk (Maps.add id uv e1) e2)
                   (IC_Synced stk (Maps.add id uv e1) (Maps.add id uv e2))
                   id id uv Logic.eq_refl Logic.eq_refl).
        * intros ? [] [] (-> & _ & _).
          apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity |]].
          eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
    - (* INSTR_Call *)
      destruct iid as [id | vn]; cbn [denote_instr];
      (eapply gen_inline_sim_bind;
       [apply (denote_call_args_caller_sim opt_call1 g0 fresh_set stk e1 e2 args);
          [intros x Hx; apply Huses, in_or_app; left; cbn [full_instr_uses];
           apply in_or_app; right; apply in_or_app; left; exact Hx
          | exact Hagree]
       | intros ? vs _ [-> <-];
         eapply gen_inline_sim_bind;
         [apply (denote_operand_bundles_caller_sim opt_call1 g0 fresh_set stk e1 e2 _ _ f obs);
            [intros x Hx; apply Huses, in_or_app; left; cbn [full_instr_uses];
               apply in_or_app; right; apply in_or_app;
               right; apply in_or_app; right; exact Hx
            | exact Hagree]
         | intros ? [] _ (-> & _ & _);
           eapply gen_inline_sim_bind with
             (RA := fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2);
           [destruct (intrinsic_exp f) as [s |];
            [unfold intrinsic, trigger_cast; apply cfg_inline_sim_trigger_refl; reflexivity
            | eapply gen_inline_sim_bind;
              [apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 None f);
                 [intros x Hx; apply Huses, in_or_app; left; cbn [full_instr_uses full_texp_uses snd];
                  apply in_or_app; left; exact Hx
                 | exact Hagree]
              | intros ? fv _ [-> <-];
                unfold call, trigger_cast; apply cfg_inline_sim_trigger_refl; reflexivity]]
           | intros ? res _ [-> <-];
             eapply gen_inline_sim_bind;
             [apply cfg_inline_sim_check_call_return; reflexivity | intros ? res' _ [-> <-]];
             destruct res' as [ex | dv];
             [eapply gen_inline_sim_bind with (RA := fun _ _ _ => False);
              [apply cfg_inline_sim_raiseLLVM; reflexivity | intros ? ? ? []]
             | eapply gen_inline_sim_obs_eq;
               [ cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
                 symmetry; apply Eqit.bind_ret_l
               | cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
                 symmetry; apply Eqit.bind_ret_l | ]]]]]);
      [(eapply gen_inline_sim_weaken;
        [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                    (IC_Synced stk e1 e2)
                    (IC_Synced stk (Maps.add id dv e1) e2)
                    (IC_Synced stk (Maps.add id dv e1) (Maps.add id dv e2))
                    id id dv Logic.eq_refl Logic.eq_refl)];
        intros ? [] [] (-> & _ & _);
        split; [reflexivity | split; [reflexivity |]];
        eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree])
      | apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]]].
    - (* INSTR_Alloca *)
      destruct iid as [id | vn]; cbn [denote_instr]; [| apply cfg_inline_sim_raise; reflexivity].
      destruct (find_option ann_num_elements annotations) as [[t num_exp] |] eqn:Eann.
      + eapply gen_inline_sim_bind with
          (RA := fun ic' r1 r2 =>
                   r1 = tt /\ r2 = tt /\
                   exists e1' e2',
                     ic' = IC_Synced stk e1' e2' /\
                     env_agree_outside fresh_set e1' e2').
        * eapply gen_inline_sim_bind.
          -- apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some t) num_exp);
               [| exact Hagree].
             intros x Hx; apply Huses, in_or_app; left; cbn [full_instr_uses].
             eapply find_option_ann_num_elements_uses; eassumption.
          -- intros ? n _ [-> <-].
             destruct (dvalue_is_poison n).
             ++ apply cfg_inline_sim_raiseUB.
             ++ eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? n' _ [-> <-]].
                eapply gen_inline_sim_bind;
                  [unfold alloca; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? v _ [-> <-]].
                eapply gen_inline_sim_weaken;
                  [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                              (IC_Synced stk e1 e2)
                              (IC_Synced stk (Maps.add id v e1) e2)
                              (IC_Synced stk (Maps.add id v e1) (Maps.add id v e2))
                              id id v Logic.eq_refl Logic.eq_refl)].
                intros ? [] [] (-> & _ & _).
                split; [reflexivity | split; [reflexivity |]].
                eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
        * intros ? [] [] (_ & _ & e1' & e2' & -> & Hag').
          apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1', e2'; auto]].
      + eapply gen_inline_sim_bind with
          (RA := fun ic' r1 r2 =>
                   r1 = tt /\ r2 = tt /\
                   exists e1' e2',
                     ic' = IC_Synced stk e1' e2' /\
                     env_agree_outside fresh_set e1' e2').
        * eapply gen_inline_sim_bind;
            [unfold alloca; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? v _ [-> <-]].
          eapply gen_inline_sim_weaken;
            [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                        (IC_Synced stk e1 e2)
                        (IC_Synced stk (Maps.add id v e1) e2)
                        (IC_Synced stk (Maps.add id v e1) (Maps.add id v e2))
                        id id v Logic.eq_refl Logic.eq_refl)].
          intros ? [] [] (-> & _ & _).
          split; [reflexivity | split; [reflexivity |]].
          eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
        * intros ? [] [] (_ & _ & e1' & e2' & -> & Hag').
          apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1', e2'; auto]].
    - (* INSTR_Load *)
      destruct iid as [id | vn]; cbn [denote_instr]; [| apply cfg_inline_sim_raise; reflexivity].
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some du) ptr);
          [| exact Hagree].
        intros x Hx; apply Huses, in_or_app; left; cbn [full_instr_uses full_texp_uses snd].
        apply in_or_app; left; exact Hx.
      + intros ? a _ [-> <-].
        eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
        eapply gen_inline_sim_bind;
          [unfold load; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? v _ [-> <-]].
        eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? v' _ [-> <-]].
        eapply gen_inline_sim_bind;
          [apply cfg_inline_sim_assert_load_deref; reflexivity | intros ? [] _ (-> & _ & _)].
        eapply gen_inline_sim_weaken;
          [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                      (IC_Synced stk e1 e2)
                      (IC_Synced stk (Maps.add id v' e1) e2)
                      (IC_Synced stk (Maps.add id v' e1) (Maps.add id v' e2))
                      id id v' Logic.eq_refl Logic.eq_refl)].
        intros ? [] [] (-> & _ & _).
        split; [reflexivity | split; [reflexivity |]].
        eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
    - (* INSTR_Store *)
      destruct iid as [id | vn]; cbn [denote_instr]; [apply cfg_inline_sim_raise; reflexivity |].
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some dt) val);
          [| exact Hagree].
        intros x Hx; apply Huses, in_or_app; left; cbn [full_instr_uses full_texp_uses snd].
        apply in_or_app; left; exact Hx.
      + intros ? v _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some du) ptr);
            [| exact Hagree].
          intros x Hx; apply Huses, in_or_app; left; cbn [full_instr_uses full_texp_uses snd].
          apply in_or_app; right; apply in_or_app; left; exact Hx.
        * intros ? a _ [-> <-].
          eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
          eapply gen_inline_sim_bind.
          -- destruct a as [db | |];
               try (unfold store; apply cfg_inline_sim_trigger_refl; reflexivity).
             destruct db;
               try (unfold store; apply cfg_inline_sim_trigger_refl; reflexivity).
             apply cfg_inline_sim_raiseUB.
          -- intros ? [] _ [-> _]; apply gen_inline_sim_ret.
             split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - (* INSTR_Fence *)
      destruct iid; cbn [denote_instr];
        (apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]]).
    - (* INSTR_AtomicCmpXchg *)
      destruct iid as [id | vn]; cbn [denote_instr]; [| apply cfg_inline_sim_raise; reflexivity].
      apply denote_cmpxchg_caller_sim; [| exact Hagree].
      intros x Hx; apply Huses, in_or_app; left; exact Hx.
    - (* INSTR_AtomicRMW *)
      destruct iid as [id | vn]; cbn [denote_instr]; [| apply cfg_inline_sim_raise; reflexivity].
      apply denote_atomicrmw_caller_sim; [| exact Hagree].
      intros x Hx; apply Huses, in_or_app; left; exact Hx.
    - (* INSTR_VAArg *)
      destruct iid as [id | vn]; cbn [denote_instr];
      (eapply gen_inline_sim_bind;
       [apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2
                 (Some (DTYPE_Base DTYPE_Pointer)) ptr_exp);
          [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree]
       | intros ? ptr_to_args _ [-> <-];
         eapply gen_inline_sim_bind;
         [unfold load; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? args_p _ [-> <-]];
         eapply gen_inline_sim_bind;
         [unfold load; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? retv _ [-> <-]];
         eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? ix _ [-> <-]];
         eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? args' _ [-> <-]];
         eapply gen_inline_sim_bind;
         [unfold store; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? [] _ [-> _]]]);
      [(eapply gen_inline_sim_weaken;
        [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                    (IC_Synced stk e1 e2)
                    (IC_Synced stk (Maps.add id retv e1) e2)
                    (IC_Synced stk (Maps.add id retv e1) (Maps.add id retv e2))
                    id id retv Logic.eq_refl Logic.eq_refl)];
        intros ? [] [] (-> & _ & _);
        split; [reflexivity | split; [reflexivity |]];
        eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree])
      | apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]]].
    - (* INSTR_LandingPad *)
      destruct iid as [id | vn]; cbn [denote_instr]; [| apply cfg_inline_sim_raise; reflexivity].
      eapply gen_inline_sim_bind;
        [unfold stack_get_exc, trigger_cast; apply cfg_inline_sim_trigger_refl; reflexivity
        | intros ? oe _ [-> <-]].
      destruct oe as [ex |]; [| apply cfg_inline_sim_raise; reflexivity].
      eapply gen_inline_sim_weaken;
        [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                    (IC_Synced stk e1 e2)
                    (IC_Synced stk (Maps.add id ex e1) e2)
                    (IC_Synced stk (Maps.add id ex e1) (Maps.add id ex e2))
                    id id ex Logic.eq_refl Logic.eq_refl)].
      intros ? [] [] (-> & _ & _).
      split; [reflexivity | split; [reflexivity |]].
      eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree].
  Qed.

  Lemma denote_code_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (va : option (@ptr (@PROV PaV) (@PTR PaV))) :
    forall (cd : code dtyp) (e1 e2 : @local_env PaV),
      (forall x,
         In x (flat_map (fun '(_, i, mds) => full_instr_uses i ++ flat_map full_metadata_uses mds) cd) ->
         ~ In x fresh_set) ->
      env_agree_outside fresh_set e1 e2 ->
      cfg_inline_sim opt_call1 g0 false
        (fun ic' r1 r2 =>
           r1 = tt /\ r2 = tt /\
           exists e1' e2',
             ic' = IC_Synced stk e1' e2' /\
             env_agree_outside fresh_set e1' e2')
        (IC_Synced stk e1 e2)
        (denote_code cd va)
        (denote_code cd va).
  Proof.
    induction cd as [| [[iid ins] md] rest IH]; intros e1 e2 Huses Hagree;
      cbn [denote_code loop_monad flat_map] in *.
    - apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - eapply gen_inline_sim_bind.
      + apply (denote_instr_caller_sim opt_call1 g0 fresh_set stk e1 e2 va iid ins md);
          [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
      + intros ? [] [] (_ & _ & e1' & e2' & -> & Hagree').
        apply IH; [intros x Hx; apply Huses, in_or_app; right; exact Hx | exact Hagree'].
  Qed.

  Lemma denote_phis_sync_writes_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk :
    forall (dvs : list (local_id * @dvalue PaV)) (e1 e2 : @local_env PaV),
      env_agree_outside fresh_set e1 e2 ->
      cfg_inline_sim opt_call1 g0 false
        (fun ic' _ _ =>
           exists e1' e2',
             ic' = IC_Synced stk e1' e2' /\
             env_agree_outside fresh_set e1' e2')
        (IC_Synced stk e1 e2)
        (map_monad (fun '(id, dv) => lwrite id dv) dvs)
        (map_monad (fun '(id, dv) => lwrite id dv) dvs).
  Proof.
    induction dvs as [| [id dv] rest IH]; intros e1 e2 Hagree; cbn [map_monad].
    - apply gen_inline_sim_ret; exists e1, e2; auto.
    - eapply gen_inline_sim_bind.
      + apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                 (IC_Synced stk e1 e2)
                 (IC_Synced stk (Maps.add id dv e1) e2)
                 (IC_Synced stk (Maps.add id dv e1) (Maps.add id dv e2))
                 id id dv Logic.eq_refl Logic.eq_refl).
      + intros ? [] [] (-> & _ & _).
        eapply gen_inline_sim_bind.
        * apply IH, env_agree_outside_add_both, Hagree.
        * intros ? r1 r2 (e1' & e2' & -> & Hag'); apply gen_inline_sim_ret; exists e1', e2'; auto.
  Qed.

  Lemma denote_phis_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    (call_bid post_bid b_from1 b_from2 : block_id)
    stk (e1 e2 : @local_env PaV)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (Huses : forall x,
               In x (flat_map (fun '(_, p, mds) => full_phi_uses p ++ flat_map full_metadata_uses mds) phis) ->
               ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2)
    (Hentry_or_remap :
       phis = [] \/
       (call_bid <> post_bid /\
        b_from1 <> post_bid /\
        b_from2 = remap_pred_id call_bid post_bid b_from1 /\
        ~ In post_bid (flat_map (fun '(_, Phi _ _ pargs, _) => List.map fst pargs) phis))) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         r1 = tt /\ r2 = tt /\
         exists e1' e2',
           ic' = IC_Synced stk e1' e2' /\
           env_agree_outside fresh_set e1' e2')
      (IC_Synced stk e1 e2)
      (denote_phis b_from1 phis)
      (denote_phis b_from2 (remap_phis_pred call_bid post_bid phis)).
  Proof.
    destruct Hentry_or_remap as [-> | (Hne_cp & Hne_fp & -> & Hnin_pb)].
    - cbn [remap_phis_pred List.map denote_phis map_monad
           ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      eapply gen_inline_sim_obs_eq;
        [ symmetry; rewrite !Eqit.bind_ret_l;
          cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
          rewrite !Eqit.bind_ret_l; reflexivity
        | symmetry; rewrite !Eqit.bind_ret_l;
          cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
          rewrite !Eqit.bind_ret_l; reflexivity
        | ].
      apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - unfold denote_phis.
      assert (Heval :
        forall ps,
          (forall x,
             In x (flat_map (fun '(_, p, mds) => full_phi_uses p ++ flat_map full_metadata_uses mds) ps) ->
             ~ In x fresh_set) ->
          ~ In post_bid (flat_map (fun '(_, Phi _ _ pargs, _) => List.map fst pargs) ps) ->
          cfg_inline_sim opt_call1 g0 false
            (fun ic' dvs1 dvs2 => ic' = IC_Synced stk e1 e2 /\ dvs1 = dvs2)
            (IC_Synced stk e1 e2)
            (map_monad (denote_phi b_from1) ps)
            (map_monad (denote_phi (remap_pred_id call_bid post_bid b_from1))
               (remap_phis_pred call_bid post_bid ps))).
      { induction ps as [| [[x [fm dt pargs]] md] rest IH]; intros Hu Hpb;
          cbn [remap_phis_pred List.map map_monad flat_map] in *.
        - apply gen_inline_sim_ret; split; reflexivity.
        - assert (Hpargs_pb : ~ In post_bid (List.map fst pargs)).
          { intros Hin; apply Hpb, in_or_app; left; exact Hin. }
          eapply gen_inline_sim_bind with
            (RA := fun ic' p1 p2 => ic' = IC_Synced stk e1 e2 /\ p1 = p2).
          + cbn [denote_phi].
            first [rewrite (assoc_remap_pred_id call_bid post_bid b_from1 pargs Hne_cp Hne_fp Hpargs_pb)
                  | lazymatch goal with
                    | |- context [@Assoc.assoc ?A ?B ?RD (remap_pred_id _ _ _) ?xs] =>
                        let t := constr:(@Assoc.assoc A B RD (remap_pred_id call_bid post_bid b_from1) xs) in
                        assert (Hassoc : t = assoc b_from1 pargs)
                          by exact (assoc_remap_pred_id call_bid post_bid b_from1 pargs Hne_cp Hne_fp Hpargs_pb);
                        rewrite Hassoc; clear Hassoc
                    end].
            destruct (assoc b_from1 pargs) as [op |] eqn:Eop;
              [| apply cfg_inline_sim_raise; reflexivity].
            pose proof (assoc_some_in _ _ _ Eop) as Hop_in.
            eapply gen_inline_sim_bind.
            * apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some dt) op);
                [| exact Hagree].
              intros z Hz; apply Hu, in_or_app; left;
                apply in_or_app; left; cbn [full_phi_uses].
              apply in_flat_map; exists (b_from1, op); split; assumption.
            * intros ? uv _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity.
          + intros ? p1 _ [-> <-].
            eapply gen_inline_sim_bind.
            * apply IH;
                [intros z Hz; apply Hu, in_or_app; right; exact Hz
                | intros Hin; apply Hpb, in_or_app; right; exact Hin].
            * intros ? dvs1 _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity. }
      eapply gen_inline_sim_bind; [apply (Heval phis Huses Hnin_pb) |].
      intros ? dvs _ [-> <-].
      eapply gen_inline_sim_bind;
        [apply (denote_phis_sync_writes_sim opt_call1 g0 fresh_set stk dvs e1 e2 Hagree) |].
      intros ? _ _ (e1' & e2' & -> & Hag').
      apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1', e2'; auto]].
  Qed.

  Lemma denote_phis_sync_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    (b_from : block_id)
    stk (e1 e2 : @local_env PaV)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (Huses : forall x,
               In x (flat_map (fun '(_, p, mds) => full_phi_uses p ++ flat_map full_metadata_uses mds) phis) ->
               ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         r1 = tt /\ r2 = tt /\
         exists e1' e2',
           ic' = IC_Synced stk e1' e2' /\
           env_agree_outside fresh_set e1' e2')
      (IC_Synced stk e1 e2)
      (denote_phis b_from phis)
      (denote_phis b_from phis).
  Proof.
    unfold denote_phis.
    assert (Heval :
      forall ps,
        (forall x,
           In x (flat_map (fun '(_, p, mds) => full_phi_uses p ++ flat_map full_metadata_uses mds) ps) ->
           ~ In x fresh_set) ->
        cfg_inline_sim opt_call1 g0 false
          (fun ic' dvs1 dvs2 => ic' = IC_Synced stk e1 e2 /\ dvs1 = dvs2)
          (IC_Synced stk e1 e2)
          (map_monad (denote_phi b_from) ps)
          (map_monad (denote_phi b_from) ps)).
    { induction ps as [| [[x [fm dt pargs]] md] rest IH]; intros Hu;
        cbn [map_monad flat_map] in *.
      - apply gen_inline_sim_ret; split; reflexivity.
      - eapply gen_inline_sim_bind with
          (RA := fun ic' p1 p2 => ic' = IC_Synced stk e1 e2 /\ p1 = p2).
        + cbn [denote_phi].
          destruct (assoc b_from pargs) as [op |] eqn:Eop;
            [| apply cfg_inline_sim_raise; reflexivity].
          pose proof (assoc_some_in _ _ _ Eop) as Hop_in.
          eapply gen_inline_sim_bind.
          * apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some dt) op);
              [| exact Hagree].
            intros z Hz; apply Hu, in_or_app; left;
              apply in_or_app; left; cbn [full_phi_uses].
            apply in_flat_map; exists (b_from, op); split; assumption.
          * intros ? uv _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity.
        + intros ? p1 _ [-> <-].
          eapply gen_inline_sim_bind.
          * apply IH; intros z Hz; apply Hu, in_or_app; right; exact Hz.
          * intros ? dvs1 _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity. }
    eapply gen_inline_sim_bind; [apply (Heval phis Huses) |].
    intros ? dvs _ [-> <-].
    eapply gen_inline_sim_bind;
      [apply (denote_phis_sync_writes_sim opt_call1 g0 fresh_set stk dvs e1 e2 Hagree) |].
    intros ? _ _ (e1' & e2' & -> & Hag').
    apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1', e2'; auto]].
  Qed.

  Lemma denote_terminator_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (e1 e2 : @local_env PaV)
    (tiid : instr_id) (tm : terminator dtyp) (tmd : list (metadata dtyp))
    (Huses : forall x,
               In x (full_term_uses tm ++ flat_map full_metadata_uses tmd) ->
               ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' bd1 bd2 =>
         bd1 = bd2 /\
         (forall succ_bid, bd1 = inl succ_bid -> In succ_bid (term_succ_bids tm)) /\
         exists e1' e2',
           ic' = IC_Synced stk e1' e2' /\
           env_agree_outside fresh_set e1' e2')
      (IC_Synced stk e1 e2)
      (denote_terminator (tiid, tm, tmd))
      (denote_terminator (tiid, tm, tmd)).
  Proof.
    destruct tm as [[dt op] | | [dt op] br1 br2 | br | [dt ex] def_b dests
                    | [t addr] brs fn | [t expr]
                    | [dt fnptrval] args to_lbl unwind_lbl anns obs | ];
      cbn [denote_terminator].
    - (* TERM_Ret *)
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some dt) op);
          [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
      + intros ? dv _ [-> <-]; apply gen_inline_sim_ret.
        split; [reflexivity | split; [intros ?; discriminate | exists e1, e2; auto]].
    - (* TERM_Ret_void *)
      apply gen_inline_sim_ret.
      split; [reflexivity | split; [intros ?; discriminate | exists e1, e2; auto]].
    - (* TERM_Br *)
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some dt) op);
          [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
      + intros ? v _ [-> <-].
        destruct v as [db | |]; cbv beta iota zeta;
          try_cfg_raise.
        destruct db; cbv beta iota zeta;
          try_cfg_raise.
        * destruct sz as [? | ? |]; cbv beta iota zeta;
            try_cfg_raise.
          lazymatch goal with | |- context [VellvmIntegers.equ ?a ?b] => destruct (VellvmIntegers.equ a b) end.
          -- apply gen_inline_sim_ret;
               split;
               [ reflexivity
               | split;
                   [intros ? H; injection H as <-; left; reflexivity | exists e1, e2; auto] ].
          -- apply gen_inline_sim_ret;
               split;
               [ reflexivity
               | split;
                   [ intros ? H; injection H as <-; right; left; reflexivity
                   | exists e1, e2; auto ] ].
        * apply cfg_inline_sim_raiseUB.
    - (* TERM_Br_1 *)
      apply gen_inline_sim_ret;
        split;
        [ reflexivity
        | split;
            [intros ? H; injection H as <-; left; reflexivity | exists e1, e2; auto] ].
    - (* TERM_Switch *)
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some dt) ex);
          [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
      + intros ? sel _ [-> <-].
        destruct (dvalue_is_poison sel); [apply cfg_inline_sim_raiseUB |].
        destruct (switch_elab_ren_b (fun b => b) sel def_b dests)
          as [(eou_err & Hnr & E1 & _) | (b & Hb & E1 & _)].
        * rewrite E1.
          destruct eou_err as [m | m | m | b0];
            [| | | exfalso; exact (Hnr b0 Logic.eq_refl)];
            cbn [EOU_to_itree].
          -- eapply gen_inline_sim_bind with (RA := fun _ _ _ => False);
               [apply cfg_inline_sim_raise; reflexivity | intros ? ? ? []].
          -- eapply gen_inline_sim_bind with (RA := fun _ _ _ => False);
               [apply cfg_inline_sim_raiseOOM | intros ? ? ? []].
          -- eapply gen_inline_sim_bind with (RA := fun _ _ _ => False);
               [apply cfg_inline_sim_raiseUB | intros ? ? ? []].
        * rewrite E1; cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
          eapply gen_inline_sim_obs_eq;
            [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
          apply gen_inline_sim_ret;
            split;
            [reflexivity | split; [intros ? H; injection H as <-; exact Hb | exists e1, e2; auto]].
    - (* TERM_IndirectBr *)
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some t) addr);
          [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
      + intros ? a _ [-> <-].
        destruct (dvalue_is_poison a); [apply cfg_inline_sim_raiseUB |].
        destruct fn as [f |]; [| apply cfg_inline_sim_raise; reflexivity].
        assert (Haddrs :
          forall bs,
            cfg_inline_sim opt_call1 g0 false
              (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
              (IC_Synced stk e1 e2)
              (map_monad (fun b => ba <- gread (blockaddress_id f b) ;; ret (dvalue_ptr_address ba)) bs)
              (map_monad (fun b => ba <- gread (blockaddress_id f b) ;; ret (dvalue_ptr_address ba)) bs)).
        { induction bs as [| b0 rest IH]; cbn [map_monad].
          - apply gen_inline_sim_ret; split; reflexivity.
          - eapply gen_inline_sim_bind with
              (RA := fun ic' oa1 oa2 => ic' = IC_Synced stk e1 e2 /\ oa1 = oa2).
            + eapply gen_inline_sim_bind.
              * unfold gread, trigger_cast; apply cfg_inline_sim_trigger_refl; reflexivity.
              * intros ? ba _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity.
            + intros ? oa _ [-> <-].
              eapply gen_inline_sim_bind; [exact IH | intros ? oas _ [-> <-]].
              apply gen_inline_sim_ret; split; reflexivity. }
        eapply gen_inline_sim_bind; [apply (Haddrs brs) | intros ? addrs _ [-> <-]].
        destruct (dvalue_ptr_address a) as [z |]; [| apply cfg_inline_sim_raise; reflexivity].
        destruct (indirectbr_target z (combine brs addrs)) as [b |] eqn:Eib;
          [| apply cfg_inline_sim_raiseUB].
        assert (Hb_in : In b brs) by (eapply indirectbr_target_In; exact Eib).
        apply gen_inline_sim_ret;
          split;
          [reflexivity | split; [intros ? H; injection H as <-; exact Hb_in | exists e1, e2; auto]].
    - (* TERM_Resume *)
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 (Some t) expr);
          [intros x Hx; apply Huses, in_or_app; left; exact Hx | exact Hagree].
      + intros ? exn _ [-> <-]; apply cfg_inline_sim_raiseLLVM; reflexivity.
    - (* TERM_Invoke *)
      eapply gen_inline_sim_bind.
      + apply (denote_call_args_caller_sim opt_call1 g0 fresh_set stk e1 e2 args);
          [| exact Hagree].
        intros x Hx; apply Huses, in_or_app; left; cbn [full_term_uses].
        apply in_or_app; right; apply in_or_app; left; exact Hx.
      + intros ? uvs _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply (denote_operand_bundles_caller_sim opt_call1 g0 fresh_set stk e1 e2 _ _ fnptrval obs);
            [| exact Hagree].
          intros x Hx; apply Huses, in_or_app; left; cbn [full_term_uses].
          apply in_or_app; right; apply in_or_app;
            right; apply in_or_app; right; exact Hx.
        * intros ? [] _ (-> & _ & _).
          eapply gen_inline_sim_bind.
          -- apply (denote_exp'_caller_sim opt_call1 g0 fresh_set stk e1 e2 None fnptrval);
               [| exact Hagree].
             intros x Hx; apply Huses, in_or_app; left; cbn [full_term_uses full_texp_uses snd].
             apply in_or_app; left; exact Hx.
          -- intros ? fv _ [-> <-].
             eapply gen_inline_sim_bind;
               [unfold call, trigger_cast; apply cfg_inline_sim_trigger_refl; reflexivity
               | intros ? rv _ [-> <-]].
             eapply gen_inline_sim_bind;
               [apply cfg_inline_sim_check_call_return; reflexivity
               | intros ? rv' _ [-> <-]].
             destruct rv' as [exn | ret_v].
             ++ eapply gen_inline_sim_bind;
                  [unfold stack_raise, trigger_cast; apply cfg_inline_sim_trigger_refl; reflexivity
                  | intros ? [] _ [-> _]].
                apply gen_inline_sim_ret.
                split;
                  [ reflexivity
                  | split;
                      [ intros ? H; injection H as <-; right; left; reflexivity
                   | exists e1, e2; auto ] ].
             ++ destruct tiid as [id | vn].
                ** eapply gen_inline_sim_bind.
                   --- apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                                (IC_Synced stk e1 e2)
                                (IC_Synced stk (Maps.add id ret_v e1) e2)
                                (IC_Synced stk (Maps.add id ret_v e1) (Maps.add id ret_v e2))
                                id id ret_v Logic.eq_refl Logic.eq_refl).
                   --- intros ? [] [] (-> & _ & _); apply gen_inline_sim_ret.
                       split; [reflexivity | split;
                         [intros ? H; injection H as <-; left; reflexivity
                         | eexists _, _; split; [reflexivity | apply env_agree_outside_add_both, Hagree]]].
                ** eapply gen_inline_sim_obs_eq;
                     [ cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
                       symmetry; apply Eqit.bind_ret_l
                     | cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
                       symmetry; apply Eqit.bind_ret_l | ].
                   apply gen_inline_sim_ret.
                   split; [reflexivity | split;
                     [intros ? H; injection H as <-; left; reflexivity | exists e1, e2; auto]].
    - (* TERM_Unreachable *)
      apply cfg_inline_sim_raiseUB.
  Qed.

  Lemma cfg_inline_sim_iter_sync
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool)
    (fresh_set : list raw_id)
    stk
    {I1 I2 R1 R2 : Type}
    (RI : I1 -> I2 -> Prop)
    (RR : R1 -> R2 -> Prop)
    (step1 : I1 -> @CFGtop PaV (I1 + R1))
    (step2 : I2 -> @CFGtop PaV (I2 + R2))
    (Hstep :
       forall i1 i2 (e1 e2 : @local_env PaV),
         RI i1 i2 ->
         env_agree_outside fresh_set e1 e2 ->
         cfg_inline_sim opt_call1 g0 false
           (fun ic' lr1 lr2 =>
              exists e1' e2',
                ic' = IC_Synced stk e1' e2' /\
                env_agree_outside fresh_set e1' e2' /\
                match lr1, lr2 with
                | inl next1, inl next2 => RI next1 next2
                | inr r1, inr r2 => RR r1 r2
                | _, _ => False
                end)
           (IC_Synced stk e1 e2)
           (step1 i1) (step2 i2)) :
    forall i1 i2 (e1 e2 : @local_env PaV),
      RI i1 i2 ->
      env_agree_outside fresh_set e1 e2 ->
      cfg_inline_sim opt_call1 g0 bf
        (fun ic' r1 r2 =>
           exists e1' e2',
             ic' = IC_Synced stk e1' e2' /\
             env_agree_outside fresh_set e1' e2' /\
             RR r1 r2)
        (IC_Synced stk e1 e2)
        (ITree.iter step1 i1)
        (ITree.iter step2 i2).
  Proof.
    set (step_rel :=
      fun ic' (lr1 : I1 + R1) (lr2 : I2 + R2) =>
        exists e1' e2',
          ic' = IC_Synced stk e1' e2' /\
          env_agree_outside fresh_set e1' e2' /\
          match lr1, lr2 with
          | inl next1, inl next2 => RI next1 next2
          | inr r1, inr r2 => RR r1 r2
          | _, _ => False
          end).
    set (out_rel :=
      fun ic' (r1 : R1) (r2 : R2) =>
        exists e1' e2',
          ic' = IC_Synced stk e1' e2' /\
          env_agree_outside fresh_set e1' e2' /\
          RR r1 r2).
    set (iter_k1 :=
      fun lr : I1 + R1 =>
        match lr with
        | inl j => Tau (ITree.iter step1 j)
        | inr v => Ret v
        end).
    set (iter_k2 :=
      fun lr : I2 + R2 =>
        match lr with
        | inl j => Tau (ITree.iter step2 j)
        | inr v => Ret v
        end).
    set (r_iter :=
      fun ic0 (a1 : @CFGtop PaV R1) (a2 : @CFGtop PaV R2) =>
        is_ic_synced ic0 = true /\
        exists u1 u2,
          a1 = ITree.bind u1 iter_k1 /\
          a2 = ITree.bind u2 iter_k2 /\
          cfg_inline_sim opt_call1 g0 false step_rel ic0 u1 u2).
    assert (Hlift_cont :
      forall ic0 w1 w2,
        is_ic_synced ic0 = true ->
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
                (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
                opt_call1 g0 false step_rel) bot3)
          ic0 w1 w2 ->
        gis_cont r_iter ic0 (ITree.bind w1 iter_k1) (ITree.bind w2 iter_k2)).
    { intros ic0 w1 w2 Hic0 (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
      exists (ITree.bind m1 iter_k1), (ITree.bind m2 iter_k2).
      split; [apply itree_tau_star_bind, Hs1 |].
      split; [apply itree_tau_star_bind, Hs2 |].
      split; [exact Hic0 | exists m1, m2; auto]. }
    assert (Hone :
      forall ic0 u1 u2,
        is_ic_synced ic0 = true ->
        cfg_inline_sim opt_call1 g0 false step_rel ic0 u1 u2 ->
        gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
          (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
          opt_call1 g0 bf out_rel r_iter
          ic0 (ITree.bind u1 iter_k1) (ITree.bind u2 iter_k2)).
    { intros ic0 u1 u2 Hic0 Hu; punfold Hu.
      revert Hic0;
        induction Hu as [ic0 u1 u2 Hst
                         | ic0 u1 mu1 u2 Hu1 _ IH
                         | ic0 u1 u2 mu2 Hu2 _ IH
                         | ic0 env1 u1 x v ku1 u2 He1 Hu1 Hlk _ IH
                         | ic0 env2 u1 u2 x v ku2 He2 Hu2 Hlk _ IH
                         | ic0 ic' u1 x v ku1 u2 Hw1 Hu1 _ IH
                         | ic0 ic' u1 u2 x v ku2 Hw2 Hu2 _ IH
                         | ic0 u1 k v ku1 u2 Hu1 Hlk _ IH
                         | stk0 ce1 ea1 ea2 u1 varg ku1 u2 Hu1 _ IH
                         | ? ? ? ? ? ? Hfr
                         | ? ? ? ? ? ? ? Hfr
                         | ? ? ? ? ? ? ? Hfr
                         | ? ? ? ? ? ? Hfr
                         | ? ? ? ? ? ? ? ? ? Hfr];
        try discriminate Hfr; intros Hic0.
      - unfold gis_step_body in Hst.
        destruct (observe u1) as [lr1 | m1 | X1 ev1 k1] eqn:Hou1.
        + destruct (observe u2) as [lr2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          destruct Hst as (e1' & e2' & -> & Hag' & Hlr).
          destruct lr1 as [next1 | r1], lr2 as [next2 | r2]; try contradiction.
          * apply GIS_Step; unfold gis_step_body; rewrite !observe_bind, Hou1, Hou2; cbn [observe iter_k1 iter_k2].
            exists (ITree.bind (step1 next1) iter_k1), (ITree.bind (step2 next2) iter_k2).
            split; [eapply ITS_Eq; [apply unfold_iter | apply ITS_Refl] |].
            split; [eapply ITS_Eq; [apply unfold_iter | apply ITS_Refl] |].
            split; [reflexivity | exists (step1 next1), (step2 next2); split; [reflexivity | split; [reflexivity |]]].
            apply (Hstep next1 next2 e1' e2' Hlr Hag').
          * apply GIS_Step; unfold gis_step_body; rewrite !observe_bind, Hou1, Hou2; cbn [observe iter_k1 iter_k2].
            exists e1', e2'; auto.
        + destruct (observe u2) as [lr2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          apply GIS_Step; unfold gis_step_body; rewrite !observe_bind, Hou1, Hou2.
          apply (Hlift_cont ic0 m1 m2 Hic0 Hst).
        + apply GIS_Step; unfold gis_step_body; rewrite (observe_bind u1 iter_k1), Hou1.
          destruct Hst as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe u2) as [lr2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          rewrite (observe_bind u2 iter_k2), Hou2.
          destruct Hvis as [(Hsync & HE & HA) | Hls].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; apply (Hlift_cont ic0 _ _ Hic0 (HA a1 a2 Ha Hp)).
          * right; destruct ic0 as [stk0 env1 env2 | |]; try discriminate Hic0.
            destruct Hls as [Hloc | [Hfr_s _]]; [| discriminate Hfr_s].
            left; destruct (as_local_cfg ev1) as [le1 |], (as_local_cfg ev2) as [le2 |]; try contradiction.
            destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
            -- destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv |]].
               eapply Hlift_cont; [| exact Hr]; reflexivity.
            -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
               intros v Hv; eapply Hlift_cont; [| exact (Hrd v Hv)]; reflexivity.
      - eapply GIS_TauL; [rewrite (observe_bind u1 iter_k1), Hu1; reflexivity | apply IH, Hic0].
      - eapply GIS_TauR; [rewrite (observe_bind u2 iter_k2), Hu2; reflexivity | apply IH, Hic0].
      - eapply GIS_ReadL; [exact He1 | rewrite Hu1, Eqit.bind_bind; reflexivity | exact Hlk | apply IH, Hic0].
      - eapply GIS_ReadR; [exact He2 | rewrite Hu2, Eqit.bind_bind; reflexivity | exact Hlk | apply IH, Hic0].
      - assert (Hic' : is_ic_synced ic' = true).
        { destruct ic0; try discriminate Hic0; cbn in Hw1; injection Hw1 as <-; reflexivity. }
        eapply GIS_WriteL; [exact Hw1 | rewrite Hu1, Eqit.bind_bind; reflexivity | apply IH, Hic'].
      - assert (Hic' : is_ic_synced ic' = true).
        { destruct ic0; try discriminate Hic0; cbn in Hw2; injection Hw2 as <-; reflexivity. }
        eapply GIS_WriteR; [exact Hw2 | rewrite Hu2, Eqit.bind_bind; reflexivity | apply IH, Hic'].
      - eapply GIS_GReadL; [rewrite Hu1, Eqit.bind_bind; reflexivity | exact Hlk | apply IH, Hic0].
      - discriminate Hic0. }
    assert (Hmain :
      forall ic0 t1 t2,
        r_iter ic0 t1 t2 ->
        cfg_inline_sim opt_call1 g0 bf out_rel ic0 t1 t2).
    { pcofix CIH.
      intros ic0 t1 t2 (Hic0 & u1 & u2 & -> & -> & Hu); pstep.
      eapply gen_inline_sim__mon with (r := r_iter);
        [apply Hone; assumption | intros ic1 a1 a2 Hr; right; apply CIH, Hr]. }
    intros i1 i2 e1 e2 Hi Hagree.
    eapply gen_inline_sim_obs_eq;
      [symmetry; apply unfold_iter | symmetry; apply unfold_iter |].
    apply Hmain; split; [reflexivity |].
    exists (step1 i1), (step2 i2); split; [reflexivity | split; [reflexivity | apply Hstep; assumption]].
  Qed.


  (** ** 10B. Single-Step [run_exc] Lifting, Unchanged Function & Caller Inlining Loop *)

  Lemma denote_exp'_global_eq (top : option dtyp) (gid : function_id) :
    @denote_exp' PaV top (EXP_Ident (ID_Global gid)) ≅
    ITree.trigger (subevent _ (GlobalRead gid)).
  Proof using.
    unfold denote_exp'; cbn [denote_exp lookup_id]; unfold gread.
    unfold withCall; try unfold trigger; unfold ITree.trigger.
    rewrite translate_vis.
    norm_subevent.
    apply eqit_Vis; intros x; apply translate_ret.
  Qed.

  Lemma denote_exp'_local_eq (top : option dtyp) (lid : local_id) :
    @denote_exp' PaV top (EXP_Ident (ID_Local lid)) ≅
    ITree.trigger (subevent _ (LocalRead lid)).
  Proof using.
    unfold denote_exp'; cbn [denote_exp lookup_id]; unfold lread.
    unfold withCall; try unfold trigger; unfold ITree.trigger.
    rewrite translate_vis.
    norm_subevent.
    apply eqit_Vis; intros x; apply translate_ret.
  Qed.

  Definition finish_cfg (r : (block_id * block_id) + @dvalue PaV) : @CFGtop PaV (@dvalue PaV) :=
    match r with
    | inl bid => raise ("Can't find block in denote_cfg " ++ show (snd bid))%string
    | inr uv  => Ret uv
    end.

  Definition step_bd_cont (bks : ocfg dtyp) (va : option (@ptr (@PROV PaV) (@PTR PaV))) (src_bid : block_id)
    (bd : block_id + @dvalue PaV) : @CFGtop PaV (@dvalue PaV) :=
    match bd with
    | inr dv => Ret dv
    | inl bid_target =>
        Tau (ITree.bind (denote_ocfg_map (ocfg_map bks) va (src_bid, bid_target)) finish_cfg)
    end.

  Lemma ocfg_bind_finish_none_eq (bks : ocfg dtyp) (va : option (@ptr (@PROV PaV) (@PTR PaV)))
    (b_from bid : block_id)
    (Hfb : find_block bks bid = None) :
    ITree.bind (denote_ocfg_map (ocfg_map bks) va (b_from, bid)) finish_cfg ≅
    raise ("Can't find block in denote_cfg " ++ show bid)%string.
  Proof using.
    rewrite denote_ocfg_map_unfold_eq, Hfb, Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma ocfg_bind_finish_some_eq (bks : ocfg dtyp) (va : option (@ptr (@PROV PaV) (@PTR PaV)))
    (b_from bid : block_id) (bk : block dtyp)
    (Hfb : find_block bks bid = Some bk) :
    ITree.bind (denote_ocfg_map (ocfg_map bks) va (b_from, bid)) finish_cfg ≅
    ITree.bind (denote_block bk b_from va) (step_bd_cont bks va bid).
  Proof using.
    rewrite denote_ocfg_map_unfold_eq, Hfb, Eqit.bind_bind.
    apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [bid_target | dv] _ <-; cbn [step_bd_cont].
    - apply Eqit.bind_tau.
    - rewrite Eqit.bind_ret_l; cbn [finish_cfg]; reflexivity.
  Qed.

  Lemma denote_cfg_other_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (c : CFG.cfg dtyp) (va : option (@ptr (@PROV PaV) (@PTR PaV)))
    stk (e1 e2 : @local_env PaV)
    (Hagree : env_agree_outside [] e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         exists e1' e2',
           ic' = IC_Synced stk e1' e2' /\
           env_agree_outside [] e1' e2' /\
           r1 = r2)
      (IC_Synced stk e1 e2)
      (denote_cfg_map (ocfg_map (blks c)) c va)
      (denote_cfg_map (ocfg_map (blks c)) c va).
  Proof using.
    unfold denote_cfg_map.
    eapply gen_inline_sim_bind.
    - unfold denote_ocfg_map.
      apply (cfg_inline_sim_iter_sync opt_call1 g0 false [] stk Logic.eq Logic.eq);
        [| reflexivity | exact Hagree].
      intros [bid_from bid_src] ? ea1 ea2 <- Hag_i.
      destruct (RM.find bid_src (ocfg_map (blks c))) as [bk |].
      + unfold denote_block; cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        eapply gen_inline_sim_obs_eq;
          [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
        eapply gen_inline_sim_bind.
        * apply (denote_phis_sync_sim opt_call1 g0 [] bid_from stk ea1 ea2 (blk_phis bk)
                   (fun _ _ H => H) Hag_i).
        * intros ? [] [] (_ & _ & e1_p & e2_p & -> & Hag_p).
          eapply gen_inline_sim_obs_eq;
            [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
          eapply gen_inline_sim_bind.
          -- apply (denote_code_caller_sim opt_call1 g0 [] stk va (blk_code bk) e1_p e2_p
                      (fun _ _ H => H) Hag_p).
          -- intros ? [] [] (_ & _ & e1_c & e2_c & -> & Hag_c).
             destruct (blk_term bk) as [[tiid tm] tmd].
             eapply gen_inline_sim_bind.
             ++ apply (denote_terminator_caller_sim opt_call1 g0 [] stk e1_c e2_c tiid tm tmd
                         (fun _ _ H => H) Hag_c).
             ++ intros ? bd1 bd2 (<- & _ & e1_t & e2_t & -> & Hag_t).
                destruct bd1 as [bid_target | dv];
                  apply gen_inline_sim_ret; exists e1_t, e2_t; auto.
      + apply gen_inline_sim_ret; exists ea1, ea2; auto.
    - intros ? r1 r2 (e1' & e2' & -> & Hag' & <-).
      destruct r1 as [bid | uv].
      + apply cfg_inline_sim_raise; reflexivity.
      + apply gen_inline_sim_ret; exists e1', e2'; auto.
  Qed.

  Lemma denote_function_from_run_exc_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (df1 df2 : definition dtyp (CFG.cfg dtyp))
    (Hproto : df_prototype df1 = df_prototype df2)
    (Hargs : df_args df1 = df_args df2)
    (Hrun :
       forall stk0 (e0 : @local_env PaV) (varg : @ptr (@PROV PaV) (@PTR PaV)),
         cfg_inline_sim opt_call1 g0 true
           (fun ic' rv1 rv2 =>
              exists e1' e2',
                ic' = IC_Synced stk0 e1' e2' /\
                rv1 = rv2)
           (IC_Synced stk0 e0 e0)
           (run_exc (denote_cfg_map (ocfg_map (blks (df_instrs df1))) (df_instrs df1) (Some varg)))
           (run_exc (denote_cfg_map (ocfg_map (blks (df_instrs df2))) (df_instrs df2) (Some varg)))) :
    forall stk e1 e2 cc args,
      cfg_inline_sim opt_call1 g0 true
        (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
        (IC_Synced stk e1 e2)
        (denote_function df1 cc args)
        (denote_function df2 cc args).
  Proof using.
    intros stk e1 e2 cc args.
    unfold denote_function; rewrite <- Hproto.
    destruct (dc_param_attrs (df_prototype df1)) as [ret_attrs args_attrs].
    eapply gen_inline_sim_bind;
      [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
    eapply gen_inline_sim_bind;
      [apply cfg_inline_sim_apply_args_attrs; reflexivity | intros ? args' _ [-> <-]].
    eapply gen_inline_sim_bind with
      (RA := fun ic' varg1 varg2 =>
               varg1 = varg2 /\
               exists bs,
                 ic' = IC_Synced ((e1, e2) :: stk) (init_local_env bs) (init_local_env bs)).
    - unfold push_call_frame; rewrite <- Hargs.
      eapply gen_inline_sim_bind;
        [apply cfg_inline_sim_EOU; reflexivity | intros ? [bs vs] _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply cfg_inline_sim_EOU; reflexivity | intros ? dts _ [-> <-]].
      eapply gen_inline_sim_bind;
        [unfold mem_push; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? [] _ [-> _]].
      eapply gen_inline_sim_bind;
        [apply cfg_inline_sim_stack_push_sync | intros ? [] [] (-> & _ & _)].
      eapply gen_inline_sim_bind;
        [unfold alloca; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? va1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [unfold store; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? [] _ [-> _]].
      destruct va1 as [[varg | | | | | | |] | |]; cbv beta iota zeta;
        try_cfg_raise.
      apply gen_inline_sim_ret.
      split; [reflexivity | exists bs; reflexivity].
    - intros ? varg1 varg2 (<- & bs & ->).
      eapply gen_inline_sim_bind.
      + apply (Hrun ((e1, e2) :: stk) (init_local_env bs) varg1).
      + intros ? rv1 rv2 (e1' & e2' & -> & <-).
        eapply gen_inline_sim_bind.
        * unfold pop_call_frame.
          eapply gen_inline_sim_bind;
            [apply cfg_inline_sim_stack_pop_sync | intros ? [] [] (-> & _ & _)].
          unfold mem_pop; apply cfg_inline_sim_trigger_refl; reflexivity.
        * intros ? [] _ [-> _].
          apply cfg_inline_sim_check_call_return; reflexivity.
  Qed.

  Lemma denote_function_other_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (df : definition dtyp (CFG.cfg dtyp)) :
    forall stk e1 e2 cc args,
      cfg_inline_sim opt_call1 g0 true
        (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
        (IC_Synced stk e1 e2)
        (denote_function df cc args)
        (denote_function df cc args).
  Proof using.
    apply (denote_function_from_run_exc_sim opt_call1 g0 df df Logic.eq_refl Logic.eq_refl).
    intros stk0 e0 varg.
    eapply (cfg_inline_sim_run_exc_both opt_call1 g0 true stk0);
      [| | exists e0, e0; reflexivity
       | apply denote_cfg_other_sim, env_agree_outside_refl].
    - intros e1' e2' ex; exists e1', e2'; auto.
    - intros ic' x1 x2 _ (e1' & e2' & -> & _ & <-); exists e1', e2'; auto.
  Qed.

  Lemma run_exc_bind_step_sync
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (stk : env_stack)
    {A1 A2 B1 B2 : Type}
    (RA : inline_ctx -> A1 -> A2 -> Prop)
    (RB : inline_ctx -> @exc PaV + B1 -> @exc PaV + B2 -> Prop)
    (r_co : inline_ctx -> @CFGtop PaV (@exc PaV + B1) -> @CFGtop PaV (@exc PaV + B2) -> Prop)
    (k1 : A1 -> @CFGtop PaV B1)
    (k2 : A2 -> @CFGtop PaV B2)
    (Hexc : forall e1 e2 ex, RB (IC_Synced stk e1 e2) (inl ex) (inl ex))
    (Hr_wrap :
       forall ic' m1 m2,
         ic_synced_stk stk ic' ->
         cfg_inline_sim opt_call1 g0 false RA ic' m1 m2 ->
         r_co ic' (run_exc (ITree.bind m1 k1)) (run_exc (ITree.bind m2 k2)))
    (Hret :
       forall ic' x1 x2,
         ic_synced_stk stk ic' ->
         RA ic' x1 x2 ->
         gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
           (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
           opt_call1 g0 bf RB r_co ic'
           (run_exc (k1 x1)) (run_exc (k2 x2))) :
    forall ic (a1 : @CFGtop PaV A1) (a2 : @CFGtop PaV A2),
      ic_synced_stk stk ic ->
      cfg_inline_sim opt_call1 g0 false RA ic a1 a2 ->
      gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
        (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
        opt_call1 g0 bf RB r_co ic
        (run_exc (ITree.bind a1 k1))
        (run_exc (ITree.bind a2 k2)).
  Proof using.
    intros ic a1 a2 Hic Hsim; punfold Hsim.
    assert (Hlift_sync_cont :
      forall ic0 u1 u2,
        ic_synced_stk stk ic0 ->
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
                (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
                opt_call1 g0 false RA) bot3)
          ic0 u1 u2 ->
        gis_cont r_co ic0
          (Tau (run_exc (ITree.bind u1 k1)))
          (Tau (run_exc (ITree.bind u2 k2)))).
    { intros ic0 u1 u2 Hic0 (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
      exists (run_exc (ITree.bind m1 k1)), (run_exc (ITree.bind m2 k2)).
      split; [apply ITS_Tau, itree_tau_star_run_exc, itree_tau_star_bind, Hs1 |].
      split; [apply ITS_Tau, itree_tau_star_run_exc, itree_tau_star_bind, Hs2 |].
      apply (Hr_wrap ic0 m1 m2 Hic0 Hm). }
    revert Hic;
      induction Hsim as [ic a1 a2 Hstep
                         | ic a1 ma1 a2 Ha1 _ IH
                         | ic a1 a2 ma2 Ha2 _ IH
                         | ic env1 a1 x v fa1 a2 He1 Ha1 Hlk _ IH
                         | ic env2 a1 a2 x v fa2 He2 Ha2 Hlk _ IH
                         | ic ic' a1 x v fa1 a2 Hw1 Ha1 _ IH
                         | ic ic' a1 a2 x v fa2 Hw2 Ha2 _ IH
                         | ic a1 k v fa1 a2 Ha1 Hlk _ IH
                         | stk0 ce1 e1 e2 a1 varg fa1 a2 Ha1 _ IH
                         | stk0 e1 e2 a1 fa1 a2 Hfr
                         | stk0 ce1 e2 bs a1 fa1 a2 Hfr
                         | stk0 ce1 e1 e2 a1 fa1 a2 Hfr
                         | stk0 ce1 e2 a1 fa1 a2 Hfr
                         | stk0 e1 e2 a1 X ce body1 fa1 a2 Hfr];
      try discriminate Hfr; intros Hic.
    - unfold gis_step_body in Hstep.
      destruct (observe a1) as [x1 | ma1 | X1 e1 fa1] eqn:Hoa1.
      + destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
        assert (Eb1 : run_exc (ITree.bind a1 k1) ≅ run_exc (k1 x1)).
        { apply run_exc_proper; rewrite (itree_eta a1), Hoa1, Eqit.bind_ret_l; reflexivity. }
        assert (Eb2 : run_exc (ITree.bind a2 k2) ≅ run_exc (k2 x2)).
        { apply run_exc_proper; rewrite (itree_eta a2), Hoa2, Eqit.bind_ret_l; reflexivity. }
        eapply gen_inline_sim__obs_eq;
          [symmetry; exact Eb1 | symmetry; exact Eb2 | apply (Hret ic x1 x2 Hic Hstep)].
      + destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
        destruct Hstep as (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
        assert (Hou1 : observe (ITree.bind a1 k1) = TauF (ITree.bind ma1 k1)).
        { rewrite observe_bind, Hoa1; reflexivity. }
        assert (Hou2 : observe (ITree.bind a2 k2) = TauF (ITree.bind ma2 k2)).
        { rewrite observe_bind, Hoa2; reflexivity. }
        eapply gen_inline_sim__obs_eq;
          [symmetry; apply (run_exc_tau_eq _ _ Hou1)
          | symmetry; apply (run_exc_tau_eq _ _ Hou2) |].
        apply GIS_Step; cbn [gis_step_body observe].
        exists (run_exc (ITree.bind m1 k1)), (run_exc (ITree.bind m2 k2)).
        split; [apply itree_tau_star_run_exc, itree_tau_star_bind, Hs1 |].
        split; [apply itree_tau_star_run_exc, itree_tau_star_bind, Hs2 |].
        apply (Hr_wrap ic m1 m2 Hic Hm).
      + assert (Hou1 : observe (ITree.bind a1 k1) = VisF e1 (fun y => ITree.bind (fa1 y) k1)).
        { rewrite observe_bind, Hoa1; reflexivity. }
        destruct Hstep as [Hub | Hvis].
        * pose proof (inl_is_ub_cfg_no_exc e1 Hub) as Hex1.
          eapply gen_inline_sim__obs_eq;
            [symmetry; apply (run_exc_vis_none_eq _ _ _ Hou1 Hex1) | reflexivity |].
          apply GIS_Step; cbn [gis_step_body observe]; left; exact Hub.
        * destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
          assert (Hou2 : observe (ITree.bind a2 k2) = VisF e2 (fun y => ITree.bind (fa2 y) k2)).
          { rewrite observe_bind, Hoa2; reflexivity. }
          destruct Hic as (env1' & env2' & ->).
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | [Hfr_s _]]]; [| | discriminate Hfr_s].
          -- pose proof (EqE_CFG_exc_of_event e1 e2 HE) as Hex12.
             destruct (exc_of_event e1) as [ex |] eqn:Hex1.
             ++ symmetry in Hex12.
                eapply gen_inline_sim__obs_eq;
                  [symmetry; apply (run_exc_vis_some_eq _ _ _ _ Hou1 Hex1)
                  | symmetry; apply (run_exc_vis_some_eq _ _ _ _ Hou2 Hex12) |].
                apply GIS_Step; cbn [gis_step_body observe]; apply Hexc.
             ++ symmetry in Hex12.
                eapply gen_inline_sim__obs_eq;
                  [symmetry; apply (run_exc_vis_none_eq _ _ _ Hou1 Hex1)
                  | symmetry; apply (run_exc_vis_none_eq _ _ _ Hou2 Hex12) |].
                apply GIS_Step; cbn [gis_step_body observe]; right; left.
                split; [exact Hsync | split; [exact HE |]].
                intros y1 y2 Hy Hp.
                apply (Hlift_sync_cont _ _ _ (ex_intro _ env1' (ex_intro _ env2' Logic.eq_refl))
                         (HA y1 y2 Hy Hp)).
          -- destruct (as_local_cfg e1) as [le1 |] eqn:Ele1,
                      (as_local_cfg e2) as [le2 |] eqn:Ele2; try contradiction.
             assert (Hex1 : exc_of_event e1 = None).
             { destruct_sum1 e1; try discriminate Ele1; reflexivity. }
             assert (Hex2 : exc_of_event e2 = None).
             { destruct_sum1 e2; try discriminate Ele2; reflexivity. }
             eapply gen_inline_sim__obs_eq;
               [symmetry; apply (run_exc_vis_none_eq _ _ _ Hou1 Hex1)
               | symmetry; apply (run_exc_vis_none_eq _ _ _ Hou2 Hex2) |].
             apply GIS_Step; cbn [gis_step_body observe]; right; right; left.
             rewrite Ele1, Ele2.
             destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
             ++ destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv |]].
                apply (Hlift_sync_cont _ _ _
                         (ex_intro _ (Maps.add x1 v1 env1') (ex_intro _ (Maps.add x2 v2 env2') Logic.eq_refl))
                         Hr).
             ++ destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                intros v Hv.
                apply (Hlift_sync_cont _ _ _ (ex_intro _ env1' (ex_intro _ env2' Logic.eq_refl))
                         (Hrd v Hv)).
    - assert (Hou1 : observe (ITree.bind a1 k1) = TauF (ITree.bind ma1 k1)).
      { rewrite observe_bind, Ha1; reflexivity. }
      eapply gen_inline_sim__obs_eq;
        [symmetry; apply (run_exc_tau_eq _ _ Hou1) | reflexivity |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - assert (Hou2 : observe (ITree.bind a2 k2) = TauF (ITree.bind ma2 k2)).
      { rewrite observe_bind, Ha2; reflexivity. }
      eapply gen_inline_sim__obs_eq;
        [reflexivity | symmetry; apply (run_exc_tau_eq _ _ Hou2) |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic].
    - assert (Eb1 : ITree.bind a1 k1 ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalRead x)))
                      (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : run_exc (ITree.bind a1 k1) ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalRead x)))
                      (fun y => Tau (run_exc (ITree.bind (fa1 y) k1)))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite run_exc_bind_trigger_none_eq by reflexivity; reflexivity. }
      eapply GIS_ReadL; [exact He1 | exact El1 | exact Hlk |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - assert (Eb2 : ITree.bind a2 k2 ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalRead x)))
                      (fun y => ITree.bind (fa2 y) k2)).
      { rewrite Ha2, Eqit.bind_bind; reflexivity. }
      assert (Er2 : run_exc (ITree.bind a2 k2) ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalRead x)))
                      (fun y => Tau (run_exc (ITree.bind (fa2 y) k2)))).
      { rewrite (run_exc_proper _ _ Eb2).
        rewrite run_exc_bind_trigger_none_eq by reflexivity; reflexivity. }
      eapply GIS_ReadR; [exact He2 | exact Er2 | exact Hlk |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic].
    - assert (Hic' : ic_synced_stk stk ic').
      { destruct Hic as (env1' & env2' & ->); cbn in Hw1; injection Hw1 as <-.
        eexists _, _; reflexivity. }
      assert (Eb1 : ITree.bind a1 k1 ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalWrite x v)))
                      (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : run_exc (ITree.bind a1 k1) ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalWrite x v)))
                      (fun y => Tau (run_exc (ITree.bind (fa1 y) k1)))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite run_exc_bind_trigger_none_eq by reflexivity; reflexivity. }
      eapply GIS_WriteL; [exact Hw1 | exact El1 |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic'].
    - assert (Hic' : ic_synced_stk stk ic').
      { destruct Hic as (env1' & env2' & ->); cbn in Hw2; injection Hw2 as <-.
        eexists _, _; reflexivity. }
      assert (Eb2 : ITree.bind a2 k2 ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalWrite x v)))
                      (fun y => ITree.bind (fa2 y) k2)).
      { rewrite Ha2, Eqit.bind_bind; reflexivity. }
      assert (Er2 : run_exc (ITree.bind a2 k2) ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalWrite x v)))
                      (fun y => Tau (run_exc (ITree.bind (fa2 y) k2)))).
      { rewrite (run_exc_proper _ _ Eb2).
        rewrite run_exc_bind_trigger_none_eq by reflexivity; reflexivity. }
      eapply GIS_WriteR; [exact Hw2 | exact Er2 |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic'].
    - assert (Eb1 : ITree.bind a1 k1 ≅
                    ITree.bind (ITree.trigger (subevent _ (GlobalRead k)))
                      (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : run_exc (ITree.bind a1 k1) ≅
                    ITree.bind (ITree.trigger (subevent _ (GlobalRead k)))
                      (fun y => Tau (run_exc (ITree.bind (fa1 y) k1)))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite run_exc_bind_trigger_none_eq by reflexivity; reflexivity. }
      eapply GIS_GReadL; [exact El1 | exact Hlk |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - destruct Hic as (? & ? & Hdisc); discriminate Hdisc.
  Qed.

  Lemma cfg_entry_has_no_phis_inv {T : Set} (c : CFG.cfg T) :
    cfg_entry_has_no_phis c = true ->
    exists b0, find_block (blks c) (init c) = Some b0 /\ blk_phis b0 = [].
  Proof using.
    unfold cfg_entry_has_no_phis.
    destruct (find_block (blks c) (init c)) as [b0 |]; [| discriminate].
    intros H; apply is_empty_list_spec in H; exists b0; auto.
  Qed.

  Lemma gen_inline_sim__run_exc_raise
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> @exc PaV + R1 -> @exc PaV + R2 -> Prop)
    (r_co : inline_ctx -> @CFGtop PaV (@exc PaV + R1) -> @CFGtop PaV (@exc PaV + R2) -> Prop)
    (ic : inline_ctx) (msg1 msg2 : string)
    (Hact : is_ic_active ic = true) :
    gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
      (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
      opt_call1 g0 bf RR r_co ic (run_exc (raise msg1)) (run_exc (raise msg2)).
  Proof using.
    unfold raise, trigger_cast.
    eapply gen_inline_sim__obs_eq;
      [symmetry;
       rewrite run_exc_bind_trigger_none_eq by reflexivity; rewrite bind_trigger;
       reflexivity
      | symmetry;
        rewrite run_exc_bind_trigger_none_eq by reflexivity; rewrite bind_trigger;
        reflexivity |].
    apply GIS_Step; cbn [gis_step_body observe]; right; left.
    split; [destruct ic; try discriminate Hact; reflexivity |].
    split; [exact I | intros [] [] _ _].
  Qed.

  Lemma run_exc_bind_step_inlined
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool)
    {A1 A2 B1 B2 C1 : Type}
    (RA : inline_ctx -> A1 -> A2 -> Prop)
    (RC : inline_ctx -> C1 -> @exc PaV + B2 -> Prop)
    (r_co : inline_ctx -> @CFGtop PaV C1 -> @CFGtop PaV (@exc PaV + B2) -> Prop)
    (k1 : A1 -> @CFGtop PaV B1)
    (K1 : @exc PaV + B1 -> @CFGtop PaV C1)
    (k2 : A2 -> @CFGtop PaV B2)
    (Hr_wrap :
       forall ic' m1 m2,
         is_ic_inlined ic' = true ->
         cfg_inline_sim opt_call1 g0 false RA ic' m1 m2 ->
         r_co ic' (ITree.bind (run_exc (ITree.bind m1 k1)) K1) (run_exc (ITree.bind m2 k2)))
    (Hret :
       forall ic' x1 x2,
         is_ic_inlined ic' = true ->
         RA ic' x1 x2 ->
         gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
           (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
           opt_call1 g0 bf RC r_co ic'
           (ITree.bind (run_exc (k1 x1)) K1)
           (run_exc (k2 x2))) :
    forall ic (a1 : @CFGtop PaV A1) (a2 : @CFGtop PaV A2),
      is_ic_inlined ic = true ->
      cfg_inline_sim opt_call1 g0 false RA ic a1 a2 ->
      gen_inline_sim_ (@inl_is_ub_cfg IP IPT) inl_sync_cfg EqE_CFG EqA_CFG
        (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
        opt_call1 g0 bf RC r_co ic
        (ITree.bind (run_exc (ITree.bind a1 k1)) K1)
        (run_exc (ITree.bind a2 k2)).
  Proof using.
    intros ic a1 a2 Hic Hsim; punfold Hsim.
    revert Hic;
      induction Hsim as [ic a1 a2 Hstep
                         | ic a1 ma1 a2 Ha1 _ IH
                         | ic a1 a2 ma2 Ha2 _ IH
                         | ic env1 a1 x v fa1 a2 He1 Ha1 Hlk _ IH
                         | ic env2 a1 a2 x v fa2 He2 Ha2 Hlk _ IH
                         | ic ic' a1 x v fa1 a2 Hw1 Ha1 _ IH
                         | ic ic' a1 a2 x v fa2 Hw2 Ha2 _ IH
                         | ic a1 k v fa1 a2 Ha1 Hlk _ IH
                         | stk ce1 e1 e2 a1 varg fa1 a2 Ha1 _ IH
                         | stk e1 e2 a1 fa1 a2 Hfr
                         | stk ce1 e2 bs a1 fa1 a2 Hfr
                         | stk ce1 e1 e2 a1 fa1 a2 Hfr
                         | stk ce1 e2 a1 fa1 a2 Hfr
                         | stk e1 e2 a1 X ce body1 fa1 a2 Hfr];
      try discriminate Hfr; intros Hic.
    - unfold gis_step_body in Hstep.
      destruct (observe a1) as [x1 | ma1 | X1 e1 fa1] eqn:Hoa1.
      + destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
        assert (Eb1 : ITree.bind (run_exc (ITree.bind a1 k1)) K1 ≅ ITree.bind (run_exc (k1 x1)) K1).
        { apply eq_itree_clo_bind with (UU := Logic.eq); [| intros ? _ <-; reflexivity].
          apply run_exc_proper; rewrite (itree_eta a1), Hoa1, Eqit.bind_ret_l; reflexivity. }
        assert (Eb2 : run_exc (ITree.bind a2 k2) ≅ run_exc (k2 x2)).
        { apply run_exc_proper; rewrite (itree_eta a2), Hoa2, Eqit.bind_ret_l; reflexivity. }
        eapply gen_inline_sim__obs_eq;
          [symmetry; exact Eb1 | symmetry; exact Eb2 | apply (Hret ic x1 x2 Hic Hstep)].
      + destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
        destruct Hstep as (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
        assert (Hou1 : observe (ITree.bind a1 k1) = TauF (ITree.bind ma1 k1)).
        { rewrite observe_bind, Hoa1; reflexivity. }
        assert (Hou2 : observe (ITree.bind a2 k2) = TauF (ITree.bind ma2 k2)).
        { rewrite observe_bind, Hoa2; reflexivity. }
        eapply gen_inline_sim__obs_eq;
          [symmetry; rewrite (run_exc_tau_eq _ _ Hou1), Eqit.bind_tau; reflexivity
          | symmetry; apply (run_exc_tau_eq _ _ Hou2) |].
        apply GIS_Step; cbn [gis_step_body observe].
        exists (ITree.bind (run_exc (ITree.bind m1 k1)) K1),
               (run_exc (ITree.bind m2 k2)).
        split; [apply itree_tau_star_bind, itree_tau_star_run_exc, itree_tau_star_bind, Hs1 |].
        split; [apply itree_tau_star_run_exc, itree_tau_star_bind, Hs2 |].
        apply (Hr_wrap ic m1 m2 Hic Hm).
      + assert (Hou1 : observe (ITree.bind a1 k1) = VisF e1 (fun y => ITree.bind (fa1 y) k1)).
        { rewrite observe_bind, Hoa1; reflexivity. }
        destruct Hstep as [Hub | Hvis].
        * pose proof (inl_is_ub_cfg_no_exc e1 Hub) as Hex1.
          eapply gen_inline_sim__obs_eq;
            [symmetry; rewrite (run_exc_vis_none_eq _ _ _ Hou1 Hex1), Eqit.bind_vis; reflexivity
            | reflexivity |].
          apply GIS_Step; cbn [gis_step_body observe]; left; exact Hub.
        * destruct (observe a2) as [x2 | ma2 | X2 e2 fa2] eqn:Hoa2; try contradiction.
          destruct ic as [| | stk ce1 e1_env e2_env]; try discriminate Hic.
          destruct Hvis as [(Hsync & HE & HA) | []].
          pose proof (inl_sync_cfg_inlined_no_exc stk ce1 e1_env e2_env e1 Hsync) as Hex1.
          pose proof (EqE_CFG_exc_of_event e1 e2 HE) as Hex12.
          assert (Hex2 : exc_of_event e2 = None) by congruence.
          assert (Hou2 : observe (ITree.bind a2 k2) = VisF e2 (fun y => ITree.bind (fa2 y) k2)).
          { rewrite observe_bind, Hoa2; reflexivity. }
          eapply gen_inline_sim__obs_eq;
            [symmetry; rewrite (run_exc_vis_none_eq _ _ _ Hou1 Hex1), Eqit.bind_vis; reflexivity
            | symmetry; apply (run_exc_vis_none_eq _ _ _ Hou2 Hex2) |].
          apply GIS_Step; cbn [gis_step_body observe]; right; left.
          split; [exact Hsync | split; [exact HE |]].
          intros y1 y2 Hy Hp.
          destruct (HA y1 y2 Hy Hp) as (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
          exists (ITree.bind (run_exc (ITree.bind m1 k1)) K1),
                 (run_exc (ITree.bind m2 k2)).
          split.
          -- eapply ITS_Eq; [apply Eqit.bind_tau |].
             apply ITS_Tau, itree_tau_star_bind, itree_tau_star_run_exc, itree_tau_star_bind, Hs1.
          -- split.
             ++ apply ITS_Tau, itree_tau_star_run_exc, itree_tau_star_bind, Hs2.
             ++ apply (Hr_wrap _ m1 m2 Hic Hm).
    - assert (Hou1 : observe (ITree.bind a1 k1) = TauF (ITree.bind ma1 k1)).
      { rewrite observe_bind, Ha1; reflexivity. }
      eapply gen_inline_sim__obs_eq;
        [symmetry; rewrite (run_exc_tau_eq _ _ Hou1), Eqit.bind_tau; reflexivity
        | reflexivity |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - assert (Hou2 : observe (ITree.bind a2 k2) = TauF (ITree.bind ma2 k2)).
      { rewrite observe_bind, Ha2; reflexivity. }
      eapply gen_inline_sim__obs_eq;
        [reflexivity | symmetry; apply (run_exc_tau_eq _ _ Hou2) |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic].
    - assert (Eb1 : ITree.bind a1 k1 ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalRead x)))
                      (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : ITree.bind (run_exc (ITree.bind a1 k1)) K1 ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalRead x)))
                      (fun y => Tau (ITree.bind (run_exc (ITree.bind (fa1 y) k1)) K1))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite run_exc_bind_trigger_none_eq by reflexivity; rewrite Eqit.bind_bind.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        rewrite Eqit.bind_tau; reflexivity. }
      eapply GIS_ReadL; [exact He1 | exact El1 | exact Hlk |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - assert (Eb2 : ITree.bind a2 k2 ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalRead x)))
                      (fun y => ITree.bind (fa2 y) k2)).
      { rewrite Ha2, Eqit.bind_bind; reflexivity. }
      assert (Er2 : run_exc (ITree.bind a2 k2) ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalRead x)))
                      (fun y => Tau (run_exc (ITree.bind (fa2 y) k2)))).
      { rewrite (run_exc_proper _ _ Eb2).
        rewrite run_exc_bind_trigger_none_eq by reflexivity; reflexivity. }
      eapply GIS_ReadR; [exact He2 | exact Er2 | exact Hlk |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic].
    - assert (Hic' : is_ic_inlined ic' = true).
      { destruct ic; try discriminate Hic; cbn in Hw1; injection Hw1 as <-; reflexivity. }
      assert (Eb1 : ITree.bind a1 k1 ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalWrite x v)))
                      (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : ITree.bind (run_exc (ITree.bind a1 k1)) K1 ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalWrite x v)))
                      (fun y => Tau (ITree.bind (run_exc (ITree.bind (fa1 y) k1)) K1))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite run_exc_bind_trigger_none_eq by reflexivity; rewrite Eqit.bind_bind.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        rewrite Eqit.bind_tau; reflexivity. }
      eapply GIS_WriteL; [exact Hw1 | exact El1 |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic'].
    - assert (Hic' : is_ic_inlined ic' = true).
      { destruct ic; try discriminate Hic; cbn in Hw2; injection Hw2 as <-; reflexivity. }
      assert (Eb2 : ITree.bind a2 k2 ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalWrite x v)))
                      (fun y => ITree.bind (fa2 y) k2)).
      { rewrite Ha2, Eqit.bind_bind; reflexivity. }
      assert (Er2 : run_exc (ITree.bind a2 k2) ≅
                    ITree.bind (ITree.trigger (subevent _ (LocalWrite x v)))
                      (fun y => Tau (run_exc (ITree.bind (fa2 y) k2)))).
      { rewrite (run_exc_proper _ _ Eb2).
        rewrite run_exc_bind_trigger_none_eq by reflexivity; reflexivity. }
      eapply GIS_WriteR; [exact Hw2 | exact Er2 |].
      eapply GIS_TauR; [reflexivity | apply IH, Hic'].
    - assert (Eb1 : ITree.bind a1 k1 ≅
                    ITree.bind (ITree.trigger (subevent _ (GlobalRead k)))
                      (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : ITree.bind (run_exc (ITree.bind a1 k1)) K1 ≅
                    ITree.bind (ITree.trigger (subevent _ (GlobalRead k)))
                      (fun y => Tau (ITree.bind (run_exc (ITree.bind (fa1 y) k1)) K1))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite run_exc_bind_trigger_none_eq by reflexivity; rewrite Eqit.bind_bind.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        rewrite Eqit.bind_tau; reflexivity. }
      eapply GIS_GReadL; [exact El1 | exact Hlk |].
      eapply GIS_TauL; [reflexivity | apply IH, Hic].
    - set (ze := Store (DTYPE_Struct true []) (DVALUE_Base (DVALUE_Pointer varg)) (DVALUE_Struct true [])).
      assert (Eb1 : ITree.bind a1 k1 ≅ ITree.bind (ITree.trigger (subevent _ ze)) (fun y => ITree.bind (fa1 y) k1)).
      { rewrite Ha1, Eqit.bind_bind; reflexivity. }
      assert (El1 : ITree.bind (run_exc (ITree.bind a1 k1)) K1 ≅
                    ITree.bind (ITree.trigger (subevent _ ze))
                      (fun y => Tau (ITree.bind (run_exc (ITree.bind (fa1 y) k1)) K1))).
      { rewrite (run_exc_proper _ _ Eb1).
        rewrite run_exc_bind_trigger_none_eq by reflexivity; rewrite Eqit.bind_bind.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
        rewrite Eqit.bind_tau; reflexivity. }
      eapply GIS_ZeroStoreL; [exact El1 |].
      eapply GIS_TauL; [reflexivity | apply IH, Logic.eq_refl].
  Qed.

End InliningSemantics.
