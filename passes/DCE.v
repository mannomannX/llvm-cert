(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Dead Code & Dead Phi Elimination ([CertPasses.DCE])

    Purpose:
      Re-exports [CertPasses.DCESpec] and [CertPasses.DCESafety], proves lockstep
      [cfg_local_sim] simulation for expressions, instructions, [denote_phis],
      and terminators, and establishes whole-program refinement
      ([dce_mcfg_refines]) for the 3-round [dce_mcfg] pass.

    Trust Contract & Fail-Closed Boundary:
      Extracted to OCaml ([Extract.v]: [dce_mcfg], [dce_mcfg_typ]). Each round
      invokes [dce_cfg_once], which fails closed to the identity CFG [c] unless
      [cfg_no_block_addresses], [nodup_raw_ids], [check_fwd_cfg], and
      [check_live_cfg] all succeed.

    Assumptions:
      Depends on Stdlib, Paco, ITree, ExtLib, Vellvm, [CertPasses.PassCommon],
      [CertPasses.DCESpec], and [CertPasses.DCESafety]; zero custom axioms
      (arbitrary [IPtr] / [IPtrTheory]).

    Section Outline:
      Lockstep [cfg_local_sim] combinators; (7) Expression safety & simulation;
      (8) Instruction, code, phi, terminator, & [dce_cfg_once_sim];
      (9) [dce_mcfg], [dce_mcfg_typ], & [dce_mcfg_refines]. *)

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
  Basics.HeterogeneousRelations.

From ExtLib Require Import
  Structures.Maps
  Structures.Monads.

From Vellvm Require Import
  Numeric
  Utils
  Syntax
  Semantics
  Semantics.VellvmIntegers
  Semantics.VellvmFloats
  ScopeTheory
  Utils.rutt_cutoff
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
Import Logic.
From CertPasses Require Export DCESpec DCESafety.

Set Default Goal Selector "!".
Unset Implicit Arguments.

Section DCESoundness.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Notation PaV := (@ParamsV IP IPT).
  #[local] Hint Resolve cfg_local_sim__mon : paco.

  (** ** Lockstep [cfg_local_sim] Combinators *)

  Lemma cfg_local_sim_trigger_post {R : Type}
    (P : R -> Prop)
    (env1 env2 : @local_env PaV)
    (e : @CFGEtop PaV R)
    (Hsync : sync_non_local_cfg e = true)
    (Hpost : forall a : R, cfg_event_post e a -> P a) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2 /\ P r1)
      env1 env2 (ITree.trigger e) (ITree.trigger e).
  Proof.
    pstep; apply CLS_Step; unfold cls_step_body, ITree.trigger; cbn [observe].
    right; left; split; [exact Hsync | split; [apply EqE_CFG_refl |]].
    intros a1 a2 Ha Hp; apply EqA_CFG_eq in Ha; subst a2.
    left; apply cfg_local_sim_ret.
    split; [reflexivity | split; [reflexivity | split; [reflexivity | apply Hpost, Hp]]].
  Qed.

  Lemma cfg_local_sim_raise_sync {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV) (msg : string) :
    cfg_local_sim RR env1 env2 (raise msg) (raise msg).
  Proof.
    unfold raise, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn.
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
  Qed.

  Lemma cfg_local_sim_withCall_raise_sync {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV) (msg : string) :
    cfg_local_sim RR env1 env2 (@withCall PaV R1 (raise msg)) (@withCall PaV R2 (raise msg)).
  Proof.
    unfold withCall, raise, trigger_cast, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body.
    repeat (rewrite observe_bind || rewrite observe_translate); cbn.
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
  Qed.

  Lemma cfg_local_sim_raiseUB_cut {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV) (msg : string) (t2 : @CFGtop PaV R2) :
    cfg_local_sim RR env1 env2 (raiseUB msg) t2.
  Proof.
    unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn.
    left; reflexivity.
  Qed.

  Lemma cfg_local_sim_raiseLLVM_sync {R1 R2 : Type}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV) (ex : @exc PaV) :
    cfg_local_sim RR env1 env2 (raiseLLVM ex) (raiseLLVM ex).
  Proof.
    unfold raiseLLVM, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn.
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
  Qed.

  Lemma cfg_local_sim_EOU_ret_sync {R : Type}
    (P : R -> Prop) (env1 env2 : @local_env PaV) (m : EOU R) :
    eou_ret_imp P m ->
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2 /\ P r1)
      env1 env2 (EOU_to_itree m) (EOU_to_itree m).
  Proof.
    intros Hm; destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - apply cfg_local_sim_raise_sync.
    - unfold raiseOOM, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn;
        right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
    - apply cfg_local_sim_raiseUB_cut.
    - apply cfg_local_sim_ret; split; [reflexivity | split; [reflexivity | split; [reflexivity | exact Hm]]].
  Qed.

  Lemma cfg_local_sim_EOU_sync {R : Type}
    (env1 env2 : @local_env PaV) (m : EOU R) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (EOU_to_itree m) (EOU_to_itree m).
  Proof.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_EOU_ret_sync (fun _ => True) env1 env2 m); destruct m; exact I].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_withCall_EOU_ret_sync {R : Type}
    (P : R -> Prop) (env1 env2 : @local_env PaV) (m : EOU R) :
    eou_ret_imp P m ->
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2 /\ P r1)
      env1 env2 (@withCall PaV R (EOU_to_itree m)) (@withCall PaV R (EOU_to_itree m)).
  Proof.
    intros Hm; destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - apply cfg_local_sim_withCall_raise_sync.
    - unfold withCall, raiseOOM, trigger_cast, ITree.trigger; pstep; apply CLS_Step;
        unfold cls_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn;
        right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
    - unfold withCall, raiseUB, trigger_cast, ITree.trigger; pstep; apply CLS_Step;
        unfold cls_step_body; repeat (rewrite observe_bind || rewrite observe_translate); cbn; left; reflexivity.
    - eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
      apply cfg_local_sim_ret; split; [reflexivity | split; [reflexivity | split; [reflexivity | exact Hm]]].
  Qed.

  Lemma cfg_local_sim_withCall_EOU_sync {R : Type}
    (env1 env2 : @local_env PaV) (m : EOU R) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (@withCall PaV R (EOU_to_itree m)) (@withCall PaV R (EOU_to_itree m)).
  Proof.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_withCall_EOU_ret_sync (fun _ => True) env1 env2 m);
         destruct m; exact I].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_gread_sync
    (env1 env2 : @local_env PaV) (id : raw_id) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (gread id) (gread id).
  Proof.
    unfold gread.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_trigger_post (fun _ => True)); [reflexivity | intros; exact I]].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_withCall_gread_sync
    (env1 env2 : @local_env PaV) (id : raw_id) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (@withCall PaV (@dvalue PaV) (gread id))
                (@withCall PaV (@dvalue PaV) (gread id)).
  Proof.
    unfold withCall, gread, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body.
    rewrite !observe_translate; cbn.
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl |]].
    intros a1 a2 Ha _; apply EqA_CFG_eq in Ha; subst a2.
    left; eapply cfg_local_sim_obs_eq;
      [symmetry; apply translate_ret | symmetry; apply translate_ret |].
    apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_withCall_draw_sync
    (env1 env2 : @local_env PaV) (dt : dtyp) :
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         e1' = env1 /\ e2' = env2 /\ r1 = r2 /\
         (is_scalar_dtyp dt = true -> dvalue_has_dtyp r1 dt))
      env1 env2 (@withCall PaV (@dvalue PaV) (draw dt))
                (@withCall PaV (@dvalue PaV) (draw dt)).
  Proof.
    unfold withCall, draw, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body.
    rewrite !observe_translate; cbn [observe subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1].
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl |]].
    intros a1 a2 Ha Hp; apply EqA_CFG_eq in Ha; subst a2.
    left; eapply cfg_local_sim_obs_eq;
      [symmetry; apply translate_ret | symmetry; apply translate_ret |].
    apply cfg_local_sim_ret; split; [reflexivity | split; [reflexivity | split; [reflexivity | exact Hp]]].
  Qed.

  Lemma cfg_local_sim_withCall_conv_sync
    (env1 env2 : @local_env PaV)
    (ic : impure_conversion) (dt_from : dtyp) (dv : @dvalue PaV) (dt_to : dtyp) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (@withCall PaV (@dvalue PaV) (conv ic dt_from dv dt_to))
                (@withCall PaV (@dvalue PaV) (conv ic dt_from dv dt_to)).
  Proof.
    unfold withCall, conv, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body.
    rewrite !observe_translate; cbn.
    right; left; split; [reflexivity | split; [apply EqE_CFG_refl |]].
    intros a1 a2 Ha _; apply EqA_CFG_eq in Ha; subst a2.
    left; eapply cfg_local_sim_obs_eq;
      [symmetry; apply translate_ret | symmetry; apply translate_ret |].
    apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma withCall_fmap_ret {A B : Type} (f : A -> B) (x : A) :
    @withCall PaV B (f <$> ret x) ≅ Ret (f x).
  Proof.
    change (ret x) with (Ret x : @MCFGtop PaV A).
    unfold withCall; pstep; red; rewrite !observe_translate;
      unfold Functor.fmap, Functor_itree, ITree.map;
      rewrite ?observe_bind; cbn; constructor; reflexivity.
  Qed.

  Lemma cfg_local_sim_withCall_freeze
    (dv : @dvalue PaV) :
    forall (dt : dtyp) (env1 env2 : @local_env PaV),
      cfg_local_sim
        (fun e1' e2' r1 r2 =>
           e1' = env1 /\ e2' = env2 /\ r1 = r2 /\
           (is_scalar_dtyp dt = true -> dvalue_has_dtyp dv dt -> dvalue_has_dtyp r1 dt))
        env1 env2 (@withCall PaV (@dvalue PaV) (freeze dt dv))
                  (@withCall PaV (@dvalue PaV) (freeze dt dv)).
  Proof.
    induction dv as [db | p fs IHfs | v es IHes] using dvalue_ind_nested;
      intros dt env1 env2.
    - (* DVALUE_Base *)
      cbn [freeze].
      destruct db as [pt | sz i | ip | d | f | | | bsz bv]; cbn [freeze_base].
      + eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_fmap_ret
          | symmetry; apply withCall_fmap_ret |].
        apply cfg_local_sim_ret; repeat split; auto.
      + eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_fmap_ret
          | symmetry; apply withCall_fmap_ret |].
        apply cfg_local_sim_ret; repeat split; auto.
      + eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_fmap_ret
          | symmetry; apply withCall_fmap_ret |].
        apply cfg_local_sim_ret; repeat split; auto.
      + eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_fmap_ret
          | symmetry; apply withCall_fmap_ret |].
        apply cfg_local_sim_ret; repeat split; auto.
      + eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_fmap_ret
          | symmetry; apply withCall_fmap_ret |].
        apply cfg_local_sim_ret; repeat split; auto.
      + (* DVALUE_Poison -> draw dt *)
        eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_draw_sync].
        intros ? ? ? ? (-> & -> & <- & Hdr).
        split; [reflexivity | split; [reflexivity | split; [reflexivity | intros Hsc _; apply Hdr, Hsc]]].
      + eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_fmap_ret
          | symmetry; apply withCall_fmap_ret |].
        apply cfg_local_sim_ret; repeat split; auto.
      + (* DVALUE_B: impossible when dt is scalar *)
        assert (Hnot_sc : forall Hsc : is_scalar_dtyp dt = true,
                  dvalue_has_dtyp (DVALUE_Base (@DVALUE_B PaV bsz bv)) dt -> False).
        { intros Hsc Hty.
          destruct (dvalue_has_dtyp_scalar_base_inv _ dt Hsc Hty) as [db' [Heq Hcases]].
          inversion Heq; subst db'.
          destruct Hcases as [Hc | Hnb]; [discriminate Hc | exact (Hnb bsz bv Logic.eq_refl)]. }
        destruct bv as [bp bidx | bi | bits]; cbn [freeze_base].
        * eapply cfg_local_sim_obs_eq;
            [symmetry; apply withCall_fmap_ret
            | symmetry; apply withCall_fmap_ret |].
          apply cfg_local_sim_ret; repeat split; auto.
        * eapply cfg_local_sim_obs_eq;
            [symmetry; apply withCall_fmap_ret
            | symmetry; apply withCall_fmap_ret |].
          apply cfg_local_sim_ret; repeat split; auto.
        * destruct (existsb is_poison_bit bits).
          -- eapply cfg_local_sim_obs_eq;
               [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
             eapply cfg_local_sim_bind; [apply cfg_local_sim_withCall_draw_sync |].
             intros ? ? x _ (-> & -> & <- & _).
             eapply cfg_local_sim_obs_eq;
               [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
             apply cfg_local_sim_ret; split;
               [reflexivity | split; [reflexivity | split; [reflexivity | intros Hsc Hty; exfalso; exact (Hnot_sc Hsc Hty)]]].
          -- eapply cfg_local_sim_obs_eq;
               [symmetry; apply withCall_fmap_ret
               | symmetry; apply withCall_fmap_ret |].
             apply cfg_local_sim_ret; repeat split; auto.
    - (* DVALUE_Struct *)
      destruct dt as [| p' dts |];
        [cbn [freeze]; apply cfg_local_sim_withCall_raise_sync | | cbn [freeze]; apply cfg_local_sim_withCall_raise_sync].
      cbn [freeze].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind with
        (RR := fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2).
      + lazymatch goal with
        | |- cfg_local_sim ?R ?e1 ?e2 (withCall (?go fs dts [])) (withCall (?go fs dts [])) =>
            cut (forall acc : list (@dvalue PaV),
                    cfg_local_sim R e1 e2 (withCall (go fs dts acc)) (withCall (go fs dts acc)));
              [intros Hcut; exact (Hcut []) |]
        end.
        revert dts env1 env2;
          induction IHfs as [| fv fvs Hfv _ IH];
          intros [| t ts] env1 env2 acc;
          lazymatch goal with
          | |- cfg_local_sim _ _ _ (withCall (raise _)) (withCall (raise _)) =>
              apply cfg_local_sim_withCall_raise_sync
          | _ => idtac
          end.
        * eapply cfg_local_sim_obs_eq;
            [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
          apply cfg_local_sim_ret; repeat split; reflexivity.
        * eapply cfg_local_sim_obs_eq;
            [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
          eapply cfg_local_sim_bind; [apply (Hfv t env1 env2) |].
          intros ? ? v' _ (-> & -> & <- & _); apply IH.
      + intros ? ? val _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
        apply cfg_local_sim_ret; split;
          [reflexivity | split; [reflexivity | split; [reflexivity | intros Hsc; discriminate Hsc]]].
    - (* DVALUE_Array *)
      destruct dt as [| | v' sz t];
        [cbn [freeze]; apply cfg_local_sim_withCall_raise_sync
        | cbn [freeze]; apply cfg_local_sim_withCall_raise_sync |].
      cbn [freeze].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind with
        (RR := fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2).
      + lazymatch goal with
        | |- cfg_local_sim ?R ?e1 ?e2 (withCall (?go es [])) (withCall (?go es [])) =>
            cut (forall acc : list (@dvalue PaV),
                    cfg_local_sim R e1 e2 (withCall (go es acc)) (withCall (go es acc)));
              [intros Hcut; exact (Hcut []) |]
        end.
        revert env1 env2;
          induction IHes as [| ev evs Hev _ IH];
          intros env1 env2 acc.
        * eapply cfg_local_sim_obs_eq;
            [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
          apply cfg_local_sim_ret; repeat split; reflexivity.
        * eapply cfg_local_sim_obs_eq;
            [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
          eapply cfg_local_sim_bind; [apply (Hev t env1 env2) |].
          intros ? ? v'' _ (-> & -> & <- & _); apply IH.
      + intros ? ? val _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
        apply cfg_local_sim_ret; split;
          [reflexivity | split; [reflexivity | split; [reflexivity | intros Hsc; discriminate Hsc]]].
  Qed.

  Lemma cfg_local_sim_withCall_lread_sync
    (env1 env2 : @local_env PaV) (x : local_id) :
    Maps.lookup x env1 = Maps.lookup x env2 ->
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         e1' = env1 /\ e2' = env2 /\ r1 = r2 /\ Maps.lookup x env1 = Some r1)
      env1 env2 (@withCall PaV (@dvalue PaV) (lread x))
                (@withCall PaV (@dvalue PaV) (lread x)).
  Proof.
    intros Hlk.
    unfold withCall, lread, ITree.trigger.
    pstep; apply CLS_Step; unfold cls_step_body.
    rewrite !observe_translate;
      cbn [observe subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1].
    right; right.
    split; [reflexivity | split; [exact Hlk |]].
    intros v Hv; left.
    eapply cfg_local_sim_obs_eq;
      [symmetry; apply translate_ret | symmetry; apply translate_ret |].
    apply cfg_local_sim_ret; split; [reflexivity | split; [reflexivity | split; [reflexivity | exact Hv]]].
  Qed.

  Lemma cfg_local_sim_lwrite_both
    (env1 env2 : @local_env PaV) (id : local_id) (v : @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         e1' = Maps.add id v env1 /\ e2' = Maps.add id v env2 /\ r1 = r2)
      env1 env2 (lwrite id v) (lwrite id v).
  Proof.
    pstep; eapply CLS_WriteL; [symmetry; apply Eqit.bind_ret_r |].
    eapply CLS_WriteR; [symmetry; apply Eqit.bind_ret_r |].
    apply CLS_Step; cbn; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_assert_dereferenceable_sync
    (env1 env2 : @local_env PaV)
    (or_null : bool) (n : N) (v : @dvalue PaV) (msg : string) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (assert_dereferenceable or_null n v msg)
                (assert_dereferenceable or_null n v msg).
  Proof.
    unfold assert_dereferenceable.
    destruct v as [db | |];
      [| apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync].
    destruct db as [p | | | | | | |];
      [| apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync
       | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync
       | apply cfg_local_sim_raiseUB_cut
       | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync].
    destruct (_ || _).
    - apply cfg_local_sim_ret; repeat split; reflexivity.
    - eapply cfg_local_sim_bind with
        (RR := fun e1' e2' (r1 r2 : @dvalue PaV) =>
                 e1' = env1 /\ e2' = env2 /\ r1 = r2 /\ True).
      + unfold load; apply (cfg_local_sim_trigger_post (fun _ => True) env1 env2);
          [reflexivity | intros; exact I].
      + intros ? ? _ _ (-> & -> & _ & _); apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_apply_attrs_sync
    (env1 env2 : @local_env PaV)
    (attrs : list param_attr) (msg : string) (v : @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (apply_attrs attrs msg v) (apply_attrs attrs msg v).
  Proof.
    unfold apply_attrs.
    eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
    intros ? ? v' _ (-> & -> & <-).
    eapply cfg_local_sim_bind with
      (RR := fun e1' e2' (r1 r2 : unit) => e1' = env1 /\ e2' = env2 /\ r1 = r2).
    - unfold assert_attrs_dereferenceable.
      destruct (find_option attr_dereferenceable attrs) as [[or_null n] |];
        [| apply cfg_local_sim_ret; repeat split; reflexivity].
      destruct v' as [db | |];
        [| apply cfg_local_sim_ret; repeat split; reflexivity
         | apply cfg_local_sim_ret; repeat split; reflexivity].
      destruct db;
        [ apply cfg_local_sim_assert_dereferenceable_sync
        | apply cfg_local_sim_ret; repeat split; reflexivity
        | apply cfg_local_sim_ret; repeat split; reflexivity
        | apply cfg_local_sim_ret; repeat split; reflexivity
        | apply cfg_local_sim_ret; repeat split; reflexivity
        | apply cfg_local_sim_ret; repeat split; reflexivity
        | apply cfg_local_sim_ret; repeat split; reflexivity
        | apply cfg_local_sim_ret; repeat split; reflexivity ].
    - intros ? ? _ _ (-> & -> & _); apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_check_call_return_sync
    (env1 env2 : @local_env PaV)
    (fattrs : list fn_attr) (rattrs : list param_attr)
    (ranges : option (list (int_syntax * int_syntax))) (loc : string)
    (args : list (@dvalue PaV)) (res : @exc PaV + @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (check_call_return fattrs rattrs ranges loc args res)
                (check_call_return fattrs rattrs ranges loc args res).
  Proof.
    unfold check_call_return.
    eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
    intros ? ? _ _ (-> & -> & _).
    destruct res as [ex | v].
    - apply cfg_local_sim_ret; repeat split; reflexivity.
    - eapply cfg_local_sim_bind; [apply cfg_local_sim_apply_attrs_sync |].
      intros ? ? v' _ (-> & -> & <-); apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_assume_check_sync
    (env1 env2 : @local_env PaV)
    (f : exp dtyp) (tag loc : string) (vs : list (@dvalue PaV))
    (chk : @assume_bundle_check PaV (@CFGEtop PaV)) :
    bundle_check f tag = Some chk ->
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (chk loc vs) (chk loc vs).
  Proof.
    unfold bundle_check; intros Hb.
    destruct (is_llvm_assume f); [| discriminate Hb].
    cbn [assume_bundle_checks List.find] in Hb.
    repeat match goal with
           | H : context [if String.eqb ?a ?b then _ else _] |- _ =>
               destruct (String.eqb a b)
           end;
      cbn [option_map snd] in Hb; try discriminate Hb;
      inversion Hb; subst chk; clear Hb.
    - (* assume_nonnull *)
      unfold assume_nonnull, assume_violated, assume_malformed.
      destruct vs as [| p [| ? ?]];
        [apply cfg_local_sim_raise_sync | | apply cfg_local_sim_raise_sync].
      destruct (dvalue_ptr_address p) as [a |]; [| apply cfg_local_sim_raiseUB_cut].
      destruct (a =? 0)%Z;
        [apply cfg_local_sim_raiseUB_cut | apply cfg_local_sim_ret; repeat split; reflexivity].
    - (* assume_noundef *)
      unfold assume_noundef, assume_violated, assume_malformed.
      destruct vs as [| v [| ? ?]];
        [apply cfg_local_sim_raise_sync | | apply cfg_local_sim_raise_sync].
      destruct (dvalue_well_defined v);
        [apply cfg_local_sim_ret; repeat split; reflexivity | apply cfg_local_sim_raiseUB_cut].
    - (* assume_align *)
      unfold assume_align, assume_violated, assume_malformed.
      destruct vs as [| p [| al off]];
        [apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync |].
      cbv zeta.
      destruct (dvalue_ptr_address p) as [a |]; [| apply cfg_local_sim_raiseUB_cut].
      destruct (bundle_uint al) as [n |]; [| apply cfg_local_sim_raiseUB_cut].
      destruct (match off with [] => Some 0%Z | [o] => bundle_sint o | _ => None end) as [o |];
        [| apply cfg_local_sim_raiseUB_cut].
      destruct (if is_power_of_two n then ((a - o) mod n =? 0)%Z else (a =? 0)%Z);
        [apply cfg_local_sim_ret; repeat split; reflexivity | apply cfg_local_sim_raiseUB_cut].
    - (* assume_dereferenceable false *)
      unfold assume_dereferenceable, assume_violated, assume_malformed.
      destruct vs as [| p [| sz [| ? ?]]];
        [apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync
         | | apply cfg_local_sim_raise_sync].
      destruct (dvalue_ptr_address p), (bundle_uint sz);
        [| apply cfg_local_sim_raiseUB_cut | apply cfg_local_sim_raiseUB_cut
         | apply cfg_local_sim_raiseUB_cut].
      destruct (_ =? 0)%Z;
        [apply cfg_local_sim_ret; repeat split; reflexivity
        | apply cfg_local_sim_assert_dereferenceable_sync].
    - (* assume_dereferenceable true *)
      unfold assume_dereferenceable, assume_violated, assume_malformed.
      destruct vs as [| p [| sz [| ? ?]]];
        [apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync
         | | apply cfg_local_sim_raise_sync].
      destruct (dvalue_ptr_address p), (bundle_uint sz);
        [| apply cfg_local_sim_raiseUB_cut | apply cfg_local_sim_raiseUB_cut
         | apply cfg_local_sim_raiseUB_cut].
      destruct (_ =? 0)%Z;
        [apply cfg_local_sim_ret; repeat split; reflexivity
        | apply cfg_local_sim_assert_dereferenceable_sync].
  Qed.

  (** * 7. Expression Safety & Lockstep Expression Simulation *)

  Lemma val_matches_oty_normalize (oty : ty_info) (v : @dvalue PaV) :
    val_matches_oty oty v ->
    val_matches_oty (normalize_oty oty) v.
  Proof.
    destruct oty as [dt |]; [| exact id].
    cbn [val_matches_oty normalize_oty].
    intros [Hsc Hv]; rewrite Hsc; cbn [val_matches_oty]; exact (conj Hsc Hv).
  Qed.

  Lemma nonpoison_int_lit_sound
    (dt : dtyp) (e : exp dtyp) (env1 : @local_env PaV) :
    is_nonpoison_int_lit dt e = true ->
    left_evals_to
      (fun v => dvalue_has_dtyp v dt /\ v <> DVALUE_Base DVALUE_Poison)
      env1 (denote_exp' (Some dt) e).
  Proof.
    intros Hlit; destruct e; try discriminate Hlit; cbn [is_nonpoison_int_lit] in Hlit.
    - (* EXP_Integer *)
      destruct (denote_int_syntax_as_int_safe dt x Hlit) as (sz & i & -> & Hden).
      unfold denote_exp'; cbn [denote_exp]; rewrite Hden.
      apply left_evals_to_withCall_EOU; cbn;
        split; [apply dvalue_has_dtyp_I | intros Hc; discriminate Hc].
    - (* EXP_Bool *)
      rewrite (is_i1_dtyp_eq dt Hlit); unfold denote_exp'; cbn [denote_exp].
      destruct b; apply left_evals_to_withCall_ret;
        (split; [apply dvalue_has_dtyp_I | intros Hc; discriminate Hc]).
    - (* EXP_Zero_initializer *)
      assert (Hsc : is_scalar_dtyp dt = true).
      { destruct (is_int_dtyp_inv dt Hlit) as [sz ->]; reflexivity. }
      destruct (default_dvalue_scalar_safe dt Hsc) as (dv & Hdef & Hty & Hnp).
      unfold denote_exp'; cbn [denote_exp]; rewrite Hdef.
      apply left_evals_to_withCall_EOU; cbn;
        split; [exact Hty | apply Hnp, Hlit].
  Qed.

  Lemma check_scalar_texp_sound
    (te : ty_env) (e : exp dtyp) :
    forall (dt : dtyp) (env1 : @local_env PaV),
      check_scalar_texp te dt e = true ->
      tenv_sound te env1 ->
      left_evals_to (fun v => dvalue_has_dtyp v dt) env1 (denote_exp' (Some dt) e).
  Proof.
    induction e as
      [ id
      | x
      | f
      | b
      |
      |
      | elts IHelts
      |
      |
      | fields IHfields
      | fields IHfields
      | elts IHelts
      | elts IHelts
      | iop dt' e1 e2 IHe1 IHe2
      | samesign cmp dt' e1 e2 IHe1 IHe2
      | fop fm dt' e1 e2 IHe1 IHe2
      | flags dt' e1 IHe1
      | cmp fm dt' e1 e2 IHe1 IHe2
      | conv dt_from e1 dt_to IHe1
      | flags t dt_p ep idxs IHep IHidxs
      | dt_v ev dt_i ei IHev IHei
      | dt_v ev dt_e ee dt_i ei IHev IHee IHei
      | dt1 e1 dt2 e2 dtm em IHe1 IHe2 IHem
      | dt_s es idxs IHes
      | dt_s es dt_e ee idxs IHes IHee
      | fm dt_c ec dt1 e1 dt2 e2 IHec IHe1 IHe2
      | dt' e1 IHe1
      | se al idia uw tmpl cstr
      | dt' e1 IHe1
      | m Hm
      | dt' e1 IHe1
      | fn blk ] using exp_ind_nested;
      intros dt env1 Hchk Hte;
      try (cbn [check_scalar_texp] in Hchk; rewrite andb_false_r in Hchk; discriminate Hchk).
    - (* EXP_Ident *)
      cbn [check_scalar_texp] in Hchk; apply andb_true_iff in Hchk as [_ Hid].
      destruct id as [g | x]; [discriminate Hid |].
      destruct (lookup_ty x te) as [[dt' |] |] eqn:Elk; try discriminate Hid.
      apply dtyp_eqb_eq in Hid; subst dt'.
      destruct (Hte x (Some dt) Elk) as (v & Hlk & [_ Hv]).
      unfold denote_exp'; cbn [denote_exp lookup_id].
      eapply left_evals_to_withCall_lread; [exact Hlk | exact Hv].
    - (* EXP_Integer *)
      cbn [check_scalar_texp] in Hchk; apply andb_true_iff in Hchk as [_ Hint].
      destruct (denote_int_syntax_as_int_safe dt x Hint) as (sz & i & -> & Hden).
      unfold denote_exp'; cbn [denote_exp]; rewrite Hden.
      apply left_evals_to_withCall_EOU; cbn; apply dvalue_has_dtyp_I.
    - (* EXP_Float *)
      cbn [check_scalar_texp] in Hchk; apply andb_true_iff in Hchk as [_ Hfl].
      unfold denote_exp'; cbn [denote_exp].
      apply left_evals_to_withCall_EOU, denote_float_syntax_safe, Hfl.
    - (* EXP_Bool *)
      cbn [check_scalar_texp] in Hchk; apply andb_true_iff in Hchk as [_ Hi1].
      rewrite (is_i1_dtyp_eq dt Hi1); unfold denote_exp'; cbn [denote_exp].
      destruct b; apply left_evals_to_withCall_ret, dvalue_has_dtyp_I.
    - (* EXP_Null *)
      cbn [check_scalar_texp] in Hchk; apply andb_true_iff in Hchk as [_ Hptr].
      rewrite (is_ptr_dtyp_eq dt Hptr); unfold denote_exp'; cbn [denote_exp].
      apply left_evals_to_withCall_ret, dvalue_has_dtyp_Ptr.
    - (* EXP_Zero_initializer *)
      cbn [check_scalar_texp] in Hchk; apply andb_true_iff in Hchk as [Hsc _].
      destruct (default_dvalue_scalar_safe dt Hsc) as (dv & Hdef & Hty & _).
      unfold denote_exp'; cbn [denote_exp]; rewrite Hdef.
      apply left_evals_to_withCall_EOU; cbn; exact Hty.
    - (* EXP_Undef *)
      unfold denote_exp'; cbn [denote_exp].
      apply left_evals_to_withCall_ret, dvalue_has_dtyp_Poison.
    - (* EXP_Poison *)
      unfold denote_exp'; cbn [denote_exp].
      apply left_evals_to_withCall_ret, dvalue_has_dtyp_Poison.
    - (* OP_IBinop *)
      cbn [check_scalar_texp] in Hchk.
      apply andb_true_iff in Hchk as [_ Hchk].
      apply andb_true_iff in Hchk as [Hchk He2].
      apply andb_true_iff in Hchk as [Hchk He1].
      apply andb_true_iff in Hchk as [Heq Hsafe].
      apply dtyp_eqb_eq in Heq; subst dt'.
      unfold is_safe_ibinop_for in Hsafe; apply andb_true_iff in Hsafe as [Hint Hdiv].
      assert (He2' : left_evals_to
                       (fun v2 => dvalue_has_dtyp v2 dt /\
                                  match iop with
                                  | SDiv _ | SRem => v2 <> DVALUE_Base DVALUE_Poison
                                  | _ => True
                                  end)
                       env1 (denote_exp' (Some dt) e2)).
      { destruct iop;
          try (eapply left_evals_to_weaken; [| exact (IHe2 dt env1 He2 Hte)];
               intros ? H; exact (conj H I));
          apply nonpoison_int_lit_sound, Hdiv. }
      unfold denote_exp'; cbn [denote_exp].
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt env1 He1 Hte) | intros v1 Hv1].
      eapply left_evals_to_withCall_bind; [exact He2' | intros v2 [Hv2 Hnp]].
      apply left_evals_to_withCall_EOU, (eval_iop_safe iop dt v1 v2 Hint Hnp Hv1 Hv2).
    - (* OP_ICmp *)
      cbn [check_scalar_texp] in Hchk.
      apply andb_true_iff in Hchk as [_ Hchk].
      apply andb_true_iff in Hchk as [Hchk He2].
      apply andb_true_iff in Hchk as [Hchk He1].
      apply andb_true_iff in Hchk as [Hi1 Hsafe].
      rewrite (is_i1_dtyp_eq dt Hi1); unfold denote_exp'; cbn [denote_exp].
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt' env1 He1 Hte) | intros v1 Hv1].
      eapply left_evals_to_withCall_bind; [exact (IHe2 dt' env1 He2 Hte) | intros v2 Hv2].
      apply left_evals_to_withCall_EOU, (eval_icmp_safe samesign cmp dt' v1 v2 Hsafe Hv1 Hv2).
    - (* OP_FBinop *)
      cbn [check_scalar_texp] in Hchk.
      apply andb_true_iff in Hchk as [_ Hchk].
      apply andb_true_iff in Hchk as [Hchk He2].
      apply andb_true_iff in Hchk as [Hchk He1].
      apply andb_true_iff in Hchk as [Hchk Hsf].
      apply andb_true_iff in Hchk as [Hfp Heq].
      apply dtyp_eqb_eq in Heq; subst dt'; unfold denote_exp'; cbn [denote_exp].
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt env1 He1 Hte) | intros v1 Hv1].
      eapply left_evals_to_withCall_bind; [exact (IHe2 dt env1 He2 Hte) | intros v2 Hv2].
      apply left_evals_to_withCall_EOU, (eval_fop_safe fop dt v1 v2 Hfp Hsf Hv1 Hv2).
    - (* OP_Fneg *)
      cbn [check_scalar_texp] in Hchk.
      apply andb_true_iff in Hchk as [_ Hchk].
      apply andb_true_iff in Hchk as [Hchk He1].
      apply andb_true_iff in Hchk as [Hfp Heq].
      apply dtyp_eqb_eq in Heq; subst dt'; unfold denote_exp'; cbn [denote_exp].
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt env1 He1 Hte) | intros v1 Hv1].
      apply left_evals_to_withCall_EOU, (eval_fneg_safe dt v1 Hfp Hv1).
    - (* OP_FCmp *)
      cbn [check_scalar_texp] in Hchk.
      apply andb_true_iff in Hchk as [_ Hchk].
      apply andb_true_iff in Hchk as [Hchk He2].
      apply andb_true_iff in Hchk as [Hchk He1].
      apply andb_true_iff in Hchk as [Hi1 Hfp].
      rewrite (is_i1_dtyp_eq dt Hi1); unfold denote_exp'; cbn [denote_exp].
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt' env1 He1 Hte) | intros v1 Hv1].
      eapply left_evals_to_withCall_bind; [exact (IHe2 dt' env1 He2 Hte) | intros v2 Hv2].
      apply left_evals_to_withCall_EOU, (eval_fcmp_safe cmp dt' v1 v2 Hfp Hv1 Hv2).
    - (* OP_Conversion *)
      destruct conv as [| pc | ic].
      + (* CONV_Bitcast *)
        cbn [check_scalar_texp] in Hchk.
        apply andb_true_iff in Hchk as [_ Hchk].
        apply andb_true_iff in Hchk as [Hchk He1].
        apply andb_true_iff in Hchk as [Heq2 Heq12].
        apply dtyp_eqb_eq in Heq2; subst dt_to.
        unfold denote_exp'; cbn [denote_exp convert]; rewrite Heq12.
        apply dtyp_eqb_eq in Heq12; subst dt_from.
        eapply left_evals_to_withCall_bind; [exact (IHe1 dt env1 He1 Hte) | intros v1 Hv1].
        apply left_evals_to_withCall_ret, Hv1.
      + (* CONV_Pure *)
        cbn [check_scalar_texp] in Hchk.
        apply andb_true_iff in Hchk as [_ Hchk].
        apply andb_true_iff in Hchk as [Hchk He1].
        apply andb_true_iff in Hchk as [Heq2 Hsafe].
        apply dtyp_eqb_eq in Heq2; subst dt_to.
        unfold denote_exp'; cbn [denote_exp convert].
        eapply left_evals_to_withCall_bind; [exact (IHe1 dt_from env1 He1 Hte) | intros v1 Hv1].
        apply left_evals_to_withCall_EOU, (convert_pure_safe pc dt_from dt v1 Hsafe Hv1).
      + (* CONV_Impure *)
        cbn [check_scalar_texp] in Hchk; rewrite andb_false_r in Hchk; discriminate Hchk.
    - (* OP_Select *)
      cbn [check_scalar_texp] in Hchk.
      apply andb_true_iff in Hchk as [_ Hchk].
      apply andb_true_iff in Hchk as [Hchk He2].
      apply andb_true_iff in Hchk as [Hchk He1].
      apply andb_true_iff in Hchk as [Hchk Hec].
      apply andb_true_iff in Hchk as [Hchk Heq2].
      apply andb_true_iff in Hchk as [Hi1 Heq1].
      rewrite (is_i1_dtyp_eq dt_c Hi1) in Hec |- *.
      apply dtyp_eqb_eq in Heq1; subst dt1.
      apply dtyp_eqb_eq in Heq2; subst dt2.
      unfold denote_exp'; cbn [denote_exp].
      eapply left_evals_to_withCall_bind; [exact (IHec _ env1 Hec Hte) | intros vc Hvc].
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt env1 He1 Hte) | intros v1 Hv1].
      eapply left_evals_to_withCall_bind; [exact (IHe2 dt env1 He2 Hte) | intros v2 Hv2].
      apply left_evals_to_withCall_EOU,
        (eval_select_safe_P _ (dvalue_has_dtyp_Poison dt) vc v1 v2 dt Hvc Hv1 Hv2).
  Qed.

  Lemma check_any_texp_safe
    (te : ty_env) (e : exp dtyp) :
    forall (dt0 : dtyp) (env1 : @local_env PaV),
      check_any_texp te dt0 e = true ->
      tenv_sound te env1 ->
      left_evals_to (fun _ => True) env1 (denote_exp' (Some dt0) e).
  Proof.
    induction e as
      [ id
      | x
      | f
      | b
      |
      |
      | elts IHelts
      |
      |
      | fields IHfields
      | fields IHfields
      | elts IHelts
      | elts IHelts
      | iop dt' e1 e2 IHe1 IHe2
      | samesign cmp dt' e1 e2 IHe1 IHe2
      | fop fm dt' e1 e2 IHe1 IHe2
      | flags dt' e1 IHe1
      | cmp fm dt' e1 e2 IHe1 IHe2
      | conv dt_from e1 dt_to IHe1
      | flags t dt_p ep idxs IHep IHidxs
      | dt_v ev dt_i ei IHev IHei
      | dt_v ev dt_e ee dt_i ei IHev IHee IHei
      | dt1 e1 dt2 e2 dtm em IHe1 IHe2 IHem
      | dt_s es idxs IHes
      | dt_s es dt_e ee idxs IHes IHee
      | fm dt_c ec dt1 e1 dt2 e2 IHec IHe1 IHe2
      | dt' e1 IHe1
      | se al idia uw tmpl cstr
      | dt' e1 IHe1
      | m Hm
      | dt' e1 IHe1
      | fn blk ] using exp_ind_nested;
      intros dt0 env1 Hany Hte;
      cbn [check_any_texp] in Hany;
      lazymatch type of Hany with
      | check_scalar_texp _ _ _ = true =>
          eapply left_evals_to_weaken;
            [intros _ _; exact I | exact (check_scalar_texp_sound te _ dt0 env1 Hany Hte)]
      | _ => idtac
      end.
    - (* EXP_Ident *)
      destruct id as [g | x];
        [eapply left_evals_to_weaken;
           [intros _ _; exact I | exact (check_scalar_texp_sound te _ dt0 env1 Hany Hte)] |].
      destruct (lookup_ty x te) as [oty |] eqn:Elk; [| discriminate Hany].
      destruct (Hte x oty Elk) as (v & Hlk & _).
      unfold denote_exp'; cbn [denote_exp lookup_id].
      eapply left_evals_to_withCall_lread; [exact Hlk | exact I].
    - (* EXP_Integer *)
      destruct (denote_int_syntax_as_int_safe dt0 x Hany) as (sz & i & -> & Hden).
      unfold denote_exp'; cbn [denote_exp]; rewrite Hden.
      apply left_evals_to_withCall_EOU; exact I.
    - (* EXP_Float *)
      unfold denote_exp'; cbn [denote_exp].
      apply left_evals_to_withCall_EOU.
      eapply eou_safe_weaken; [| apply (denote_float_syntax_safe dt0 f Hany)].
      intros _ _; exact I.
    - (* EXP_Bool *)
      unfold denote_exp'; cbn [denote_exp]; destruct b; apply left_evals_to_withCall_ret, I.
    - (* EXP_Null *)
      unfold denote_exp'; cbn [denote_exp]; apply left_evals_to_withCall_ret, I.
    - (* EXP_Zero_initializer *)
      destruct (default_dvalue_scalar_safe dt0 Hany) as (dv & Hdef & _).
      unfold denote_exp'; cbn [denote_exp]; rewrite Hdef.
      apply left_evals_to_withCall_EOU; exact I.
    - (* EXP_Undef *)
      unfold denote_exp'; cbn [denote_exp]; apply left_evals_to_withCall_ret, I.
    - (* EXP_Poison *)
      unfold denote_exp'; cbn [denote_exp]; apply left_evals_to_withCall_ret, I.
    - (* OP_Conversion *)
      destruct conv as [| pc | ic];
        [| eapply left_evals_to_weaken;
             [intros _ _; exact I | exact (check_scalar_texp_sound te _ dt0 env1 Hany Hte)]
         | eapply left_evals_to_weaken;
             [intros _ _; exact I | exact (check_scalar_texp_sound te _ dt0 env1 Hany Hte)]].
      apply andb_true_iff in Hany as [Heq12 Hany1].
      unfold denote_exp'; cbn [denote_exp convert]; rewrite Heq12.
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt_from env1 Hany1 Hte) | intros v1 _].
      apply left_evals_to_withCall_ret, I.
    - (* OP_Select *)
      cbn [check_any_texp] in Hany.
      apply andb_true_iff in Hany as [Hany Hany2].
      apply andb_true_iff in Hany as [Hany Hany1].
      apply andb_true_iff in Hany as [Hi1 Hsc_c].
      rewrite (is_i1_dtyp_eq dt_c Hi1) in Hsc_c |- *.
      unfold denote_exp'; cbn [denote_exp].
      eapply left_evals_to_withCall_bind;
        [exact (check_scalar_texp_sound te ec _ env1 Hsc_c Hte) | intros vc Hvc].
      eapply left_evals_to_withCall_bind; [exact (IHe1 dt1 env1 Hany1 Hte) | intros v1 _].
      eapply left_evals_to_withCall_bind; [exact (IHe2 dt2 env1 Hany2 Hte) | intros v2 _].
      apply left_evals_to_withCall_EOU, (eval_select_safe_P _ I vc v1 v2 dt1 Hvc I I).
  Qed.

  Lemma check_any_texp_sound
    (te : ty_env) (e : exp dtyp) (dt : dtyp) (env1 : @local_env PaV) :
    check_any_texp te dt e = true ->
    tenv_sound te env1 ->
    left_evals_to
      (fun v => guarantees_scalar_dtyp te dt e = true -> dvalue_has_dtyp v dt)
      env1 (denote_exp' (Some dt) e).
  Proof.
    intros Hany Hte.
    destruct (guarantees_scalar_dtyp te dt e) eqn:Eguar.
    - pose proof (check_any_guarantees_scalar te e dt Hany Eguar) as Hsc.
      eapply left_evals_to_weaken; [| exact (check_scalar_texp_sound te e dt env1 Hsc Hte)].
      intros v Hv _; exact Hv.
    - eapply left_evals_to_weaken; [| exact (check_any_texp_safe te e dt env1 Hany Hte)].
      intros v _ Hc; discriminate Hc.
  Qed.

  Lemma op_cand_dtyp_denote_eq (op : exp dtyp) (dt : dtyp) :
    op_cand_dtyp op = Some dt ->
    @denote_exp' PaV None op = @denote_exp' PaV (Some dt) op.
  Proof.
    destruct op; intros H; try discriminate H; reflexivity.
  Qed.

  Lemma check_safe_op_sound
    (te : ty_env) (op : exp dtyp) (env1 : @local_env PaV) :
    check_safe_op te op = true ->
    tenv_sound te env1 ->
    left_evals_to
      (val_matches_oty (normalize_oty (infer_op_oty te op)))
      env1 (denote_exp' None op).
  Proof.
    intros Hchk Hte.
    assert (Hcand_branch :
      (match op with EXP_Ident (ID_Local _) => False | _ => True end) ->
      match op_cand_dtyp op with
      | Some dt => check_any_texp te dt op = true
      | None => False
      end ->
      left_evals_to
        (val_matches_oty (normalize_oty (infer_op_oty te op)))
        env1 (denote_exp' None op)).
    { intros Hnot_loc Hcand.
      destruct (op_cand_dtyp op) as [dt |] eqn:Ecand; [| contradiction].
      rewrite (op_cand_dtyp_denote_eq op dt Ecand).
      assert (Hinf : infer_op_oty te op =
                     if guarantees_scalar_dtyp te dt op then Some dt else None).
      { destruct op; try (destruct id; [| contradiction]);
          unfold infer_op_oty; rewrite Ecand; reflexivity. }
      rewrite Hinf.
      eapply left_evals_to_weaken; [| exact (check_any_texp_sound te op dt env1 Hcand Hte)].
      intros v Hv.
      destruct (guarantees_scalar_dtyp te dt op) eqn:Eguar.
      - apply val_matches_normalize_oty; intros _; apply Hv, Logic.eq_refl.
      - exact I. }
    destruct op as
      [ id | x | f | b | | | elts | | | fields | fields | elts | elts
      | iop dt1 e1 e2 | samesign cmp dt1 e1 e2 | fop fm dt1 e1 e2
      | flags [dt1 e1] | cmp fm dt1 e1 e2 | conv dt_from e1 dt_to
      | flags t [dt_p ep] idxs | p1 p2 | p1 p2 p3 | p1 p2 p3
      | p1 idxs | p1 p2 idxs | fm [dt_c ec] [dt1 e1] [dt2 e2]
      | [dt1 e1] | se al idia uw tmpl cstr | md | p1 | fn blk ];
      cbn [check_safe_op op_cand_dtyp] in Hchk;
      try discriminate Hchk;
      lazymatch goal with
      | |- context [infer_op_oty _ ?op0] =>
          let c := eval cbn [op_cand_dtyp] in (op_cand_dtyp op0) in
          lazymatch c with
          | Some _ => apply Hcand_branch; [exact I | cbn [op_cand_dtyp check_any_texp]; exact Hchk]
          | _ => idtac
          end
      end.
    - (* EXP_Ident *)
      destruct id as [g | x]; [discriminate Hchk |].
      cbn [infer_op_oty].
      destruct (lookup_ty x te) as [oty |] eqn:Elk; [| discriminate Hchk].
      destruct (Hte x oty Elk) as (v & Hlk & Hv).
      unfold denote_exp'; cbn [denote_exp lookup_id].
      eapply left_evals_to_withCall_lread; [exact Hlk | apply val_matches_oty_normalize, Hv].
    - (* EXP_Undef *)
      cbn [infer_op_oty op_cand_dtyp normalize_oty].
      unfold denote_exp'; cbn [denote_exp]; apply left_evals_to_withCall_ret, I.
    - (* EXP_Poison *)
      cbn [infer_op_oty op_cand_dtyp normalize_oty].
      unfold denote_exp'; cbn [denote_exp]; apply left_evals_to_withCall_ret, I.
    - (* OP_Conversion *)
      destruct conv as [| pc | ic].
      + apply Hcand_branch; [exact I | cbn [op_cand_dtyp check_any_texp]; exact Hchk].
      + apply Hcand_branch; [exact I | cbn [op_cand_dtyp check_any_texp]; exact Hchk].
      + discriminate Hchk.
  Qed.

  (** ** Lockstep Expression Denotation Simulation *)

  Lemma cfg_local_sim_withCall_map_monad {A B : Type}
    (f : A -> @MCFGtop PaV B)
    (uses : A -> list raw_id)
    (env1 env2 : @local_env PaV)
    (l : list A)
    (Hl : Forall
            (fun a =>
               env_agree_on (uses a) env1 env2 ->
               cfg_local_sim
                 (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
                 env1 env2 (@withCall PaV B (f a)) (@withCall PaV B (f a)))
            l)
    (Hagree : forall a, In a l -> env_agree_on (uses a) env1 env2) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2
      (@withCall PaV (list B) (map_monad f l))
      (@withCall PaV (list B) (map_monad f l)).
  Proof.
    induction Hl as [| a rest Ha _ IH]; cbn [map_monad].
    - eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
      apply cfg_local_sim_ret; repeat split; reflexivity.
    - eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [apply Ha, Hagree; left; reflexivity |].
      intros ? ? y _ (-> & -> & <-).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [apply IH; intros z Hz; apply Hagree; right; exact Hz |].
      intros ? ? ys _ (-> & -> & <-).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
      apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma env_agree_on_texp_list
    (elts : list (dtyp * exp dtyp)) (env1 env2 : @local_env PaV) :
    env_agree_on
      ((fix go (l : list (dtyp * exp dtyp)) : list raw_id :=
          match l with
          | [] => []
          | (_, ex) :: rest => full_exp_uses ex ++ go rest
          end) elts)
      env1 env2 ->
    forall p, In p elts -> env_agree_on (full_exp_uses (snd p)) env1 env2.
  Proof.
    induction elts as [| [dt ex] rest IH]; intros Hagree p Hin; [contradiction |].
    destruct Hin as [<- | Hin].
    - cbn [snd]; eapply env_agree_on_app_l; exact Hagree.
    - apply IH; [eapply env_agree_on_app_r; exact Hagree | exact Hin].
  Qed.

  Lemma cfg_local_sim_denote_exp_sync
    (te : ty_env) (env1 env2 : @local_env PaV) (e : exp dtyp) :
    tenv_sound te env1 ->
    env_agree_on (full_exp_uses e) env1 env2 ->
    forall top : option dtyp,
      cfg_local_sim
        (fun e1' e2' v1 v2 =>
           e1' = env1 /\ e2' = env2 /\ v1 = v2 /\
           match top with
           | Some dt => guarantees_scalar_dtyp te dt e = true -> dvalue_has_dtyp v1 dt
           | None => True
           end)
        env1 env2 (denote_exp' top e) (denote_exp' top e).
  Proof.
    intros Hte.
    induction e as
      [ id
      | x
      | f
      | b
      |
      |
      | elts IHelts
      |
      |
      | fields IHfields
      | fields IHfields
      | elts IHelts
      | elts IHelts
      | iop dt' e1 e2 IHe1 IHe2
      | samesign cmp dt' e1 e2 IHe1 IHe2
      | fop fm dt' e1 e2 IHe1 IHe2
      | flags dt' e1 IHe1
      | cmp fm dt' e1 e2 IHe1 IHe2
      | conv dt_from e1 dt_to IHe1
      | flags t dt_p ep idxs IHep IHidxs
      | dt_v ev dt_i ei IHev IHei
      | dt_v ev dt_e ee dt_i ei IHev IHee IHei
      | dt1 e1 dt2 e2 dtm em IHe1 IHe2 IHem
      | dt_s es idxs IHes
      | dt_s es dt_e ee idxs IHes IHee
      | fm dt_c ec dt1 e1 dt2 e2 IHec IHe1 IHe2
      | dt' e1 IHe1
      | se al idia uw tmpl cstr
      | dt' e1 IHe1
      | m Hm
      | dt' e1 IHe1
      | fn blk ] using exp_ind_nested;
      intros Hagree top.
    - (* EXP_Ident *)
      destruct id as [g | x]; unfold denote_exp'; cbn [denote_exp lookup_id].
      + eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_gread_sync].
        intros ? ? v _ (-> & -> & <-); repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
      + assert (Hlk : Maps.lookup x env1 = Maps.lookup x env2).
        { apply (env_agree_on_in [x] env1 env2 x Hagree); left; reflexivity. }
        eapply cfg_local_sim_weaken; [| apply (cfg_local_sim_withCall_lread_sync env1 env2 x Hlk)].
        intros ? ? v _ (-> & -> & <- & Hv).
        repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hid].
        destruct (lookup_ty x te) as [[dt' |] |] eqn:Elk; try discriminate Hid.
        apply dtyp_eqb_eq in Hid; subst dt'.
        destruct (Hte x (Some dt) Elk) as (v' & Hlk' & [_ Hv']).
        congruence.
    - (* EXP_Integer *)
      unfold denote_exp'; cbn [denote_exp].
      destruct top as [dt |]; [| apply cfg_local_sim_withCall_raise_sync].
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun v => is_int_dtyp dt = true -> dvalue_has_dtyp v dt))].
      + intros ? ? v _ (-> & -> & <- & Hv); repeat split; try reflexivity.
        cbn [guarantees_scalar_dtyp]; intros Hguar;
          apply andb_true_iff in Hguar as [_ Hint]; apply Hv, Hint.
      + destruct (denote_int_syntax_as_int dt x) as [| | | v] eqn:E; cbn; try exact I.
        intros Hint.
        destruct (denote_int_syntax_as_int_safe dt x Hint) as (sz & i & -> & Hden).
        rewrite Hden in E; inversion E; subst v; apply dvalue_has_dtyp_I.
    - (* EXP_Float *)
      unfold denote_exp'; cbn [denote_exp].
      destruct top as [dt |]; [| apply cfg_local_sim_withCall_raise_sync].
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun v => is_fp_dtyp dt = true -> dvalue_has_dtyp v dt))].
      + intros ? ? v _ (-> & -> & <- & Hv); repeat split; try reflexivity.
        cbn [guarantees_scalar_dtyp]; intros Hguar;
          apply andb_true_iff in Hguar as [_ Hfp]; apply Hv, Hfp.
      + destruct (denote_float_syntax_as_float dt f) as [| | | v] eqn:E; cbn; try exact I.
        intros Hfp; pose proof (denote_float_syntax_ret_imp dt f Hfp) as Hret.
        rewrite E in Hret; exact Hret.
    - (* EXP_Bool *)
      unfold denote_exp'; cbn [denote_exp].
      destruct b;
        (eapply cfg_local_sim_obs_eq;
         [symmetry; apply withCall_ret | symmetry; apply withCall_ret |];
         apply cfg_local_sim_ret; repeat split; try reflexivity;
         destruct top as [dt |]; [| exact I];
         cbn [guarantees_scalar_dtyp]; intros Hguar;
         apply andb_true_iff in Hguar as [_ Hi1];
         rewrite (is_i1_dtyp_eq dt Hi1); apply dvalue_has_dtyp_I).
    - (* EXP_Null *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
      apply cfg_local_sim_ret; repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; intros Hguar.
      apply andb_true_iff in Hguar as [_ Hptr].
      rewrite (is_ptr_dtyp_eq dt Hptr); apply dvalue_has_dtyp_Ptr.
    - (* EXP_Zero_initializer *)
      unfold denote_exp'; cbn [denote_exp].
      destruct top as [dt |]; [| apply cfg_local_sim_withCall_raise_sync].
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun v => is_scalar_dtyp dt = true -> dvalue_has_dtyp v dt))].
      + intros ? ? v _ (-> & -> & <- & Hv); repeat split; try reflexivity.
        cbn [guarantees_scalar_dtyp]; intros Hguar;
          apply andb_true_iff in Hguar as [Hsc _]; apply Hv, Hsc.
      + destruct (default_dvalue_of_dtyp dt) as [| | | v] eqn:E; cbn; try exact I.
        intros Hsc; eapply default_dvalue_scalar_typ; eassumption.
    - (* EXP_Cstring *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind.
      + eapply cfg_local_sim_withCall_map_monad with (uses := fun p => full_exp_uses (snd p)).
        * eapply Forall_impl; [| exact IHelts].
          intros [dt_i ex_i] H_i Hag_i; cbn [snd] in *.
          eapply cfg_local_sim_weaken; [| exact (H_i Hag_i (Some dt_i))].
          intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
        * apply env_agree_on_texp_list, Hagree.
      + intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* EXP_Undef *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
      apply cfg_local_sim_ret; repeat split; try reflexivity.
      destruct top as [dt |]; [intros _; apply dvalue_has_dtyp_Poison | exact I].
    - (* EXP_Poison *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
      apply cfg_local_sim_ret; repeat split; try reflexivity.
      destruct top as [dt |]; [intros _; apply dvalue_has_dtyp_Poison | exact I].
    - (* EXP_Struct *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind.
      + eapply cfg_local_sim_withCall_map_monad with (uses := fun p => full_exp_uses (snd p)).
        * eapply Forall_impl; [| exact IHfields].
          intros [dt_i ex_i] H_i Hag_i; cbn [snd] in *.
          eapply cfg_local_sim_weaken; [| exact (H_i Hag_i (Some dt_i))].
          intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
        * apply env_agree_on_texp_list, Hagree.
      + intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* EXP_Packed_struct *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [apply cfg_local_sim_withCall_EOU_sync |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind.
      + eapply cfg_local_sim_withCall_map_monad with (uses := fun p => full_exp_uses (snd p)).
        * eapply Forall_impl; [| exact IHfields].
          intros [dt_i ex_i] H_i Hag_i; cbn [snd] in *.
          eapply cfg_local_sim_weaken; [| exact (H_i Hag_i (Some dt_i))].
          intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
        * apply env_agree_on_texp_list, Hagree.
      + intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* EXP_Array *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind.
      + eapply cfg_local_sim_withCall_map_monad with (uses := fun p => full_exp_uses (snd p)).
        * eapply Forall_impl; [| exact IHelts].
          intros [dt_i ex_i] H_i Hag_i; cbn [snd] in *.
          eapply cfg_local_sim_weaken; [| exact (H_i Hag_i (Some dt_i))].
          intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
        * apply env_agree_on_texp_list, Hagree.
      + intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* EXP_Vector *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind.
      + eapply cfg_local_sim_withCall_map_monad with (uses := fun p => full_exp_uses (snd p)).
        * eapply Forall_impl; [| exact IHelts].
          intros [dt_i ex_i] H_i Hag_i; cbn [snd] in *.
          eapply cfg_local_sim_weaken; [| exact (H_i Hag_i (Some dt_i))].
          intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
        * apply env_agree_on_texp_list, Hagree.
      + intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
        apply cfg_local_sim_ret; repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* OP_IBinop *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag1.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag2.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hag1 (Some dt')) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe2 Hag2 (Some dt')) |].
      intros ? ? v2 _ (-> & -> & <- & Hv2).
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun r =>
                       match top with
                       | Some dt => guarantees_scalar_dtyp te dt (OP_IBinop iop dt' e1 e2) = true -> dvalue_has_dtyp r dt
                       | None => True
                       end))].
      + intros ? ? r _ (-> & -> & <- & Hr); repeat split; auto.
      + destruct (eval_iop iop v1 v2) as [| | | r] eqn:E; cbn; try exact I.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hguar].
        apply andb_true_iff in Hguar as [Hguar Hg2].
        apply andb_true_iff in Hguar as [Hguar Hg1].
        apply andb_true_iff in Hguar as [Hint Heq].
        apply dtyp_eqb_eq in Heq; subst dt'.
        pose proof (eval_iop_ret_imp iop dt v1 v2 Hint (Hv1 Hg1) (Hv2 Hg2)) as Hret.
        rewrite E in Hret; exact Hret.
    - (* OP_ICmp *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag1.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag2.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hag1 (Some dt')) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe2 Hag2 (Some dt')) |].
      intros ? ? v2 _ (-> & -> & <- & _).
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun r =>
                       match top with
                       | Some dt => guarantees_scalar_dtyp te dt (OP_ICmp samesign cmp dt' e1 e2) = true -> dvalue_has_dtyp r dt
                       | None => True
                       end))].
      + intros ? ? r _ (-> & -> & <- & Hr); repeat split; auto.
      + destruct (eval_icmp samesign cmp v1 v2) as [| | | r] eqn:E; cbn; try exact I.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hguar].
        apply andb_true_iff in Hguar as [Hguar Hg1].
        apply andb_true_iff in Hguar as [Hi1 Hty].
        rewrite (is_i1_dtyp_eq dt Hi1).
        pose proof (eval_icmp_ret_imp samesign cmp dt' v1 v2 Hty (Hv1 Hg1)) as Hret.
        rewrite E in Hret; exact Hret.
    - (* OP_FBinop *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag1.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag2.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hag1 (Some dt')) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe2 Hag2 (Some dt')) |].
      intros ? ? v2 _ (-> & -> & <- & _).
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun r =>
                       match top with
                       | Some dt => guarantees_scalar_dtyp te dt (OP_FBinop fop fm dt' e1 e2) = true -> dvalue_has_dtyp r dt
                       | None => True
                       end))].
      + intros ? ? r _ (-> & -> & <- & Hr); repeat split; auto.
      + destruct (eval_fop fop v1 v2) as [| | | r] eqn:E; cbn; try exact I.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hguar].
        apply andb_true_iff in Hguar as [Hguar Hg1].
        apply andb_true_iff in Hguar as [Hfp Heq].
        apply dtyp_eqb_eq in Heq; subst dt'.
        pose proof (eval_fop_ret_imp fop dt v1 v2 Hfp (Hv1 Hg1)) as Hret.
        rewrite E in Hret; exact Hret.
    - (* OP_Fneg *)
      cbn [full_exp_uses] in Hagree.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hagree (Some dt')) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun r =>
                       match top with
                       | Some dt => guarantees_scalar_dtyp te dt (OP_Fneg flags (dt', e1)) = true -> dvalue_has_dtyp r dt
                       | None => True
                       end))].
      + intros ? ? r _ (-> & -> & <- & Hr); repeat split; auto.
      + destruct (eval_fneg v1) as [| | | r] eqn:E; cbn; try exact I.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hguar].
        apply andb_true_iff in Hguar as [Hguar Hg1].
        apply andb_true_iff in Hguar as [Hfp Heq].
        apply dtyp_eqb_eq in Heq; subst dt'.
        pose proof (eou_safe_to_ret_imp _ _ (eval_fneg_safe dt v1 Hfp (Hv1 Hg1))) as Hret.
        rewrite E in Hret; exact Hret.
    - (* OP_FCmp *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag1.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag2.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hag1 (Some dt')) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe2 Hag2 (Some dt')) |].
      intros ? ? v2 _ (-> & -> & <- & _).
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun r =>
                       match top with
                       | Some dt => guarantees_scalar_dtyp te dt (OP_FCmp cmp fm dt' e1 e2) = true -> dvalue_has_dtyp r dt
                       | None => True
                       end))].
      + intros ? ? r _ (-> & -> & <- & Hr); repeat split; auto.
      + destruct (eval_fcmp cmp v1 v2) as [| | | r] eqn:E; cbn; try exact I.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hguar].
        apply andb_true_iff in Hguar as [Hguar Hg1].
        apply andb_true_iff in Hguar as [Hi1 Hfp].
        rewrite (is_i1_dtyp_eq dt Hi1).
        pose proof (eval_fcmp_ret_imp cmp dt' v1 v2 Hfp (Hv1 Hg1)) as Hret.
        rewrite E in Hret; exact Hret.
    - (* OP_Conversion *)
      cbn [full_exp_uses] in Hagree.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hagree (Some dt_from)) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      destruct conv as [| pc | ic]; cbn [convert].
      + (* CONV_Bitcast *)
        destruct (dtyp_eqb dt_from dt_to) eqn:Eeq12.
        * eapply cfg_local_sim_obs_eq;
            [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
          apply cfg_local_sim_ret; repeat split; try reflexivity.
          destruct top as [dt |]; [| exact I].
          cbn [guarantees_scalar_dtyp]; rewrite Eeq12; intros Hguar.
          apply andb_true_iff in Hguar as [_ Hguar].
          apply andb_true_iff in Hguar as [Heq2 Hg1].
          apply dtyp_eqb_eq in Heq2; subst dt_to.
          apply dtyp_eqb_eq in Eeq12; subst dt_from.
          apply Hv1, Hg1.
        * destruct (bit_sizeof_dtyp dt_from =? bit_sizeof_dtyp dt_to)%N;
            [| apply cfg_local_sim_withCall_raise_sync].
          eapply cfg_local_sim_weaken;
            [| apply (cfg_local_sim_withCall_EOU_ret_sync
                        (fun r => is_scalar_dtyp dt_to = true -> dvalue_has_dtyp r dt_to))].
          -- intros ? ? r _ (-> & -> & <- & Hr); repeat split; try reflexivity.
             destruct top as [dt |]; [| exact I].
             cbn [guarantees_scalar_dtyp]; rewrite Eeq12, andb_true_r; intros Hguar.
             apply andb_true_iff in Hguar as [Hsc Heq2].
             apply dtyp_eqb_eq in Heq2; subst dt_to; apply Hr, Hsc.
          -- destruct (dvalue_to_memory_bytes dt_from v1 None) as [| | | bytes]; cbn; try exact I.
             destruct (memory_bytes_to_dvalue bytes dt_to) as [| | | r] eqn:Erd; cbn; try exact I.
             intros Hsc; eapply memory_bytes_to_dvalue_scalar_typ; eassumption.
      + (* CONV_Pure *)
        eapply cfg_local_sim_weaken;
          [| apply (cfg_local_sim_withCall_EOU_ret_sync
                      (fun r => is_scalar_dtyp dt_to = true -> dvalue_has_dtyp r dt_to))].
        * intros ? ? r _ (-> & -> & <- & Hr); repeat split; try reflexivity.
          destruct top as [dt |]; [| exact I].
          cbn [guarantees_scalar_dtyp]; intros Hguar.
          apply andb_true_iff in Hguar as [Hsc Heq2].
          apply dtyp_eqb_eq in Heq2; subst dt_to; apply Hr, Hsc.
        * destruct (convert_pure pc dt_from v1 dt_to) as [| | | r] eqn:E; cbn; try exact I.
          intros Hsc; pose proof (convert_pure_ret_imp pc dt_from dt_to v1 Hsc) as Hret.
          rewrite E in Hret; exact Hret.
      + (* CONV_Impure *)
        eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_conv_sync].
        intros ? ? r _ (-> & -> & <-); repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* OP_GetElementPtr *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag_p.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag_i.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHep Hag_p (Some dt_p)) |].
      intros ? ? vptr _ (-> & -> & <- & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind.
      + eapply cfg_local_sim_withCall_map_monad with (uses := fun p => full_exp_uses (snd p)).
        * eapply Forall_impl; [| exact IHidxs].
          intros [dt_i ex_i] H_i Hag_k; cbn [snd] in *.
          eapply cfg_local_sim_weaken; [| exact (H_i Hag_k (Some dt_i))].
          intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
        * apply env_agree_on_texp_list, Hag_i.
      + intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_weaken;
          [| apply (cfg_local_sim_withCall_EOU_ret_sync
                      (fun r => dvalue_has_dtyp r (DTYPE_Base DTYPE_Pointer))
                      env1 env2 _ (eval_gep_ret_imp flags t vptr vs))].
        intros ? ? r _ (-> & -> & <- & Hr); repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hptr].
        rewrite (is_ptr_dtyp_eq dt Hptr); exact Hr.
    - (* OP_ExtractElement *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag_v.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag_i.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHev Hag_v (Some dt_v)) |].
      intros ? ? vec _ (-> & -> & <- & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHei Hag_i (Some dt_i)) |].
      intros ? ? idx _ (-> & -> & <- & _).
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_EOU_sync].
      intros ? ? r _ (-> & -> & <-); repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* OP_InsertElement *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag_v.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag_ei.
      pose proof (env_agree_on_app_l _ _ _ _ Hag_ei) as Hag_e.
      pose proof (env_agree_on_app_r _ _ _ _ Hag_ei) as Hag_i.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHev Hag_v (Some dt_v)) |].
      intros ? ? vec _ (-> & -> & <- & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind.
      + eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
        eapply cfg_local_sim_bind; [exact (IHee Hag_e (Some dt_e)) |].
        intros ? ? ve _ (-> & -> & <- & _); apply cfg_local_sim_withCall_EOU_sync.
      + intros ? ? elt _ (-> & -> & <-).
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
        eapply cfg_local_sim_bind; [exact (IHei Hag_i (Some dt_i)) |].
        intros ? ? idx _ (-> & -> & <- & _).
        eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_EOU_sync].
        intros ? ? r _ (-> & -> & <-); repeat split; try reflexivity.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* OP_ShuffleVector *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag1.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag2m.
      pose proof (env_agree_on_app_l _ _ _ _ Hag2m) as Hag2.
      pose proof (env_agree_on_app_r _ _ _ _ Hag2m) as Hagm.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hag1 (Some dt1)) |].
      intros ? ? v1 _ (-> & -> & <- & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe2 Hag2 (Some dt2)) |].
      intros ? ? v2 _ (-> & -> & <- & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHem Hagm (Some dtm)) |].
      intros ? ? vm _ (-> & -> & <- & _).
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_EOU_sync].
      intros ? ? r _ (-> & -> & <-); repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* OP_ExtractValue *)
      cbn [full_exp_uses] in Hagree.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHes Hagree (Some dt_s)) |].
      intros ? ? str _ (-> & -> & <- & _).
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_EOU_sync].
      intros ? ? r _ (-> & -> & <-); repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* OP_InsertValue *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag_s.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag_e.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHes Hag_s (Some dt_s)) |].
      intros ? ? str _ (-> & -> & <- & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHee Hag_e (Some dt_e)) |].
      intros ? ? elt _ (-> & -> & <- & _).
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_EOU_sync].
      intros ? ? r _ (-> & -> & <-); repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* OP_Select *)
      cbn [full_exp_uses] in Hagree.
      pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag_c.
      pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag12.
      pose proof (env_agree_on_app_l _ _ _ _ Hag12) as Hag1.
      pose proof (env_agree_on_app_r _ _ _ _ Hag12) as Hag2.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHec Hag_c (Some dt_c)) |].
      intros ? ? vc _ (-> & -> & <- & Hvc).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hag1 (Some dt1)) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe2 Hag2 (Some dt2)) |].
      intros ? ? v2 _ (-> & -> & <- & Hv2).
      eapply cfg_local_sim_weaken;
        [| apply (cfg_local_sim_withCall_EOU_ret_sync
                    (fun r =>
                       match top with
                       | Some dt => guarantees_scalar_dtyp te dt (OP_Select fm (dt_c, ec) (dt1, e1) (dt2, e2)) = true -> dvalue_has_dtyp r dt
                       | None => True
                       end))].
      + intros ? ? r _ (-> & -> & <- & Hr); repeat split; auto.
      + destruct (eval_select vc dt1 v1 v2) as [| | | r] eqn:E; cbn; try exact I.
        destruct top as [dt |]; [| exact I].
        cbn [guarantees_scalar_dtyp]; intros Hguar.
        apply andb_true_iff in Hguar as [_ Hguar].
        apply andb_true_iff in Hguar as [Hguar Hg2].
        apply andb_true_iff in Hguar as [Hguar Hg1].
        apply andb_true_iff in Hguar as [Hguar Hgc].
        apply andb_true_iff in Hguar as [Hguar Heq2].
        apply andb_true_iff in Hguar as [Hi1 Heq1].
        apply dtyp_eqb_eq in Heq1; subst dt1.
        apply dtyp_eqb_eq in Heq2; subst dt2.
        assert (Hvc_i1 : dvalue_has_dtyp vc (DTYPE_Base (DTYPE_I 1%positive))).
        { rewrite <- (is_i1_dtyp_eq dt_c Hi1); apply Hvc, Hgc. }
        pose proof (eou_safe_to_ret_imp (fun x => dvalue_has_dtyp x dt) _
                      (eval_select_safe_P (fun x => dvalue_has_dtyp x dt)
                         (dvalue_has_dtyp_Poison dt)
                         vc v1 v2 dt Hvc_i1 (Hv1 Hg1) (Hv2 Hg2))) as Hret.
        rewrite E in Hret; exact Hret.
    - (* OP_Freeze *)
      cbn [full_exp_uses] in Hagree.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hagree (Some dt')) |].
      intros ? ? v1 _ (-> & -> & <- & Hv1).
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_freeze].
      intros ? ? r _ (-> & -> & <- & Hfr); repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; intros Hguar.
      apply andb_true_iff in Hguar as [Hsc Hguar].
      apply andb_true_iff in Hguar as [Heq Hg1].
      apply dtyp_eqb_eq in Heq; subst dt'.
      apply Hfr; [exact Hsc | apply Hv1, Hg1].
    - (* EXP_Asm *)
      unfold denote_exp'; cbn [denote_exp]; apply cfg_local_sim_withCall_raise_sync.
    - (* EXP_Metadata METADATA_Const *)
      cbn [full_exp_uses] in Hagree.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_weaken; [| exact (IHe1 Hagree (Some dt'))].
      intros ? ? r _ (-> & -> & <- & _); repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* EXP_Metadata other *)
      unfold denote_exp'; cbn [denote_exp].
      destruct m as [| mid | [dt' e1] | mds | m1 m2 | s1 s2 | fi];
        [| | exfalso; exact (Hm dt' e1 Logic.eq_refl) | | | |];
        (eapply cfg_local_sim_obs_eq;
         [symmetry; apply withCall_ret | symmetry; apply withCall_ret |];
         apply cfg_local_sim_ret; repeat split; try reflexivity;
         destruct top as [dt |]; [| exact I];
         cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc).
    - (* EXP_Splat *)
      cbn [full_exp_uses] in Hagree.
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [apply cfg_local_sim_withCall_EOU_sync |].
      intros ? ? [sz t] _ (-> & -> & <-).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_bind | symmetry; apply withCall_bind |].
      eapply cfg_local_sim_bind; [exact (IHe1 Hagree (Some dt')) |].
      intros ? ? v1 _ (-> & -> & <- & _).
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply withCall_ret | symmetry; apply withCall_ret |].
      apply cfg_local_sim_ret; repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
    - (* EXP_BlockAddress *)
      unfold denote_exp'; cbn [denote_exp].
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_withCall_gread_sync].
      intros ? ? v _ (-> & -> & <-); repeat split; try reflexivity.
      destruct top as [dt |]; [| exact I].
      cbn [guarantees_scalar_dtyp]; rewrite andb_false_r; intros Hc; discriminate Hc.
  Qed.

  Lemma cfg_local_sim_denote_op_sync
    (te : ty_env) (env1 env2 : @local_env PaV) (op : exp dtyp) :
    tenv_sound te env1 ->
    env_agree_on (full_exp_uses op) env1 env2 ->
    cfg_local_sim
      (fun e1' e2' v1 v2 =>
         e1' = env1 /\ e2' = env2 /\ v1 = v2 /\
         val_matches_oty (normalize_oty (infer_op_oty te op)) v1)
      env1 env2 (denote_exp' None op) (denote_exp' None op).
  Proof.
    intros Hte Hagree.
    assert (Hnon_loc :
      (match op with EXP_Ident (ID_Local _) => False | _ => True end) ->
      cfg_local_sim
        (fun e1' e2' v1 v2 =>
           e1' = env1 /\ e2' = env2 /\ v1 = v2 /\
           val_matches_oty (normalize_oty (infer_op_oty te op)) v1)
        env1 env2 (denote_exp' None op) (denote_exp' None op)).
    { intros Hnl.
      destruct (op_cand_dtyp op) as [dt |] eqn:Ecand.
      - rewrite (op_cand_dtyp_denote_eq op dt Ecand).
        assert (Hinf : infer_op_oty te op =
                       if guarantees_scalar_dtyp te dt op then Some dt else None).
        { destruct op; try (destruct id; [| contradiction]);
            unfold infer_op_oty; rewrite Ecand; reflexivity. }
        rewrite Hinf.
        eapply cfg_local_sim_weaken;
          [| exact (cfg_local_sim_denote_exp_sync te env1 env2 op Hte Hagree (Some dt))].
        intros ? ? v _ (-> & -> & <- & Hv); repeat split; try reflexivity.
        destruct (guarantees_scalar_dtyp te dt op) eqn:Eguar.
        + apply val_matches_normalize_oty; intros _; apply Hv, Logic.eq_refl.
        + exact I.
      - assert (Hinf : infer_op_oty te op = None).
        { destruct op; try (destruct id; [| contradiction]);
            unfold infer_op_oty; rewrite Ecand; reflexivity. }
        rewrite Hinf; cbn [normalize_oty].
        eapply cfg_local_sim_weaken;
          [| exact (cfg_local_sim_denote_exp_sync te env1 env2 op Hte Hagree None)].
        intros ? ? v _ (-> & -> & <- & _); repeat split; try reflexivity; exact I. }
    destruct op; try (apply Hnon_loc; exact I).
    destruct id as [g | x]; [apply Hnon_loc; exact I |].
    assert (Hlk : Maps.lookup x env1 = Maps.lookup x env2).
    { apply (env_agree_on_in [x] env1 env2 x Hagree); left; reflexivity. }
    unfold denote_exp'; cbn [denote_exp lookup_id infer_op_oty].
    eapply cfg_local_sim_weaken; [| apply (cfg_local_sim_withCall_lread_sync env1 env2 x Hlk)].
    intros ? ? v _ (-> & -> & <- & Hv); repeat split; try reflexivity.
    destruct (lookup_ty x te) as [oty |] eqn:Elk; [| exact I].
    destruct (Hte x oty Elk) as (v' & Hlk' & Hv').
    replace v with v' by congruence.
    apply val_matches_oty_normalize, Hv'.
  Qed.

  (** * 8. Instruction, Block, Phi, Terminator, & Whole-CFG Simulation *)

  (** ** Lockstep [CFGtop] Helpers, Call Arguments, Operand Bundles, & Atomics *)

  Lemma cfg_local_sim_map_monad_sync {A B : Type}
    (f : A -> @CFGtop PaV B)
    (env1 env2 : @local_env PaV)
    (l : list A)
    (Hf : forall a,
            In a l ->
            cfg_local_sim
              (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
              env1 env2 (f a) (f a)) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (map_monad f l) (map_monad f l).
  Proof.
    induction l as [| a rest IH]; cbn [map_monad].
    - apply cfg_local_sim_ret; repeat split; reflexivity.
    - eapply cfg_local_sim_bind; [apply Hf; left; reflexivity |].
      intros ? ? y _ (-> & -> & <-).
      eapply cfg_local_sim_bind;
        [apply IH; intros z Hz; apply Hf; right; exact Hz |].
      intros ? ? ys _ (-> & -> & <-).
      apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_denote_exp_plain_sync
    (env1 env2 : @local_env PaV) (top : option dtyp) (e : exp dtyp) :
    env_agree_on (full_exp_uses e) env1 env2 ->
    cfg_local_sim
      (fun e1' e2' v1 v2 => e1' = env1 /\ e2' = env2 /\ v1 = v2)
      env1 env2 (denote_exp' top e) (denote_exp' top e).
  Proof.
    intros Hagree.
    eapply cfg_local_sim_weaken;
      [| exact (cfg_local_sim_denote_exp_sync [] env1 env2 e
                  (tenv_sound_nil env1) Hagree top)].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_alloca_sync
    (env1 env2 : @local_env PaV) (dt : dtyp) (n : N) (align : option N) :
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         e1' = env1 /\ e2' = env2 /\ r1 = r2 /\
         dvalue_has_dtyp r1 (DTYPE_Base DTYPE_Pointer))
      env1 env2 (alloca dt n align) (alloca dt n align).
  Proof.
    unfold alloca.
    apply (cfg_local_sim_trigger_post
             (fun r => dvalue_has_dtyp r (DTYPE_Base DTYPE_Pointer)));
      [reflexivity | intros r H; exact H].
  Qed.

  Lemma cfg_local_sim_load_sync
    (env1 env2 : @local_env PaV) (dt : dtyp) (a : @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         e1' = env1 /\ e2' = env2 /\ r1 = r2 /\
         (is_scalar_dtyp dt = true -> dvalue_has_dtyp r1 dt))
      env1 env2 (load dt a) (load dt a).
  Proof.
    unfold load.
    apply (cfg_local_sim_trigger_post
             (fun r => is_scalar_dtyp dt = true -> dvalue_has_dtyp r dt));
      [reflexivity | intros r H; exact H].
  Qed.

  Lemma cfg_local_sim_store_sync
    (env1 env2 : @local_env PaV) (dt : dtyp) (a v : @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (store dt a v) (store dt a v).
  Proof.
    unfold store.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_trigger_post (fun _ => True));
         [reflexivity | intros; exact I]].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_call_sync
    (env1 env2 : @local_env PaV)
    (dt : dtyp) (cc : cconv) (fv : @dvalue PaV) (vs : list (@dvalue PaV)) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (call dt cc fv vs) (call dt cc fv vs).
  Proof.
    unfold call.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_trigger_post (fun _ => True));
         [reflexivity | intros; exact I]].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_intrinsic_sync
    (env1 env2 : @local_env PaV)
    (dt : dtyp) (s : string) (vs : list (@dvalue PaV)) (va : option (@ptr (@PROV PaV) (@PTR PaV))) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (intrinsic dt s vs va) (intrinsic dt s vs va).
  Proof.
    unfold intrinsic.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_trigger_post (fun _ => True));
         [reflexivity | intros; exact I]].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_stack_get_exc_sync
    (env1 env2 : @local_env PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 stack_get_exc stack_get_exc.
  Proof.
    unfold stack_get_exc.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_trigger_post (fun _ => True));
         [reflexivity | intros; exact I]].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_stack_raise_sync
    (env1 env2 : @local_env PaV) (ex : @exc PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (stack_raise ex) (stack_raise ex).
  Proof.
    unfold stack_raise.
    eapply cfg_local_sim_weaken;
      [| apply (cfg_local_sim_trigger_post (fun _ => True));
         [reflexivity | intros; exact I]].
    intros ? ? ? ? (-> & -> & <- & _); repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_denote_call_args_sync
    (env1 env2 : @local_env PaV)
    (args : list (texp dtyp * list param_attr)) (msg : string) :
    env_agree_on (flat_map (fun '(te, _) => full_texp_uses te) args) env1 env2 ->
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (denote_call_args args msg) (denote_call_args args msg).
  Proof.
    intros Hagree; unfold denote_call_args.
    apply cfg_local_sim_map_monad_sync; intros [[t op] attrs] Hin.
    eapply cfg_local_sim_bind.
    - apply cfg_local_sim_denote_exp_plain_sync.
      intros x Hx; apply Hagree, in_raw_ids_spec.
      apply in_raw_ids_spec in Hx; apply in_flat_map.
      exists ((t, op), attrs); split; [exact Hin | exact Hx].
    - intros ? ? v _ (-> & -> & <-).
      apply cfg_local_sim_apply_attrs_sync.
  Qed.

  Lemma cfg_local_sim_denote_operand_bundles_sync
    (env1 env2 : @local_env PaV)
    (loc : string) (f : exp dtyp) (obs : list (@operand_bundle dtyp)) :
    env_agree_on (flat_map full_ob_uses obs) env1 env2 ->
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (denote_operand_bundles loc f obs) (denote_operand_bundles loc f obs).
  Proof.
    intros Hagree; unfold denote_operand_bundles.
    eapply cfg_local_sim_bind.
    - apply cfg_local_sim_map_monad_sync; intros ob Hob.
      eapply cfg_local_sim_bind.
      + apply cfg_local_sim_map_monad_sync; intros o Ho.
        destruct o as [[t e] | md].
        * apply cfg_local_sim_denote_exp_plain_sync.
          intros x Hx; apply Hagree, in_raw_ids_spec.
          apply in_raw_ids_spec in Hx; apply in_flat_map.
          exists ob; split; [exact Hob |].
          unfold full_ob_uses; apply in_flat_map.
          exists (SSA_value (t, e)); split; [exact Ho | exact Hx].
        * apply cfg_local_sim_ret; repeat split; reflexivity.
      + intros ? ? vs _ (-> & -> & <-).
        destruct (bundle_check f (ob_tag ob)) as [chk |] eqn:Echk.
        * exact (cfg_local_sim_assume_check_sync env1 env2 f (ob_tag ob) loc vs chk Echk).
        * apply cfg_local_sim_ret; repeat split; reflexivity.
    - intros ? ? _ _ (-> & -> & _); apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_local_sim_denote_cmpxchg_sync
    (env1 env2 : @local_env PaV) (id : raw_id) (cpx : cmpxchg dtyp) :
    env_agree_on
      (full_texp_uses (c_ptr cpx)
       ++ full_texp_uses (c_cmp cpx)
       ++ full_texp_uses (c_new cpx))
      env1 env2 ->
    cfg_local_sim
      (fun e1' e2' _ _ =>
         exists v, e1' = Maps.add id v env1 /\ e2' = Maps.add id v env2)
      env1 env2 (denote_cmpxchg id cpx) (denote_cmpxchg id cpx).
  Proof.
    intros Hagree.
    pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag_ptr.
    pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag_cn.
    pose proof (env_agree_on_app_l _ _ _ _ Hag_cn) as Hag_cmp.
    pose proof (env_agree_on_app_r _ _ _ _ Hag_cn) as Hag_new.
    unfold denote_cmpxchg.
    destruct (c_ptr cpx) as [ptr_ty ptr_val];
      destruct (c_cmp cpx) as [cmp_ty cmp_val];
      destruct (c_new cpx) as [new_ty new_val];
      cbn [full_texp_uses snd] in Hag_ptr, Hag_cmp, Hag_new;
      cbv beta iota zeta.
    destruct (dtyp_eq_dec cmp_ty new_ty) as [<- | _];
      [| apply cfg_local_sim_raise_sync].
    eapply cfg_local_sim_bind;
      [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some ptr_ty) ptr_val Hag_ptr) |].
    intros ? ? ptr_v _ (-> & -> & <-).
    eapply cfg_local_sim_bind;
      [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some cmp_ty) cmp_val Hag_cmp) |].
    intros ? ? cmp_v _ (-> & -> & <-).
    eapply cfg_local_sim_bind;
      [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some cmp_ty) new_val Hag_new) |].
    intros ? ? new_v _ (-> & -> & <-).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
    intros ? ? _ _ (-> & -> & _).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
    intros ? ? loaded_v _ (-> & -> & <- & _).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
    intros ? ? dv _ (-> & -> & <-).
    destruct dv as [db | |];
      [| apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync].
    destruct db as [p | sz cb | ip | d | f | | | bsz bv];
      [ apply cfg_local_sim_raise_sync | | apply cfg_local_sim_raise_sync
      | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync
      | | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync ].
    - destruct sz as [p | p |];
        [apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync |].
      match goal with |- context [if ?b then _ else _] => destruct b end.
      + eapply cfg_local_sim_bind; [apply cfg_local_sim_store_sync |].
        intros ? ? _ _ (-> & -> & _); cbv zeta.
        eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
        intros ? ? _ _ (-> & -> & _); eexists; split; reflexivity.
      + cbv zeta.
        eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
        intros ? ? _ _ (-> & -> & _); eexists; split; reflexivity.
    - apply cfg_local_sim_raiseUB_cut.
  Qed.

  Lemma cfg_local_sim_denote_atomic_rmw_op_sync
    (env1 env2 : @local_env PaV)
    (a_op : atomic_rmw_operation) (pv val : @dvalue PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2
      (denote_atomic_rmw_operation a_op pv val)
      (denote_atomic_rmw_operation a_op pv val).
  Proof.
    destruct a_op; cbn [denote_atomic_rmw_operation];
      lazymatch goal with
      | |- cfg_local_sim _ _ _ (EOU_to_itree _) (EOU_to_itree _) =>
          apply cfg_local_sim_EOU_sync
      | |- cfg_local_sim _ _ _ (raise _) (raise _) =>
          apply cfg_local_sim_raise_sync
      | _ => idtac
      end.
    - (* Axchg *)
      apply cfg_local_sim_ret; repeat split; reflexivity.
    - (* Anand *)
      destruct val as [db | |];
        [| apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync].
      destruct db as [p | sz i | ip | d | f | | | bsz bv];
        [ apply cfg_local_sim_raise_sync | apply cfg_local_sim_EOU_sync
        | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync
        | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync
        | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync ].
  Qed.

  Lemma cfg_local_sim_denote_atomicrmw_sync
    (env1 env2 : @local_env PaV) (id : raw_id) (armw : atomicrmw dtyp) :
    env_agree_on
      (full_texp_uses (a_ptr armw) ++ full_texp_uses (a_val armw))
      env1 env2 ->
    cfg_local_sim
      (fun e1' e2' _ _ =>
         exists v, e1' = Maps.add id v env1 /\ e2' = Maps.add id v env2)
      env1 env2 (denote_atomicrmw id armw) (denote_atomicrmw id armw).
  Proof.
    intros Hagree.
    pose proof (env_agree_on_app_l _ _ _ _ Hagree) as Hag_ptr.
    pose proof (env_agree_on_app_r _ _ _ _ Hagree) as Hag_val.
    unfold denote_atomicrmw.
    destruct (a_ptr armw) as [ptr_ty ptr_val];
      destruct (a_val armw) as [a_ty a_val];
      cbn [full_texp_uses snd] in Hag_ptr, Hag_val; cbv beta iota zeta.
    eapply cfg_local_sim_bind;
      [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some ptr_ty) ptr_val Hag_ptr) |].
    intros ? ? ptr_v _ (-> & -> & <-).
    eapply cfg_local_sim_bind;
      [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some a_ty) a_val Hag_val) |].
    intros ? ? a_v _ (-> & -> & <-).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
    intros ? ? _ _ (-> & -> & _).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
    intros ? ? loaded_v _ (-> & -> & <- & _).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_denote_atomic_rmw_op_sync |].
    intros ? ? stored_v _ (-> & -> & <-).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_store_sync |].
    intros ? ? _ _ (-> & -> & _).
    eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
    intros ? ? _ _ (-> & -> & _).
    apply cfg_local_sim_ret; exists loaded_v; split; reflexivity.
  Qed.

  (** ** Lockstep Instruction & Intra-Block Backward DCE Simulation *)

  Definition instr_live_before
    (ins : instr_id * instr dtyp * list (metadata dtyp))
    (live_after : list raw_id) : list raw_id :=
    let '(iid, i, _) := ins in
    let live_killed :=
      match instr_must_kill iid i with
      | Some x => remove_raw_id x live_after
      | None => live_after
      end in
    add_raw_ids (full_instr_uses i) live_killed.

  Lemma cfg_local_sim_denote_instr_sync
    (te : ty_env) (live_after : list raw_id)
    (env1 env2 : @local_env PaV)
    (ins : instr_id * instr dtyp * list (metadata dtyp))
    (va : option (@ptr (@PROV PaV) (@PTR PaV))) :
    tenv_sound te env1 ->
    env_agree_on (instr_live_before ins live_after) env1 env2 ->
    cfg_local_sim
      (fun e1' e2' _ _ =>
         (env1 = env2 -> e1' = e2') /\
         tenv_sound (step_tenv_instr te ins) e1' /\
         env_agree_on live_after e1' e2')
      env1 env2 (denote_instr ins va) (denote_instr ins va).
  Proof.
    intros Hte Hagree.
    destruct ins as [[iid i] md].
    unfold instr_live_before in Hagree.
    apply env_agree_on_add_raw_ids_split in Hagree as [Huses Hkill].
    destruct i as
      [ msg
      | op
      | [dt f] args anns obs
      | dt anns
      | dt [du ptr] anns
      | [dt val] [du ptr] anns
      | syncscope o
      | cpx
      | armw
      | [t ptr_exp] argty
      | resultty cleanup cs ].
    - (* INSTR_Comment *)
      destruct iid as [id | vid]; unfold denote_instr; cbv beta iota zeta.
      + apply cfg_local_sim_raise_sync.
      + cbn [step_tenv_instr instr_must_kill] in Hkill |- *.
        apply cfg_local_sim_ret; split; [intros Heq; exact Heq | exact (conj Hte Hkill)].
    - (* INSTR_Op *)
      destruct iid as [id | vid];
        [| unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [full_instr_uses step_tenv_instr instr_must_kill] in Huses, Hkill |- *.
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_op_sync te env1 env2 op Hte Huses) |].
      intros ? ? uv _ (-> & -> & <- & Huv).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
      intros ? ? _ _ (-> & -> & _).
      apply cfg_local_sim_ret; split; [intros ->; reflexivity |].
      split;
        [ apply (tenv_sound_set_ty id (infer_op_oty te op) uv te env1 Huv Hte)
        | apply (env_agree_on_add_both live_after id uv env1 env2 Hkill) ].
    - (* INSTR_Call *)
      cbn [full_instr_uses] in Huses.
      pose proof (env_agree_on_app_l _ _ _ _ Huses) as Hag_f.
      pose proof (env_agree_on_app_r _ _ _ _ Huses) as Hag_rest1.
      pose proof (env_agree_on_app_l _ _ _ _ Hag_rest1) as Hag_args.
      pose proof (env_agree_on_app_r _ _ _ _ Hag_rest1) as Hag_rest2.
      pose proof (env_agree_on_app_r _ _ _ _ Hag_rest2) as Hag_obs.
      cbn [full_texp_uses snd] in Hag_f.
      destruct iid as [id | vid];
        cbn [step_tenv_instr instr_must_kill] in Hkill |- *;
        unfold denote_instr; cbv beta iota zeta.
      + eapply cfg_local_sim_bind;
          [apply (cfg_local_sim_denote_call_args_sync env1 env2 args _ Hag_args) |].
        intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_bind;
          [apply (cfg_local_sim_denote_operand_bundles_sync env1 env2 _ f obs Hag_obs) |].
        intros ? ? _ _ (-> & -> & _).
        eapply cfg_local_sim_bind.
        * destruct (intrinsic_exp f) as [s |].
          -- apply cfg_local_sim_intrinsic_sync.
          -- eapply cfg_local_sim_bind;
               [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 None f Hag_f) |].
             intros ? ? fv _ (-> & -> & <-); apply cfg_local_sim_call_sync.
        * intros ? ? res _ (-> & -> & <-).
          eapply cfg_local_sim_bind; [apply cfg_local_sim_check_call_return_sync |].
          intros ? ? res' _ (-> & -> & <-).
          eapply cfg_local_sim_bind with
            (RR := fun e1' e2' (r1 r2 : @dvalue PaV) => e1' = env1 /\ e2' = env2 /\ r1 = r2).
          -- destruct res' as [ex | dv];
               [apply cfg_local_sim_raiseLLVM_sync
               | apply cfg_local_sim_ret; repeat split; reflexivity].
          -- intros ? ? rv _ (-> & -> & <-).
             eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
             intros ? ? _ _ (-> & -> & _); split; [intros ->; reflexivity |].
             split;
               [ apply (tenv_sound_set_ty id None rv te env1 I Hte)
               | apply (env_agree_on_add_both live_after id rv env1 env2 Hkill) ].
      + eapply cfg_local_sim_bind;
          [apply (cfg_local_sim_denote_call_args_sync env1 env2 args _ Hag_args) |].
        intros ? ? vs _ (-> & -> & <-).
        eapply cfg_local_sim_bind;
          [apply (cfg_local_sim_denote_operand_bundles_sync env1 env2 _ f obs Hag_obs) |].
        intros ? ? _ _ (-> & -> & _).
        eapply cfg_local_sim_bind.
        * destruct (intrinsic_exp f) as [s |].
          -- apply cfg_local_sim_intrinsic_sync.
          -- eapply cfg_local_sim_bind;
               [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 None f Hag_f) |].
             intros ? ? fv _ (-> & -> & <-); apply cfg_local_sim_call_sync.
        * intros ? ? res _ (-> & -> & <-).
          eapply cfg_local_sim_bind; [apply cfg_local_sim_check_call_return_sync |].
          intros ? ? res' _ (-> & -> & <-).
          eapply cfg_local_sim_bind with
            (RR := fun e1' e2' (r1 r2 : @dvalue PaV) => e1' = env1 /\ e2' = env2 /\ r1 = r2).
          -- destruct res' as [ex | dv];
               [apply cfg_local_sim_raiseLLVM_sync
               | apply cfg_local_sim_ret; repeat split; reflexivity].
          -- intros ? ? dv1 dv2 (-> & -> & _).
             apply cfg_local_sim_ret; split; [intros Heq; exact Heq | exact (conj Hte Hkill)].
    - (* INSTR_Alloca *)
      destruct iid as [id | vid];
        [| unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [full_instr_uses step_tenv_instr instr_must_kill] in Huses, Hkill |- *.
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_bind with
        (RR := fun e1' e2' _ _ =>
                 exists v,
                   e1' = Maps.add id v env1 /\
                   e2' = Maps.add id v env2 /\
                   dvalue_has_dtyp v (DTYPE_Base DTYPE_Pointer)).
      + destruct (find_option ann_num_elements anns) as [[t num_exp] |] eqn:Efind.
        * assert (Hag_num : env_agree_on (full_exp_uses num_exp) env1 env2).
          { intros x Hx; apply Huses, in_raw_ids_spec.
            apply in_raw_ids_spec in Hx.
            exact (find_option_ann_num_elements_uses anns (t, num_exp) x Efind Hx). }
          eapply cfg_local_sim_bind;
            [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some t) num_exp Hag_num) |].
          intros ? ? n _ (-> & -> & <-).
          destruct (dvalue_is_poison n); [apply cfg_local_sim_raiseUB_cut |].
          eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
          intros ? ? n' _ (-> & -> & <-).
          eapply cfg_local_sim_bind; [apply cfg_local_sim_alloca_sync |].
          intros ? ? v _ (-> & -> & <- & Hv).
          eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
          intros ? ? _ _ (-> & -> & _); exists v; split; [reflexivity | split; [reflexivity | exact Hv]].
        * eapply cfg_local_sim_bind; [apply cfg_local_sim_alloca_sync |].
          intros ? ? v _ (-> & -> & <- & Hv).
          eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
          intros ? ? _ _ (-> & -> & _); exists v; split; [reflexivity | split; [reflexivity | exact Hv]].
      + intros ? ? _ _ (v & -> & -> & Hv).
        apply cfg_local_sim_ret; split; [intros ->; reflexivity |].
        split.
        * apply (tenv_sound_set_ty id (Some (DTYPE_Base DTYPE_Pointer)) v te env1);
            [apply val_matches_normalize_oty; intros _; exact Hv | exact Hte].
        * apply (env_agree_on_add_both live_after id v env1 env2 Hkill).
    - (* INSTR_Load *)
      destruct iid as [id | vid];
        [| unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [full_instr_uses step_tenv_instr instr_must_kill] in Huses, Hkill |- *.
      pose proof (env_agree_on_app_l _ _ _ _ Huses) as Hag_ptr.
      cbn [full_texp_uses snd] in Hag_ptr.
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some du) ptr Hag_ptr) |].
      intros ? ? a _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
      intros ? ? v _ (-> & -> & <- & Hv).
      eapply cfg_local_sim_bind.
      + apply (cfg_local_sim_EOU_ret_sync
                 (fun v' => is_scalar_dtyp dt = true -> dvalue_has_dtyp v' dt)).
        eapply eou_ret_imp_weaken;
          [| apply (apply_value_attrs_scalar_typ
                      (load_metadata_attrs md) _ dt
                      (value_metadata_range (metadata_range md) v))].
        intros v' Hattr Hsc.
        apply (Hattr Hsc), (value_metadata_range_scalar_typ (metadata_range md) dt v Hsc (Hv Hsc)).
      + intros ? ? v' _ (-> & -> & <- & Hv').
        eapply cfg_local_sim_bind.
        * unfold assert_load_dereferenceable.
          destruct (load_metadata_dereferenceable md) as [[or_null n] |];
            [ apply cfg_local_sim_assert_dereferenceable_sync
            | apply cfg_local_sim_ret; repeat split; reflexivity ].
        * intros ? ? _ _ (-> & -> & _).
          eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
          intros ? ? _ _ (-> & -> & _); split; [intros ->; reflexivity |].
          split.
          -- apply (tenv_sound_set_ty id (Some dt) v' te env1);
               [apply val_matches_normalize_oty, Hv' | exact Hte].
          -- apply (env_agree_on_add_both live_after id v' env1 env2 Hkill).
    - (* INSTR_Store *)
      destruct iid as [id | vid];
        [unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync |].
      cbn [full_instr_uses step_tenv_instr instr_must_kill] in Huses, Hkill |- *.
      pose proof (env_agree_on_app_l _ _ _ _ Huses) as Hag_val.
      pose proof (env_agree_on_app_r _ _ _ _ Huses) as Hag_pa.
      pose proof (env_agree_on_app_l _ _ _ _ Hag_pa) as Hag_ptr.
      cbn [full_texp_uses snd] in Hag_val, Hag_ptr.
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some dt) val Hag_val) |].
      intros ? ? v _ (-> & -> & <-).
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some du) ptr Hag_ptr) |].
      intros ? ? a _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_bind.
      + destruct a as [db | |];
          [destruct db as [p | sz k | ip | d | f | | | bsz bv];
           [ apply cfg_local_sim_store_sync | apply cfg_local_sim_store_sync
           | apply cfg_local_sim_store_sync | apply cfg_local_sim_store_sync
           | apply cfg_local_sim_store_sync | apply cfg_local_sim_raiseUB_cut
           | apply cfg_local_sim_store_sync | apply cfg_local_sim_store_sync ]
          | apply cfg_local_sim_store_sync
          | apply cfg_local_sim_store_sync].
      + intros ? ? _ _ (-> & -> & _).
        apply cfg_local_sim_ret; split; [intros Heq; exact Heq | exact (conj Hte Hkill)].
    - (* INSTR_Fence *)
      destruct iid as [id | vid];
        cbn [step_tenv_instr instr_must_kill] in Hkill |- *;
        unfold denote_instr; cbv beta iota zeta;
        apply cfg_local_sim_ret; (split; [intros Heq; exact Heq | exact (conj Hte Hkill)]).
    - (* INSTR_AtomicCmpXchg *)
      destruct iid as [id | vid];
        [| unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [full_instr_uses step_tenv_instr instr_must_kill] in Huses, Hkill |- *.
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_weaken;
        [| exact (cfg_local_sim_denote_cmpxchg_sync env1 env2 id cpx Huses)].
      intros ? ? _ _ (v & -> & ->); split; [intros ->; reflexivity |].
      split;
        [ apply (tenv_sound_set_ty id None v te env1 I Hte)
        | apply (env_agree_on_add_both live_after id v env1 env2 Hkill) ].
    - (* INSTR_AtomicRMW *)
      destruct iid as [id | vid];
        [| unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [full_instr_uses step_tenv_instr instr_must_kill] in Huses, Hkill |- *.
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_weaken;
        [| exact (cfg_local_sim_denote_atomicrmw_sync env1 env2 id armw Huses)].
      intros ? ? _ _ (v & -> & ->); split; [intros ->; reflexivity |].
      split;
        [ apply (tenv_sound_set_ty id None v te env1 I Hte)
        | apply (env_agree_on_add_both live_after id v env1 env2 Hkill) ].
    - (* INSTR_VAArg *)
      cbn [full_instr_uses full_texp_uses snd] in Huses.
      destruct iid as [id | vid];
        cbn [step_tenv_instr instr_must_kill] in Hkill |- *;
        unfold denote_instr; cbv beta iota zeta.
      + eapply cfg_local_sim_bind;
          [exact (cfg_local_sim_denote_exp_plain_sync
                    env1 env2 (Some (DTYPE_Base DTYPE_Pointer)) ptr_exp Huses) |].
        intros ? ? ptr_to_args _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
        intros ? ? args_p _ (-> & -> & <- & _).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
        intros ? ? retv _ (-> & -> & <- & _).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
        intros ? ? ix _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
        intros ? ? args' _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_store_sync |].
        intros ? ? _ _ (-> & -> & _).
        eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
        intros ? ? _ _ (-> & -> & _); split; [intros ->; reflexivity |].
        split;
          [ apply (tenv_sound_set_ty id None retv te env1 I Hte)
          | apply (env_agree_on_add_both live_after id retv env1 env2 Hkill) ].
      + eapply cfg_local_sim_bind;
          [exact (cfg_local_sim_denote_exp_plain_sync
                    env1 env2 (Some (DTYPE_Base DTYPE_Pointer)) ptr_exp Huses) |].
        intros ? ? ptr_to_args _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
        intros ? ? args_p _ (-> & -> & <- & _).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_load_sync |].
        intros ? ? _ _ (-> & -> & _ & _).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
        intros ? ? ix _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_EOU_sync |].
        intros ? ? args' _ (-> & -> & <-).
        eapply cfg_local_sim_bind; [apply cfg_local_sim_store_sync |].
        intros ? ? _ _ (-> & -> & _).
        apply cfg_local_sim_ret; split; [intros Heq; exact Heq | exact (conj Hte Hkill)].
    - (* INSTR_LandingPad *)
      destruct iid as [id | vid];
        [| unfold denote_instr; cbv beta iota zeta; apply cfg_local_sim_raise_sync].
      cbn [step_tenv_instr instr_must_kill] in Hkill |- *.
      unfold denote_instr; cbv beta iota zeta.
      eapply cfg_local_sim_bind; [apply cfg_local_sim_stack_get_exc_sync |].
      intros ? ? oe _ (-> & -> & <-).
      destruct oe as [ex |]; [| apply cfg_local_sim_raise_sync].
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_lwrite_both].
      intros ? ? _ _ (-> & -> & _); split; [intros ->; reflexivity |].
      split;
        [ apply (tenv_sound_set_ty id None ex te env1 I Hte)
        | apply (env_agree_on_add_both live_after id ex env1 env2 Hkill) ].
  Qed.

  Lemma dce_code_cons_cases
    (te : ty_env) (ins : instr_id * instr dtyp * list (metadata dtyp))
    (rest : code dtyp) (live_after : list raw_id) :
    let '(live_mid, rest') := dce_code (step_tenv_instr te ins) rest live_after in
    (exists x op md,
       ins = (IId x, INSTR_Op op, md) /\
       in_raw_ids x live_mid = false /\
       check_safe_op te op = true /\
       dce_code te (ins :: rest) live_after = (live_mid, rest'))
    \/
    (dce_code te (ins :: rest) live_after =
       (instr_live_before ins live_mid, ins :: rest')).
  Proof.
    cbn [dce_code].
    destruct (dce_code (step_tenv_instr te ins) rest live_after) as [live_mid rest'].
    destruct ins as [[iid i] md].
    destruct iid as [x | vid], i;
      try (right; reflexivity).
    destruct (negb (in_raw_ids x live_mid) && check_safe_op te op) eqn:Edel.
    - apply andb_true_iff in Edel as [Hnx Hsafe].
      apply negb_true_iff in Hnx.
      left; exists x, op, md; repeat split; try reflexivity; assumption.
    - right; reflexivity.
  Qed.

  Lemma left_deleted_op_sim
    (te : ty_env) (x : local_id) (op : exp dtyp) (md : list (metadata dtyp))
    (va : option (@ptr (@PROV PaV) (@PTR PaV)))
    (RR : @local_env PaV -> @local_env PaV -> unit -> unit -> Prop)
    (env1 env2 : @local_env PaV)
    (k1 : @CFGtop PaV unit) (t2 : @CFGtop PaV unit) :
    check_safe_op te op = true ->
    tenv_sound te env1 ->
    (forall uv : @dvalue PaV,
       val_matches_oty (normalize_oty (infer_op_oty te op)) uv ->
       cfg_local_sim RR (Maps.add x uv env1) env2 k1 t2) ->
    cfg_local_sim RR env1 env2
      (ITree.bind (denote_instr (IId x, INSTR_Op op, md) va) (fun _ => k1))
      t2.
  Proof.
    intros Hsafe Hte Hk.
    unfold denote_instr; cbv beta iota zeta.
    eapply cfg_local_sim_obs_eq; [symmetry; apply Eqit.bind_bind | reflexivity |].
    eapply left_evals_to_bind_sim;
      [exact (check_safe_op_sound te op env1 Hsafe Hte) |].
    intros uv Huv.
    specialize (Hk uv Huv).
    pstep; eapply CLS_WriteL with (x := x) (v := uv) (k1 := fun _ => k1).
    - unfold lwrite; cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [] _ _; apply Eqit.bind_ret_l.
    - punfold Hk; exact Hk.
  Qed.

  Lemma dce_code_sim
    (cs : code dtyp) (va : option (@ptr (@PROV PaV) (@PTR PaV))) :
    forall (te : ty_env) (live_after : list raw_id)
           (env1 env2 : @local_env PaV),
      let '(live_in, cs') := dce_code te cs live_after in
      tenv_sound te env1 ->
      env_agree_on live_in env1 env2 ->
      cfg_local_sim
        (fun e1' e2' _ _ =>
           tenv_sound (step_tenv_code te cs) e1' /\
           env_agree_on live_after e1' e2')
        env1 env2 (denote_code cs va) (denote_code cs' va).
  Proof.
    induction cs as [| ins rest IH]; intros te live_after env1 env2.
    - cbn [dce_code step_tenv_code]; intros Hte Hagree.
      eapply cfg_local_sim_obs_eq;
        [symmetry; apply denote_code_nil | symmetry; apply denote_code_nil |].
      apply cfg_local_sim_ret; exact (conj Hte Hagree).
    - pose proof (dce_code_cons_cases te ins rest live_after) as Hcases.
      specialize (IH (step_tenv_instr te ins) live_after).
      destruct (dce_code (step_tenv_instr te ins) rest live_after) as [live_mid rest'].
      cbn [step_tenv_code].
      destruct Hcases as [(x & op & md & -> & Hnx & Hsafe & ->) | ->].
      + (* Deleted dead INSTR_Op *)
        intros Hte Hagree.
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply denote_code_cons | reflexivity |].
        eapply left_deleted_op_sim; [exact Hsafe | exact Hte |].
        intros uv Huv; apply IH.
        * cbn [step_tenv_instr].
          apply (tenv_sound_set_ty x (infer_op_oty te op) uv te env1 Huv Hte).
        * apply (env_agree_on_add_dead_l live_mid x uv env1 env2 Hnx Hagree).
      + (* Kept instruction *)
        intros Hte Hagree.
        eapply cfg_local_sim_obs_eq;
          [symmetry; apply denote_code_cons | symmetry; apply denote_code_cons |].
        eapply cfg_local_sim_bind;
          [exact (cfg_local_sim_denote_instr_sync te live_mid env1 env2 ins va Hte Hagree) |].
        intros e1' e2' _ _ (_ & Hte' & Hagree').
        exact (IH e1' e2' Hte' Hagree').
  Qed.

  Lemma denote_code_refl_sim
    (cs : code dtyp) (va : option (@ptr (@PROV PaV) (@PTR PaV))) (env : @local_env PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = e2' /\ r1 = r2)
      env env (denote_code cs va) (denote_code cs va).
  Proof.
    revert env; induction cs as [| ins rest IH]; intros env.
    - eapply cfg_local_sim_obs_eq;
        [symmetry; apply denote_code_nil | symmetry; apply denote_code_nil |].
      apply cfg_local_sim_ret; split; reflexivity.
    - eapply cfg_local_sim_obs_eq;
        [symmetry; apply denote_code_cons | symmetry; apply denote_code_cons |].
      eapply cfg_local_sim_bind.
      + apply (cfg_local_sim_denote_instr_sync [] [] env env ins va
                 (tenv_sound_nil env) (env_agree_on_refl _ env)).
      + intros e1' e2' _ _ (Heq & _ & _).
        rewrite (Heq Logic.eq_refl); apply IH.
  Qed.

  (** ** Two-Phase [denote_phis] Dead-Phi Simulation *)

  Inductive phi_vals_rel (live_after : list raw_id)
    : list (local_id * ty_info) ->
      list local_id ->
      list (local_id * @dvalue PaV) ->
      list (local_id * @dvalue PaV) -> Prop :=
  | PVR_nil :
      phi_vals_rel live_after [] [] [] []
  | PVR_keep (id : local_id) (oty : ty_info) (v : @dvalue PaV)
      (ws : list (local_id * ty_info)) (kds : list local_id)
      (dvs1 dvs2 : list (local_id * @dvalue PaV)) :
      val_matches_oty (normalize_oty oty) v ->
      phi_vals_rel live_after ws kds dvs1 dvs2 ->
      phi_vals_rel live_after ((id, oty) :: ws) (id :: kds)
        ((id, v) :: dvs1) ((id, v) :: dvs2)
  | PVR_drop (id : local_id) (oty : ty_info) (v : @dvalue PaV)
      (ws : list (local_id * ty_info)) (kds : list local_id)
      (dvs1 dvs2 : list (local_id * @dvalue PaV)) :
      in_raw_ids id live_after = false ->
      val_matches_oty (normalize_oty oty) v ->
      phi_vals_rel live_after ws kds dvs1 dvs2 ->
      phi_vals_rel live_after ((id, oty) :: ws) kds
        ((id, v) :: dvs1) dvs2.

  Lemma phi_writes_sim
    (live_after : list raw_id)
    (ws : list (local_id * ty_info))
    (kds : list local_id)
    (dvs1 dvs2 : list (local_id * @dvalue PaV))
    (Hpvr : phi_vals_rel live_after ws kds dvs1 dvs2) :
    forall (te : ty_env) (env1 env2 : @local_env PaV),
      tenv_sound te env1 ->
      env_agree_on (remove_raw_ids kds live_after) env1 env2 ->
      cfg_local_sim
        (fun e1' e2' _ _ =>
           tenv_sound (apply_phi_writes ws te) e1' /\
           env_agree_on live_after e1' e2')
        env1 env2
        (map_monad (fun '(id, dv) => lwrite id dv) dvs1)
        (map_monad (fun '(id, dv) => lwrite id dv) dvs2).
  Proof.
    induction Hpvr as
      [ | id oty v ws kds dvs1 dvs2 Hv _ IH
        | id oty v ws kds dvs1 dvs2 Hdead Hv _ IH ];
      intros te env1 env2 Hte Hpass;
      cbn [apply_phi_writes map_monad].
    - cbn [remove_raw_ids fold_right] in Hpass.
      apply cfg_local_sim_ret; exact (conj Hte Hpass).
    - cbn [remove_raw_ids fold_right] in Hpass.
      eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
      intros ? ? [] [] (-> & -> & _).
      eapply cfg_local_sim_bind.
      + apply IH.
        * apply (tenv_sound_set_ty id oty v te env1 Hv Hte).
        * apply (env_agree_on_add_both _ id v env1 env2 Hpass).
      + intros e1' e2' r1 r2 Hpost; apply cfg_local_sim_ret, Hpost.
    - assert (Hsim_next :
        cfg_local_sim
          (fun e1' e2' _ _ =>
             tenv_sound (apply_phi_writes ws (set_ty id oty te)) e1' /\
             env_agree_on live_after e1' e2')
          (Maps.add id v env1) env2
          (ITree.bind
             (map_monad (fun '(id0, dv) => lwrite id0 dv) dvs1)
             (fun us => Ret (tt :: us)))
          (map_monad (fun '(id0, dv) => lwrite id0 dv) dvs2)).
      { eapply cfg_local_sim_obs_eq;
          [reflexivity | apply Eqit.bind_ret_r |].
        eapply cfg_local_sim_bind.
        - apply IH.
          + apply (tenv_sound_set_ty id oty v te env1 Hv Hte).
          + apply env_agree_on_add_dead_l; [| exact Hpass].
            destruct (in_raw_ids id (remove_raw_ids kds live_after)) eqn:Ein;
              [| reflexivity].
            apply in_remove_raw_ids in Ein as [_ Hin]; congruence.
        - intros e1' e2' r1 r2 Hpost; apply cfg_local_sim_ret, Hpost. }
      pstep; eapply CLS_WriteL with
        (x := id) (v := v)
        (k1 := fun b =>
                 ITree.bind (map_monad (fun '(id0, dv) => lwrite id0 dv) dvs1)
                   (fun us => Ret (b :: us))).
      + unfold lwrite;
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
          reflexivity.
      + punfold Hsim_next; exact Hsim_next.
  Qed.

  Lemma dce_phis_eval_sim
    (edges : list (block_id * ty_env))
    (bid_from : block_id) (te_edge : ty_env)
    (live_after : list raw_id)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (env1 env2 : @local_env PaV) :
    In (bid_from, te_edge) edges ->
    tenv_sound te_edge env1 ->
    env_agree_on
      (kept_phis_uses_from bid_from (dce_phis edges live_after phis))
      env1 env2 ->
    cfg_local_sim
      (fun e1' e2' dvs1 dvs2 =>
         e1' = env1 /\ e2' = env2 /\
         phi_vals_rel live_after
           (List.map (fun '(id, p, _) => (id, phi_res_oty bid_from te_edge p)) phis)
           (kept_phi_defs (dce_phis edges live_after phis))
           dvs1 dvs2)
      env1 env2
      (map_monad (denote_phi bid_from) phis)
      (map_monad (denote_phi bid_from) (dce_phis edges live_after phis)).
  Proof.
    intros Hin Hte.
    induction phis as [| [[id [pfm dt args]] md] rest IH]; intros Huses.
    - cbn [dce_phis kept_phi_defs List.map map_monad].
      apply cfg_local_sim_ret; split; [reflexivity | split; [reflexivity | constructor]].
    - cbn [dce_phis List.map] in Huses |- *.
      destruct (negb (in_raw_ids id live_after) &&
                forallb (fun '(pred, te_e) =>
                           is_safe_phi_on_edge pred te_e (Phi pfm dt args))
                        edges) eqn:Edel.
      + (* Deleted dead phi *)
        apply andb_true_iff in Edel as [Hnid Hall].
        apply negb_true_iff in Hnid.
        rewrite forallb_forall in Hall.
        specialize (Hall (bid_from, te_edge) Hin);
          unfold is_safe_phi_on_edge in Hall; cbv beta iota in Hall.
        destruct (assoc bid_from args) as [op |] eqn:Eassoc; [| discriminate Hall].
        assert (Hphi_eval :
          left_evals_to
            (fun y =>
               exists uv,
                 y = (id, uv) /\
                 val_matches_oty
                   (normalize_oty (phi_res_oty bid_from te_edge (Phi pfm dt args)))
                   uv)
            env1
            (denote_phi bid_from (id, Phi pfm dt args, md))).
        { unfold denote_phi; cbv beta iota zeta; rewrite Eassoc.
          eapply left_evals_to_bind;
            [exact (check_any_texp_sound te_edge op dt env1 Hall Hte) |].
          intros uv Huv; apply left_evals_to_ret.
          exists uv; split; [reflexivity |].
          unfold phi_res_oty; rewrite Eassoc.
          destruct (guarantees_scalar_dtyp te_edge dt op) eqn:Eguar.
          - apply val_matches_normalize_oty; intros _; apply Huv, Logic.eq_refl.
          - exact I. }
        cbn [map_monad].
        eapply left_evals_to_bind_sim; [exact Hphi_eval |].
        intros _ (uv & -> & Huv).
        eapply cfg_local_sim_obs_eq;
          [reflexivity | apply Eqit.bind_ret_r |].
        eapply cfg_local_sim_bind; [exact (IH Huses) |].
        intros ? ? dvs1 dvs2 (-> & -> & Hpvr).
        apply cfg_local_sim_ret; split;
          [reflexivity | split; [reflexivity | apply PVR_drop; assumption]].
      + (* Kept phi *)
        cbn [kept_phis_uses_from flat_map] in Huses.
        pose proof (env_agree_on_app_l _ _ _ _ Huses) as Hag_hd.
        pose proof (env_agree_on_app_r _ _ _ _ Huses) as Hag_tl.
        cbn [kept_phi_defs List.map map_monad].
        eapply cfg_local_sim_bind.
        * unfold denote_phi; cbv beta iota zeta.
          destruct (assoc bid_from args) as [op |] eqn:Eassoc;
            [| apply cfg_local_sim_raise_sync].
          eapply cfg_local_sim_bind;
            [exact (cfg_local_sim_denote_exp_sync te_edge env1 env2 op Hte Hag_hd (Some dt)) |].
          intros ? ? uv _ (-> & -> & <- & Huv).
          apply cfg_local_sim_ret.
          instantiate (1 := fun e1' e2' y1 y2 =>
                              e1' = env1 /\ e2' = env2 /\ y1 = y2 /\
                              exists uv0,
                                y1 = (id, uv0) /\
                                val_matches_oty
                                  (normalize_oty (phi_res_oty bid_from te_edge (Phi pfm dt args)))
                                  uv0).
          repeat split; try reflexivity.
          exists uv; split; [reflexivity |].
          unfold phi_res_oty; rewrite Eassoc.
          destruct (guarantees_scalar_dtyp te_edge dt op) eqn:Eguar.
          -- apply val_matches_normalize_oty; intros _; apply Huv, Logic.eq_refl.
          -- exact I.
        * intros ? ? _ _ (-> & -> & <- & uv & -> & Huv).
          eapply cfg_local_sim_bind; [exact (IH Hag_tl) |].
          intros ? ? dvs1 dvs2 (-> & -> & Hpvr).
          apply cfg_local_sim_ret; split;
            [reflexivity | split; [reflexivity | apply PVR_keep; assumption]].
  Qed.

  Lemma dce_phis_sim
    (edges : list (block_id * ty_env))
    (bid_from : block_id) (te_edge : ty_env)
    (live_after : list raw_id)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (env1 env2 : @local_env PaV) :
    In (bid_from, te_edge) edges ->
    tenv_sound te_edge env1 ->
    env_agree_on
      (edge_live_req bid_from (dce_phis edges live_after phis) live_after)
      env1 env2 ->
    cfg_local_sim
      (fun e1' e2' _ _ =>
         tenv_sound (step_tenv_phis_from bid_from phis te_edge) e1' /\
         env_agree_on live_after e1' e2')
      env1 env2
      (denote_phis bid_from phis)
      (denote_phis bid_from (dce_phis edges live_after phis)).
  Proof.
    intros Hin Hte Hagree.
    unfold edge_live_req in Hagree.
    apply env_agree_on_add_raw_ids_split in Hagree as [Huses Hpass].
    unfold denote_phis, step_tenv_phis_from.
    eapply cfg_local_sim_bind;
      [exact (dce_phis_eval_sim edges bid_from te_edge live_after phis
                env1 env2 Hin Hte Huses) |].
    intros ? ? dvs1 dvs2 (-> & -> & Hpvr).
    eapply cfg_local_sim_bind;
      [exact (phi_writes_sim live_after _ _ dvs1 dvs2 Hpvr te_edge env1 env2 Hte Hpass) |].
    intros e1' e2' r1 r2 Hpost; apply cfg_local_sim_ret, Hpost.
  Qed.

  Lemma denote_phis_refl_sim
    (bid_from : block_id)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (env : @local_env PaV) :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = e2' /\ r1 = r2)
      env env (denote_phis bid_from phis) (denote_phis bid_from phis).
  Proof.
    unfold denote_phis.
    eapply cfg_local_sim_bind.
    - apply cfg_local_sim_map_monad_sync; intros [[id [pfm dt args]] md] _.
      unfold denote_phi; cbv beta iota zeta.
      destruct (assoc bid_from args) as [op |]; [| apply cfg_local_sim_raise_sync].
      eapply cfg_local_sim_bind;
        [apply cfg_local_sim_denote_exp_plain_sync, env_agree_on_refl |].
      intros ? ? uv _ (-> & -> & <-).
      apply cfg_local_sim_ret; repeat split; reflexivity.
    - intros ? ? dvs _ (-> & -> & <-).
      eapply cfg_local_sim_bind with
        (RR := fun e1' e2' r1 r2 => e1' = e2' /\ r1 = r2).
      + revert env; induction dvs as [| [id dv] rest IH]; intros env; cbn [map_monad].
        * apply cfg_local_sim_ret; split; reflexivity.
        * eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
          intros ? ? [] [] (-> & -> & _).
          eapply cfg_local_sim_bind; [apply IH |].
          intros e1' e2' l1 l2 [-> ->]; apply cfg_local_sim_ret; split; reflexivity.
      + intros e1' e2' l1 l2 [-> ->]; apply cfg_local_sim_ret; split; reflexivity.
  Qed.

  (** ** Terminator Simulation *)

  Lemma select_switch_in
    (selector : @dvalue PaV) (default_br : block_id)
    (switches : list (@dvalue PaV * block_id)) :
    eou_ret_imp
      (fun bid => bid = default_br \/ In bid (List.map snd switches))
      (@select_switch PaV selector default_br switches).
  Proof.
    induction switches as [| [v id] rest IH]; cbn [select_switch].
    - cbn; left; reflexivity.
    - destruct selector as [db1 | |]; try exact I.
      destruct db1 as [p1 | sz1 i1 | ip1 | d1 | f1 | | | bsz1 bv1]; try exact I.
      destruct v as [db2 | |]; try exact I.
      destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2]; try exact I.
      destruct (Pos.eq_dec sz1 sz2) as [Heq | _]; [| exact I].
      subst sz2; cbn [eq_rec_r eq_rec eq_rect eq_rect_r eq_sym].
      match goal with |- context [if ?b then _ else _] => destruct b end.
      + cbn; right; left; reflexivity.
      + eapply eou_ret_imp_weaken; [| exact IH].
        intros b [-> | Hin]; [left; reflexivity | right; right; exact Hin].
  Qed.

  Lemma map_monad_switch_dests_snd
    (dests : list (tint_literal * block_id)) :
    eou_ret_imp
      (fun switches : list (@dvalue PaV * block_id) =>
         List.map snd switches = List.map snd dests)
      (map_monad
         (fun '((TInt_Literal sz x), id) =>
            s <- @coerce_integer_to_int PaV (Some sz) (denote_int_syntax x) ;;
            ret (DVALUE_Base s, id))
         dests).
  Proof.
    set (f := fun '((TInt_Literal sz x), id) =>
                s <- @coerce_integer_to_int PaV (Some sz) (denote_int_syntax x) ;;
                (ret (DVALUE_Base s, id) : EOU (@dvalue PaV * block_id))).
    change (eou_ret_imp
              (fun switches : list (@dvalue PaV * block_id) =>
                 List.map snd switches = List.map snd dests)
              (map_monad f dests)).
    induction dests as [| [[sz x] id] rest IH]; cbn [map_monad List.map snd].
    - reflexivity.
    - unfold f at 1.
      destruct (@coerce_integer_to_int PaV (Some sz) (denote_int_syntax x))
        as [| | | s]; cbn; try exact I.
      destruct (map_monad f rest) as [| | | sws]; cbn in IH |- *; try exact I.
      f_equal; exact IH.
  Qed.

  Lemma switch_target_eou_in
    (selector : @dvalue PaV) (default_br : block_id)
    (dests : list (tint_literal * block_id)) :
    eou_ret_imp
      (fun bid => In bid (default_br :: List.map snd dests))
      (switches <- map_monad
                     (fun '((TInt_Literal sz x), id) =>
                        s <- @coerce_integer_to_int PaV (Some sz) (denote_int_syntax x) ;;
                        ret (DVALUE_Base s, id))
                     dests ;;
       @select_switch PaV selector default_br switches).
  Proof.
    pose proof (map_monad_switch_dests_snd dests) as Hsw.
    destruct
      (map_monad
         (fun '((TInt_Literal sz x), id) =>
            s <- @coerce_integer_to_int PaV (Some sz) (denote_int_syntax x) ;;
            (ret (DVALUE_Base s, id) : EOU (@dvalue PaV * block_id)))
         dests) as [| | | switches];
      cbn in Hsw |- *; try exact I.
    rewrite <- Hsw; eapply eou_ret_imp_weaken; [| apply select_switch_in].
    intros b [-> | Hin]; [left; reflexivity | right; exact Hin].
  Qed.

  Lemma step_tenv_term_non_invoke
    (iid : instr_id) (tm : terminator dtyp) (md : list (metadata dtyp))
    (succ : block_id) (te : ty_env) :
    (match tm with TERM_Invoke _ _ _ _ _ _ => False | _ => True end) ->
    step_tenv_term (iid, tm, md) succ te = te.
  Proof.
    destruct iid, tm; intros H; try contradiction; reflexivity.
  Qed.

  Lemma cfg_local_sim_denote_terminator_sync
    (te : ty_env) (live_out : list raw_id)
    (env1 env2 : @local_env PaV)
    (trm : instr_id * terminator dtyp * list (metadata dtyp)) :
    let '(_, tm, _) := trm in
    tenv_sound te env1 ->
    env_agree_on (add_raw_ids (full_term_uses tm) live_out) env1 env2 ->
    cfg_local_sim
      (fun e1' e2' r1 r2 =>
         (env1 = env2 -> e1' = e2') /\
         r1 = r2 /\
         match r1 with
         | inl succ =>
             In succ (term_successors tm) /\
             tenv_sound (step_tenv_term trm succ te) e1' /\
             env_agree_on live_out e1' e2'
         | inr _ => True
         end)
      env1 env2 (denote_terminator trm) (denote_terminator trm).
  Proof.
    destruct trm as [[iid tm] md].
    intros Hte Hagree.
    apply env_agree_on_add_raw_ids_split in Hagree as [Huses Hlive].
    destruct tm as
      [ [dt op]
      |
      | [dt op] br1 br2
      | br
      | [dt e] default_br dests
      | [t addr] brs fn
      | [t expr]
      | [dt fnptrval] args to_label unwind_label anns obs
      | ];
      unfold denote_terminator; cbv beta iota zeta.
    - (* TERM_Ret *)
      cbn [full_term_uses full_texp_uses snd] in Huses.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some dt) op Huses) |].
      intros ? ? dv _ (-> & -> & <-).
      apply cfg_local_sim_ret;
        split; [intros Heq; exact Heq | split; [reflexivity | exact I]].
    - (* TERM_Ret_void *)
      apply cfg_local_sim_ret;
        split; [intros Heq; exact Heq | split; [reflexivity | exact I]].
    - (* TERM_Br *)
      cbn [full_term_uses full_texp_uses snd] in Huses.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some dt) op Huses) |].
      intros ? ? v _ (-> & -> & <-).
      destruct v as [db | |];
        [| apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync].
      destruct db as [p | sz cb | ip | d | f | | | bsz bv];
        [ apply cfg_local_sim_raise_sync | | apply cfg_local_sim_raise_sync
        | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync
        | | apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync ].
      + destruct sz as [p | p |];
          [apply cfg_local_sim_raise_sync | apply cfg_local_sim_raise_sync |].
        match goal with |- context [if ?b then _ else _] => destruct b end;
          apply cfg_local_sim_ret;
          (split; [intros Heq; exact Heq | split; [reflexivity |]]);
          rewrite (step_tenv_term_non_invoke iid (TERM_Br (dt, op) br1 br2) md _ te I);
          (split; [cbn; auto | exact (conj Hte Hlive)]).
      + apply cfg_local_sim_raiseUB_cut.
    - (* TERM_Br_1 *)
      apply cfg_local_sim_ret;
        split; [intros Heq; exact Heq | split; [reflexivity |]].
      rewrite (step_tenv_term_non_invoke iid (TERM_Br_1 br) md _ te I).
      split; [cbn; left; reflexivity | exact (conj Hte Hlive)].
    - (* TERM_Switch *)
      cbn [full_term_uses full_texp_uses snd] in Huses.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some dt) e Huses) |].
      intros ? ? selector _ (-> & -> & <-).
      destruct (dvalue_is_poison selector); [apply cfg_local_sim_raiseUB_cut |].
      eapply cfg_local_sim_bind;
        [apply (cfg_local_sim_EOU_ret_sync _ env1 env2 _
                  (switch_target_eou_in selector default_br dests)) |].
      intros ? ? bid _ (-> & -> & <- & Hbid).
      apply cfg_local_sim_ret;
        split; [intros Heq; exact Heq | split; [reflexivity |]].
      rewrite (step_tenv_term_non_invoke iid (TERM_Switch (dt, e) default_br dests) md _ te I).
      split; [exact Hbid | exact (conj Hte Hlive)].
    - (* TERM_IndirectBr *)
      cbn [full_term_uses full_texp_uses snd] in Huses.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some t) addr Huses) |].
      intros ? ? a _ (-> & -> & <-).
      destruct (dvalue_is_poison a); [apply cfg_local_sim_raiseUB_cut |].
      destruct fn as [f |]; [| apply cfg_local_sim_raise_sync].
      eapply cfg_local_sim_bind.
      + apply cfg_local_sim_map_monad_sync; intros b _.
        eapply cfg_local_sim_bind; [apply cfg_local_sim_gread_sync |].
        intros ? ? ba _ (-> & -> & <-); apply cfg_local_sim_ret; repeat split; reflexivity.
      + intros ? ? addrs _ (-> & -> & <-).
        destruct (dvalue_ptr_address a) as [z |]; [| apply cfg_local_sim_raise_sync].
        destruct (indirectbr_target z (combine brs addrs)) as [b |] eqn:Etgt;
          [| apply cfg_local_sim_raiseUB_cut].
        apply cfg_local_sim_ret;
          split; [intros Heq; exact Heq | split; [reflexivity |]].
        rewrite (step_tenv_term_non_invoke iid (TERM_IndirectBr (t, addr) brs (Some f)) md _ te I).
        split; [cbn; eapply indirectbr_target_In; exact Etgt | exact (conj Hte Hlive)].
    - (* TERM_Resume *)
      cbn [full_term_uses full_texp_uses snd] in Huses.
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 (Some t) expr Huses) |].
      intros ? ? exn _ (-> & -> & <-).
      apply cfg_local_sim_raiseLLVM_sync.
    - (* TERM_Invoke *)
      cbn [full_term_uses] in Huses.
      pose proof (env_agree_on_app_l _ _ _ _ Huses) as Hag_f.
      pose proof (env_agree_on_app_r _ _ _ _ Huses) as Hag_rest1.
      pose proof (env_agree_on_app_l _ _ _ _ Hag_rest1) as Hag_args.
      pose proof (env_agree_on_app_r _ _ _ _ Hag_rest1) as Hag_rest2.
      pose proof (env_agree_on_app_r _ _ _ _ Hag_rest2) as Hag_obs.
      cbn [full_texp_uses snd] in Hag_f.
      eapply cfg_local_sim_bind;
        [apply (cfg_local_sim_denote_call_args_sync env1 env2 args _ Hag_args) |].
      intros ? ? uvs _ (-> & -> & <-).
      eapply cfg_local_sim_bind;
        [apply (cfg_local_sim_denote_operand_bundles_sync env1 env2 _ fnptrval obs Hag_obs) |].
      intros ? ? _ _ (-> & -> & _).
      eapply cfg_local_sim_bind;
        [exact (cfg_local_sim_denote_exp_plain_sync env1 env2 None fnptrval Hag_f) |].
      intros ? ? fv _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_call_sync |].
      intros ? ? rv _ (-> & -> & <-).
      eapply cfg_local_sim_bind; [apply cfg_local_sim_check_call_return_sync |].
      intros ? ? rv' _ (-> & -> & <-).
      destruct rv' as [exn | returned_value].
      + (* Unwind branch -> unwind_label *)
        eapply cfg_local_sim_bind; [apply cfg_local_sim_stack_raise_sync |].
        intros ? ? _ _ (-> & -> & _).
        apply cfg_local_sim_ret;
          split; [intros Heq; exact Heq | split; [reflexivity |]].
        split; [cbn; right; left; reflexivity | split; [| exact Hlive]].
        destruct iid as [x | vid]; cbn [step_tenv_term]; [| exact Hte].
        rewrite raw_id_eqb_refl; cbn [negb]; rewrite andb_false_r.
        destruct (raw_id_eqb unwind_label to_label); cbn [negb];
          [apply tenv_sound_remove_ty_same, Hte | exact Hte].
      + (* Normal branch -> to_label *)
        destruct iid as [x | vid].
        * eapply cfg_local_sim_bind; [apply cfg_local_sim_lwrite_both |].
          intros ? ? _ _ (-> & -> & _).
          apply cfg_local_sim_ret; split; [intros ->; reflexivity | split; [reflexivity |]].
          split; [cbn; left; reflexivity |].
          split; [| apply env_agree_on_add_both_same, Hlive].
          cbn [step_tenv_term]; rewrite raw_id_eqb_refl; cbn [andb negb].
          destruct (raw_id_eqb to_label unwind_label); cbn [negb];
            [ apply tenv_sound_remove_ty_add, Hte
            | apply (tenv_sound_set_ty x None returned_value te env1 I Hte) ].
        * eapply cfg_local_sim_bind;
            [apply cfg_local_sim_ret; instantiate (1 := fun e1' e2' _ _ => e1' = env1 /\ e2' = env2); split; reflexivity |].
          intros ? ? _ _ (-> & ->).
          apply cfg_local_sim_ret;
            split; [intros Heq; exact Heq | split; [reflexivity |]].
          cbn [step_tenv_term]; split; [cbn; left; reflexivity | exact (conj Hte Hlive)].
    - (* TERM_Unreachable *)
      apply cfg_local_sim_raiseUB_cut.
  Qed.

  (** ** Validator Soundness & Whole-CFG Iteration Simulation *)

  Lemma denote_cfg_refl_sim
    (c : CFG.cfg dtyp) (va : option (@ptr (@PROV PaV) (@PTR PaV))) (env : @local_env PaV) :
    cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
      env env (denote_cfg c va) (denote_cfg c va).
  Proof.
    unfold denote_cfg, denote_cfg_map, denote_ocfg_map.
    eapply cfg_local_sim_bind.
    - eapply (cfg_local_sim_iter
                (fun e1 e2 (s1 s2 : block_id * block_id) => e1 = e2 /\ s1 = s2)
                (fun _ _ r1 r2 => r1 = r2));
        [| split; reflexivity].
      intros env1 env2 [bid_from bid_src] s2 [<- <-].
      destruct (RM.find bid_src (ocfg_map (blks c))) as [bk_src |].
      + eapply cfg_local_sim_bind with
          (RR := fun e1' e2' bd1 bd2 => e1' = e2' /\ bd1 = bd2).
        * unfold denote_block.
          eapply cfg_local_sim_bind; [apply denote_phis_refl_sim |].
          intros e1' e2' _ _ [<- _].
          eapply cfg_local_sim_bind; [apply denote_code_refl_sim |].
          intros e1'' e2'' _ _ [<- _].
          destruct (blk_term bk_src) as [[tiid tm] tmd].
          eapply cfg_local_sim_weaken;
            [| apply (cfg_local_sim_denote_terminator_sync
                        [] [] e1'' e1'' (tiid, tm, tmd)
                        (tenv_sound_nil e1'') (env_agree_on_refl _ e1''))].
          intros ? ? ? ? (Heq & <- & _); split; [exact (Heq Logic.eq_refl) | reflexivity].
        * intros e1' e2' [bid_tgt | dv] _ [<- <-];
            apply cfg_local_sim_ret; cbn; auto.
      + apply cfg_local_sim_ret; cbn; reflexivity.
    - intros ? ? [bid | uv] _ <-;
        [apply cfg_local_sim_raise_sync | apply cfg_local_sim_ret; reflexivity].
  Qed.

  Lemma check_fwd_cfg_init
    (fargs : list local_id) (reach : list block_id)
    (fm : fwd_map) (c : CFG.cfg dtyp) :
    check_fwd_cfg fargs reach fm c = true ->
    in_raw_ids (init c) reach = true /\
    (forall bk_init,
       find_block (blks c) (init c) = Some bk_init ->
       tenv_subsumes
         (lookup_fwd (init c) fm)
         (step_tenv_phis_from (init c) (blk_phis bk_init) (init_tenv fargs)) = true).
  Proof.
    unfold check_fwd_cfg; intros Hchk.
    apply andb_true_iff in Hchk as [Hchk _].
    apply andb_true_iff in Hchk as [Hreach Hinit].
    split; [exact Hreach |].
    intros bk_init Efind; rewrite Efind in Hinit; exact Hinit.
  Qed.

  Lemma check_fwd_cfg_edge
    (fargs : list local_id) (reach : list block_id)
    (fm : fwd_map) (c : CFG.cfg dtyp)
    (bk : block dtyp) (succ : block_id) :
    check_fwd_cfg fargs reach fm c = true ->
    In bk (blks c) ->
    in_raw_ids (blk_id bk) reach = true ->
    In succ (block_successors bk) ->
    in_raw_ids succ reach = true /\
    (forall bk_succ,
       find_block (blks c) succ = Some bk_succ ->
       let te_end := step_tenv_code (lookup_fwd (blk_id bk) fm) (blk_code bk) in
       let te_edge := step_tenv_term (blk_term bk) succ te_end in
       tenv_subsumes
         (lookup_fwd succ fm)
         (step_tenv_phis_from (blk_id bk) (blk_phis bk_succ) te_edge) = true).
  Proof.
    unfold check_fwd_cfg; intros Hchk Hin_bk Hreach Hsucc.
    apply andb_true_iff in Hchk as [_ Hall].
    rewrite forallb_forall in Hall.
    specialize (Hall bk Hin_bk); rewrite Hreach in Hall.
    cbv zeta in Hall; rewrite forallb_forall in Hall.
    specialize (Hall succ Hsucc).
    apply andb_true_iff in Hall as [Hr_succ Hsub].
    split; [exact Hr_succ |].
    intros bk_succ Efind; rewrite Efind in Hsub; exact Hsub.
  Qed.

  Lemma check_live_cfg_edge
    (fargs : list local_id) (reach : list block_id)
    (fm : fwd_map) (lm : live_map) (c : CFG.cfg dtyp)
    (bk bk_succ : block dtyp) (succ : block_id) :
    check_live_cfg fargs reach fm lm c = true ->
    In bk (blks c) ->
    in_raw_ids (blk_id bk) reach = true ->
    In succ (block_successors bk) ->
    find_block (blks c) succ = Some bk_succ ->
    let '(live_code_s, bk_dce_s) := dce_block_info fargs reach fm lm c bk_succ in
    raw_ids_subset
      (edge_live_req (blk_id bk) (blk_phis bk_dce_s) live_code_s)
      (lookup_live (blk_id bk) lm) = true.
  Proof.
    unfold check_live_cfg; intros Hchk Hin_bk Hreach Hsucc Efind.
    rewrite forallb_forall in Hchk.
    specialize (Hchk bk Hin_bk); rewrite Hreach in Hchk.
    rewrite forallb_forall in Hchk.
    specialize (Hchk succ Hsucc); rewrite Efind in Hchk;
      destruct (dce_block_info fargs reach fm lm c bk_succ); exact Hchk.
  Qed.

  Definition dce_iter_inv
    (fargs : list local_id) (reach : list block_id)
    (fm : fwd_map) (lm : live_map) (c : CFG.cfg dtyp)
    (env1 env2 : @local_env PaV)
    (s1 s2 : block_id * block_id) : Prop :=
    s1 = s2 /\
    let '(bid_from, bid_src) := s1 in
    in_raw_ids bid_src reach = true /\
    exists te_edge : ty_env,
      In (bid_from, te_edge) (incoming_edges_for fargs reach fm c bid_src) /\
      tenv_sound te_edge env1 /\
      (forall bk_src : block dtyp,
         find_block (blks c) bid_src = Some bk_src ->
         tenv_subsumes
           (lookup_fwd bid_src fm)
           (step_tenv_phis_from bid_from (blk_phis bk_src) te_edge) = true /\
         let '(live_code_s, bk_dce_s) :=
           dce_block_info fargs reach fm lm c bk_src in
         env_agree_on
           (edge_live_req bid_from (blk_phis bk_dce_s) live_code_s)
           env1 env2).

  Lemma dce_cfg_once_sim
    (fargs : list local_id) (c : CFG.cfg dtyp)
    (env : @local_env PaV) (va : option (@ptr (@PROV PaV) (@PTR PaV))) :
    (forall x, In x fargs -> exists v, Maps.lookup x env = Some v) ->
    cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
      env env (denote_cfg c va) (denote_cfg (dce_cfg_once fargs c) va).
  Proof.
    intros Henv; unfold dce_cfg_once; cbn zeta.
    destruct (cfg_no_block_addresses c && nodup_raw_ids (List.map blk_id (blks c)));
      [| apply denote_cfg_refl_sim].
    set (reach := compute_reach c).
    set (fm := compute_fwd_tenv fargs reach c).
    set (lm := compute_live_out fargs reach fm c).
    destruct (check_fwd_cfg fargs reach fm c) eqn:Efwd; cbn [andb];
      [| apply denote_cfg_refl_sim].
    destruct (check_live_cfg fargs reach fm lm c) eqn:Elive;
      [| apply denote_cfg_refl_sim].
    unfold denote_cfg, denote_cfg_map, denote_ocfg_map; cbn [init blks].
    eapply cfg_local_sim_bind.
    - eapply (cfg_local_sim_iter
                (dce_iter_inv fargs reach fm lm c)
                (fun _ _ r1 r2 => r1 = r2)).
      + (* Loop body simulation *)
        intros env1 env2 [bid_from bid_src] s2
          (<- & Hreach & te_edge & Hin_edge & Hte_edge & Hbk_inv).
        rewrite !(@ocfg_map_find_block dtyp).
        rewrite (@find_block_map dtyp (dce_block fargs reach fm lm c)
                   (blks c) bid_src (dce_block_id fargs reach fm lm c)).
        destruct (find_block (blks c) bid_src) as [bk_src |] eqn:Efind;
          cbn [option_map].
        * pose proof (@find_block_has_id dtyp (blks c) bid_src bk_src Efind) as Hbid.
          pose proof (@find_block_In' dtyp (blks c) bid_src bk_src Efind) as Hin_bk.
          specialize (Hbk_inv bk_src Logic.eq_refl) as [Hsub_in Hag_in].
          subst bid_src.
          unfold dce_block; unfold dce_block_info in Hag_in |- *; cbn zeta in Hag_in |- *.
          rewrite Hreach in Hag_in |- *.
          set (te_in := lookup_fwd (blk_id bk_src) fm) in *.
          set (live_end := block_live_before_term bk_src lm) in *.
          set (edges := incoming_edges_for fargs reach fm c (blk_id bk_src)) in *.
          pose proof (dce_code_sim (blk_code bk_src) va te_in live_end) as Hcode_sim.
          destruct (dce_code te_in (blk_code bk_src) live_end) as [live_code code'].
          cbn [snd blk_phis] in Hag_in |- *.
          eapply cfg_local_sim_bind with
            (RR := fun e1_t e2_t bd1 bd2 =>
                     bd1 = bd2 /\
                     match bd1 with
                     | inl bid_tgt =>
                         In bid_tgt (block_successors bk_src) /\
                         tenv_sound
                           (step_tenv_term (blk_term bk_src) bid_tgt
                              (step_tenv_code te_in (blk_code bk_src)))
                           e1_t /\
                         env_agree_on (lookup_live (blk_id bk_src) lm) e1_t e2_t
                     | inr _ => True
                     end).
          -- (* Block body: phis ;; code ;; term *)
             unfold denote_block; cbn [blk_phis blk_code blk_term].
             eapply cfg_local_sim_bind;
               [exact (dce_phis_sim edges bid_from te_edge live_code
                         (blk_phis bk_src) env1 env2 Hin_edge Hte_edge Hag_in) |].
             intros e1_p e2_p u1_p u2_p [Hte_p Hag_p].
             assert (Hte_in : tenv_sound te_in e1_p)
               by exact (tenv_sound_subsumes _ _ e1_p Hsub_in Hte_p).
             eapply cfg_local_sim_bind;
               [exact (Hcode_sim e1_p e2_p Hte_in Hag_p) |].
             intros e1_c e2_c u1_c u2_c [Hte_c Hag_c].
             unfold live_end, block_live_before_term in Hag_c.
             unfold block_successors.
             pose proof (cfg_local_sim_denote_terminator_sync
                           (step_tenv_code te_in (blk_code bk_src))
                           (lookup_live (blk_id bk_src) lm)
                           e1_c e2_c (blk_term bk_src)) as Hterm_sim.
             destruct (blk_term bk_src) as [[tiid tm] tmd].
             eapply cfg_local_sim_weaken;
               [| exact (Hterm_sim Hte_c Hag_c)].
             intros e1_t e2_t bd1 bd2 (_ & <- & Hbd); exact (conj Logic.eq_refl Hbd).
          -- (* Transition to next block or return *)
             intros e1_t e2_t [bid_tgt | dv] _ [<- Hbd].
             ++ destruct Hbd as (Hsucc & Hte_next & Hag_out).
                apply cfg_local_sim_ret; cbn [iter_step_rel].
                destruct (check_fwd_cfg_edge fargs reach fm c bk_src bid_tgt
                            Efwd Hin_bk Hreach Hsucc) as [Hreach_tgt Hfwd_tgt].
                split; [reflexivity | split; [exact Hreach_tgt |]].
                exists (step_tenv_term (blk_term bk_src) bid_tgt
                          (step_tenv_code te_in (blk_code bk_src))).
                split.
                ** unfold incoming_edges_for; apply in_or_app; right.
                   apply in_flat_map; exists bk_src; split; [exact Hin_bk |].
                   rewrite Hreach, (proj2 (in_raw_ids_spec bid_tgt _) Hsucc); cbn [andb].
                   left; reflexivity.
                ** split; [exact Hte_next |].
                   intros bk_tgt Efind_tgt.
                   split; [exact (Hfwd_tgt bk_tgt Efind_tgt) |].
                   pose proof (check_live_cfg_edge fargs reach fm lm c
                                 bk_src bk_tgt bid_tgt
                                 Elive Hin_bk Hreach Hsucc Efind_tgt) as Hsub_live.
                   destruct (dce_block_info fargs reach fm lm c bk_tgt)
                     as [live_code_t bk_dce_t].
                   exact (env_agree_on_subset _ _ e1_t e2_t
                            (raw_ids_subset_spec _ _ Hsub_live) Hag_out).
             ++ apply cfg_local_sim_ret; cbn [iter_step_rel]; reflexivity.
        * apply cfg_local_sim_ret; cbn [iter_step_rel]; reflexivity.
      + (* Initial state invariant *)
        destruct (check_fwd_cfg_init fargs reach fm c Efwd) as [Hreach_init Hfwd_init].
        split; [reflexivity | split; [exact Hreach_init |]].
        exists (init_tenv fargs).
        split.
        * unfold incoming_edges_for; rewrite raw_id_eqb_refl; left; reflexivity.
        * split; [exact (init_tenv_sound fargs env Henv) |].
          intros bk_init Efind_init.
          split; [exact (Hfwd_init bk_init Efind_init) |].
          destruct (dce_block_info fargs reach fm lm c bk_init).
          apply env_agree_on_refl.
    - intros ? ? [bid | uv] _ <-;
        [apply cfg_local_sim_raise_sync | apply cfg_local_sim_ret; reflexivity].
  Qed.

End DCESoundness.

(** * 9. Module-Level Dead Code Elimination Pass & Soundness Theorem *)

Definition dce_mcfg_once (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  map_mcfg_with_args dce_cfg_once M.

Lemma dce_mcfg_once_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (dce_mcfg_once M).
Proof.
  intros IP IPT M.
  exact (@lift_cfg_with_args_local_pass IP IPT
           dce_cfg_once
           dce_cfg_once_block_addresses
           (@dce_cfg_once_sim IP IPT)
           M).
Qed.

(** Three rounds of whole-CFG backward/forward DCE eliminate multi-block and
    cyclic dead [Phi]/[INSTR_Op] chains in a single pass invocation. *)
Definition dce_mcfg (M : CFG.mcfg dtyp) : CFG.mcfg dtyp :=
  dce_mcfg_once (dce_mcfg_once (dce_mcfg_once M)).

Definition dce_mcfg_typ (M : CFG.mcfg typ) : CFG.mcfg dtyp :=
  dce_mcfg (convert_types M).

Theorem dce_mcfg_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (dce_mcfg M).
Proof.
  intros IP IPT M; unfold dce_mcfg.
  eapply (@prog_refines_trans IP IPT); [apply dce_mcfg_once_refines |].
  eapply (@prog_refines_trans IP IPT); [apply dce_mcfg_once_refines |].
  apply dce_mcfg_once_refines.
Qed.
