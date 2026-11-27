(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Mem2Reg Semantic Model & Interpreter Combinators ([CertPasses.Mem2RegModel])

    Purpose:
      Proves strong bisimulation laws for [interp_mrec], [interp_mcfg_model],
      and [interp_cfg_model], [refine_prov] combinators with [tau_star],
      primitive event reductions, and the [interp_cfg_exc] layer.

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml. Supports [Mem2Reg] soundness
      under [refine_prov] without [Eqdep] or [JMeq].

    Assumptions:
      Parametric over [IP : IPtr] and [IPT : @IPtrTheory IP]; depends on
      [PassCommon] and [Vellvm]; zero custom axioms or [Admitted].

    Section Outline:
      - [BindCompat] and [mrec_ctx].
      - [ModelCombinators]: interpreter equations, [refine_prov]/[tau_star]
        combinators, primitive reductions, and [interp_cfg_exc] lemmas. *)

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
  Structures.Functor
  Data.Monads.EitherMonad.

From Vellvm Require Import
  Numeric
  Utils
  Syntax
  Semantics
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
  Semantics.Implementations.Sizeof
  Semantics.Implementations.Memory
  Semantics.Handlers
  Semantics.InterpretationStack
  Semantics.TopLevel
  Semantics.Libraries.

From CertPasses Require Import PassCommon.
Import Logic.

Set Default Goal Selector "!".
Unset Implicit Arguments.

(** * 2. Provenance-Model & Interpreter Combinators *)

Section BindCompat.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  Lemma m2r_refine_prov_bind {R1 R2 S1 S2}
    (RR : list N -> R1 -> R2 -> Prop) (RS : list N -> S1 -> S2 -> Prop)
    (U : list N)
    (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2)
    (k1 : R1 -> itree ProvBotE S1) (k2 : R2 -> itree ProvBotE S2)
    (Ht : refine_prov RR U t1 t2)
    (Hk : forall U' r1 r2, RR U' r1 r2 -> refine_prov RS U' (k1 r1) (k2 r2)) :
    refine_prov RS U (ITree.bind t1 k1) (ITree.bind t2 k2).
  Proof using.
    eapply PassCommonModel.refine_prov_bind; [exact Ht |].
    intros U' r1 r2 _ HR; exact (Hk U' r1 r2 HR).
  Qed.
End BindCompat.

#[local] Notation refine_prov_bind := m2r_refine_prov_bind (only parsing).

Definition mrec_ctx {IP : IPtr} {IPT : @IPtrTheory IP}
  (fundefs : IntMap (@function_denotation (@ParamsV IP IPT)))
  : @CallE (@ParamsV IP IPT) ~> @CFGtop (@ParamsV IP IPT) :=
  fun T call_ev =>
    match call_ev with
    | Call dt cc fv args =>
        @ExtLib.Structures.Monad.bind (@CFGtop (@ParamsV IP IPT)) _ _ _
          (EOU_to_itree (check_callee fv))
          (fun _ =>
             match lookup_defn fv fundefs with
             | Some f_den => f_den cc args
             | None => Functor.fmap inr (external_call dt fv args)
             end)
    end.

Section ModelCombinators.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Existing Instance MemoryModelStateV.
  #[local] Existing Instance MemoryModelPrimitivesV.
  #[local] Existing Instance PointerV.
  #[local] Existing Instance PIV.
  #[local] Existing Instance PITheoryV.
  #[local] Hint Resolve refine_prov__mon : paco.
  Arguments memM_interp_prov {_ _} [T] _ _.
  Arguments interp_vellvm_prov_h {_ _} [T] _ _.

  (** ** Strong Bisimulation Equations for [interp_mrec], [interp_mcfg_model], [interp_cfg_model] *)

  Lemma interp_mrec_ret {D E : Type -> Type} (ctx : D ~> itree (D +' E)) {R} (x : R) :
    interp_mrec ctx (Ret x) ≅ Ret x.
  Proof using.
    rewrite unfold_interp_mrec; reflexivity.
  Qed.

  Lemma interp_mrec_tau {D E : Type -> Type} (ctx : D ~> itree (D +' E)) {R}
    (t : itree (D +' E) R) :
    interp_mrec ctx (Tau t) ≅ Tau (interp_mrec ctx t).
  Proof using.
    rewrite unfold_interp_mrec; reflexivity.
  Qed.

  Lemma interp_mrec_proper_eq {D E : Type -> Type} (ctx : D ~> itree (D +' E)) {R} :
    forall (t1 t2 : itree (D +' E) R),
      t1 ≅ t2 ->
      interp_mrec ctx t1 ≅ interp_mrec ctx t2.
  Proof using.
    ginit; gcofix CIH; intros t1 t2 Heq.
    rewrite (unfold_interp_mrec ctx _ t1), (unfold_interp_mrec ctx _ t2).
    punfold Heq; red in Heq.
    destruct Heq as [r1 r2 <- | m1 m2 Hm | X [d | e] k1 k2 Hk | ? ? Hchk _ | ? ? Hchk _]; try inversion Hchk; pclearbot.
    - gstep; constructor; reflexivity.
    - gstep; constructor; gfinal; left; apply CIH, Hm.
    - gstep; constructor; gfinal; left; apply CIH.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros x _ <-; apply Hk.
    - gstep; constructor; intros x; gstep; constructor; gfinal; left; apply CIH, Hk.
  Qed.

  Lemma interp_mrec_bind_eq {D E : Type -> Type} (ctx : D ~> itree (D +' E)) {R S} :
    forall (t : itree (D +' E) R) (k : R -> itree (D +' E) S),
      interp_mrec ctx (ITree.bind t k) ≅
      ITree.bind (interp_mrec ctx t) (fun x => interp_mrec ctx (k x)).
  Proof using.
    ginit; gcofix CIH; intros t k.
    rewrite (unfold_interp_mrec ctx _ t).
    destruct (observe t) as [rv | m | X [d | e] h] eqn:Hot; cbn [_interp_mrec].
    - assert (Htk : ITree.bind t k ≅ k rv).
      { rewrite (itree_eta t), Hot, Eqit.bind_ret_l; reflexivity. }
      rewrite (interp_mrec_proper_eq ctx _ _ Htk), Eqit.bind_ret_l.
      gfinal; right; apply pacobot2; match goal with |- _ ?lhs ?rhs => change (eq_itree eq lhs rhs); reflexivity end.
    - rewrite (unfold_interp_mrec ctx _ (ITree.bind t k)), observe_bind, Hot; cbn [_interp_mrec].
      rewrite Eqit.bind_tau.
      gstep; constructor; gfinal; left; apply CIH.
    - rewrite (unfold_interp_mrec ctx _ (ITree.bind t k)), observe_bind, Hot; cbn [_interp_mrec].
      rewrite Eqit.bind_tau.
      gstep; constructor.
      rewrite <- (interp_mrec_proper_eq ctx _ _ (Eqit.bind_bind (ctx X d) h k)).
      gfinal; left; apply CIH.
    - rewrite (unfold_interp_mrec ctx _ (ITree.bind t k)), observe_bind, Hot; cbn [_interp_mrec].
      rewrite Eqit.bind_vis.
      gstep; constructor; intros x.
      rewrite Eqit.bind_tau.
      gstep; constructor; gfinal; left; apply CIH.
  Qed.

  Lemma interp_mcfg_model_ret {R} (x : R) (s : FusedS) :
    interp_mcfg_model (Ret x) s ≅ Ret (s, x).
  Proof using.
    unfold interp_mcfg_model, interp_intrinsics.
    rewrite interp_ret, interp_state_ret; reflexivity.
  Qed.

  Lemma interp_mcfg_model_tau {R} (t : @MCFGtop (@ParamsV IP IPT) R) (s : FusedS) :
    interp_mcfg_model (Tau t) s ≅ Tau (interp_mcfg_model t s).
  Proof using.
    unfold interp_mcfg_model, interp_intrinsics.
    rewrite interp_tau, interp_state_tau; reflexivity.
  Qed.

  Lemma interp_mcfg_model_bind {R S}
    (t : @MCFGtop (@ParamsV IP IPT) R)
    (k : R -> @MCFGtop (@ParamsV IP IPT) S) (s : FusedS) :
    interp_mcfg_model (ITree.bind t k) s ≅
    ITree.bind (interp_mcfg_model t s) (fun '(s', x) => interp_mcfg_model (k x) s').
  Proof using.
    unfold interp_mcfg_model, interp_intrinsics.
    rewrite interp_bind, interp_state_bind; eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [s' x] ? <-; cbn [fst snd]; reflexivity].
  Qed.

  Lemma interp_mcfg_model_obs_eq {R}
    (t1 t2 : @MCFGtop (@ParamsV IP IPT) R) (s : FusedS) :
    t1 ≅ t2 ->
    interp_mcfg_model t1 s ≅ interp_mcfg_model t2 s.
  Proof using.
    intros Heq; unfold interp_mcfg_model, interp_intrinsics.
    rewrite Heq; reflexivity.
  Qed.

  Definition interp_cfg_model {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t : @CFGtop (@ParamsV IP IPT) R) (s : FusedS)
    : itree ProvBotE (Res R) :=
    interp_mcfg_model (interp_mrec (mrec_ctx ctx) t) s.

  Lemma denote_mcfg_eq_interp_mrec
    (fundefs : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (fv : @dvalue (@ParamsV IP IPT))
    (args : list (@dvalue (@ParamsV IP IPT))) :
    denote_mcfg fundefs dt fv args =
    interp_mrec (mrec_ctx fundefs) (mrec_ctx fundefs _ (Call dt CC_Ccc fv args)).
  Proof using.
    unfold denote_mcfg, mrec; reflexivity.
  Qed.

  Lemma interp_cfg_model_ret {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : R) (s : FusedS) :
    interp_cfg_model ctx (Ret x) s ≅ Ret (s, x).
  Proof using.
    unfold interp_cfg_model.
    rewrite (interp_mcfg_model_obs_eq _ _ s (interp_mrec_ret (mrec_ctx ctx) x)).
    apply interp_mcfg_model_ret.
  Qed.

  Lemma interp_cfg_model_tau {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t : @CFGtop (@ParamsV IP IPT) R) (s : FusedS) :
    interp_cfg_model ctx (Tau t) s ≅ Tau (interp_cfg_model ctx t s).
  Proof using.
    unfold interp_cfg_model.
    rewrite (interp_mcfg_model_obs_eq _ _ s (interp_mrec_tau (mrec_ctx ctx) t)).
    apply interp_mcfg_model_tau.
  Qed.

  Lemma interp_cfg_model_bind {R S}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t : @CFGtop (@ParamsV IP IPT) R)
    (k : R -> @CFGtop (@ParamsV IP IPT) S) (s : FusedS) :
    interp_cfg_model ctx (ITree.bind t k) s ≅
    ITree.bind (interp_cfg_model ctx t s) (fun '(s', x) => interp_cfg_model ctx (k x) s').
  Proof using.
    unfold interp_cfg_model.
    rewrite (interp_mcfg_model_obs_eq _ _ s (interp_mrec_bind_eq (mrec_ctx ctx) t k)).
    apply interp_mcfg_model_bind.
  Qed.

  Lemma interp_cfg_model_obs_eq {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t1 t2 : @CFGtop (@ParamsV IP IPT) R) (s : FusedS) :
    t1 ≅ t2 ->
    interp_cfg_model ctx t1 s ≅ interp_cfg_model ctx t2 s.
  Proof using.
    intros Heq; unfold interp_cfg_model.
    apply interp_mcfg_model_obs_eq, interp_mrec_proper_eq, Heq.
  Qed.

  (** ** [refine_prov] Combinators & Finite-Tau Closure ([tau_star]) *)

  Lemma refine_prov_ret {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (r1 : R1) (r2 : R2) :
    RR U r1 r2 ->
    refine_prov RR U (Ret r1) (Ret r2).
  Proof using.
    intros H; pstep; apply RP_Step; cbn; exact H.
  Qed.

  Lemma refine_prov_tau_l {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (m1 : itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    refine_prov RR U m1 t2 ->
    refine_prov RR U (Tau m1) t2.
  Proof using.
    intros H; punfold H; pstep.
    eapply RP_TauL; [reflexivity | eapply refine_prov__mon; [exact H | auto]].
  Qed.

  Lemma refine_prov_tau_r {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (m2 : itree ProvBotE R2) :
    refine_prov RR U t1 m2 ->
    refine_prov RR U t1 (Tau m2).
  Proof using.
    intros H; punfold H; pstep.
    eapply RP_TauR; [reflexivity | eapply refine_prov__mon; [exact H | auto]].
  Qed.

  Lemma refine_prov_tau_both {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (m1 : itree ProvBotE R1) (m2 : itree ProvBotE R2) :
    refine_prov RR U m1 m2 ->
    refine_prov RR U (Tau m1) (Tau m2).
  Proof using.
    intros H; pstep; apply RP_Step; cbn; left; exact H.
  Qed.

  Lemma refine_prov_ub_vis_l {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) {X} (e : ProvBotE X) (k1 : X -> itree ProvBotE R1)
    (t2 : itree ProvBotE R2) :
    is_ub_prov e = true ->
    refine_prov RR U (Vis e k1) t2.
  Proof using.
    intros Hub; pstep; apply RP_Step; cbn; left; exact Hub.
  Qed.

  Lemma refine_prov_fresh_both {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (k1 : N -> itree ProvBotE R1) (k2 : N -> itree ProvBotE R2) :
    (forall p : N, ~ In p U -> refine_prov RR (p :: U) (k1 p) (k2 p)) ->
    refine_prov RR U (Vis (inl1 FreshProv) k1) (Vis (inl1 FreshProv) k2).
  Proof using.
    intros Hk; pstep; apply RP_Step; cbn.
    right; right; intros p Hp; left; apply Hk, Hp.
  Qed.

  Lemma refine_prov_fresh_l {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (k1 : N -> itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    (forall p : N, ~ In p U -> refine_prov RR (p :: U) (k1 p) t2) ->
    refine_prov RR U (Vis (inl1 FreshProv) k1) t2.
  Proof using.
    intros Hk; pstep; apply RP_Step; cbn.
    right; left; intros p Hp; left; apply Hk, Hp.
  Qed.

  Lemma refine_prov_incl {R1 R2} (RR : list N -> R1 -> R2 -> Prop) :
    forall (U0 U : list N) (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2),
      incl U0 U ->
      refine_prov RR U t1 t2 ->
      refine_prov (fun U' r1 r2 => incl U0 U' /\ RR U' r1 r2) U t1 t2.
  Proof using.
    intros U0; pcofix CIH.
    intros U t1 t2 Hincl Hrel; pstep; punfold Hrel.
    revert Hincl;
      induction Hrel as [U t1 t2 Hstep | U t1 m1 t2 Ht1 _ IH | U t1 t2 m2 Ht2 _ IH];
      intros Hincl.
    - apply RP_Step; unfold rp_step_body in *.
      destruct (observe t1) as [x1 | m1 | X1 e1 k1].
      + destruct (observe t2); try contradiction; split; assumption.
      + destruct (observe t2); try contradiction; pclearbot; right; eapply CIH; eassumption.
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left; destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hleft p Hp); pclearbot; right; eapply CIH; [| exact Hleft].
          intros z Hz; right; apply Hincl, Hz.
        * right; right; destruct (observe t2) as [x2 | m2 | X2 e2 k2]; try contradiction.
          destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
          -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot; right; eapply CIH; [| exact Hboth].
             intros z Hz; right; apply Hincl, Hz.
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot; right; eapply CIH; [| exact HA].
             intros z Hz; apply in_app_iff; right; apply Hincl, Hz.
    - eapply RP_TauL; [exact Ht1 | apply IH, Hincl].
    - eapply RP_TauR; [exact Ht2 | apply IH, Hincl].
  Qed.

  Lemma refine_prov_weaken_incl {R1 R2}
    (RR RR' : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2)
    (Hrel : refine_prov RR U t1 t2)
    (Himp : forall U' r1 r2, incl U U' -> RR U' r1 r2 -> RR' U' r1 r2) :
    refine_prov RR' U t1 t2.
  Proof using.
    eapply refine_prov_obs_eq;
      [apply Eqit.bind_ret_r | apply Eqit.bind_ret_r |].
    eapply PassCommonModel.refine_prov_bind; [exact Hrel |].
    intros U' r1 r2 Hincl Hr; apply refine_prov_ret; exact (Himp U' r1 r2 Hincl Hr).
  Qed.

  Lemma refine_prov_weaken {R1 R2}
    (RR RR' : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2)
    (Hrel : refine_prov RR U t1 t2)
    (Himp : forall U' r1 r2, RR U' r1 r2 -> RR' U' r1 r2) :
    refine_prov RR' U t1 t2.
  Proof using.
    eapply refine_prov_weaken_incl; [exact Hrel |].
    intros U' r1 r2 _ Hr; exact (Himp U' r1 r2 Hr).
  Qed.

  Lemma refine_prov_iter {I1 I2 R1 R2}
    (RI : list N -> I1 -> I2 -> Prop)
    (RR : list N -> R1 -> R2 -> Prop)
    (b1 : I1 -> itree ProvBotE (I1 + R1))
    (b2 : I2 -> itree ProvBotE (I2 + R2))
    (U0 : list N)
    (Hbody : forall U i1 i2,
               incl U0 U ->
               RI U i1 i2 ->
               refine_prov
                 (fun U' lr1 lr2 =>
                    match lr1, lr2 with
                    | inl j1, inl j2 => RI U' j1 j2
                    | inr r1, inr r2 => RR U' r1 r2
                    | _, _ => False
                    end)
                 U (b1 i1) (b2 i2)) :
    forall i1 i2,
      RI U0 i1 i2 ->
      refine_prov RR U0 (ITree.iter b1 i1) (ITree.iter b2 i2).
  Proof using.
    set (RBody := fun U' (lr1 : I1 + R1) (lr2 : I2 + R2) =>
                    incl U0 U' /\
                    match lr1, lr2 with
                    | inl j1, inl j2 => RI U' j1 j2
                    | inr r1, inr r2 => RR U' r1 r2
                    | _, _ => False
                    end).
    set (k1 := fun lr : I1 + R1 =>
                 match lr with
                 | inl j => Tau (ITree.iter b1 j)
                 | inr r => Ret r
                 end).
    set (k2 := fun lr : I2 + R2 =>
                 match lr with
                 | inl j => Tau (ITree.iter b2 j)
                 | inr r => Ret r
                 end).
    set (r_it := fun U (t1 : itree ProvBotE R1) (t2 : itree ProvBotE R2) =>
                   exists u1 u2,
                     ITree.bind u1 k1 ≅ t1 /\
                     ITree.bind u2 k2 ≅ t2 /\
                     refine_prov RBody U u1 u2).
    assert (Hr_eq : forall U a1 a1' a2 a2',
                      a1 ≅ a1' -> a2 ≅ a2' -> r_it U a1 a2 -> r_it U a1' a2').
    { intros U a1 a1' a2 a2' E1 E2 (u1 & u2 & Eu1 & Eu2 & Hu).
      exists u1, u2; split; [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hu]]. }
    assert (Hcore : forall U t1 t2, r_it U t1 t2 -> refine_prov RR U t1 t2).
    { pcofix CIH.
      intros U t1 t2 (u1 & u2 & Eu1 & Eu2 & Hu); pstep.
      eapply refine_prov__mon with (r := r_it);
        [| intros U' a1 a2 Hr; right; apply CIH, Hr].
      eapply refine_prov__obs_eq; [exact Hr_eq | exact Eu1 | exact Eu2 |].
      punfold Hu; clear t1 t2 Eu1 Eu2.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [lr1 | m1 | X1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [lr2 | m2 | X2 e2 h2] eqn:Hou2; try contradiction.
          destruct Hstep as [Hincl Hlr].
          destruct lr1 as [j1 | r1], lr2 as [j2 | r2]; try contradiction.
          * apply RP_Step; unfold rp_step_body; rewrite !observe_bind, Hou1, Hou2; cbn.
            exists (b1 j1), (b2 j2).
            split; [symmetry; apply unfold_iter |].
            split; [symmetry; apply unfold_iter |].
            apply refine_prov_incl; [exact Hincl | apply Hbody; assumption].
          * apply RP_Step; unfold rp_step_body; rewrite !observe_bind, Hou1, Hou2; cbn; exact Hlr.
        + destruct (observe u2) as [lr2 | m2 | X2 e2 h2] eqn:Hou2; try contradiction.
          pclearbot; apply RP_Step; unfold rp_step_body; rewrite !observe_bind, Hou1, Hou2.
          exists m1, m2; split; [reflexivity | split; [reflexivity | exact Hstep]].
        + apply RP_Step; unfold rp_step_body; rewrite (observe_bind u1 k1), Hou1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            exists (h1 p), u2; split; [reflexivity | split; [reflexivity | exact Hleft]].
          * right; right; destruct (observe u2) as [lr2 | m2 | X2 e2 h2] eqn:Hou2; try contradiction.
            rewrite (observe_bind u2 k2), Hou2.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               exists (h1 p), (h2 p); split; [reflexivity | split; [reflexivity | exact Hboth]].
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               exists (h1 a1), (h2 a2); split; [reflexivity | split; [reflexivity | exact HA]].
      - eapply RP_TauL; [rewrite (observe_bind u1 k1), Hu1; reflexivity | exact IH].
      - eapply RP_TauR; [rewrite (observe_bind u2 k2), Hu2; reflexivity | exact IH]. }
    intros i1 i2 Hinit; apply Hcore.
    exists (b1 i1), (b2 i2).
    split; [symmetry; apply unfold_iter |].
    split; [symmetry; apply unfold_iter |].
    apply refine_prov_incl; [apply incl_refl | apply Hbody; [apply incl_refl | exact Hinit]].
  Qed.

  Lemma refine_mcfg_model_bind {A1 A2 B1 B2}
    (RA : list N -> Res A1 -> Res A2 -> Prop)
    (RB : list N -> Res B1 -> Res B2 -> Prop)
    (U : list N)
    (t1 : @MCFGtop (@ParamsV IP IPT) A1) (t2 : @MCFGtop (@ParamsV IP IPT) A2)
    (k1 : A1 -> @MCFGtop (@ParamsV IP IPT) B1) (k2 : A2 -> @MCFGtop (@ParamsV IP IPT) B2)
    (s1 s2 : FusedS) :
    refine_prov RA U (interp_mcfg_model t1 s1) (interp_mcfg_model t2 s2) ->
    (forall U' s1' a1 s2' a2,
       incl U U' ->
       RA U' (s1', a1) (s2', a2) ->
       refine_prov RB U' (interp_mcfg_model (k1 a1) s1') (interp_mcfg_model (k2 a2) s2')) ->
    refine_prov RB U
      (interp_mcfg_model (ITree.bind t1 k1) s1)
      (interp_mcfg_model (ITree.bind t2 k2) s2).
  Proof using.
    intros Ht Hk.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind | symmetry; apply interp_mcfg_model_bind |].
    eapply refine_prov_bind.
    - apply (refine_prov_incl RA U U _ _ (incl_refl U) Ht).
    - intros U' [s1' a1] [s2' a2] [Hincl Ha]; eapply Hk; eassumption.
  Qed.

  Lemma refine_cfg_model_bind {A1 A2 B1 B2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RA : list N -> Res A1 -> Res A2 -> Prop)
    (RB : list N -> Res B1 -> Res B2 -> Prop)
    (U : list N)
    (t1 : @CFGtop (@ParamsV IP IPT) A1) (t2 : @CFGtop (@ParamsV IP IPT) A2)
    (k1 : A1 -> @CFGtop (@ParamsV IP IPT) B1) (k2 : A2 -> @CFGtop (@ParamsV IP IPT) B2)
    (s1 s2 : FusedS) :
    refine_prov RA U (interp_cfg_model ctx1 t1 s1) (interp_cfg_model ctx2 t2 s2) ->
    (forall U' s1' a1 s2' a2,
       incl U U' ->
       RA U' (s1', a1) (s2', a2) ->
       refine_prov RB U' (interp_cfg_model ctx1 (k1 a1) s1') (interp_cfg_model ctx2 (k2 a2) s2')) ->
    refine_prov RB U
      (interp_cfg_model ctx1 (ITree.bind t1 k1) s1)
      (interp_cfg_model ctx2 (ITree.bind t2 k2) s2).
  Proof using.
    intros Ht Hk.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_model_bind | symmetry; apply interp_cfg_model_bind |].
    eapply refine_prov_bind.
    - apply (refine_prov_incl RA U U _ _ (incl_refl U) Ht).
    - intros U' [s1' a1] [s2' a2] [Hincl Ha]; eapply Hk; eassumption.
  Qed.

  Inductive tau_star {R} : itree ProvBotE R -> itree ProvBotE R -> Prop :=
  | TS_Refl t : tau_star t t
  | TS_Eq t1 t2 t3 : t1 ≅ t2 -> tau_star t2 t3 -> tau_star t1 t3
  | TS_Tau m t' : tau_star m t' -> tau_star (Tau m) t'.

  Lemma tau_star_trans {R} (t1 t2 t3 : itree ProvBotE R) :
    tau_star t1 t2 ->
    tau_star t2 t3 ->
    tau_star t1 t3.
  Proof using.
    intros H12; revert t3;
      induction H12 as [t | a b c Heq _ IH | m b _ IH]; intros t3 H23.
    - exact H23.
    - eapply TS_Eq; [exact Heq | apply IH, H23].
    - apply TS_Tau, IH, H23.
  Qed.

  Lemma tau_star_bind {A B}
    (u u' : itree ProvBotE A) (k : A -> itree ProvBotE B) :
    tau_star u u' ->
    tau_star (ITree.bind u k) (ITree.bind u' k).
  Proof using.
    intros Hts; induction Hts as [t | t1 t2 t3 Heq _ IH | m t' _ IH].
    - apply TS_Refl.
    - eapply TS_Eq; [rewrite Heq; reflexivity | exact IH].
    - eapply TS_Eq; [apply Eqit.bind_tau | apply TS_Tau, IH].
  Qed.

  Lemma refine_prov_tau_star_l {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 t1' : itree ProvBotE R1) (t2 : itree ProvBotE R2) :
    tau_star t1 t1' ->
    refine_prov RR U t1' t2 ->
    refine_prov RR U t1 t2.
  Proof using.
    intros Hts; revert t2;
      induction Hts as [t | a b c Heq _ IH | m b _ IH]; intros t2 Hrel.
    - exact Hrel.
    - eapply refine_prov_obs_eq; [symmetry; exact Heq | reflexivity | apply IH, Hrel].
    - apply refine_prov_tau_l, IH, Hrel.
  Qed.

  Lemma refine_prov_tau_star_r {R1 R2} (RR : list N -> R1 -> R2 -> Prop)
    (U : list N) (t1 : itree ProvBotE R1) (t2 t2' : itree ProvBotE R2) :
    tau_star t2 t2' ->
    refine_prov RR U t1 t2' ->
    refine_prov RR U t1 t2.
  Proof using.
    intros Hts; revert t1;
      induction Hts as [t | a b c Heq _ IH | m b _ IH]; intros t1 Hrel.
    - exact Hrel.
    - eapply refine_prov_obs_eq; [reflexivity | symmetry; exact Heq | apply IH, Hrel].
    - apply refine_prov_tau_r, IH, Hrel.
  Qed.

  (** ** Primitive Event Reductions under [interp_mcfg_model] & [interp_cfg_model] *)

  Lemma interp_cfg_model_call
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (cc : cconv) (fv : @dvalue (@ParamsV IP IPT))
    (vs : list (@dvalue (@ParamsV IP IPT))) (s : FusedS) :
    interp_cfg_model ctx (call dt cc fv vs) s ≅
    Tau (interp_cfg_model ctx (mrec_ctx ctx _ (Call dt cc fv vs)) s).
  Proof using.
    assert (Hm : interp_mrec (mrec_ctx ctx) (call dt cc fv vs) ≅
                 Tau (interp_mrec (mrec_ctx ctx) (mrec_ctx ctx _ (Call dt cc fv vs)))).
    { unfold call, trigger, ITree.trigger.
      cbn [subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1].
      rewrite unfold_interp_mrec.
      transitivity (Tau (interp_mrec (mrec_ctx ctx) (ITree.bind (mrec_ctx ctx _ (Call dt cc fv vs)) (fun x => Ret x)))).
      - reflexivity.
      - apply eqit_Tau, interp_mrec_proper_eq, Eqit.bind_ret_r. }
    unfold interp_cfg_model.
    rewrite (interp_mcfg_model_obs_eq _ _ s Hm), interp_mcfg_model_tau.
    reflexivity.
  Qed.

  Lemma interp_mcfg_model_non_intr {X}
    (me : @MCFGEtop (@ParamsV IP IPT) X) (s : FusedS)
    (Hni : interp_intrinsics_h me = ITree.trigger me) :
    interp_mcfg_model (ITree.trigger me) s ≅
    ITree.bind (interp_vellvm_prov_h me s)
      (fun '(s', x) => Tau (Tau (Ret (s', x)))).
  Proof using.
    unfold interp_mcfg_model, interp_intrinsics, ITree.trigger.
    rewrite interp_vis, Hni.
    unfold ITree.trigger; rewrite Eqit.bind_vis, interp_state_vis.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [s' x] _ <-.
    rewrite Eqit.bind_ret_l, interp_state_tau, interp_ret, interp_state_ret.
    reflexivity.
  Qed.

  Lemma interp_cfg_model_non_intr {X}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (me : @MCFGEtop (@ParamsV IP IPT) X) (s : FusedS)
    (Hni : interp_intrinsics_h me = ITree.trigger me) :
    interp_cfg_model ctx (ITree.trigger (inr1 me)) s ≅
    ITree.bind (interp_vellvm_prov_h me s)
      (fun '(s', x) => Tau (Tau (Tau (Ret (s', x))))).
  Proof using.
    assert (Hm : interp_mrec (mrec_ctx ctx) (ITree.trigger (inr1 me)) ≅
                 Vis me (fun x => Tau (interp_mrec (mrec_ctx ctx) (Ret x)))).
    { unfold ITree.trigger; rewrite unfold_interp_mrec; reflexivity. }
    unfold interp_cfg_model.
    rewrite (interp_mcfg_model_obs_eq _ _ s Hm).
    unfold interp_mcfg_model, interp_intrinsics.
    rewrite interp_vis, Hni.
    unfold ITree.trigger; rewrite Eqit.bind_vis, interp_state_vis.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [s' x] _ <-.
    rewrite Eqit.bind_ret_l, !interp_tau, !interp_state_tau, interp_mrec_ret, interp_ret, interp_state_ret.
    reflexivity.
  Qed.

  Lemma tau_star_mcfg_det {X}
    (me : @MCFGEtop (@ParamsV IP IPT) X) (s s' : FusedS) (v : X)
    (Hni : interp_intrinsics_h me = ITree.trigger me)
    (Hstep : interp_vellvm_prov_h me s ≅ Ret (s', v)) :
    tau_star (interp_mcfg_model (ITree.trigger me) s) (Ret (s', v)).
  Proof using.
    eapply TS_Eq; [apply interp_mcfg_model_non_intr, Hni |].
    eapply TS_Eq; [rewrite Hstep, Eqit.bind_ret_l; reflexivity |].
    apply TS_Tau, TS_Tau, TS_Refl.
  Qed.

  Lemma tau_star_cfg_det {X}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (me : @MCFGEtop (@ParamsV IP IPT) X) (s s' : FusedS) (v : X)
    (Hni : interp_intrinsics_h me = ITree.trigger me)
    (Hstep : interp_vellvm_prov_h me s ≅ Ret (s', v)) :
    tau_star (interp_cfg_model ctx (ITree.trigger (inr1 me)) s) (Ret (s', v)).
  Proof using.
    eapply TS_Eq; [apply interp_cfg_model_non_intr, Hni |].
    eapply TS_Eq; [rewrite Hstep, Eqit.bind_ret_l; reflexivity |].
    apply TS_Tau, TS_Tau, TS_Tau, TS_Refl.
  Qed.

  Lemma refine_mcfg_raiseUB_l {X R2}
    (RR : list N -> Res X -> R2 -> Prop) (U : list N)
    (msg : string) (s1 : FusedS) (t2 : itree ProvBotE R2) :
    refine_prov RR U (interp_mcfg_model (raiseUB msg) s1) t2.
  Proof using.
    unfold raiseUB, trigger_cast.
    eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_bind | reflexivity |].
    eapply refine_prov_obs_eq;
      [symmetry;
       match goal with
       | |- ITree.bind _ ?k ≅ _ =>
           eapply eq_itree_clo_bind with (UU := Logic.eq) (k2 := k);
           [apply interp_mcfg_model_non_intr; reflexivity | intros ? ? <-; reflexivity]
       end
      | reflexivity |].
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    unfold fused_trigger_prov, ITree.trigger.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity | reflexivity |].
    apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma refine_mcfg_raiseOOM_l {X R2}
    (RR : list N -> Res X -> R2 -> Prop) (U : list N)
    (msg : string) (s1 : FusedS) (t2 : itree ProvBotE R2) :
    refine_prov RR U (interp_mcfg_model (raiseOOM msg) s1) t2.
  Proof using.
    unfold raiseOOM, trigger_cast.
    eapply refine_prov_obs_eq; [symmetry; apply interp_mcfg_model_bind | reflexivity |].
    eapply refine_prov_obs_eq;
      [symmetry;
       match goal with
       | |- ITree.bind _ ?k ≅ _ =>
           eapply eq_itree_clo_bind with (UU := Logic.eq) (k2 := k);
           [apply interp_mcfg_model_non_intr; reflexivity | intros ? ? <-; reflexivity]
       end
      | reflexivity |].
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    unfold fused_trigger_prov, ITree.trigger.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity | reflexivity |].
    apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma refine_mcfg_raise_both {X1 X2}
    (RR : list N -> Res X1 -> Res X2 -> Prop) (U : list N)
    (msg1 msg2 : string) (s1 s2 : FusedS) :
    refine_prov RR U
      (interp_mcfg_model (raise msg1) s1)
      (interp_mcfg_model (raise msg2) s2).
  Proof using.
    unfold raise, trigger_cast.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_bind | symmetry; apply interp_mcfg_model_bind |].
    eapply refine_prov_obs_eq;
      [symmetry;
       match goal with
       | |- ITree.bind _ ?k ≅ _ =>
           eapply eq_itree_clo_bind with (UU := Logic.eq) (k2 := k);
           [apply interp_mcfg_model_non_intr; reflexivity | intros ? ? <-; reflexivity]
       end
      | symmetry;
        match goal with
        | |- ITree.bind _ ?k ≅ _ =>
            eapply eq_itree_clo_bind with (UU := Logic.eq) (k2 := k);
            [apply interp_mcfg_model_non_intr; reflexivity | intros ? ? <-; reflexivity]
        end |].
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    unfold fused_trigger_prov, ITree.trigger.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
      | symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
    pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma refine_cfg_raiseUB_l {X R2}
    (ctx1 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res X -> R2 -> Prop) (U : list N)
    (msg : string) (s1 : FusedS) (t2 : itree ProvBotE R2) :
    refine_prov RR U (interp_cfg_model ctx1 (raiseUB msg) s1) t2.
  Proof using.
    unfold raiseUB, trigger_cast.
    eapply refine_prov_obs_eq; [symmetry; apply interp_cfg_model_bind | reflexivity |].
    eapply refine_prov_obs_eq;
      [symmetry;
       match goal with
       | |- ITree.bind _ ?k ≅ _ =>
           eapply eq_itree_clo_bind with (UU := Logic.eq) (k2 := k);
           [apply interp_cfg_model_non_intr; reflexivity | intros ? ? <-; reflexivity]
       end
      | reflexivity |].
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    unfold fused_trigger_prov, ITree.trigger.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity | reflexivity |].
    apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma refine_cfg_raiseOOM_l {X R2}
    (ctx1 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res X -> R2 -> Prop) (U : list N)
    (msg : string) (s1 : FusedS) (t2 : itree ProvBotE R2) :
    refine_prov RR U (interp_cfg_model ctx1 (raiseOOM msg) s1) t2.
  Proof using.
    unfold raiseOOM, trigger_cast.
    eapply refine_prov_obs_eq; [symmetry; apply interp_cfg_model_bind | reflexivity |].
    eapply refine_prov_obs_eq;
      [symmetry;
       match goal with
       | |- ITree.bind _ ?k ≅ _ =>
           eapply eq_itree_clo_bind with (UU := Logic.eq) (k2 := k);
           [apply interp_cfg_model_non_intr; reflexivity | intros ? ? <-; reflexivity]
       end
      | reflexivity |].
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    unfold fused_trigger_prov, ITree.trigger.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity | reflexivity |].
    apply refine_prov_ub_vis_l; reflexivity.
  Qed.

  Lemma refine_cfg_raise_both {X1 X2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res X1 -> Res X2 -> Prop) (U : list N)
    (msg1 msg2 : string) (s1 s2 : FusedS) :
    refine_prov RR U
      (interp_cfg_model ctx1 (raise msg1) s1)
      (interp_cfg_model ctx2 (raise msg2) s2).
  Proof using.
    unfold raise, trigger_cast.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_model_bind | symmetry; apply interp_cfg_model_bind |].
    eapply refine_prov_obs_eq;
      [symmetry;
       match goal with
       | |- ITree.bind _ ?k ≅ _ =>
           eapply eq_itree_clo_bind with (UU := Logic.eq) (k2 := k);
           [apply interp_cfg_model_non_intr; reflexivity | intros ? ? <-; reflexivity]
       end
      | symmetry;
        match goal with
        | |- ITree.bind _ ?k ≅ _ =>
            eapply eq_itree_clo_bind with (UU := Logic.eq) (k2 := k);
            [apply interp_cfg_model_non_intr; reflexivity | intros ? ? <-; reflexivity]
        end |].
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    unfold fused_trigger_prov, ITree.trigger.
    eapply refine_prov_obs_eq;
      [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
      | symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
    pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma refine_mcfg_EOU {A1 A2}
    (RVal : A1 -> A2 -> Prop)
    (RR : list N -> Res A1 -> Res A2 -> Prop)
    (U : list N) (m1 : EOU A1) (m2 : EOU A2) (s1 s2 : FusedS)
    (Hm : refine_EOU RVal m1 m2)
    (Hret : forall a1 a2, RVal a1 a2 -> RR U (s1, a1) (s2, a2)) :
    refine_prov RR U
      (interp_mcfg_model (EOU_to_itree m1) s1)
      (interp_mcfg_model (EOU_to_itree m2) s2).
  Proof using.
    destruct Hm as [a1 a2 Ha | msg1 msg2 | msg1 msg2 | msg1 m2']; cbn [EOU_to_itree].
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret, Hret, Ha.
    - apply refine_mcfg_raise_both.
    - apply refine_mcfg_raiseOOM_l.
    - apply refine_mcfg_raiseUB_l.
  Qed.

  Lemma refine_cfg_EOU {A1 A2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RVal : A1 -> A2 -> Prop)
    (RR : list N -> Res A1 -> Res A2 -> Prop)
    (U : list N) (m1 : EOU A1) (m2 : EOU A2) (s1 s2 : FusedS)
    (Hm : refine_EOU RVal m1 m2)
    (Hret : forall a1 a2, RVal a1 a2 -> RR U (s1, a1) (s2, a2)) :
    refine_prov RR U
      (interp_cfg_model ctx1 (EOU_to_itree m1) s1)
      (interp_cfg_model ctx2 (EOU_to_itree m2) s2).
  Proof using.
    destruct Hm as [a1 a2 Ha | msg1 msg2 | msg1 msg2 | msg1 m2']; cbn [EOU_to_itree].
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
      apply refine_prov_ret, Hret, Ha.
    - apply refine_cfg_raise_both.
    - apply refine_cfg_raiseOOM_l.
    - apply refine_cfg_raiseUB_l.
  Qed.

  (** Lift [memM_interp_prov] refinement to any [MemoryE] trigger in [CFGtop] or [MCFGtop]. *)
  Lemma refine_mcfg_memory_event {X1 X2}
    (RR : list N -> Res X1 -> Res X2 -> Prop)
    (me1 : @MemoryE (@ParamsV IP IPT) X1)
    (me2 : @MemoryE (@ParamsV IP IPT) X2)
    (U : list N) (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env) :
    refine_prov
      (fun U' '(σ1', x1) '(σ2', x2) => RR U' ((σ1', rest1), x1) ((σ2', rest2), x2))
      U
      (memM_interp_prov (handle_memoryM me1) σ1)
      (memM_interp_prov (handle_memoryM me2) σ2) ->
    refine_prov RR U
      (interp_mcfg_model (ITree.trigger (subevent _ me1)) (σ1, rest1))
      (interp_mcfg_model (ITree.trigger (subevent _ me2)) (σ2, rest2)).
  Proof using.
    intros Hmem.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_non_intr; reflexivity
      | symmetry; apply interp_mcfg_model_non_intr; reflexivity |].
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    unfold fused_memory_prov, on_mem_prov, handle_memory.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    eapply refine_prov_bind; [exact Hmem |].
    intros U' [σ1' x1] [σ2' x2] HRR.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    apply refine_prov_tau_both, refine_prov_tau_both, refine_prov_ret, HRR.
  Qed.

  Lemma refine_cfg_memory_event {X1 X2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res X1 -> Res X2 -> Prop)
    (me1 : @MemoryE (@ParamsV IP IPT) X1)
    (me2 : @MemoryE (@ParamsV IP IPT) X2)
    (U : list N) (σ1 σ2 : state)
    (rest1 rest2 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env) :
    refine_prov
      (fun U' '(σ1', x1) '(σ2', x2) => RR U' ((σ1', rest1), x1) ((σ2', rest2), x2))
      U
      (memM_interp_prov (handle_memoryM me1) σ1)
      (memM_interp_prov (handle_memoryM me2) σ2) ->
    refine_prov RR U
      (interp_cfg_model ctx1 (ITree.trigger (subevent _ me1)) (σ1, rest1))
      (interp_cfg_model ctx2 (ITree.trigger (subevent _ me2)) (σ2, rest2)).
  Proof using.
    intros Hmem.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_model_non_intr; reflexivity
      | symmetry; apply interp_cfg_model_non_intr; reflexivity |].
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    unfold fused_memory_prov, on_mem_prov, handle_memory.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    eapply refine_prov_bind; [exact Hmem |].
    intros U' [σ1' x1] [σ2' x2] HRR.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    apply refine_prov_tau_both, refine_prov_tau_both, refine_prov_tau_both, refine_prov_ret, HRR.
  Qed.

  (** One-sided left [MemoryE] step against an arbitrary right-hand model tree [t2]. *)
  Lemma refine_cfg_memory_event_l {X1 R2}
    (ctx1 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res X1 -> R2 -> Prop)
    (me1 : @MemoryE (@ParamsV IP IPT) X1)
    (U : list N) (σ1 : state)
    (rest1 : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (t2 : itree ProvBotE R2) :
    refine_prov
      (fun U' '(σ1', x1) r2 => RR U' ((σ1', rest1), x1) r2)
      U
      (memM_interp_prov (handle_memoryM me1) σ1)
      t2 ->
    refine_prov RR U
      (interp_cfg_model ctx1 (ITree.trigger (subevent _ me1)) (σ1, rest1))
      t2.
  Proof using.
    intros Hmem.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_model_non_intr; reflexivity | apply Eqit.bind_ret_r |].
    cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    unfold fused_memory_prov, on_mem_prov, handle_memory.
    eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_bind | reflexivity |].
    eapply refine_prov_bind; [exact Hmem |].
    intros U' [σ1' x1] r2 HRR.
    eapply refine_prov_obs_eq; [symmetry; apply Eqit.bind_ret_l | reflexivity |].
    apply refine_prov_tau_l, refine_prov_tau_l, refine_prov_tau_l, refine_prov_ret, HRR.
  Qed.

  (** ** Exception-Reifying Interpreter ([interp_cfg_exc]) for [run_exc] *)

  Lemma run_exc_ret_eq {A} (a : A) :
    @run_exc (@ParamsV IP IPT) A (Ret a) ≅ Ret (inr a).
  Proof using.
    rewrite unfold_run_exc_obs; reflexivity.
  Qed.

  Lemma run_exc_tau_eq {A} (t : @CFGtop (@ParamsV IP IPT) A) :
    run_exc (Tau t) ≅ Tau (run_exc t).
  Proof using.
    rewrite unfold_run_exc_obs; reflexivity.
  Qed.

  Lemma run_exc_proper_eq {A} :
    forall (t1 t2 : @CFGtop (@ParamsV IP IPT) A),
      t1 ≅ t2 ->
      run_exc t1 ≅ run_exc t2.
  Proof using.
    ginit; gcofix CIH; intros t1 t2 Heq.
    rewrite (unfold_run_exc_obs t1), (unfold_run_exc_obs t2).
    punfold Heq; red in Heq.
    destruct Heq as [r1 r2 <- | m1 m2 Hm | X e k1 k2 Hk | ? ? Hchk _ | ? ? Hchk _]; try inversion Hchk; pclearbot.
    - gstep; constructor; reflexivity.
    - gstep; constructor; gfinal; left; apply CIH, Hm.
    - destruct (exc_of_event e) as [x |].
      + gstep; constructor; reflexivity.
      + gstep; constructor; intros y; gstep; constructor; gfinal; left; apply CIH, Hk.
  Qed.

  Lemma run_exc_bind_eq {A B} :
    forall (t : @CFGtop (@ParamsV IP IPT) A)
           (k : A -> @CFGtop (@ParamsV IP IPT) B),
      run_exc (ITree.bind t k) ≅
      ITree.bind (run_exc t)
        (fun res =>
           match res with
           | inl x => Ret (inl x)
           | inr a => run_exc (k a)
           end).
  Proof using.
    ginit; gcofix CIH; intros t k.
    rewrite (unfold_run_exc_obs t).
    destruct (observe t) as [a | m | X e h] eqn:Hot.
    - assert (Htk : ITree.bind t k ≅ k a).
      { rewrite (itree_eta t), Hot, Eqit.bind_ret_l; reflexivity. }
      rewrite (run_exc_proper_eq _ _ Htk), Eqit.bind_ret_l.
      gfinal; right; apply pacobot2; match goal with |- _ ?lhs ?rhs => change (eq_itree eq lhs rhs); reflexivity end.
    - rewrite (unfold_run_exc_obs (ITree.bind t k)), observe_bind, Hot, Eqit.bind_tau.
      gstep; constructor; gfinal; left; apply CIH.
    - rewrite (unfold_run_exc_obs (ITree.bind t k)), observe_bind, Hot.
      destruct (exc_of_event e) as [x |].
      + rewrite Eqit.bind_ret_l; gstep; constructor; reflexivity.
      + rewrite Eqit.bind_vis; gstep; constructor; intros y.
        rewrite Eqit.bind_tau; gstep; constructor; gfinal; left; apply CIH.
  Qed.

  Lemma run_exc_raiseLLVM_eq {A} (x : @exc (@ParamsV IP IPT)) :
    @run_exc (@ParamsV IP IPT) A (raiseLLVM x) ≅ Ret (inl x).
  Proof using.
    unfold raiseLLVM, trigger_cast, ITree.trigger.
    rewrite unfold_run_exc_obs, observe_bind.
    cbn [observe exc_of_event subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1].
    reflexivity.
  Qed.

  Lemma run_exc_trigger_non_exc {X}
    (e : @CFGEtop (@ParamsV IP IPT) X)
    (Hne : exc_of_event e = None) :
    run_exc (ITree.trigger e) ≅
    ITree.bind (ITree.trigger e) (fun y => Tau (Ret (inr y))).
  Proof using.
    unfold ITree.trigger.
    rewrite unfold_run_exc_obs; cbn - [exc_of_event run_exc]; rewrite Hne, Eqit.bind_vis.
    apply eqit_Vis; intros y; rewrite run_exc_ret_eq, Eqit.bind_ret_l; reflexivity.
  Qed.

  Definition interp_cfg_exc {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t : @CFGtop (@ParamsV IP IPT) R) (s : FusedS)
    : itree ProvBotE (Res (@exc (@ParamsV IP IPT) + R)) :=
    interp_cfg_model ctx (run_exc t) s.

  Lemma interp_cfg_exc_obs_eq {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t1 t2 : @CFGtop (@ParamsV IP IPT) R) (s : FusedS) :
    t1 ≅ t2 ->
    interp_cfg_exc ctx t1 s ≅ interp_cfg_exc ctx t2 s.
  Proof using.
    intros Heq; unfold interp_cfg_exc.
    apply interp_cfg_model_obs_eq, run_exc_proper_eq, Heq.
  Qed.

  Lemma interp_cfg_exc_ret {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (a : R) (s : FusedS) :
    interp_cfg_exc ctx (Ret a) s ≅ Ret (s, inr a).
  Proof using.
    unfold interp_cfg_exc.
    rewrite (interp_cfg_model_obs_eq ctx _ _ s (run_exc_ret_eq a)).
    apply interp_cfg_model_ret.
  Qed.

  Lemma interp_cfg_exc_tau {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t : @CFGtop (@ParamsV IP IPT) R) (s : FusedS) :
    interp_cfg_exc ctx (Tau t) s ≅ Tau (interp_cfg_exc ctx t s).
  Proof using.
    unfold interp_cfg_exc.
    rewrite (interp_cfg_model_obs_eq ctx _ _ s (run_exc_tau_eq t)).
    apply interp_cfg_model_tau.
  Qed.

  Lemma interp_cfg_exc_raiseLLVM {R}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (x : @exc (@ParamsV IP IPT)) (s : FusedS) :
    @interp_cfg_exc R ctx (raiseLLVM x) s ≅ Ret (s, inl x).
  Proof using.
    unfold interp_cfg_exc.
    rewrite (interp_cfg_model_obs_eq ctx _ _ s (run_exc_raiseLLVM_eq x)).
    apply interp_cfg_model_ret.
  Qed.

  Lemma interp_cfg_exc_bind {A B}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (t : @CFGtop (@ParamsV IP IPT) A)
    (k : A -> @CFGtop (@ParamsV IP IPT) B) (s : FusedS) :
    interp_cfg_exc ctx (ITree.bind t k) s ≅
    ITree.bind (interp_cfg_exc ctx t s)
      (fun '(s', res) =>
         match res with
         | inl x => Ret (s', inl x)
         | inr a => interp_cfg_exc ctx (k a) s'
         end).
  Proof using.
    unfold interp_cfg_exc.
    rewrite (interp_cfg_model_obs_eq ctx _ _ s (run_exc_bind_eq t k)).
    rewrite interp_cfg_model_bind.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [s' [x | a]] _ <-.
    - apply interp_cfg_model_ret.
    - reflexivity.
  Qed.

  Lemma interp_cfg_exc_trigger_non_exc {X}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (e : @CFGEtop (@ParamsV IP IPT) X) (s : FusedS)
    (Hne : exc_of_event e = None) :
    interp_cfg_exc ctx (ITree.trigger e) s ≅
    ITree.bind (interp_cfg_model ctx (ITree.trigger e) s)
      (fun '(s', y) => Tau (Ret (s', inr y))).
  Proof using.
    unfold interp_cfg_exc.
    rewrite (interp_cfg_model_obs_eq ctx _ _ s (run_exc_trigger_non_exc e Hne)).
    rewrite interp_cfg_model_bind.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [s' y] _ <-.
    rewrite interp_cfg_model_tau, interp_cfg_model_ret; reflexivity.
  Qed.

  Definition exc_post {A1 A2}
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (U : list N)
    (r1 : Res (@exc (@ParamsV IP IPT) + A1))
    (r2 : Res (@exc (@ParamsV IP IPT) + A2)) : Prop :=
    let '(s1, v1) := r1 in
    let '(s2, v2) := r2 in
    match v1, v2 with
    | inl x1, inl x2 => RExc U s1 s2 x1 x2
    | inr a1, inr a2 => RA U s1 s2 a1 a2
    | _, _ => False
    end.

  Lemma refine_cfg_exc_ret {A1 A2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (U : list N) (a1 : A1) (a2 : A2) (s1 s2 : FusedS) :
    RA U s1 s2 a1 a2 ->
    refine_prov (exc_post RExc RA) U
      (interp_cfg_exc ctx1 (Ret a1) s1)
      (interp_cfg_exc ctx2 (Ret a2) s2).
  Proof using.
    intros Hra.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_exc_ret | symmetry; apply interp_cfg_exc_ret |].
    apply refine_prov_ret; exact Hra.
  Qed.

  Lemma refine_cfg_exc_bind {A1 A2 B1 B2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (RB   : list N -> FusedS -> FusedS -> B1 -> B2 -> Prop)
    (U : list N)
    (t1 : @CFGtop (@ParamsV IP IPT) A1) (t2 : @CFGtop (@ParamsV IP IPT) A2)
    (k1 : A1 -> @CFGtop (@ParamsV IP IPT) B1) (k2 : A2 -> @CFGtop (@ParamsV IP IPT) B2)
    (s1 s2 : FusedS) :
    refine_prov (exc_post RExc RA) U
      (interp_cfg_exc ctx1 t1 s1)
      (interp_cfg_exc ctx2 t2 s2) ->
    (forall U' s1' a1 s2' a2,
       incl U U' ->
       RA U' s1' s2' a1 a2 ->
       refine_prov (exc_post RExc RB) U'
         (interp_cfg_exc ctx1 (k1 a1) s1')
         (interp_cfg_exc ctx2 (k2 a2) s2')) ->
    refine_prov (exc_post RExc RB) U
      (interp_cfg_exc ctx1 (ITree.bind t1 k1) s1)
      (interp_cfg_exc ctx2 (ITree.bind t2 k2) s2).
  Proof using.
    intros Ht Hk.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_exc_bind | symmetry; apply interp_cfg_exc_bind |].
    eapply refine_prov_bind.
    - apply (refine_prov_incl (exc_post RExc RA) U U _ _ (incl_refl U) Ht).
    - intros U' [s1' [x1 | a1]] [s2' [x2 | a2]] [Hincl Hres]; try contradiction.
      + apply refine_prov_ret; exact Hres.
      + eapply Hk; eassumption.
  Qed.

  Lemma refine_cfg_exc_trigger {X1 X2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> X1 -> X2 -> Prop)
    (e1 : @CFGEtop (@ParamsV IP IPT) X1)
    (e2 : @CFGEtop (@ParamsV IP IPT) X2)
    (U : list N) (s1 s2 : FusedS)
    (Hne1 : exc_of_event e1 = None)
    (Hne2 : exc_of_event e2 = None) :
    refine_prov (fun U' '(s1', y1) '(s2', y2) => RA U' s1' s2' y1 y2) U
      (interp_cfg_model ctx1 (ITree.trigger e1) s1)
      (interp_cfg_model ctx2 (ITree.trigger e2) s2) ->
    refine_prov (exc_post RExc RA) U
      (interp_cfg_exc ctx1 (ITree.trigger e1) s1)
      (interp_cfg_exc ctx2 (ITree.trigger e2) s2).
  Proof using.
    intros Htr.
    eapply refine_prov_obs_eq;
      [symmetry; apply (interp_cfg_exc_trigger_non_exc ctx1 e1 s1 Hne1)
      | symmetry; apply (interp_cfg_exc_trigger_non_exc ctx2 e2 s2 Hne2) |].
    eapply refine_prov_bind; [exact Htr |].
    intros U' [s1' y1] [s2' y2] Hra.
    apply refine_prov_tau_both, refine_prov_ret; exact Hra.
  Qed.

  Lemma refine_cfg_exc_EOU {A1 A2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RVal : A1 -> A2 -> Prop)
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (U : list N) (m1 : EOU A1) (m2 : EOU A2) (s1 s2 : FusedS)
    (Hm : refine_EOU RVal m1 m2)
    (Hret : forall a1 a2, RVal a1 a2 -> RA U s1 s2 a1 a2) :
    refine_prov (exc_post RExc RA) U
      (interp_cfg_exc ctx1 (EOU_to_itree m1) s1)
      (interp_cfg_exc ctx2 (EOU_to_itree m2) s2).
  Proof using.
    destruct Hm as [a1 a2 Ha | msg1 msg2 | msg1 msg2 | msg1 m2']; cbn [EOU_to_itree].
    - apply refine_cfg_exc_ret, Hret, Ha.
    - unfold raise, trigger_cast; eapply refine_cfg_exc_bind.
      + eapply refine_cfg_exc_trigger with (RA := fun _ _ _ (v1 : void) (_ : void) => match v1 with end);
          [reflexivity | reflexivity |].
        eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_non_intr; reflexivity
          | symmetry; apply interp_cfg_model_non_intr; reflexivity |].
        cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
        unfold fused_trigger_prov, ITree.trigger.
        eapply refine_prov_obs_eq;
          [symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity
          | symmetry; rewrite !Eqit.bind_bind, Eqit.bind_vis; reflexivity |].
        pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
      + intros _ _ [] _ _ _ _.
    - unfold raiseOOM, trigger_cast, interp_cfg_exc.
      assert (Hoom : run_exc (A := A1)
                       (ITree.bind (ITree.trigger (subevent _ (ThrowOOM (print_msg msg1))))
                          void_elim)
                     ≅ ITree.bind (ITree.trigger (subevent _ (ThrowOOM (print_msg msg1))))
                         void_elim).
      { rewrite run_exc_bind_eq, run_exc_trigger_non_exc;
          [rewrite Eqit.bind_bind; apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _]
          | reflexivity]. }
      eapply refine_prov_obs_eq;
        [symmetry; apply (interp_cfg_model_obs_eq ctx1 _ _ s1 Hoom) | reflexivity |].
      apply (refine_cfg_raiseOOM_l ctx1 _ U msg1 s1).
    - unfold raiseUB, trigger_cast, interp_cfg_exc.
      assert (Hub : run_exc (A := A1)
                      (ITree.bind (ITree.trigger (subevent _ (ThrowUB (print_msg msg1))))
                         void_elim)
                    ≅ ITree.bind (ITree.trigger (subevent _ (ThrowUB (print_msg msg1))))
                        void_elim).
      { rewrite run_exc_bind_eq, run_exc_trigger_non_exc;
          [rewrite Eqit.bind_bind; apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _]
          | reflexivity]. }
      eapply refine_prov_obs_eq;
        [symmetry; apply (interp_cfg_model_obs_eq ctx1 _ _ s1 Hub) | reflexivity |].
      apply (refine_cfg_raiseUB_l ctx1 _ U msg1 s1).
  Qed.

  Lemma refine_cfg_exc_raiseUB_l {A1 R2}
    (ctx1 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res (@exc (@ParamsV IP IPT) + A1) -> R2 -> Prop)
    (U : list N) (msg : string) (s1 : FusedS) (t2 : itree ProvBotE R2) :
    refine_prov RR U (interp_cfg_exc ctx1 (raiseUB msg) s1) t2.
  Proof using.
    unfold raiseUB, trigger_cast, interp_cfg_exc.
    assert (Hub : run_exc (A := A1)
                    (ITree.bind (ITree.trigger (subevent _ (ThrowUB (print_msg msg))))
                       (fun v : void => match v with end))
                  ≅ ITree.bind (ITree.trigger (subevent _ (ThrowUB (print_msg msg))))
                      (fun v : void => match v with end)).
    { rewrite run_exc_bind_eq, run_exc_trigger_non_exc;
        [rewrite Eqit.bind_bind; apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _]
        | reflexivity]. }
    eapply refine_prov_obs_eq;
      [symmetry; apply (interp_cfg_model_obs_eq ctx1 _ _ s1 Hub) | reflexivity |].
    apply (refine_cfg_raiseUB_l ctx1 RR U msg s1 t2).
  Qed.

  Lemma refine_cfg_exc_iter {I1 I2 R1 R2}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RI   : list N -> FusedS -> FusedS -> I1 -> I2 -> Prop)
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RRet : list N -> FusedS -> FusedS -> R1 -> R2 -> Prop)
    (b1 : I1 -> @CFGtop (@ParamsV IP IPT) (I1 + R1))
    (b2 : I2 -> @CFGtop (@ParamsV IP IPT) (I2 + R2))
    (U0 : list N)
    (Hbody : forall U s1 s2 i1 i2,
               incl U0 U ->
               RI U s1 s2 i1 i2 ->
               refine_prov
                 (exc_post RExc
                    (fun U' s1' s2' lr1 lr2 =>
                       match lr1, lr2 with
                       | inl j1, inl j2 => RI U' s1' s2' j1 j2
                       | inr r1, inr r2 => RRet U' s1' s2' r1 r2
                       | _, _ => False
                       end))
                 U
                 (interp_cfg_exc ctx1 (b1 i1) s1)
                 (interp_cfg_exc ctx2 (b2 i2) s2)) :
    forall s1 s2 i1 i2,
      RI U0 s1 s2 i1 i2 ->
      refine_prov (exc_post RExc RRet) U0
        (interp_cfg_exc ctx1 (ITree.iter b1 i1) s1)
        (interp_cfg_exc ctx2 (ITree.iter b2 i2) s2).
  Proof using.
    set (RStep := fun U' (x1 : Res (@exc (@ParamsV IP IPT) + (I1 + R1)))
                         (x2 : Res (@exc (@ParamsV IP IPT) + (I2 + R2))) =>
                    incl U0 U' /\
                    exc_post RExc
                      (fun U'' s1' s2' lr1 lr2 =>
                         match lr1, lr2 with
                         | inl j1, inl j2 => RI U'' s1' s2' j1 j2
                         | inr r1, inr r2 => RRet U'' s1' s2' r1 r2
                         | _, _ => False
                         end) U' x1 x2).
    set (k1 := fun '(s', res) =>
                 match res with
                 | inl x => Ret (s', inl x)
                 | inr (inl j) => Tau (interp_cfg_exc ctx1 (ITree.iter b1 j) s')
                 | inr (inr r) => Ret (s', inr r)
                 end : itree ProvBotE (Res (@exc (@ParamsV IP IPT) + R1))).
    set (k2 := fun '(s', res) =>
                 match res with
                 | inl x => Ret (s', inl x)
                 | inr (inl j) => Tau (interp_cfg_exc ctx2 (ITree.iter b2 j) s')
                 | inr (inr r) => Ret (s', inr r)
                 end : itree ProvBotE (Res (@exc (@ParamsV IP IPT) + R2))).
    assert (Hunf1 : forall s i,
              interp_cfg_exc ctx1 (ITree.iter b1 i) s ≅
              ITree.bind (interp_cfg_exc ctx1 (b1 i) s) k1).
    { intros s i.
      rewrite (interp_cfg_exc_obs_eq ctx1 _ _ s (unfold_iter b1 i)).
      rewrite interp_cfg_exc_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' [x | [j | r]]] _ <-; cbn [k1].
      - reflexivity.
      - apply interp_cfg_exc_tau.
      - apply interp_cfg_exc_ret. }
    assert (Hunf2 : forall s i,
              interp_cfg_exc ctx2 (ITree.iter b2 i) s ≅
              ITree.bind (interp_cfg_exc ctx2 (b2 i) s) k2).
    { intros s i.
      rewrite (interp_cfg_exc_obs_eq ctx2 _ _ s (unfold_iter b2 i)).
      rewrite interp_cfg_exc_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' [x | [j | r]]] _ <-; cbn [k2].
      - reflexivity.
      - apply interp_cfg_exc_tau.
      - apply interp_cfg_exc_ret. }
    set (r_it := fun U t1 t2 =>
                   exists u1 u2,
                     ITree.bind u1 k1 ≅ t1 /\
                     ITree.bind u2 k2 ≅ t2 /\
                     refine_prov RStep U u1 u2).
    assert (Hr_eq : forall U a1 a1' a2 a2',
                      a1 ≅ a1' -> a2 ≅ a2' -> r_it U a1 a2 -> r_it U a1' a2').
    { intros U a1 a1' a2 a2' E1 E2 (u1 & u2 & Eu1 & Eu2 & Hu).
      exists u1, u2; split; [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hu]]. }
    assert (Hcore : forall U t1 t2, r_it U t1 t2 -> refine_prov (exc_post RExc RRet) U t1 t2).
    { pcofix CIH.
      intros U t1 t2 (u1 & u2 & Eu1 & Eu2 & Hu); pstep.
      eapply refine_prov__mon with (r := r_it);
        [| intros U' a1 a2 Hr; right; apply CIH, Hr].
      eapply refine_prov__obs_eq; [exact Hr_eq | exact Eu1 | exact Eu2 |].
      punfold Hu; clear t1 t2 Eu1 Eu2.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [[s1' res1] | m1 | X1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [[s2' res2] | m2 | X2 e2 h2] eqn:Hou2; try contradiction.
          destruct Hstep as [Hincl Hres].
          destruct res1 as [x1 | [j1 | r1]], res2 as [x2 | [j2 | r2]]; cbn in Hres; try contradiction.
          * eapply refine_prov__obs_eq;
              [exact Hr_eq
              | symmetry; rewrite (itree_eta u1), Hou1, Eqit.bind_ret_l; reflexivity
              | symmetry; rewrite (itree_eta u2), Hou2, Eqit.bind_ret_l; reflexivity
              | apply RP_Step; unfold rp_step_body; cbn; exact Hres].
          * eapply refine_prov__obs_eq;
              [exact Hr_eq
              | symmetry; rewrite (itree_eta u1), Hou1, Eqit.bind_ret_l; reflexivity
              | symmetry; rewrite (itree_eta u2), Hou2, Eqit.bind_ret_l; reflexivity
              | apply RP_Step; unfold rp_step_body; cbn].
            exists (interp_cfg_exc ctx1 (b1 j1) s1'), (interp_cfg_exc ctx2 (b2 j2) s2').
            split; [symmetry; apply Hunf1 |].
            split; [symmetry; apply Hunf2 |].
            apply refine_prov_incl; [exact Hincl | eapply Hbody; eassumption].
          * eapply refine_prov__obs_eq;
              [exact Hr_eq
              | symmetry; rewrite (itree_eta u1), Hou1, Eqit.bind_ret_l; reflexivity
              | symmetry; rewrite (itree_eta u2), Hou2, Eqit.bind_ret_l; reflexivity
              | apply RP_Step; unfold rp_step_body; cbn; exact Hres].
        + destruct (observe u2) as [? | m2 | ? ? ?] eqn:Hou2; try contradiction.
          pclearbot.
          eapply refine_prov__obs_eq;
            [exact Hr_eq
            | symmetry; rewrite (itree_eta u1), Hou1, Eqit.bind_tau; reflexivity
            | symmetry; rewrite (itree_eta u2), Hou2, Eqit.bind_tau; reflexivity
            | apply RP_Step; unfold rp_step_body; cbn].
          exists m1, m2; split; [reflexivity | split; [reflexivity | exact Hstep]].
        + eapply refine_prov__obs_eq;
            [exact Hr_eq
            | symmetry; rewrite (itree_eta u1), Hou1, Eqit.bind_vis; reflexivity
            | reflexivity |].
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * apply RP_Step; unfold rp_step_body; cbn; left; exact Hub.
          * apply RP_Step; unfold rp_step_body; cbn; right; left.
            destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            exists (h1 p), u2; split; [reflexivity | split; [reflexivity | exact Hleft]].
          * destruct (observe u2) as [? | ? | X2 e2 h2] eqn:Hou2; try contradiction.
            eapply refine_prov__obs_eq;
              [exact Hr_eq
              | reflexivity
              | symmetry; rewrite (itree_eta u2), Hou2, Eqit.bind_vis; reflexivity |].
            apply RP_Step; unfold rp_step_body; cbn; right; right.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               exists (h1 p), (h2 p); split; [reflexivity | split; [reflexivity | exact Hboth]].
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               exists (h1 a1), (h2 a2); split; [reflexivity | split; [reflexivity | exact HA]].
      - eapply refine_prov__obs_eq;
          [exact Hr_eq
          | symmetry; rewrite (itree_eta u1), Hu1, Eqit.bind_tau; reflexivity
          | reflexivity
          | eapply RP_TauL; [reflexivity | exact IH]].
      - eapply refine_prov__obs_eq;
          [exact Hr_eq
          | reflexivity
          | symmetry; rewrite (itree_eta u2), Hu2, Eqit.bind_tau; reflexivity
          | eapply RP_TauR; [reflexivity | exact IH]]. }
    intros s1 s2 i1 i2 Hinit; apply Hcore.
    exists (interp_cfg_exc ctx1 (b1 i1) s1), (interp_cfg_exc ctx2 (b2 i2) s2).
    split; [symmetry; apply Hunf1 |].
    split; [symmetry; apply Hunf2 |].
    apply refine_prov_incl; [apply incl_refl | apply Hbody; [apply incl_refl | exact Hinit]].
  Qed.

End ModelCombinators.


