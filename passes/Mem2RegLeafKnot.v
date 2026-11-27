(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Mem2Reg Leaf-Call Synchronization Knot ([CertPasses.Mem2RegLeafKnot])

    Purpose:
      Defines the [ev_ok] predicate and global-environment-preserving leaf
      knot ([LeafKnotG], [lg_rel], [cfg_leaf_g_sync], [mrec_knot_leaf_call_sim])
      to synchronize unpromoted leaf callees across [CallE] boundaries.

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml. Isolates non-recursive leaf
      call simulation under preserved safe provenance and global state.

    Assumptions:
      Parametric over [IP : IPtr] and [IPT : @IPtrTheory IP]; depends on
      [PassCommon] and [Mem2RegSpec]..[Mem2RegCpsSSA]; zero custom axioms.

    Section Outline:
      - [MemoryAndSerialization]: 3M. [mcfg_eq_g_post], [ev_ok] syntactic/denote
        closure, [leaf_ctx_fn_rel], and [Section LeafKnotG]. *)

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

From CertPasses Require Import Mem2RegSpec Mem2RegModel Mem2RegMemBase Mem2RegGhostInv Mem2RegExprLift Mem2RegCpsSSA.

#[local] Notation refine_prov_bind := m2r_refine_prov_bind (only parsing).

Section MemoryAndSerialization.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Existing Instance MemoryModelStateV.
  #[local] Existing Instance MemoryModelPrimitivesV.
  #[local] Existing Instance PointerV.
  #[local] Existing Instance PIV.
  #[local] Existing Instance PITheoryV.
  #[local] Hint Resolve refine_prov__mon : paco.
  Arguments memM_interp_prov {_ _} [T] _ _.
  Arguments interp_vellvm_prov_h {_ _} [T] _ _.
  #[local] Hint Resolve tau_expand__mon prov_te__mon : paco.

  (** ** 3M. Global-Environment-Preserving Leaf Module Knot & Stage 2 Simulation *)

  Definition mcfg_eq_g_post {R : Type}
    (g0 : @global_env (@ParamsV IP IPT)) (U0 U' : list N)
    (x1 x2 : Res R) : Prop :=
    let '(s1', r1) := x1 in
    let '(s2', r2) := x2 in
    incl U0 U' /\
    mem_stack_equal (state_memory_stack (fst s1')) (state_memory_stack (fst s2')) /\
    snd s1' = snd s2' /\
    snd (snd s1') = g0 /\
    r1 = r2.

  Definition is_non_global_mcfg_ev {X : Type}
    (e : @MCFGEtop (@ParamsV IP IPT) X) : bool :=
    match e with
    | inr1 (inr1 (inl1 (GlobalWrite _ _))) => false
    | _ => true
    end.

  Definition is_non_global_cfg_ev {X : Type}
    (e : @CFGEtop (@ParamsV IP IPT) X) : bool :=
    match e with
    | inl1 _ => true
    | inr1 me => is_non_global_mcfg_ev me
    end.

  Lemma on_mem_prov_g_sync {T : Type}
    (m : @memM (@ParamsV IP IPT) _ T)
    (g0 : @global_env (@ParamsV IP IPT)) (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (Hm : refine_prov (eq_sync_post U) U
            (memM_interp_prov m σ1)
            (memM_interp_prov m σ2)) :
    refine_prov (mcfg_eq_g_post g0 U) U
      (on_mem_prov (memM_interp_prov m) (σ1, (ls, g0)))
      (on_mem_prov (memM_interp_prov m) (σ2, (ls, g0))).
  Proof using.
    unfold on_mem_prov.
    eapply PassCommonModel.refine_prov_bind; [exact Hm |].
    intros U' [σ1' r1] [σ2' r2] _ (Hinc & Heq & <-).
    apply refine_prov_ret;
      exact (conj Hinc (conj Heq (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
  Qed.

  Lemma on_ls_prov_g_sync {T : Type}
    (f : Monads.stateT (@stack_frame (@ParamsV IP IPT) * stack)
           (itree (@MCFGEbot (@ParamsV IP IPT))) T)
    (g0 : @global_env (@ParamsV IP IPT)) (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_g_post g0 U) U
      (on_ls_prov f (σ1, (ls, g0)))
      (on_ls_prov f (σ2, (ls, g0))).
  Proof using.
    unfold on_ls_prov.
    eapply PassCommonModel.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' [ls1' r1] [ls2' r2] _ [Hinc Heq_p].
    inversion Heq_p; subst ls2' r2.
    apply refine_prov_ret;
      exact (conj Hinc (conj Heq (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
  Qed.

  Lemma fused_trigger_prov_g_sync {F : Type -> Type} `{F -< ProvBotE} {T : Type}
    (e : F T) (g0 : @global_env (@ParamsV IP IPT)) (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_g_post g0 U) U
      (fused_trigger_prov T e (σ1, (ls, g0)))
      (fused_trigger_prov T e (σ2, (ls, g0))).
  Proof using.
    unfold fused_trigger_prov.
    eapply PassCommonModel.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' r1 r2 _ [Hinc <-].
    apply refine_prov_ret;
      exact (conj Hinc (conj Heq (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
  Qed.

  Lemma fused_draw_prov_g_sync {T : Type}
    (e : @DrawE (@ParamsV IP IPT) T)
    (g0 : @global_env (@ParamsV IP IPT)) (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_g_post g0 U) U
      (fused_draw_prov T e (σ1, (ls, g0)))
      (fused_draw_prov T e (σ2, (ls, g0))).
  Proof using.
    unfold fused_draw_prov.
    eapply PassCommonModel.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' r1 r2 _ [Hinc <-].
    apply refine_prov_ret;
      exact (conj Hinc (conj Heq (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
  Qed.

  Lemma interp_vellvm_prov_h_non_global_g_sync {X : Type}
    (e : @MCFGEtop (@ParamsV IP IPT) X)
    (Hng : is_non_global_mcfg_ev e = true)
    (g0 : @global_env (@ParamsV IP IPT)) (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_g_post g0 U) U
      (interp_vellvm_prov_h e (σ1, (ls, g0)))
      (interp_vellvm_prov_h e (σ2, (ls, g0))).
  Proof using.
    unfold interp_vellvm_prov_h.
    destruct e as [e1 | [e2 | [e3 | [[e4a | e4b] | [e5 | [e6 | [e7 | [e8 | [e9 | [e10 | e11]]]]]]]]]];
      cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
    - apply fused_trigger_prov_g_sync, Heq.
    - unfold fused_intrinsic_prov, handle_intrinsic.
      apply on_mem_prov_g_sync, handle_intrinsicM_equal_sync, Heq.
    - destruct e3 as [gid dv | gid]; [discriminate Hng |].
      unfold fused_global_prov, on_genv_prov, handle_global_debug, handle_global, update_globals_ref.
      cbn - [Maps.lookup Maps.add lift_bot_prov].
      destruct (Maps.lookup gid g0) as [v |];
        cbn - [Maps.lookup Maps.add lift_bot_prov].
      + eapply refine_prov_obs_eq;
          [symmetry; rewrite ?lift_bot_prov_bind_ret, ?lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite ?lift_bot_prov_bind_ret, ?lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity |].
        apply refine_prov_ret;
          exact (conj (incl_refl U) (conj Heq (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
      + unfold raise, trigger_cast, ITree.trigger, lift_bot_prov;
          cbn - [Maps.lookup Maps.add].
        pstep; apply RP_Step; unfold rp_step_body.
        repeat (rewrite observe_bind || rewrite observe_translate); cbn; right; right;
          split; [exact I | intros [] [] _].
    - unfold fused_local_prov; apply on_ls_prov_g_sync, Heq.
    - unfold fused_stack_prov; apply on_ls_prov_g_sync, Heq.
    - unfold fused_memory_prov, handle_memory.
      apply on_mem_prov_g_sync, handle_memoryM_equal_sync, Heq.
    - apply fused_draw_prov_g_sync, Heq.
    - apply fused_trigger_prov_g_sync, Heq.
    - apply fused_trigger_prov_g_sync, Heq.
    - apply fused_trigger_prov_g_sync, Heq.
    - apply fused_trigger_prov_g_sync, Heq.
    - apply fused_trigger_prov_g_sync, Heq.
  Qed.

  Inductive ev_ok_ {E : Type -> Type} {R : Type}
    (ok_ev : forall X, E X -> bool) (r : itree E R -> Prop) : itree E R -> Prop :=
  | EOK_Ret (x : R) (t : itree E R) :
      observe t = RetF x -> ev_ok_ ok_ev r t
  | EOK_Tau (m t : itree E R) :
      observe t = TauF m -> r m -> ev_ok_ ok_ev r t
  | EOK_Vis X (e : E X) (k : X -> itree E R) (t : itree E R) :
      observe t = VisF e k ->
      ok_ev X e = true ->
      (forall x, r (k x)) ->
      ev_ok_ ok_ev r t.

  Lemma ev_ok__mon {E : Type -> Type} {R : Type}
    (ok_ev : forall X, E X -> bool) :
    monotone1 (@ev_ok_ E R ok_ev).
  Proof using.
    intros t r r' H Hle.
    destruct H as [x t Ho | m t Ho Hm | X e k t Ho Hok Hk].
    - exact (EOK_Ret ok_ev r' x t Ho).
    - exact (EOK_Tau ok_ev r' m t Ho (Hle _ Hm)).
    - exact (EOK_Vis ok_ev r' X e k t Ho Hok (fun x => Hle _ (Hk x))).
  Qed.
  #[local] Hint Resolve ev_ok__mon : paco.

  Definition ev_ok {E : Type -> Type} {R : Type}
    (ok_ev : forall X, E X -> bool) (t : itree E R) : Prop :=
    paco1 (ev_ok_ ok_ev) bot1 t.

  Lemma ev_ok_obs_eq {E : Type -> Type} {R : Type}
    (ok_ev : forall X, E X -> bool) (t1 t2 : itree E R) :
    t1 ≅ t2 ->
    ev_ok ok_ev t1 ->
    ev_ok ok_ev t2.
  Proof using.
    revert t1 t2; pcofix CIH; intros t1 t2 Heq Hok; pstep.
    punfold Hok; punfold Heq; red in Heq.
    destruct Hok as [x t1' Ho1 | m1 t1' Ho1 Hm1 | X e k1 t1' Ho1 He Hk1];
      rewrite Ho1 in Heq; pclearbot.
    - apply eqitF_inv_Ret_l in Heq as (x2 & Ho2 & <-).
      exact (EOK_Ret ok_ev _ x t2 Ho2).
    - apply eqitF_inv_Tau_l in Heq as (m2 & Ho2 & Hm12); pclearbot.
      eapply EOK_Tau; [exact Ho2 | right; exact (CIH m1 m2 Hm12 Hm1)].
    - apply eqitF_inv_Vis_l in Heq as (k2 & Ho2 & Hk12).
      eapply EOK_Vis; [exact Ho2 | exact He |].
      intros x; specialize (Hk12 x); pclearbot.
      right; exact (CIH _ _ Hk12 (Hk1 x)).
  Qed.

  Lemma ev_ok_ret {E : Type -> Type} {R : Type}
    (ok_ev : forall X, E X -> bool) (x : R) :
    ev_ok ok_ev (Ret x).
  Proof using.
    pstep; exact (EOK_Ret ok_ev _ x (Ret x) Logic.eq_refl).
  Qed.

  Lemma ev_ok_trigger {E : Type -> Type} {X : Type}
    (ok_ev : forall Y, E Y -> bool) (e : E X) :
    ok_ev X e = true ->
    ev_ok ok_ev (ITree.trigger e).
  Proof using.
    intros Hok; pstep.
    refine (EOK_Vis ok_ev _ X e (fun x => Ret x) (ITree.trigger e) Logic.eq_refl Hok _).
    intros x; left; apply ev_ok_ret.
  Qed.

  Lemma ev_ok_bind {E : Type -> Type} {A B : Type}
    (ok_ev : forall X, E X -> bool)
    (t : itree E A) (k : A -> itree E B) :
    ev_ok ok_ev t ->
    (forall a, ev_ok ok_ev (k a)) ->
    ev_ok ok_ev (ITree.bind t k).
  Proof using.
    intros Ht Hk.
    assert (Hgen : forall b : itree E B,
              (exists t0, ITree.bind t0 k ≅ b /\ ev_ok ok_ev t0) ->
              ev_ok ok_ev b).
    { pcofix CIH; intros b (t0 & Eb & Ht0); punfold Ht0.
      destruct Ht0 as [a t0' Ho | m t0' Ho Hm | X e h t0' Ho Hok Hh]; pclearbot.
      - assert (Eka : k a ≅ b).
        { rewrite <- Eb, (itree_eta t0'), Ho, Eqit.bind_ret_l; reflexivity. }
        pose proof (ev_ok_obs_eq ok_ev (k a) b Eka (Hk a)) as Hb.
        eapply paco1_mon; [exact Hb | intros ? []].
      - pstep; punfold Eb; red in Eb; rewrite observe_bind, Ho in Eb; cbn in Eb.
        apply eqitF_inv_Tau_l in Eb as (m' & Ho' & Hm'); pclearbot.
        eapply EOK_Tau; [exact Ho' |].
        right; apply CIH; exists m; split; [exact Hm' | exact Hm].
      - pstep; punfold Eb; red in Eb; rewrite observe_bind, Ho in Eb; cbn in Eb.
        apply eqitF_inv_Vis_l in Eb as (k' & Ho' & Hk').
        eapply EOK_Vis; [exact Ho' | exact Hok |].
        intros x; specialize (Hk' x); pclearbot.
        right; apply CIH; exists (h x); split; [exact Hk' | exact (Hh x)]. }
    apply Hgen; exists t; split; [reflexivity | exact Ht].
  Qed.

  Lemma ev_ok_EOU_mcfg {R : Type} (m : EOU R) :
    ev_ok (@is_non_global_mcfg_ev) (EOU_to_itree m).
  Proof using.
    destruct m as [msg | msg | msg | x]; cbn [EOU_to_itree].
    - unfold raise, trigger_cast; eapply ev_ok_bind;
        [apply ev_ok_trigger; reflexivity | intros []].
    - unfold raiseOOM, trigger_cast; eapply ev_ok_bind;
        [apply ev_ok_trigger; reflexivity | intros []].
    - unfold raiseUB, trigger_cast; eapply ev_ok_bind;
        [apply ev_ok_trigger; reflexivity | intros []].
    - apply ev_ok_ret.
  Qed.

  Lemma m2r_assoc_in {K V : Type} {Heq : ExtLib.Core.RelDec.RelDec (@Logic.eq K)}
    {Hcorr : ExtLib.Core.RelDec.RelDec_Correct Heq}
    (k : K) (l : list (K * V)) (v : V) :
    assoc k l = Some v ->
    exists k0, In (k0, v) l.
  Proof using.
    induction l as [| [k0 v0] rest IH]; cbn [assoc]; [intros H; discriminate H |].
    destruct (ExtLib.Core.RelDec.rel_dec k k0).
    - intros H; inversion H; subst v0; exists k0;
      left; reflexivity.
    - intros H; destruct (IH H) as [k1 Hin]; exists k1; right; exact Hin.
  Qed.

  Lemma defined_intrinsics_ev_ok :
    Forall
      (fun '(_, f) =>
         forall args va,
           ev_ok (@is_non_global_mcfg_ev) (f args va))
      (defined_intrinsics (Pa := @ParamsV IP IPT) (E := @MCFGEtop (@ParamsV IP IPT))).
  Proof using.
    assert (Hpure : forall pf args va,
              ev_ok (@is_non_global_mcfg_ev)
                (pure_to_semantic (Pa := @ParamsV IP IPT) (E := @MCFGEtop (@ParamsV IP IPT)) pf args va)).
    { intros pf args va; unfold pure_to_semantic; apply ev_ok_EOU_mcfg. }
    assert (Hpbase : forall pbf args va,
              ev_ok (@is_non_global_mcfg_ev)
                (pure_base_to_semantic (Pa := @ParamsV IP IPT) (E := @MCFGEtop (@ParamsV IP IPT)) pbf args va)).
    { intros pbf args va; unfold pure_base_to_semantic; apply Hpure. }
    unfold defined_intrinsics, extra_fp_intrinsics, extra_int_intrinsics,
           mk_int_unop_defs, mk_int_unop_flag_defs, mk_int_binop_defs,
           mk_expect_int_defs, mk_int_ternop_defs, mk_int_ovf_binop_defs.
    repeat (apply Forall_app; split);
      try (apply Forall_map, Forall_forall; intros ? _ args va; first [apply Hpbase | apply Hpure]).
    - repeat (apply Forall_cons; [intros args va; apply Hpbase |]); apply Forall_nil.
    - repeat (apply Forall_cons; [intros args va; apply Hpbase |]); apply Forall_nil.
    - apply Forall_cons; [intros args va; apply Hpbase |].
      apply Forall_cons; [intros args va; apply Hpbase |].
      apply Forall_cons.
      + intros args va; unfold llvm_va_start.
        destruct args as [| a [| ? ?]], va as [vp |];
          lazymatch goal with
          | |- ev_ok _ (match ?x with _ => _ end) => idtac
          | |- _ =>
              unfold raise, trigger_cast; eapply ev_ok_bind;
              [apply ev_ok_trigger; reflexivity | intros []]
          end.
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        destruct a as [db | |];
          [destruct db;
           lazymatch goal with
           | |- ev_ok _ (ITree.bind _ _) =>
               eapply ev_ok_bind;
               [unfold store, Subevent.trigger; try unfold trigger_cast; apply ev_ok_trigger; reflexivity
               | intros u0; apply ev_ok_ret]
           | |- _ =>
               unfold raiseUB, trigger_cast; eapply ev_ok_bind;
               [apply ev_ok_trigger; reflexivity | intros []]
           end
          | eapply ev_ok_bind;
            [unfold store, Subevent.trigger; try unfold trigger_cast; apply ev_ok_trigger; reflexivity
            | intros u0; apply ev_ok_ret]
          | eapply ev_ok_bind;
            [unfold store, Subevent.trigger; try unfold trigger_cast; apply ev_ok_trigger; reflexivity
            | intros u0; apply ev_ok_ret]].
      + apply Forall_cons.
        * intros args va; unfold llvm_va_end;
            cbn [ExtLib.Structures.Monad.ret Monad_itree]; apply ev_ok_ret.
        * apply Forall_cons; [| apply Forall_nil].
          intros args va; unfold llvm_va_copy.
          destruct args as [| dest [| src [| ? ?]]];
            cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
            lazymatch goal with
            | |- ev_ok _ (ITree.bind (load _ _) _) =>
                eapply ev_ok_bind;
                [unfold load, Subevent.trigger; try unfold trigger_cast; apply ev_ok_trigger; reflexivity |];
                intros vargs; eapply ev_ok_bind;
                [unfold store, Subevent.trigger; try unfold trigger_cast; apply ev_ok_trigger; reflexivity |];
                intros u0; apply ev_ok_ret
            | |- _ =>
                unfold raise, trigger_cast; eapply ev_ok_bind;
                [apply ev_ok_trigger; reflexivity | intros []]
            end.
  Qed.

  Lemma interp_state_ev_ok_g_sync {R : Type}
    (t : @MCFGtop (@ParamsV IP IPT) R)
    (Hok : ev_ok (@is_non_global_mcfg_ev) t)
    (g0 : @global_env (@ParamsV IP IPT)) (U0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_g_post g0 U0) U0
      (interp_state interp_vellvm_prov_h t (σ1, (ls, g0)))
      (interp_state interp_vellvm_prov_h t (σ2, (ls, g0))).
  Proof using.
    set (k_cont := fun {X : Type} (k : X -> @MCFGtop (@ParamsV IP IPT) R)
                       '(s', x) => Tau (interp_state interp_vellvm_prov_h (k x) s')).
    set (rel := fun (U : list N) (a1 a2 : itree ProvBotE (Res R)) =>
                  (exists t0 s_a s_b ls0,
                     interp_state interp_vellvm_prov_h t0 (s_a, (ls0, g0)) ≅ a1 /\
                     interp_state interp_vellvm_prov_h t0 (s_b, (ls0, g0)) ≅ a2 /\
                     ev_ok (@is_non_global_mcfg_ev) t0 /\
                     incl U0 U /\
                     mem_stack_equal (state_memory_stack s_a) (state_memory_stack s_b)) \/
                  (exists X (u1 u2 : itree ProvBotE (Res X)) (k : X -> @MCFGtop (@ParamsV IP IPT) R),
                     ITree.bind u1 (k_cont X k) ≅ a1 /\
                     ITree.bind u2 (k_cont X k) ≅ a2 /\
                     (forall x, ev_ok (@is_non_global_mcfg_ev) (k x)) /\
                     refine_prov (mcfg_eq_g_post g0 U0) U u1 u2)).
    assert (Hobs : forall U a1 a1' a2 a2',
              a1 ≅ a1' -> a2 ≅ a2' -> rel U a1 a2 -> rel U a1' a2').
    { intros U a1 a1' a2 a2' E1 E2 [(t0 & s_a & s_b & ls0 & Ea & Eb & Ht0 & Hinc & Hm)
                                   | (X & u1 & u2 & k & Ea & Eb & Hk & Hu)].
      - left; exists t0, s_a, s_b, ls0;
          exact (conj (transitivity Ea E1) (conj (transitivity Eb E2) (conj Ht0 (conj Hinc Hm)))).
      - right; exists X, u1, u2, k;
          exact (conj (transitivity Ea E1) (conj (transitivity Eb E2) (conj Hk Hu))). }
    assert (Hbind_step :
              forall X U (u1 u2 : itree ProvBotE (Res X)) k,
                (forall x, ev_ok (@is_non_global_mcfg_ev) (k x)) ->
                refine_prov (mcfg_eq_g_post g0 U0) U u1 u2 ->
                refine_prov_ (mcfg_eq_g_post g0 U0) rel U
                  (ITree.bind u1 (k_cont X k))
                  (ITree.bind u2 (k_cont X k))).
    { intros X U u1 u2 k Hk Hu; punfold Hu.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [[[s_a' [ls1' g1']] x1] | m1 | Y1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [[[s_b' rest2'] x2] | m2 | Y2 e2 h2] eqn:Hou2;
            try contradiction.
          destruct Hstep as (Hinc & Hm & Hrest & Hg1 & <-).
          cbn [fst snd] in Hm, Hrest, Hg1; subst rest2' g1'.
          apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2; cbn.
          left; exists (k x1), s_a', s_b', ls1';
            split; [reflexivity | split; [reflexivity | exact (conj (Hk x1) (conj Hinc Hm))]].
        + destruct (observe u2) as [? | m2 | ? ? ?] eqn:Hou2; try contradiction.
          pclearbot; apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2.
          right; exists X, m1, m2, k;
            split; [reflexivity | split; [reflexivity | exact (conj Hk Hstep)]].
        + apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind u1), Hou1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            right; exists X, (h1 p), u2, k;
              split; [reflexivity | split; [reflexivity | exact (conj Hk Hleft)]].
          * right; right.
            destruct (observe u2) as [? | ? | Y2 e2 h2] eqn:Hou2; try contradiction.
            rewrite (observe_bind u2), Hou2.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               right; exists X, (h1 p), (h2 p), k;
                 split; [reflexivity | split; [reflexivity | exact (conj Hk Hboth)]].
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               right; exists X, (h1 a1), (h2 a2), k;
                 split; [reflexivity | split; [reflexivity | exact (conj Hk HA)]].
      - eapply RP_TauL;
          [rewrite (observe_bind u1), Hu1; reflexivity | exact IH].
      - eapply RP_TauR;
          [rewrite (observe_bind u2), Hu2; reflexivity | exact IH]. }
    assert (Hcore : forall U a1 a2, rel U a1 a2 -> refine_prov (mcfg_eq_g_post g0 U0) U a1 a2).
    { pcofix CIH; intros U a1 a2 Hst; pstep.
      eapply refine_prov__mon with (r := rel); [| intros U' x1 x2 Hx; right; apply CIH, Hx].
      destruct Hst as [(t0 & s_a & s_b & ls0 & E1 & E2 & Ht0 & Hinc & Hm)
                      | (X & u1 & u2 & k & E1 & E2 & Hk & Hu)].
      - eapply refine_prov__obs_eq; [exact Hobs | exact E1 | exact E2 |].
        punfold Ht0; destruct Ht0 as [rv t0' Hot | mt t0' Hot Hmt | X e k t0' Hot He Hk]; pclearbot.
        + assert (Et1 : Ret ((s_a, (ls0, g0)), rv) ≅ interp_state interp_vellvm_prov_h t0' (s_a, (ls0, g0)))
            by (symmetry; rewrite (itree_eta t0'), Hot; apply interp_state_ret).
          assert (Et2 : Ret ((s_b, (ls0, g0)), rv) ≅ interp_state interp_vellvm_prov_h t0' (s_b, (ls0, g0)))
            by (symmetry; rewrite (itree_eta t0'), Hot; apply interp_state_ret).
          eapply refine_prov__obs_eq; [exact Hobs | exact Et1 | exact Et2 |].
          apply RP_Step; cbn;
            exact (conj Hinc (conj Hm (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
        + assert (Et1 : Tau (interp_state interp_vellvm_prov_h mt (s_a, (ls0, g0))) ≅
                        interp_state interp_vellvm_prov_h t0' (s_a, (ls0, g0)))
            by (symmetry; rewrite (itree_eta t0'), Hot; apply interp_state_tau).
          assert (Et2 : Tau (interp_state interp_vellvm_prov_h mt (s_b, (ls0, g0))) ≅
                        interp_state interp_vellvm_prov_h t0' (s_b, (ls0, g0)))
            by (symmetry; rewrite (itree_eta t0'), Hot; apply interp_state_tau).
          eapply refine_prov__obs_eq; [exact Hobs | exact Et1 | exact Et2 |].
          apply RP_Step; cbn; left; exists mt, s_a, s_b, ls0;
            split; [reflexivity | split; [reflexivity | exact (conj Hmt (conj Hinc Hm))]].
        + assert (Et1 : ITree.bind (interp_vellvm_prov_h e (s_a, (ls0, g0))) (k_cont X k) ≅
                        interp_state interp_vellvm_prov_h t0' (s_a, (ls0, g0))).
          { symmetry; rewrite (itree_eta t0'), Hot, interp_state_vis.
            eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [? ?] _ <-; reflexivity]. }
          assert (Et2 : ITree.bind (interp_vellvm_prov_h e (s_b, (ls0, g0))) (k_cont X k) ≅
                        interp_state interp_vellvm_prov_h t0' (s_b, (ls0, g0))).
          { symmetry; rewrite (itree_eta t0'), Hot, interp_state_vis.
            eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [? ?] _ <-; reflexivity]. }
          eapply refine_prov__obs_eq; [exact Hobs | exact Et1 | exact Et2 |].
          apply Hbind_step; [exact Hk |].
          eapply refine_prov_weaken;
            [exact (interp_vellvm_prov_h_non_global_g_sync e He g0 U s_a s_b ls0 Hm) |].
          intros U' [s1' r1] [s2' r2] (Huu' & Hm' & Hrs & Hg' & Hr);
            exact (conj (incl_tran Hinc Huu') (conj Hm' (conj Hrs (conj Hg' Hr)))).
      - eapply refine_prov__obs_eq; [exact Hobs | exact E1 | exact E2 |].
        exact (Hbind_step X U u1 u2 k Hk Hu). }
    apply Hcore; left; exists t, σ1, σ2, ls;
      split; [reflexivity | split; [reflexivity | exact (conj Hok (conj (incl_refl U0) Heq))]].
  Qed.

  Lemma trigger_mcfg_non_global_g_sync {X : Type}
    (me : @MCFGEtop (@ParamsV IP IPT) X)
    (Hng : is_non_global_mcfg_ev me = true)
    (g0 : @global_env (@ParamsV IP IPT)) (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_g_post g0 U) U
      (interp_mcfg_model (ITree.trigger me) (σ1, (ls, g0)))
      (interp_mcfg_model (ITree.trigger me) (σ2, (ls, g0))).
  Proof using.
    unfold interp_mcfg_model.
    apply interp_state_ev_ok_g_sync; [| exact Heq].
    unfold interp_intrinsics.
    match goal with
    | |- ev_ok _ (interp ?h (ITree.trigger _)) =>
        assert (Etr : interp h (ITree.trigger me) ≅
                      ITree.bind (h X me) (fun x => Tau (Ret x)))
    end.
    { unfold ITree.trigger; rewrite interp_vis.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros x _ <-; rewrite interp_ret; reflexivity. }
    eapply ev_ok_obs_eq; [symmetry; exact Etr |].
    eapply ev_ok_bind; [| intros x; pstep; eapply EOK_Tau; [reflexivity |
      left; apply ev_ok_ret]].
    destruct me as [e1 | [ie | fe]].
    - cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ E_trigger Subevent.trigger];
      apply ev_ok_trigger; reflexivity.
    - cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
      unfold handle_intrinsics.
      destruct ie as [dt fname args va]; cbn beta iota.
      destruct (assoc fname defs_assoc) as [f |] eqn:Eassoc.
      + cbn beta iota.
        apply m2r_assoc_in in Eassoc as [k0 Hin].
        unfold defs_assoc in Hin; apply in_map_iff in Hin as ([decl f0] & Heq_p & Hin_def).
        destruct (dc_name decl); inversion Heq_p; subst f0;
          (pose proof defined_intrinsics_ev_ok as Hall; rewrite Forall_forall in Hall;
           exact (Hall (decl, f) Hin_def args va)).
      + cbn beta iota; apply ev_ok_trigger; reflexivity.
    - cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ F_trigger Subevent.trigger].
      apply ev_ok_trigger, Hng.
  Qed.

  Lemma ev_ok_tau {E : Type -> Type} {R : Type}
    (ok_ev : forall X, E X -> bool) (m : itree E R) :
    ev_ok ok_ev m ->
    ev_ok ok_ev (Tau m).
  Proof using.
    intros Hm; pstep; exact (EOK_Tau ok_ev _ m (Tau m) Logic.eq_refl (or_introl Hm)).
  Qed.

  Lemma ev_ok_fmap {E : Type -> Type} {A B : Type}
    (ok_ev : forall X, E X -> bool) (f : A -> B) (t : itree E A) :
    ev_ok ok_ev t ->
    ev_ok ok_ev (f <$> t).
  Proof using IP IPT.
    intros Ht; unfold Functor.fmap, Functor_itree, ITree.map.
    eapply ev_ok_bind; [exact Ht | intros a; apply ev_ok_ret].
  Qed.

  Lemma ev_ok_map_monad {E : Type -> Type} {A B : Type}
    (ok_ev : forall X, E X -> bool)
    (f : A -> itree E B) (xs : list A) :
    (forall a, In a xs -> ev_ok ok_ev (f a)) ->
    ev_ok ok_ev (map_monad f xs).
  Proof using IP IPT.
    intros Hf; induction xs as [| x xs' IH];
      cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    - apply ev_ok_ret.
    - eapply ev_ok_bind; [apply Hf; left; reflexivity |].
      intros b; eapply ev_ok_bind.
      + apply IH; intros a Ha; apply Hf; right; exact Ha.
      + intros bs; apply ev_ok_ret.
  Qed.

  Lemma ev_ok_loop_monad {E : Type -> Type} {A : Type}
    (ok_ev : forall X, E X -> bool)
    (f : A -> itree E unit) (xs : list A) :
    (forall a, In a xs -> ev_ok ok_ev (f a)) ->
    ev_ok ok_ev (loop_monad f xs).
  Proof using IP IPT.
    intros Hf; induction xs as [| x xs' IH];
      cbn [loop_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    - apply ev_ok_ret.
    - eapply ev_ok_bind; [apply Hf; left; reflexivity |].
      intros []; apply IH; intros a Ha; apply Hf;
        right; exact Ha.
  Qed.

  Lemma ev_ok_iter {E : Type -> Type} {I R : Type}
    (ok_ev : forall X, E X -> bool)
    (body : I -> itree E (I + R)) (i0 : I) :
    (forall i, ev_ok ok_ev (body i)) ->
    ev_ok ok_ev (ITree.iter body i0).
  Proof using IP IPT.
    intros Hbody.
    set (k_it := fun lr : I + R =>
                   match lr with
                   | inl j => Tau (ITree.iter body j)
                   | inr r => Ret r
                   end).
    assert (Hgen : forall b : itree E R,
              (exists t0, ITree.bind t0 k_it ≅ b /\ ev_ok ok_ev t0) ->
              ev_ok ok_ev b).
    { pcofix CIH; intros b (t0 & Eb & Ht0); punfold Ht0.
      destruct Ht0 as [[j | rv] t0' Ho | m t0' Ho Hm | X e h t0' Ho Hok Hh]; pclearbot.
      - assert (Et : Tau (ITree.iter body j) ≅ b).
        { rewrite <- Eb, (itree_eta t0'), Ho, Eqit.bind_ret_l; reflexivity. }
        pstep; punfold Et; red in Et; cbn in Et;
          apply eqitF_inv_Tau_l in Et as (m' & Ho' & Hm'); pclearbot.
        eapply EOK_Tau; [exact Ho' |].
        right; apply CIH; exists (body j); split; [| exact (Hbody j)].
        etransitivity; [symmetry; apply unfold_iter | exact Hm'].
      - assert (Er : Ret rv ≅ b).
        { rewrite <- Eb, (itree_eta t0'), Ho, Eqit.bind_ret_l; reflexivity. }
        pstep; punfold Er; red in Er; cbn in Er;
          apply eqitF_inv_Ret_l in Er as (rv' & Ho' & <-).
        exact (EOK_Ret ok_ev _ rv b Ho').
      - pstep; punfold Eb; red in Eb; rewrite observe_bind, Ho in Eb; cbn in Eb.
        apply eqitF_inv_Tau_l in Eb as (m' & Ho' & Hm'); pclearbot.
        eapply EOK_Tau; [exact Ho' |].
        right; apply CIH; exists m; split; [exact Hm' | exact Hm].
      - pstep; punfold Eb; red in Eb; rewrite observe_bind, Ho in Eb; cbn in Eb.
        apply eqitF_inv_Vis_l in Eb as (k' & Ho' & Hk').
        eapply EOK_Vis; [exact Ho' | exact Hok |].
        intros x; specialize (Hk' x); pclearbot.
        right; apply CIH; exists (h x); split; [exact Hk' | exact (Hh x)]. }
    apply Hgen; exists (body i0); split; [symmetry; apply unfold_iter | exact (Hbody i0)].
  Qed.

  Lemma ev_ok_cfg_subevent {F : Type -> Type} `{F -< @CFGEtop (@ParamsV IP IPT)} {X : Type}
    (e : F X)
    (Hok : is_non_global_cfg_ev (subevent X e) = true) :
    ev_ok (@is_non_global_cfg_ev) (Subevent.trigger e).
  Proof using.
    unfold Subevent.trigger; apply ev_ok_trigger, Hok.
  Qed.

  Lemma ev_ok_cfg_raise {A : Type} (msg : string) :
    ev_ok (@is_non_global_cfg_ev) (@raise (@CFGEtop (@ParamsV IP IPT)) A _ msg).
  Proof using.
    unfold raise, trigger_cast; eapply ev_ok_bind;
      [apply ev_ok_trigger; reflexivity | intros []].
  Qed.

  Lemma ev_ok_cfg_raiseOOM {A : Type} (msg : string) :
    ev_ok (@is_non_global_cfg_ev) (@raiseOOM (@CFGEtop (@ParamsV IP IPT)) _ A msg).
  Proof using.
    unfold raiseOOM, trigger_cast; eapply ev_ok_bind;
      [apply ev_ok_trigger; reflexivity | intros []].
  Qed.

  Lemma ev_ok_cfg_raiseUB {A : Type} (msg : string) :
    ev_ok (@is_non_global_cfg_ev) (@raiseUB (@CFGEtop (@ParamsV IP IPT)) _ A msg).
  Proof using.
    unfold raiseUB, trigger_cast; eapply ev_ok_bind;
      [apply ev_ok_trigger; reflexivity | intros []].
  Qed.

  Lemma ev_ok_cfg_raiseLLVM {A : Type} (x : @exc (@ParamsV IP IPT)) :
    ev_ok (@is_non_global_cfg_ev) (@raiseLLVM (@ParamsV IP IPT) (@CFGEtop (@ParamsV IP IPT)) A _ x).
  Proof using.
    unfold raiseLLVM, trigger_cast; eapply ev_ok_bind;
      [apply ev_ok_trigger; reflexivity | intros []].
  Qed.

  Lemma ev_ok_EOU_cfg {R : Type} (m : EOU R) :
    ev_ok (@is_non_global_cfg_ev) (EOU_to_itree m).
  Proof using.
    destruct m as [msg | msg | msg | x]; cbn [EOU_to_itree].
    - apply ev_ok_cfg_raise.
    - apply ev_ok_cfg_raiseOOM.
    - apply ev_ok_cfg_raiseUB.
    - apply ev_ok_ret.
  Qed.

  Lemma ev_ok_withCall_ret {R : Type} (x : R) :
    ev_ok (@is_non_global_cfg_ev) (withCall (Ret x)).
  Proof using.
    eapply ev_ok_obs_eq; [symmetry; apply withCall_ret_eq | apply ev_ok_ret].
  Qed.

  Lemma ev_ok_withCall_bind {A B : Type}
    (u : @MCFGtop (@ParamsV IP IPT) A)
    (k : A -> @MCFGtop (@ParamsV IP IPT) B) :
    ev_ok (@is_non_global_cfg_ev) (withCall u) ->
    (forall a, ev_ok (@is_non_global_cfg_ev) (withCall (k a))) ->
    ev_ok (@is_non_global_cfg_ev) (withCall (ITree.bind u k)).
  Proof using.
    intros Hu Hk.
    eapply ev_ok_obs_eq; [symmetry; apply withCall_bind_eq |].
    exact (ev_ok_bind (@is_non_global_cfg_ev) (withCall u) (fun x => withCall (k x)) Hu Hk).
  Qed.

  Lemma ev_ok_withCall_trigger {X : Type} (me : @MCFGEtop (@ParamsV IP IPT) X) :
    is_non_global_mcfg_ev me = true ->
    ev_ok (@is_non_global_cfg_ev) (withCall (ITree.trigger me)).
  Proof using.
    intros Hng.
    eapply ev_ok_obs_eq; [symmetry; apply withCall_trigger_eq |].
    apply ev_ok_trigger, Hng.
  Qed.

  Lemma ev_ok_withCall_EOU {A : Type} (m : EOU A) :
    ev_ok (@is_non_global_cfg_ev) (withCall (EOU_to_itree m)).
  Proof using.
    destruct m as [msg | msg | msg | v]; cbn [EOU_to_itree].
    - unfold raise, trigger_cast; eapply ev_ok_withCall_bind;
        [apply ev_ok_withCall_trigger; reflexivity | intros []].
    - unfold raiseOOM, trigger_cast; eapply ev_ok_withCall_bind;
        [apply ev_ok_withCall_trigger; reflexivity | intros []].
    - unfold raiseUB, trigger_cast; eapply ev_ok_withCall_bind;
        [apply ev_ok_withCall_trigger; reflexivity | intros []].
    - apply ev_ok_withCall_ret.
  Qed.

  Lemma ev_ok_withCall_map_monad {A B : Type}
    (f : A -> @MCFGtop (@ParamsV IP IPT) B) (xs : list A) :
    (forall a, In a xs -> ev_ok (@is_non_global_cfg_ev) (withCall (f a))) ->
    ev_ok (@is_non_global_cfg_ev) (withCall (map_monad f xs)).
  Proof using.
    intros Hf; induction xs as [| a xs' IH];
      cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    - apply ev_ok_withCall_ret.
    - eapply ev_ok_withCall_bind; [apply Hf; left; reflexivity |].
      intros b; eapply ev_ok_withCall_bind.
      + apply IH; intros a' Ha'; apply Hf; right; exact Ha'.
      + intros bs; apply ev_ok_withCall_ret.
  Qed.

  Lemma ev_ok_withCall_convert
    (ct : conversion_type) (t_from : dtyp) (dv : @dvalue (@ParamsV IP IPT)) (t_to : dtyp) :
    ev_ok (@is_non_global_cfg_ev) (withCall (convert ct t_from dv t_to)).
  Proof using.
    unfold convert; destruct ct as [| pct | ict].
    - destruct (dtyp_eqb t_from t_to); [apply ev_ok_withCall_ret |].
      match goal with |- context [(?a =? ?b)%N] => destruct (a =? b)%N end.
      + apply ev_ok_withCall_EOU.
      + apply (ev_ok_withCall_EOU (raise_error _)).
    - apply ev_ok_withCall_EOU.
    - unfold conv, Subevent.trigger; try unfold trigger_cast;
        apply ev_ok_withCall_trigger; reflexivity.
  Qed.

  Lemma ev_ok_withCall_freeze_base
    (dt : dtyp) (db : @dvalue_base (@ParamsV IP IPT)) :
    ev_ok (@is_non_global_cfg_ev) (withCall (freeze_base dt db)).
  Proof using.
    unfold freeze_base.
    destruct db as [| | | | | | | sz bv].
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros x0; apply ev_ok_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros x0; apply ev_ok_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros x0; apply ev_ok_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros x0; apply ev_ok_withCall_ret].
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros x0; apply ev_ok_withCall_ret].
    - unfold draw, Subevent.trigger; try unfold trigger_cast;
        apply ev_ok_withCall_trigger; reflexivity.
    - unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
        eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros x0; apply ev_ok_withCall_ret].
    - destruct bv as [| | bits].
      + unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
          eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros x0; apply ev_ok_withCall_ret].
      + unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
          eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros x0; apply ev_ok_withCall_ret].
      + destruct (existsb is_poison_bit bits); cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret
        Monad_itree].
        * eapply ev_ok_withCall_bind.
          -- unfold draw, Subevent.trigger; try unfold trigger_cast;
               apply ev_ok_withCall_trigger; reflexivity.
          -- intros x; apply ev_ok_withCall_ret.
        * unfold Functor.fmap, Functor_itree, ITree.map, ExtLib.Structures.Monad.ret, Monad_itree;
            eapply ev_ok_withCall_bind; [apply ev_ok_withCall_ret | intros x0; apply ev_ok_withCall_ret].
  Qed.

  Lemma ev_ok_withCall_freeze
    (dt : dtyp) (dv : @dvalue (@ParamsV IP IPT)) :
    ev_ok (@is_non_global_cfg_ev) (withCall (freeze dt dv)).
  Proof using.
    remember (m2r_dvalue_size dv) as sz eqn:Esz.
    assert (Hle : (m2r_dvalue_size dv <= sz)%nat) by lia; clear Esz.
    revert dv dt Hle; induction sz as [| sz IH]; intros dv dt Hle.
    - pose proof (m2r_dvalue_size_pos dv); lia.
    - destruct dv as [db | p fields | vec elts]; cbn [freeze].
      + apply ev_ok_withCall_freeze_base.
      + destruct dt as [| p' dts |];
          [apply (ev_ok_withCall_EOU (raise_error _)) | | apply (ev_ok_withCall_EOU (raise_error _))].
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        eapply ev_ok_withCall_bind; [| intros vals; apply ev_ok_withCall_ret].
        cbn [m2r_dvalue_size] in Hle.
        assert (Hfld : ((fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) fields
          <= sz)%nat) by lia.
        clear Hle.
        lazymatch goal with
        | |- ev_ok ?P (withCall (?go fields dts [])) =>
            cut (forall acc : list (@dvalue (@ParamsV IP IPT)),
                    ev_ok P (withCall (go fields dts acc)));
              [intros Hcut; exact (Hcut []) |]
        end.
        revert dts Hfld; induction fields as [| v vs IHf]; intros [| t ts] Hfld acc;
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        * apply ev_ok_withCall_ret.
        * apply (ev_ok_withCall_EOU (raise_error _)).
        * apply (ev_ok_withCall_EOU (raise_error _)).
        * eapply ev_ok_withCall_bind.
          -- fold (@freeze (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT)) _ _ _ _ t v); apply IH; lia.
          -- intros dv'; apply IHf; lia.
      + destruct dt as [| | v' sz_n t];
          [apply (ev_ok_withCall_EOU (raise_error _)) | apply (ev_ok_withCall_EOU (raise_error _)) |].
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        eapply ev_ok_withCall_bind; [| intros vals; apply ev_ok_withCall_ret].
        cbn [m2r_dvalue_size] in Hle.
        assert (Helt : ((fix list_sz l := match l with [] => O | v :: r => S (m2r_dvalue_size v + list_sz r) end) elts
          <= sz)%nat) by lia.
        clear Hle.
        lazymatch goal with
        | |- ev_ok ?P (withCall (?go elts [])) =>
            cut (forall acc : list (@dvalue (@ParamsV IP IPT)),
                    ev_ok P (withCall (go elts acc)));
              [intros Hcut; exact (Hcut []) |]
        end.
        revert Helt; induction elts as [| v vs IHe]; intros Helt acc;
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        * apply ev_ok_withCall_ret.
        * eapply ev_ok_withCall_bind.
          -- fold (@freeze (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT)) _ _ _ _ t v); apply IH; lia.
          -- intros dv'; apply IHe; lia.
  Qed.

  Lemma ev_ok_denote_exp' (top : option dtyp) (e : exp dtyp) :
    ev_ok (@is_non_global_cfg_ev) (@denote_exp' (@ParamsV IP IPT) top e).
  Proof using.
    unfold denote_exp'.
    remember (m2r_exp_size e) as sz eqn:Esz.
    assert (Hle : (m2r_exp_size e <= sz)%nat) by lia; clear Esz.
    revert top e Hle; induction sz as [| sz IH]; intros top e Hle.
    - pose proof (m2r_exp_size_pos e); lia.
    - assert (Hlist :
        forall (elts : list (dtyp * exp dtyp)),
          (S ((fix list_sz l := match l with [] => O | (_, ex) :: r => S (m2r_exp_size ex + list_sz r) end) elts) <= S
            sz)%nat ->
          ev_ok (@is_non_global_cfg_ev)
            (withCall (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) elts))).
      { intros elts Helts; apply ev_ok_withCall_map_monad.
        intros [dt0 ex0] Hin; apply IH.
        clear -Hin Helts; induction elts as [| [d1 e1] rest IHr]; [contradiction |].
        destruct Hin as [Heq | Hin]; [inversion Heq; subst; lia | apply IHr; [lia | exact Hin]]. }
      destruct e; cbn [denote_exp ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree]; cbn
        [m2r_exp_size] in Hle.
      + destruct id as [gid | lid]; cbn [lookup_id];
          unfold gread, lread, Subevent.trigger; try unfold trigger_cast;
          apply ev_ok_withCall_trigger; reflexivity.
      + destruct top as [t |]; [apply ev_ok_withCall_EOU | apply (ev_ok_withCall_EOU (raise_error _))].
      + destruct top as [t |]; [apply ev_ok_withCall_EOU | apply (ev_ok_withCall_EOU (raise_error _))].
      + destruct b; apply ev_ok_withCall_ret.
      + apply ev_ok_withCall_ret.
      + destruct top as [t |]; [apply ev_ok_withCall_EOU | apply (ev_ok_withCall_EOU (raise_error _))].
      + eapply ev_ok_withCall_bind; [apply (Hlist elts Hle) | intros vs0; apply ev_ok_withCall_ret].
      + apply ev_ok_withCall_ret.
      + apply ev_ok_withCall_ret.
      + eapply ev_ok_withCall_bind; [apply (Hlist fields Hle) | intros vs0; apply ev_ok_withCall_ret].
      + eapply ev_ok_withCall_bind; [apply ev_ok_withCall_EOU |].
        intros []; eapply ev_ok_withCall_bind; [apply (Hlist fields Hle) | intros vs0; apply ev_ok_withCall_ret].
      + eapply ev_ok_withCall_bind; [apply (Hlist elts Hle) | intros vs0; apply ev_ok_withCall_ret].
      + eapply ev_ok_withCall_bind; [apply (Hlist elts Hle) | intros vs0; apply ev_ok_withCall_ret].
      + eapply ev_ok_withCall_bind; [apply IH; lia | intros x1; eapply ev_ok_withCall_bind; [apply
        IH; lia | intros x2; apply ev_ok_withCall_EOU]].
      + eapply ev_ok_withCall_bind; [apply IH; lia | intros x1; eapply ev_ok_withCall_bind; [apply
        IH; lia | intros x2; apply ev_ok_withCall_EOU]].
      + eapply ev_ok_withCall_bind; [apply IH; lia | intros x1; eapply ev_ok_withCall_bind; [apply
        IH; lia | intros x2; apply ev_ok_withCall_EOU]].
      + destruct v as [dt1 op1]; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros
        x1; apply ev_ok_withCall_EOU].
      + eapply ev_ok_withCall_bind; [apply IH; lia | intros x1; eapply ev_ok_withCall_bind; [apply
        IH; lia | intros x2; apply ev_ok_withCall_EOU]].
      + eapply ev_ok_withCall_bind; [apply IH; lia | intros x1; apply ev_ok_withCall_convert].
      + destruct ptrval as [dt2 ptr_e].
        eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia |].
        intros x1; eapply ev_ok_withCall_bind; [apply Hlist; cbn in Hle; lia | intros
          x2; apply ev_ok_withCall_EOU].
      + destruct vec as [dt1 e1], idx as [dt2 e2].
        eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros x1; eapply
          ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros x2; apply ev_ok_withCall_EOU]].
      + destruct vec as [dt1 e1], elt as [dt2 e2], idx as [dt3 e3].
        eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia |].
        intros x1; eapply ev_ok_withCall_bind.
        * eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros x2; apply ev_ok_withCall_EOU].
        * intros x2; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros
          x3; apply ev_ok_withCall_EOU].
      + destruct vec1 as [dt1 e1], vec2 as [dt2 e2], idxmask as [dt3 e3].
        eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros x1; eapply
          ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros x2; eapply
          ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros x3; apply ev_ok_withCall_EOU]]].
      + destruct vec as [dt1 e1]; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros
        x1; apply ev_ok_withCall_EOU].
      + destruct vec as [dt1 e1], elt as [dt2 e2].
        eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros x1; eapply
          ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros x2; apply ev_ok_withCall_EOU]].
      + destruct cnd as [dt1 e1], v1 as [dt2 e2], v2 as [dt3 e3].
        eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros x1; eapply
          ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros x2; eapply
          ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros x3; apply ev_ok_withCall_EOU]]].
      + destruct v as [dt1 e1]; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros
        x1; apply ev_ok_withCall_freeze].
      + apply (ev_ok_withCall_EOU (raise_error _)).
      + match goal with m0 : metadata _ |- _ => destruct m0 as [| | [dt1 ex1] | | | |] end;
          try apply ev_ok_withCall_ret.
        apply IH; cbn in Hle; lia.
      + destruct elt as [dt1 e1].
        eapply ev_ok_withCall_bind; [apply ev_ok_withCall_EOU |].
        intros [sz_v t_v]; eapply ev_ok_withCall_bind; [apply IH; cbn in Hle; lia | intros
          x1; apply ev_ok_withCall_ret].
      + unfold gread, Subevent.trigger; try unfold trigger_cast;
          apply ev_ok_withCall_trigger; reflexivity.
  Qed.

  Lemma ev_ok_run_exc {A : Type} (t : @CFGtop (@ParamsV IP IPT) A) :
    ev_ok (@is_non_global_cfg_ev) t ->
    ev_ok (@is_non_global_cfg_ev) (run_exc t).
  Proof using.
    intros Ht.
    assert (Hgen : forall b : @CFGtop (@ParamsV IP IPT) (@exc (@ParamsV IP IPT) + A),
              (exists t0, (run_exc t0 ≅ b \/ Tau (run_exc t0) ≅ b) /\
                          ev_ok (@is_non_global_cfg_ev) t0) ->
              ev_ok (@is_non_global_cfg_ev) b).
    { pcofix CIH; intros b (t0 & [Eb | Eb] & Ht0).
      - punfold Ht0.
        destruct Ht0 as [a t0' Ho | m t0' Ho Hm | X e h t0' Ho Hok Hh]; pclearbot.
        + assert (Er : Ret (inr a) ≅ b).
          { rewrite <- Eb, (unfold_run_exc_obs t0'), Ho; reflexivity. }
          pstep; punfold Er; red in Er; cbn in Er;
            apply eqitF_inv_Ret_l in Er as (r' & Ho' & <-).
          exact (EOK_Ret _ _ (inr a) b Ho').
        + assert (Et : Tau (run_exc m) ≅ b).
          { rewrite <- Eb, (unfold_run_exc_obs t0'), Ho; reflexivity. }
          pstep; punfold Et; red in Et; cbn in Et;
            apply eqitF_inv_Tau_l in Et as (m' & Ho' & Hm'); pclearbot.
          eapply EOK_Tau; [exact Ho' |].
          right; apply CIH; exists m; split;
            [left; exact Hm' | exact Hm].
        + assert (Ev : match exc_of_event e with
                       | Some x => Ret (inl x)
                       | None => Vis e (fun y => Tau (run_exc (h y)))
                       end ≅ b).
          { rewrite <- Eb, (unfold_run_exc_obs t0'), Ho; reflexivity. }
          destruct (exc_of_event e) as [x |].
          * pstep; punfold Ev; red in Ev; cbn in Ev;
              apply eqitF_inv_Ret_l in Ev as (r' & Ho' & <-).
            exact (EOK_Ret _ _ (inl x) b Ho').
          * pstep; punfold Ev; red in Ev; cbn in Ev;
              apply eqitF_inv_Vis_l in Ev as (k' & Ho' & Hk').
            eapply EOK_Vis; [exact Ho' | exact Hok |].
            intros y; specialize (Hk' y); pclearbot.
            right; apply CIH; exists (h y); split;
              [right; exact Hk' | exact (Hh y)].
      - pstep; punfold Eb; red in Eb; cbn in Eb;
          apply eqitF_inv_Tau_l in Eb as (m' & Ho' & Hm'); pclearbot.
        eapply EOK_Tau; [exact Ho' |].
        right; apply CIH; exists t0; split;
          [left; exact Hm' | exact Ht0]. }
    apply Hgen; exists t; split; [left; reflexivity | exact Ht].
  Qed.

  Lemma ev_ok_assert_dereferenceable
    (or_null : bool) (n : N) (v : @dvalue (@ParamsV IP IPT)) (msg : string) :
    ev_ok (@is_non_global_cfg_ev)
      (assert_dereferenceable (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT)) or_null n v msg).
  Proof using.
    unfold assert_dereferenceable.
    destruct v as [db | |]; [| apply ev_ok_cfg_raise | apply ev_ok_cfg_raise].
    destruct db as [p | ? ? | ? | ? | ? | | | ? ?]; cbv beta iota;
      lazymatch goal with
      | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise
      | _ => idtac
      end.
    - destruct ((or_null && (ptr_to_int p =? ptr_to_int null)%Z) || (n =? 0)%N).
      + apply ev_ok_ret.
      + eapply ev_ok_bind;
          [unfold load; apply ev_ok_cfg_subevent; reflexivity | intros r0; apply ev_ok_ret].
    - apply ev_ok_cfg_raiseUB.
  Qed.

  Lemma ev_ok_assert_attrs_dereferenceable
    (attrs : list param_attr) (v : @dvalue (@ParamsV IP IPT)) (msg : string) :
    ev_ok (@is_non_global_cfg_ev)
      (assert_attrs_dereferenceable (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT)) attrs v msg).
  Proof using.
    unfold assert_attrs_dereferenceable.
    destruct (find_option attr_dereferenceable attrs) as [[or_null n] |];
      [| apply ev_ok_ret].
    destruct v as [db | |]; [| apply ev_ok_ret | apply ev_ok_ret].
    destruct db;
      lazymatch goal with
      | |- ev_ok _ (assert_dereferenceable _ _ _ _) => apply ev_ok_assert_dereferenceable
      | |- _ => apply ev_ok_ret
      end.
  Qed.

  Lemma ev_ok_assert_load_dereferenceable
    (md : list (metadata dtyp)) (v : @dvalue (@ParamsV IP IPT)) (msg : string) :
    ev_ok (@is_non_global_cfg_ev)
      (assert_load_dereferenceable (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT)) md v msg).
  Proof using.
    unfold assert_load_dereferenceable.
    destruct (load_metadata_dereferenceable md) as [[or_null n] |];
      [apply ev_ok_assert_dereferenceable | apply ev_ok_ret].
  Qed.

  Lemma ev_ok_apply_attrs
    (attrs : list param_attr) (msg : string) (v : @dvalue (@ParamsV IP IPT)) :
    ev_ok (@is_non_global_cfg_ev) (@apply_attrs (@ParamsV IP IPT) (@CFGEtop (@ParamsV IP IPT)) _ _ _ _ attrs msg v).
  Proof using.
    unfold apply_attrs.
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg |].
    intros v'; eapply ev_ok_bind;
      [apply ev_ok_assert_attrs_dereferenceable | intros r0; apply ev_ok_ret].
  Qed.

  Lemma ev_ok_apply_args_attrs
    (attrss : list (list param_attr)) (msg : string) (args : list (@dvalue (@ParamsV IP IPT))) :
    ev_ok (@is_non_global_cfg_ev) (@apply_args_attrs (@ParamsV IP IPT) (@CFGEtop (@ParamsV IP IPT)) _ _ _ _ attrss msg
      args).
  Proof using.
    revert attrss; induction args as [| v vs IH]; intros attrss; cbn [apply_args_attrs].
    - apply ev_ok_ret.
    - destruct attrss as [| a r];
        (eapply ev_ok_bind; [apply ev_ok_apply_attrs | intros v'; eapply ev_ok_bind; [apply IH | intros vs'; apply
          ev_ok_ret]]).
  Qed.

  Lemma ev_ok_check_call_return
    (fattrs : list fn_attr) (ret_attrs : list param_attr)
    (ranges : option (list (int_syntax * int_syntax))) (loc : string)
    (args : list (@dvalue (@ParamsV IP IPT)))
    (res : @exc (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT)) :
    ev_ok (@is_non_global_cfg_ev)
      (@check_call_return (@ParamsV IP IPT) (@CFGEtop (@ParamsV IP IPT)) _ _ _ _
         fattrs ret_attrs ranges loc args res).
  Proof using.
    unfold check_call_return.
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg |].
    intros r0; destruct res as [ex | v]; [apply ev_ok_ret |].
    eapply ev_ok_bind; [apply ev_ok_apply_attrs | intros v'; apply ev_ok_ret].
  Qed.

  Lemma ev_ok_denote_call_args
    (args : list (texp dtyp * list param_attr)) (msg : string) :
    ev_ok (@is_non_global_cfg_ev) (@denote_call_args (@ParamsV IP IPT) args msg).
  Proof using.
    unfold denote_call_args; apply ev_ok_map_monad.
    intros [[t op] attrs] _; eapply ev_ok_bind;
      [apply ev_ok_denote_exp' | intros v; apply ev_ok_apply_attrs].
  Qed.

  Lemma ev_ok_bundle_check
    (f : exp dtyp) (tag : string)
    (check : assume_bundle_check (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT)))
    (loc : string) (vs : list (@dvalue (@ParamsV IP IPT))) :
    bundle_check f tag = Some check ->
    ev_ok (@is_non_global_cfg_ev) (check loc vs).
  Proof using.
    unfold bundle_check; destruct (is_llvm_assume f); [| intros H; discriminate H].
    unfold assume_bundle_checks; cbn [List.find].
    repeat match goal with
           | |- context [if String.eqb ?a ?b then _ else _] => destruct (String.eqb a b)
           end;
      cbn [option_map snd]; intros H; try discriminate H; inversion H; subst
        check; clear H.
    - unfold assume_nonnull, assume_violated, assume_malformed.
      destruct vs as [| p [| ? ?]]; cbv beta iota;
        lazymatch goal with
        | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise
        | _ => idtac
        end.
      destruct (dvalue_ptr_address p) as [a |]; [| apply ev_ok_cfg_raiseUB].
      destruct (a =? 0)%Z; [apply ev_ok_cfg_raiseUB | apply ev_ok_ret].
    - unfold assume_noundef, assume_violated, assume_malformed.
      destruct vs as [| v [| ? ?]]; cbv beta iota;
        lazymatch goal with
        | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise
        | _ => idtac
        end.
      destruct (dvalue_well_defined v); [apply ev_ok_ret | apply ev_ok_cfg_raiseUB].
    - unfold assume_align, assume_violated, assume_malformed.
      destruct vs as [| p [| al off]]; cbv beta iota;
        lazymatch goal with
        | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise
        | _ => idtac
        end.
      destruct (dvalue_ptr_address p) as [a |]; [| apply ev_ok_cfg_raiseUB].
      destruct (bundle_uint al) as [n |]; [| apply ev_ok_cfg_raiseUB].
      destruct (match off with [] => Some 0%Z | [o] => bundle_sint o | _ => None end) as [o |];
        [| apply ev_ok_cfg_raiseUB].
      destruct ((if is_power_of_two n then (a - o) mod n =? 0 else a =? 0)%Z);
        [apply ev_ok_ret | apply ev_ok_cfg_raiseUB].
    - unfold assume_dereferenceable, assume_violated, assume_malformed.
      destruct vs as [| p [| sz [| ? ?]]]; cbv beta iota;
        lazymatch goal with
        | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise
        | _ => idtac
        end.
      destruct (dvalue_ptr_address p), (bundle_uint sz); cbv beta iota;
        lazymatch goal with
        | |- ev_ok _ (raiseUB _) => apply ev_ok_cfg_raiseUB
        | _ => idtac
        end.
      destruct (_ =? 0)%Z; [apply ev_ok_ret | apply ev_ok_assert_dereferenceable].
    - unfold assume_dereferenceable, assume_violated, assume_malformed.
      destruct vs as [| p [| sz [| ? ?]]]; cbv beta iota;
        lazymatch goal with
        | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise
        | _ => idtac
        end.
      destruct (dvalue_ptr_address p), (bundle_uint sz); cbv beta iota;
        lazymatch goal with
        | |- ev_ok _ (raiseUB _) => apply ev_ok_cfg_raiseUB
        | _ => idtac
        end.
      destruct (_ =? 0)%Z; [apply ev_ok_ret | apply ev_ok_assert_dereferenceable].
  Qed.

  Lemma ev_ok_denote_operand_bundles
    (loc : string) (f : exp dtyp) (obs : list (@operand_bundle dtyp)) :
    ev_ok (@is_non_global_cfg_ev) (@denote_operand_bundles (@ParamsV IP IPT) loc f obs).
  Proof using.
    unfold denote_operand_bundles.
    eapply ev_ok_bind; [| intros r0; apply ev_ok_ret].
    apply ev_ok_map_monad; intros ob _.
    eapply ev_ok_bind.
    - apply ev_ok_map_monad; intros [[t e] | s] _;
        [apply ev_ok_denote_exp' | apply ev_ok_ret].
    - intros vs; destruct (bundle_check f (ob_tag ob)) as [check |] eqn:Ebc;
        [eapply ev_ok_bundle_check; exact Ebc | apply ev_ok_ret].
  Qed.

  Lemma ev_ok_denote_cmpxchg (id : raw_id) (cpx : cmpxchg dtyp) :
    ev_ok (@is_non_global_cfg_ev) (@denote_cmpxchg (@ParamsV IP IPT) id cpx).
  Proof using.
    unfold denote_cmpxchg.
    destruct (c_ptr cpx) as [ptr_ty ptr_val],
             (c_cmp cpx) as [cmp_ty cmp_val],
             (c_new cpx) as [new_ty new_val].
    destruct (dtyp_eq_dec cmp_ty new_ty); [| apply ev_ok_cfg_raise].
    eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros ptr_v].
    eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros cmp_v].
    eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros new_v].
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros u0].
    eapply ev_ok_bind; [unfold load; apply ev_ok_cfg_subevent; reflexivity | intros loaded_v].
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros dv].
    destruct dv as [db | |]; [| apply ev_ok_cfg_raise | apply ev_ok_cfg_raise].
    destruct db as [? | sz x | ? | ? | ? | | | ? ?]; cbv beta iota;
      lazymatch goal with
      | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise
      | _ => idtac
      end.
    - destruct sz as [? | ? |]; [apply ev_ok_cfg_raise | apply ev_ok_cfg_raise |].
      destruct (VellvmIntegers.equ x VellvmIntegers.one).
      + eapply ev_ok_bind;
          [unfold store; apply ev_ok_cfg_subevent; reflexivity
          | intros u1; unfold lwrite; apply ev_ok_cfg_subevent; reflexivity].
      + unfold lwrite; apply ev_ok_cfg_subevent; reflexivity.
    - apply ev_ok_cfg_raiseUB.
  Qed.

  Lemma ev_ok_denote_atomic_rmw_operation
    (a_op : atomic_rmw_operation) (pv val : @dvalue (@ParamsV IP IPT)) :
    ev_ok (@is_non_global_cfg_ev) (@denote_atomic_rmw_operation (@ParamsV IP IPT) a_op pv val).
  Proof using.
    unfold denote_atomic_rmw_operation.
    destruct a_op; cbv beta iota;
      try apply ev_ok_ret;
      try apply ev_ok_EOU_cfg;
      lazymatch goal with
      | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise
      | _ => idtac
      end.
    destruct val as [db | |]; [| apply ev_ok_cfg_raise | apply ev_ok_cfg_raise].
    destruct db; cbv beta iota;
      lazymatch goal with
      | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise
      | _ => idtac
      end;
      apply ev_ok_EOU_cfg.
  Qed.

  Lemma ev_ok_denote_atomicrmw (id : raw_id) (armw : atomicrmw dtyp) :
    ev_ok (@is_non_global_cfg_ev) (@denote_atomicrmw (@ParamsV IP IPT) id armw).
  Proof using.
    unfold denote_atomicrmw.
    destruct (a_ptr armw) as [ptr_ty ptr_val], (a_val armw) as [a_ty a_val].
    eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros ptr_v].
    eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros a_v].
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros u0].
    eapply ev_ok_bind; [unfold load; apply ev_ok_cfg_subevent; reflexivity | intros loaded_v].
    eapply ev_ok_bind; [apply ev_ok_denote_atomic_rmw_operation | intros stored_v].
    eapply ev_ok_bind; [unfold store; apply ev_ok_cfg_subevent; reflexivity | intros u1].
    eapply ev_ok_bind;
      [unfold lwrite; apply ev_ok_cfg_subevent; reflexivity | intros u2; apply ev_ok_ret].
  Qed.

  Lemma ev_ok_denote_instr
    (i : instr_id * instr dtyp * list (metadata dtyp))
    (va : option (@ptr ProvenanceV (@PointerV IP))) :
    ev_ok (@is_non_global_cfg_ev) (@denote_instr (@ParamsV IP IPT) i va).
  Proof using.
    destruct i as [[iid ins] md]; cbn [denote_instr].
    destruct ins as [msg_c | op | [dt f] args anns obs | dt annotations
                    | dt [du ptr_e] anns | [dt val_e] [du ptr_e] anns
                    | sync ord | cpx | armw | [t ptr_e] argty | rty clp cs].
    - destruct iid; [apply ev_ok_cfg_raise | apply ev_ok_ret].
    - destruct iid as [id |]; [| apply ev_ok_cfg_raise].
      eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros uv].
      eapply ev_ok_bind;
        [unfold lwrite; apply ev_ok_cfg_subevent; reflexivity | intros u0; apply ev_ok_ret].
    - destruct iid as [id |];
        (eapply ev_ok_bind; [apply ev_ok_denote_call_args | intros vs];
         eapply ev_ok_bind; [apply ev_ok_denote_operand_bundles | intros u0];
         eapply ev_ok_bind;
           [destruct (intrinsic_exp f) as [s |];
            [unfold intrinsic; apply ev_ok_cfg_subevent; reflexivity
            | eapply ev_ok_bind;
              [apply ev_ok_denote_exp' | intros fv; unfold call; apply ev_ok_cfg_subevent; reflexivity]]
           | intros res; eapply ev_ok_bind; [apply ev_ok_check_call_return | intros res'];
             eapply ev_ok_bind;
               [destruct res' as [ex | dv]; [apply ev_ok_cfg_raiseLLVM | apply ev_ok_ret] |];
             intros rv;
             lazymatch goal with
             | |- ev_ok _ (lwrite _ _) => unfold lwrite; apply ev_ok_cfg_subevent; reflexivity
             | |- _ => apply ev_ok_ret
             end]).
    - destruct iid as [id |]; [| apply ev_ok_cfg_raise].
      eapply ev_ok_bind; [| intros u0; apply ev_ok_ret].
      destruct (find_option ann_num_elements annotations) as [[t num_exp] |].
      + eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros n].
        destruct (dvalue_is_poison n); [apply ev_ok_cfg_raiseUB |].
        eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros n'].
        eapply ev_ok_bind;
          [unfold alloca; apply ev_ok_cfg_subevent; reflexivity
          | intros v; unfold lwrite; apply ev_ok_cfg_subevent; reflexivity].
      + eapply ev_ok_bind;
          [unfold alloca; apply ev_ok_cfg_subevent; reflexivity
          | intros v; unfold lwrite; apply ev_ok_cfg_subevent; reflexivity].
    - destruct iid as [id |]; [| apply ev_ok_cfg_raise].
      eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros a].
      eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros u0].
      eapply ev_ok_bind; [unfold load; apply ev_ok_cfg_subevent; reflexivity | intros v].
      eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros v'].
      eapply ev_ok_bind;
        [apply ev_ok_assert_load_dereferenceable
        | intros u1; unfold lwrite; apply ev_ok_cfg_subevent; reflexivity].
    - destruct iid; [apply ev_ok_cfg_raise |].
      eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros v].
      eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros a].
      eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros u0].
      eapply ev_ok_bind; [| intros u1; apply ev_ok_ret].
      destruct a as [db | |];
        [destruct db; try (unfold store; apply ev_ok_cfg_subevent; reflexivity);
         apply ev_ok_cfg_raiseUB
        | unfold store; apply ev_ok_cfg_subevent; reflexivity
        | unfold store; apply ev_ok_cfg_subevent; reflexivity].
    - destruct iid; cbn [ExtLib.Structures.Monad.ret Monad_itree]; apply ev_ok_ret.
    - destruct iid as [id |]; [apply ev_ok_denote_cmpxchg | apply ev_ok_cfg_raise].
    - destruct iid as [id |]; [apply ev_ok_denote_atomicrmw | apply ev_ok_cfg_raise].
    - destruct iid as [id |].
      all: eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros ptr_to_args].
      all: eapply ev_ok_bind; [unfold load; apply ev_ok_cfg_subevent; reflexivity | intros args].
      all: eapply ev_ok_bind; [unfold load; apply ev_ok_cfg_subevent; reflexivity | intros retv].
      all: eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros ix].
      all: eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros args'].
      all: eapply ev_ok_bind; [unfold store; apply ev_ok_cfg_subevent; reflexivity | intros u0].
      all: lazymatch goal with
           | |- ev_ok _ (lwrite _ _) => unfold lwrite; apply ev_ok_cfg_subevent; reflexivity
           | |- _ => apply ev_ok_ret
           end.
    - destruct iid as [id |]; [| apply ev_ok_cfg_raise].
      eapply ev_ok_bind; [unfold stack_get_exc; apply ev_ok_cfg_subevent; reflexivity |].
      intros [e |];
        [unfold lwrite; apply ev_ok_cfg_subevent; reflexivity | apply ev_ok_cfg_raise].
  Qed.

  Lemma ev_ok_denote_code
    (c : code dtyp) (va : option (@ptr ProvenanceV (@PointerV IP))) :
    ev_ok (@is_non_global_cfg_ev) (@denote_code (@ParamsV IP IPT) c va).
  Proof using.
    unfold denote_code; apply ev_ok_loop_monad.
    intros i _; apply ev_ok_denote_instr.
  Qed.

  Lemma ev_ok_denote_phi
    (bid_from : block_id) (pe : local_id * phi dtyp * list (metadata dtyp)) :
    ev_ok (@is_non_global_cfg_ev) (@denote_phi (@ParamsV IP IPT) bid_from pe).
  Proof using.
    destruct pe as [[id [anns dt args]] md]; cbn [denote_phi].
    destruct (assoc bid_from args) as [op |]; [| apply ev_ok_cfg_raise].
    eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros uv; apply ev_ok_ret].
  Qed.

  Lemma ev_ok_denote_phis
    (bid_from : block_id) (phis : list (local_id * phi dtyp * list (metadata dtyp))) :
    ev_ok (@is_non_global_cfg_ev) (@denote_phis (@ParamsV IP IPT) bid_from phis).
  Proof using.
    unfold denote_phis.
    eapply ev_ok_bind; [apply ev_ok_map_monad; intros pe _; apply ev_ok_denote_phi |].
    intros dvs; eapply ev_ok_bind.
    - apply ev_ok_map_monad; intros [id dv] _;
        unfold lwrite; apply ev_ok_cfg_subevent; reflexivity.
    - intros u0; apply ev_ok_ret.
  Qed.

  Lemma ev_ok_denote_terminator
    (trm : instr_id * terminator dtyp * list (metadata dtyp)) :
    ev_ok (@is_non_global_cfg_ev) (@denote_terminator (@ParamsV IP IPT) trm).
  Proof using.
    destruct trm as [[iid tm] md]; cbn [denote_terminator].
    destruct tm as [[dt op] | | [dt op] br1 br2 | br | [dt e] default_br dests
                   | [t addr] brs fn | [t expr]
                   | [dt fnptrval] args to_label unwind_label anns obs |].
    - eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros dv; apply ev_ok_ret].
    - apply ev_ok_ret.
    - eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros v].
      destruct v as [db | |]; [| apply ev_ok_cfg_raise | apply ev_ok_cfg_raise].
      destruct db as [? | sz x | ? | ? | ? | | | ? ?]; cbv beta iota;
      lazymatch goal with
      | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise
      | _ => idtac
      end.
      + destruct sz as [? | ? |]; [apply ev_ok_cfg_raise | apply ev_ok_cfg_raise |].
        destruct (VellvmIntegers.equ x VellvmIntegers.one); apply ev_ok_ret.
      + apply ev_ok_cfg_raiseUB.
    - apply ev_ok_ret.
    - eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros selector].
      destruct (dvalue_is_poison selector); [apply ev_ok_cfg_raiseUB |].
      eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros bid; apply ev_ok_ret].
    - eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros a].
      destruct (dvalue_is_poison a); [apply ev_ok_cfg_raiseUB |].
      destruct fn as [f |]; [| apply ev_ok_cfg_raise].
      eapply ev_ok_bind.
      + apply ev_ok_map_monad; intros b _.
        eapply ev_ok_bind;
          [unfold gread; apply ev_ok_cfg_subevent; reflexivity | intros ba; apply ev_ok_ret].
      + intros addrs; destruct (dvalue_ptr_address a) as [z |]; [| apply ev_ok_cfg_raise].
        destruct (indirectbr_target z (List.combine brs addrs)) as [b |];
          [apply ev_ok_ret | apply ev_ok_cfg_raiseUB].
    - eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros exn; apply ev_ok_cfg_raiseLLVM].
    - eapply ev_ok_bind; [apply ev_ok_denote_call_args | intros uvs].
      eapply ev_ok_bind; [apply ev_ok_denote_operand_bundles | intros u0].
      eapply ev_ok_bind; [apply ev_ok_denote_exp' | intros fv].
      eapply ev_ok_bind; [unfold call; apply ev_ok_cfg_subevent; reflexivity | intros rv].
      eapply ev_ok_bind; [apply ev_ok_check_call_return | intros [exn | retv]].
      + eapply ev_ok_bind;
          [unfold stack_raise; apply ev_ok_cfg_subevent; reflexivity | intros u1; apply ev_ok_ret].
      + eapply ev_ok_bind;
          [destruct iid as [id |];
             [unfold lwrite; apply ev_ok_cfg_subevent; reflexivity | apply ev_ok_ret]
          | intros u1; apply ev_ok_ret].
    - apply ev_ok_cfg_raiseUB.
  Qed.

  Lemma ev_ok_denote_block
    (b : block dtyp) (bid_from : block_id)
    (va : option (@ptr ProvenanceV (@PointerV IP))) :
    ev_ok (@is_non_global_cfg_ev) (@denote_block (@ParamsV IP IPT) b bid_from va).
  Proof using.
    unfold denote_block.
    eapply ev_ok_bind; [apply ev_ok_denote_phis | intros u0].
    eapply ev_ok_bind; [apply ev_ok_denote_code | intros u1].
    apply ev_ok_denote_terminator.
  Qed.

  Lemma ev_ok_denote_ocfg_map
    (bmap : rmap (block dtyp)) (va : option (@ptr ProvenanceV (@PointerV IP)))
    (ids : block_id * block_id) :
    ev_ok (@is_non_global_cfg_ev) (@denote_ocfg_map (@ParamsV IP IPT) bmap va ids).
  Proof using.
    unfold denote_ocfg_map; apply ev_ok_iter.
    intros [bid_from bid_src].
    destruct (RM.find bid_src bmap) as [block_src |]; [| apply ev_ok_ret].
    eapply ev_ok_bind; [apply ev_ok_denote_block | intros [bid_target | dv]; apply ev_ok_ret].
  Qed.

  Lemma ev_ok_denote_cfg_map
    (bmap : rmap (block dtyp)) (f : CFG.cfg dtyp)
    (va : option (@ptr ProvenanceV (@PointerV IP))) :
    ev_ok (@is_non_global_cfg_ev) (@denote_cfg_map (@ParamsV IP IPT) bmap f va).
  Proof using.
    unfold denote_cfg_map.
    eapply ev_ok_bind; [apply ev_ok_denote_ocfg_map | intros [bid | uv];
      [apply ev_ok_cfg_raise | apply ev_ok_ret]].
  Qed.

  Lemma ev_ok_push_call_frame
    (df : definition dtyp (CFG.cfg dtyp)) (args : list (@dvalue (@ParamsV IP IPT))) :
    ev_ok (@is_non_global_cfg_ev) (@push_call_frame (@ParamsV IP IPT) df args).
  Proof using.
    unfold push_call_frame.
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros [bs vs]].
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros dts].
    eapply ev_ok_bind; [unfold mem_push; apply ev_ok_cfg_subevent; reflexivity | intros u0].
    eapply ev_ok_bind; [unfold stack_push; apply ev_ok_cfg_subevent; reflexivity | intros u1].
    eapply ev_ok_bind; [unfold alloca; apply ev_ok_cfg_subevent; reflexivity | intros varargs].
    eapply ev_ok_bind; [unfold store; apply ev_ok_cfg_subevent; reflexivity | intros u2].
    destruct varargs as [db | |]; [| apply ev_ok_cfg_raise | apply ev_ok_cfg_raise].
    destruct db as [varg | ? ? | ? | ? | ? | | | ? ?];
      [apply ev_ok_ret | apply ev_ok_cfg_raise ..].
  Qed.

  Lemma ev_ok_pop_call_frame :
    ev_ok (@is_non_global_cfg_ev) (@pop_call_frame (@ParamsV IP IPT) (@CFGEtop (@ParamsV IP IPT)) _ _).
  Proof using.
    unfold pop_call_frame.
    eapply ev_ok_bind;
      [unfold stack_pop; apply ev_ok_cfg_subevent; reflexivity
      | intros u0; unfold mem_pop; apply ev_ok_cfg_subevent; reflexivity].
  Qed.

  Lemma ev_ok_denote_function
    (df : definition dtyp (CFG.cfg dtyp))
    (cc : cconv) (args : list (@dvalue (@ParamsV IP IPT))) :
    ev_ok (@is_non_global_cfg_ev) (@denote_function (@ParamsV IP IPT) df cc args).
  Proof using.
    unfold denote_function.
    destruct (dc_param_attrs (df_prototype df)) as [ret_attrs args_attrs].
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros u0].
    eapply ev_ok_bind; [apply ev_ok_apply_args_attrs | intros args'].
    eapply ev_ok_bind; [apply ev_ok_push_call_frame | intros varg].
    eapply ev_ok_bind; [apply ev_ok_run_exc, ev_ok_denote_cfg_map | intros rv].
    eapply ev_ok_bind; [apply ev_ok_pop_call_frame | intros u1].
    apply ev_ok_check_call_return.
  Qed.

  Lemma ev_ok_i8_str_index
    (strptr : @ptr ProvenanceV (@PointerV IP)) (idx : Z) :
    ev_ok (@is_non_global_cfg_ev)
      (@i8_str_index (@ParamsV IP IPT) strptr idx).
  Proof using.
    unfold i8_str_index.
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros i].
    eapply ev_ok_bind; [apply ev_ok_EOU_cfg | intros addr].
    eapply ev_ok_bind; [unfold load; apply ev_ok_cfg_subevent; reflexivity | intros d_byte].
    destruct d_byte as [db | |]; [| apply ev_ok_cfg_raise | apply ev_ok_cfg_raise].
    destruct db as [? | sz b | ? | ? | ? | | | ? ?]; cbv beta iota;
      lazymatch goal with
      | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise
      | _ => idtac
      end.
    destruct sz as [p | p |]; cbv beta iota;
      lazymatch goal with | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise | _ => idtac end;
      destruct p as [p | p |]; cbv beta iota;
      lazymatch goal with | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise | _ => idtac end;
      destruct p as [p | p |]; cbv beta iota;
      lazymatch goal with | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise | _ => idtac end;
      destruct p as [p | p |]; cbv beta iota;
      lazymatch goal with | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise | _ => idtac end.
    apply ev_ok_ret.
  Qed.

  Lemma ev_ok_putchar_denotation
    (cc : cconv) (args : list (@dvalue (@ParamsV IP IPT))) :
    ev_ok (@is_non_global_cfg_ev) (@putchar_denotation (@ParamsV IP IPT) cc args).
  Proof using.
    unfold putchar_denotation.
    destruct args as [| ch [| ? ?]]; cbv beta iota;
      lazymatch goal with
      | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise
      | _ => idtac
      end.
    apply ev_ok_fmap.
    destruct ch as [db | |]; [| apply ev_ok_cfg_raiseUB | apply ev_ok_cfg_raiseUB].
    destruct db as [? | sz x32 | ? | ? | ? | | | ? ?]; cbv beta iota;
      lazymatch goal with
      | |- ev_ok _ (raiseUB _) => apply ev_ok_cfg_raiseUB
      | _ => idtac
      end.
    destruct (Pos.eq_dec 32 sz) as [<- | _]; [| apply ev_ok_cfg_raiseUB].
    eapply ev_ok_bind;
      [unfold io_stdout; apply ev_ok_cfg_subevent; reflexivity | intros u0; apply ev_ok_ret].
  Qed.

  Lemma ev_ok_puts_denotation
    (cc : cconv) (args : list (@dvalue (@ParamsV IP IPT))) :
    ev_ok (@is_non_global_cfg_ev) (@puts_denotation (@ParamsV IP IPT) cc args).
  Proof using.
    unfold puts_denotation.
    destruct args as [| u_strptr [| ? ?]]; cbv beta iota;
      lazymatch goal with
      | |- ev_ok _ (raise _) => apply ev_ok_cfg_raise
      | _ => idtac
      end.
    apply ev_ok_fmap.
    destruct u_strptr as [db | |]; [| apply ev_ok_cfg_raiseUB | apply ev_ok_cfg_raiseUB].
    destruct db as [strptr | ? ? | ? | ? | ? | | | ? ?]; cbv beta iota;
      lazymatch goal with
      | |- ev_ok _ (raiseUB _) => apply ev_ok_cfg_raiseUB
      | _ => idtac
      end.
    eapply ev_ok_bind; [apply ev_ok_i8_str_index | intros ch].
    eapply ev_ok_bind.
    - apply ev_ok_iter.
      intros [[c bytes] offset].
      destruct (@Integers.eq 8 c (@Integers.zero 8)); [apply ev_ok_ret |].
      eapply ev_ok_bind; [apply ev_ok_i8_str_index | intros c'; apply ev_ok_ret].
    - intros bytes; eapply ev_ok_bind;
        [unfold io_stdout; apply ev_ok_cfg_subevent; reflexivity | intros u0; apply ev_ok_ret].
  Qed.

  Lemma library_functions_ev_ok (decls : list (declaration dtyp)) :
    Forall
      (fun lib =>
         forall cc args,
           ev_ok (@is_non_global_cfg_ev) (snd lib cc args))
      (@library_functions (@ParamsV IP IPT) decls).
  Proof using.
    rewrite Forall_forall; intros [n fn] Hin.
    unfold library_functions, _LIBRARIES in Hin; rewrite filter_In in Hin; destruct Hin as [Hin _].
    destruct Hin as [Heq | [Heq | []]]; inversion Heq; subst; intros cc args; cbn
      [snd];
      [apply ev_ok_puts_denotation | apply ev_ok_putchar_denotation].
  Qed.

  Lemma ev_ok_external_call_inr
    (dt : dtyp) (fv : @dvalue (@ParamsV IP IPT)) (vs : list (@dvalue (@ParamsV IP IPT))) :
    ev_ok (@is_non_global_cfg_ev)
      (@Functor.fmap (@CFGtop (@ParamsV IP IPT)) _ _ (@exc (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT))
         inr (external_call dt fv vs)).
  Proof using.
    apply ev_ok_fmap; unfold external_call; apply ev_ok_cfg_subevent; reflexivity.
  Qed.

  Definition leaf_ctx_fn_rel
    (P0 : list N) (g0 : @global_env (@ParamsV IP IPT))
    (f1 f2 : @function_denotation (@ParamsV IP IPT)) : Prop :=
    (f1 = f2 /\ forall cc args, ev_ok (@is_non_global_cfg_ev) (f1 cc args)) \/
    (forall ctx1 ctx2 cc args U σ1 σ2 ls,
       incl P0 U ->
       mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
       refine_prov (mcfg_eq_g_post g0 U) U
         (interp_cfg_model ctx1 (f1 cc args) (σ1, (ls, g0)))
         (interp_cfg_model ctx2 (f2 cc args) (σ2, (ls, g0)))).

  Section LeafKnotG.
    Context (P0 : list N)
            (g0 : @global_env (@ParamsV IP IPT))
            (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
            (Hctx : forall k, option_rel (leaf_ctx_fn_rel P0 g0) (lookup k ctx1) (lookup k ctx2)).

    Local Definition k_lg {X R : Type}
      (tau_flag : bool)
      (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
      (k : X -> @CFGtop (@ParamsV IP IPT) R)
      : Res X -> itree ProvBotE (Res R) :=
      fun '(s', x) =>
        if tau_flag then Tau (interp_cfg_model ctx (k x) s')
        else interp_cfg_model ctx (k x) s'.

    Inductive lg_rel {R : Type} (U0 : list N)
      : list N -> itree ProvBotE (Res R) -> itree ProvBotE (Res R) -> Prop :=
    | LG_Tree U (t0 : @CFGtop (@ParamsV IP IPT) R) (s_a s_b : state) ls0
        (a1 a2 : itree ProvBotE (Res R)) :
        interp_cfg_model ctx1 t0 (s_a, (ls0, g0)) ≅ a1 ->
        interp_cfg_model ctx2 t0 (s_b, (ls0, g0)) ≅ a2 ->
        ev_ok (@is_non_global_cfg_ev) t0 ->
        incl U0 U ->
        mem_stack_equal (state_memory_stack s_a) (state_memory_stack s_b) ->
        lg_rel U0 U a1 a2
    | LG_Bind X (tau_flag : bool) U
        (u1 u2 : itree ProvBotE (Res X))
        (k : X -> @CFGtop (@ParamsV IP IPT) R)
        (a1 a2 : itree ProvBotE (Res R)) :
        ITree.bind u1 (k_lg tau_flag ctx1 k) ≅ a1 ->
        ITree.bind u2 (k_lg tau_flag ctx2 k) ≅ a2 ->
        (forall x, ev_ok (@is_non_global_cfg_ev) (k x)) ->
        refine_prov (mcfg_eq_g_post g0 U0) U u1 u2 ->
        lg_rel U0 U a1 a2.

    Local Lemma lg_rel_obs_eq {R : Type} (U0 U : list N)
      (a1 a1' a2 a2' : itree ProvBotE (Res R)) :
      a1 ≅ a1' ->
      a2 ≅ a2' ->
      lg_rel U0 U a1 a2 ->
      lg_rel U0 U a1' a2'.
    Proof using.
      intros E1 E2 H.
      destruct H as [U t0 s_a s_b ls0 b1 b2 Eb1 Eb2 Ht0 Hinc Hm
                    | X tf U u1 u2 k b1 b2 Eb1 Eb2 Hk Hu].
      - eapply LG_Tree;
          [exact (transitivity Eb1 E1) | exact (transitivity Eb2 E2) | exact Ht0 | exact Hinc | exact Hm].
      - eapply LG_Bind;
          [exact (transitivity Eb1 E1) | exact (transitivity Eb2 E2) | exact Hk | exact Hu].
    Qed.

    Local Lemma lg_bind_true_step {X R : Type} (U0 U : list N)
      (u1 u2 : itree ProvBotE (Res X))
      (k : X -> @CFGtop (@ParamsV IP IPT) R)
      (Hk : forall x, ev_ok (@is_non_global_cfg_ev) (k x))
      (Hu : refine_prov (mcfg_eq_g_post g0 U0) U u1 u2) :
      refine_prov_ (mcfg_eq_g_post g0 U0) (lg_rel U0) U
        (ITree.bind u1 (k_lg true ctx1 k))
        (ITree.bind u2 (k_lg true ctx2 k)).
    Proof using.
      punfold Hu.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [[[s_a' [ls1' g1']] x1] | m1 | Y1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [[[s_b' rest2'] x2] | m2 | Y2 e2 h2] eqn:Hou2;
            try contradiction.
          destruct Hstep as (Hinc & Hm & Hrest & Hg1 & <-).
          cbn [fst snd] in Hm, Hrest, Hg1; subst rest2' g1'.
          apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2; cbn.
          eapply LG_Tree; [reflexivity | reflexivity | exact (Hk x1) | exact Hinc | exact Hm].
        + destruct (observe u2) as [? | m2 | ? ? ?] eqn:Hou2; try contradiction; pclearbot.
          apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2.
          eapply LG_Bind; [reflexivity | reflexivity | exact Hk | exact Hstep].
        + apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind u1 (k_lg true ctx1 k)), Hou1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            eapply LG_Bind; [reflexivity | reflexivity | exact Hk | exact Hleft].
          * right; right.
            destruct (observe u2) as [? | ? | Y2 e2 h2] eqn:Hou2; try contradiction.
            rewrite (observe_bind u2 (k_lg true ctx2 k)), Hou2.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               eapply LG_Bind; [reflexivity | reflexivity | exact Hk | exact Hboth].
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               eapply LG_Bind; [reflexivity | reflexivity | exact Hk | exact HA].
      - eapply RP_TauL;
          [rewrite (observe_bind u1 (k_lg true ctx1 k)), Hu1; reflexivity | exact IH].
      - eapply RP_TauR;
          [rewrite (observe_bind u2 (k_lg true ctx2 k)), Hu2; reflexivity | exact IH].
    Qed.

    Local Lemma lg_call_dispatch {X : Type} (ce : @CallE (@ParamsV IP IPT) X)
      (U0 U : list N) (s_a s_b : state) ls0
      (Hpu0 : incl P0 U0)
      (Hinc : incl U0 U)
      (Hm : mem_stack_equal (state_memory_stack s_a) (state_memory_stack s_b)) :
      (exists t_call : @CFGtop (@ParamsV IP IPT) X,
         mrec_ctx ctx1 X ce ≅ t_call /\
         mrec_ctx ctx2 X ce ≅ t_call /\
         ev_ok (@is_non_global_cfg_ev) t_call) \/
      refine_prov (mcfg_eq_g_post g0 U0) U
        (interp_cfg_model ctx1 (mrec_ctx ctx1 X ce) (s_a, (ls0, g0)))
        (interp_cfg_model ctx2 (mrec_ctx ctx2 X ce) (s_b, (ls0, g0))).
    Proof using Hctx.
      destruct ce as [dt cc fv vs]; unfold mrec_ctx; cbn [ExtLib.Structures.Monad.bind Monad_itree].
      destruct fv as [db | |];
        [| right; eapply refine_cfg_model_bind with (RA := fun _ _ _ => False);
             [apply refine_cfg_raise_both | intros _ _ _ _ _ _ []]
        | right; eapply refine_cfg_model_bind with (RA := fun _ _ _ => False);
             [apply refine_cfg_raise_both | intros _ _ _ _ _ _ []]].
      destruct db as [addr | ? ? | ? | ? | ? | | | ? ?]; cbn [check_callee EOU_to_itree];
        lazymatch goal with
        | |- context [ITree.bind (raise _) _] =>
            right; eapply refine_cfg_model_bind with (RA := fun _ _ _ => False);
            [apply refine_cfg_raise_both | intros _ _ _ _ _ _ []]
        | _ => idtac
        end.
      - cbn [check_callee].
        destruct ((ptr_to_int addr =? ptr_to_int null)%Z).
        + right; cbn [EOU_to_itree].
          eapply refine_prov_obs_eq;
            [symmetry; apply interp_cfg_model_bind | symmetry; apply interp_cfg_model_bind |].
          eapply PassCommonModel.refine_prov_bind with (RR := fun _ _ _ => False);
            [apply refine_cfg_raiseUB_l | intros _ _ _ _ []].
        + cbn [EOU_to_itree lookup_defn].
          pose proof (Hctx (ptr_to_int addr)) as Hlk.
          destruct (lookup (ptr_to_int addr) ctx1) as [f1 |],
                   (lookup (ptr_to_int addr) ctx2) as [f2 |];
            inversion Hlk; subst; clear Hlk;
            try match goal with H : leaf_ctx_fn_rel _ _ _ _ |- _ => destruct H as [[<- Hf1] | Hf12] end.
          * left; exists (f1 cc vs);
              exact (conj (Eqit.bind_ret_l tt _) (conj (Eqit.bind_ret_l tt _) (Hf1 cc vs))).
          * right.
            eapply refine_prov_obs_eq;
              [symmetry; apply interp_cfg_model_obs_eq, Eqit.bind_ret_l
              | symmetry; apply interp_cfg_model_obs_eq, Eqit.bind_ret_l |].
            eapply refine_prov_weaken_incl;
              [apply (Hf12 ctx1 ctx2 cc vs U s_a s_b ls0 (incl_tran Hpu0 Hinc) Hm) |].
            intros U' [? ?] [? ?] _ (Hi & H1 & H2 & H3 & H4);
              exact (conj (incl_tran Hinc Hi) (conj H1 (conj H2 (conj H3 H4)))).
          * left; exists (inr <$> external_call dt (DVALUE_Base (DVALUE_Pointer addr)) vs);
              exact (conj (Eqit.bind_ret_l tt _) (conj (Eqit.bind_ret_l tt _) (ev_ok_external_call_inr dt _ vs))).
      - right; cbn [check_callee EOU_to_itree].
        eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_bind | symmetry; apply interp_cfg_model_bind |].
        eapply PassCommonModel.refine_prov_bind with (RR := fun _ _ _ => False);
          [apply refine_cfg_raiseUB_l | intros _ _ _ _ []].
    Qed.

    Local Lemma lg_tree_step {R : Type} (U0 U : list N)
      (t0 : @CFGtop (@ParamsV IP IPT) R) (s_a s_b : state) ls0
      (Ht0 : ev_ok (@is_non_global_cfg_ev) t0)
      (Hpu0 : incl P0 U0)
      (Hinc : incl U0 U)
      (Hm : mem_stack_equal (state_memory_stack s_a) (state_memory_stack s_b)) :
      refine_prov_ (mcfg_eq_g_post g0 U0) (lg_rel U0) U
        (interp_cfg_model ctx1 t0 (s_a, (ls0, g0)))
        (interp_cfg_model ctx2 t0 (s_b, (ls0, g0))).
    Proof using Hctx.
      punfold Ht0; destruct Ht0 as [rv t0' Hot | mt t0' Hot Hmt | X e k t0' Hot He Hk]; pclearbot.
      - assert (E1 : Ret ((s_a, (ls0, g0)), rv) ≅ interp_cfg_model ctx1 t0' (s_a, (ls0, g0))).
        { symmetry; etransitivity;
            [apply interp_cfg_model_obs_eq; rewrite (itree_eta t0'), Hot; reflexivity
            | apply interp_cfg_model_ret]. }
        assert (E2 : Ret ((s_b, (ls0, g0)), rv) ≅ interp_cfg_model ctx2 t0' (s_b, (ls0, g0))).
        { symmetry; etransitivity;
            [apply interp_cfg_model_obs_eq; rewrite (itree_eta t0'), Hot; reflexivity
            | apply interp_cfg_model_ret]. }
        eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | exact E1 | exact E2 |].
        apply RP_Step; cbn;
          exact (conj Hinc (conj Hm (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
      - assert (E1 : Tau (interp_cfg_model ctx1 mt (s_a, (ls0, g0))) ≅ interp_cfg_model ctx1 t0' (s_a, (ls0, g0))).
        { symmetry; etransitivity;
            [apply interp_cfg_model_obs_eq; rewrite (itree_eta t0'), Hot; reflexivity
            | apply interp_cfg_model_tau]. }
        assert (E2 : Tau (interp_cfg_model ctx2 mt (s_b, (ls0, g0))) ≅ interp_cfg_model ctx2 t0' (s_b, (ls0, g0))).
        { symmetry; etransitivity;
            [apply interp_cfg_model_obs_eq; rewrite (itree_eta t0'), Hot; reflexivity
            | apply interp_cfg_model_tau]. }
        eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | exact E1 | exact E2 |].
        apply RP_Step; cbn;
          eapply LG_Tree; [reflexivity | reflexivity | exact Hmt | exact Hinc | exact Hm].
      - destruct e as [ce | me].
        + assert (Ecall : forall ctx s,
                    Tau (interp_cfg_model ctx (ITree.bind (mrec_ctx ctx X ce) k) s) ≅
                    interp_cfg_model ctx t0' s).
          { intros ctx s; symmetry; etransitivity;
              [apply interp_cfg_model_obs_eq; rewrite (itree_eta t0'), Hot; reflexivity |].
            unfold interp_cfg_model.
            assert (Hm0 : interp_mrec (mrec_ctx ctx) (Vis (inl1 ce) k) ≅
                          Tau (interp_mrec (mrec_ctx ctx) (ITree.bind (mrec_ctx ctx X ce) k))).
            { rewrite unfold_interp_mrec; reflexivity. }
            rewrite (interp_mcfg_model_obs_eq _ _ s Hm0); apply interp_mcfg_model_tau. }
          eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | apply Ecall | apply Ecall |].
          apply RP_Step; cbn.
          destruct (lg_call_dispatch ce U0 U s_a s_b ls0 Hpu0 Hinc Hm)
            as [(t_call & Ec1 & Ec2 & Ht_call) | Href_call].
          * eapply LG_Tree;
              [symmetry; apply interp_cfg_model_obs_eq; rewrite Ec1; reflexivity
              | symmetry; apply interp_cfg_model_obs_eq; rewrite Ec2; reflexivity
              | eapply ev_ok_bind; [exact Ht_call | exact Hk]
              | exact Hinc
              | exact Hm].
          * eapply LG_Bind with (tau_flag := false);
              [symmetry; apply interp_cfg_model_bind
              | symmetry; apply interp_cfg_model_bind
              | exact Hk
              | exact Href_call].
        + assert (Emcfg : forall ctx s,
                    ITree.bind (interp_mcfg_model (ITree.trigger me) s) (k_lg true ctx k) ≅
                    interp_cfg_model ctx t0' s).
          { intros ctx s; symmetry; etransitivity;
              [apply interp_cfg_model_obs_eq; rewrite (itree_eta t0'), Hot; reflexivity |].
            unfold interp_cfg_model.
            assert (Hm0 : interp_mrec (mrec_ctx ctx) (Vis (inr1 me) k) ≅
                          Vis me (fun x => Tau (interp_mrec (mrec_ctx ctx) (k x)))).
            { rewrite unfold_interp_mrec; reflexivity. }
            assert (Ev : Vis me (fun x => Tau (interp_mrec (mrec_ctx ctx) (k x))) ≅
                         ITree.bind (ITree.trigger me) (fun x => Tau (interp_mrec (mrec_ctx ctx) (k x)))).
            { unfold ITree.trigger; rewrite Eqit.bind_vis; apply eqit_Vis; intros x; rewrite
              Eqit.bind_ret_l; reflexivity. }
            rewrite (interp_mcfg_model_obs_eq _ _ s Hm0), (interp_mcfg_model_obs_eq _ _ s Ev), interp_mcfg_model_bind.
            eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
            intros [s' x] _ <-; apply interp_mcfg_model_tau. }
          eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | apply Emcfg | apply Emcfg |].
          apply lg_bind_true_step; [exact Hk |].
          eapply refine_prov_weaken_incl;
            [apply (trigger_mcfg_non_global_g_sync me He g0 U s_a s_b ls0 Hm) |].
          intros U' [? ?] [? ?] _ (Hi & H1 & H2 & H3 & H4);
            exact (conj (incl_tran Hinc Hi) (conj H1 (conj H2 (conj H3 H4)))).
    Qed.

    Local Lemma lg_bind_false_step {X R : Type} (U0 U : list N)
      (u1 u2 : itree ProvBotE (Res X))
      (k : X -> @CFGtop (@ParamsV IP IPT) R)
      (Hpu0 : incl P0 U0)
      (Hk : forall x, ev_ok (@is_non_global_cfg_ev) (k x))
      (Hu : refine_prov (mcfg_eq_g_post g0 U0) U u1 u2) :
      refine_prov_ (mcfg_eq_g_post g0 U0) (lg_rel U0) U
        (ITree.bind u1 (k_lg false ctx1 k))
        (ITree.bind u2 (k_lg false ctx2 k)).
    Proof using Hctx.
      punfold Hu.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [[[s_a' [ls1' g1']] x1] | m1 | Y1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [[[s_b' rest2'] x2] | m2 | Y2 e2 h2] eqn:Hou2;
            try contradiction.
          destruct Hstep as (Hinc & Hm & Hrest & Hg1 & <-).
          cbn [fst snd] in Hm, Hrest, Hg1; subst rest2' g1'.
          assert (Eb1 : interp_cfg_model ctx1 (k x1) (s_a', (ls1', g0)) ≅ ITree.bind u1 (k_lg false ctx1 k))
            by (symmetry; rewrite (itree_eta u1), Hou1, Eqit.bind_ret_l; reflexivity).
          assert (Eb2 : interp_cfg_model ctx2 (k x1) (s_b', (ls1', g0)) ≅ ITree.bind u2 (k_lg false ctx2 k))
            by (symmetry; rewrite (itree_eta u2), Hou2, Eqit.bind_ret_l; reflexivity).
          eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | exact Eb1 | exact Eb2 |].
          exact (lg_tree_step U0 U (k x1) s_a' s_b' ls1' (Hk x1) Hpu0 Hinc Hm).
        + destruct (observe u2) as [? | m2 | ? ? ?] eqn:Hou2; try contradiction; pclearbot.
          apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2.
          eapply LG_Bind with (tau_flag := false); [reflexivity | reflexivity | exact Hk | exact Hstep].
        + apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind u1 (k_lg false ctx1 k)), Hou1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            eapply LG_Bind with (tau_flag := false); [reflexivity | reflexivity | exact Hk | exact Hleft].
          * right; right.
            destruct (observe u2) as [? | ? | Y2 e2 h2] eqn:Hou2; try contradiction.
            rewrite (observe_bind u2 (k_lg false ctx2 k)), Hou2.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               eapply LG_Bind with (tau_flag := false); [reflexivity | reflexivity | exact Hk | exact Hboth].
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               eapply LG_Bind with (tau_flag := false); [reflexivity | reflexivity | exact Hk | exact HA].
      - eapply RP_TauL;
          [rewrite (observe_bind u1 (k_lg false ctx1 k)), Hu1; reflexivity | exact IH].
      - eapply RP_TauR;
          [rewrite (observe_bind u2 (k_lg false ctx2 k)), Hu2; reflexivity | exact IH].
    Qed.

    Lemma cfg_leaf_g_sync {R : Type}
      (t : @CFGtop (@ParamsV IP IPT) R)
      (Hok : ev_ok (@is_non_global_cfg_ev) t)
      (U0 : list N) (σ1 σ2 : state)
      (ls : @stack_frame (@ParamsV IP IPT) * stack)
      (Hpu0 : incl P0 U0)
      (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
      refine_prov (mcfg_eq_g_post g0 U0) U0
        (interp_cfg_model ctx1 t (σ1, (ls, g0)))
        (interp_cfg_model ctx2 t (σ2, (ls, g0))).
    Proof using Hctx.
      assert (Hcore : forall U (a1 a2 : itree ProvBotE (Res R)),
                lg_rel U0 U a1 a2 ->
                refine_prov (mcfg_eq_g_post g0 U0) U a1 a2).
      { pcofix CIH; intros U a1 a2 Hst; pstep.
        eapply refine_prov__mon with (r := lg_rel U0);
          [| intros U' x1 x2 Hx; right; apply CIH, Hx].
        destruct Hst as [U t0 s_a s_b ls0 b1 b2 Eb1 Eb2 Ht0 Hinc Hm
                        | X [|] U u1 u2 k b1 b2 Eb1 Eb2 Hk Hu].
        - eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | exact Eb1 | exact Eb2 |].
          exact (lg_tree_step U0 U t0 s_a s_b ls0 Ht0 Hpu0 Hinc Hm).
        - eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | exact Eb1 | exact Eb2 |].
          exact (lg_bind_true_step U0 U u1 u2 k Hk Hu).
        - eapply refine_prov__obs_eq; [exact (@lg_rel_obs_eq R U0) | exact Eb1 | exact Eb2 |].
          exact (lg_bind_false_step U0 U u1 u2 k Hpu0 Hk Hu). }
      apply Hcore.
      eapply LG_Tree; [reflexivity | reflexivity | exact Hok | apply incl_refl | exact Heq].
    Qed.

    Lemma mrec_knot_leaf_call_sim {X : Type} (ce : @CallE (@ParamsV IP IPT) X)
      (U0 : list N) (σ1 σ2 : state)
      (ls : @stack_frame (@ParamsV IP IPT) * stack)
      (Hpu0 : incl P0 U0)
      (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
      refine_prov (mcfg_eq_g_post g0 U0) U0
        (interp_cfg_model ctx1 (mrec_ctx ctx1 X ce) (σ1, (ls, g0)))
        (interp_cfg_model ctx2 (mrec_ctx ctx2 X ce) (σ2, (ls, g0))).
    Proof using Hctx.
      destruct (lg_call_dispatch ce U0 U0 σ1 σ2 ls Hpu0 (incl_refl U0) Heq)
        as [(t_call & Ec1 & Ec2 & Ht_call) | Href_call].
      - eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_obs_eq, Ec1
          | symmetry; apply interp_cfg_model_obs_eq, Ec2 |].
        exact (cfg_leaf_g_sync t_call Ht_call U0 σ1 σ2 ls Hpu0 Heq).
      - exact Href_call.
    Qed.
  End LeafKnotG.

End MemoryAndSerialization.
