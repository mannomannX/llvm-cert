(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Inlining Callee Block & Parameter-Copy Simulation ([CertPasses.InlineCalleeProof])

    Purpose:
      Proves local-environment invariants ([env_agree_outside],
      [callee_defs_bound]), primitive [lread]/[lwrite]/[stack_push]/[stack_pop]
      steps, renamed expression/attribute simulation, [denote_block_callee_sim],
      and parameter-copy simulation.

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml.

    Assumptions:
      Depends on Stdlib, Paco, ITree, ExtLib, Vellvm, [CertPasses.PassCommon],
      [CertPasses.common.ItreeTactics], and
      [CertPasses.Inline{Spec,SyntaxProof,FrameGenv,Sim}]; zero custom axioms.

    Section Outline:
      (9A) Local-env invariants & [ren_exp_id]; (9B) Primitive local/stack/exc
      lemmas; (9C) Expression simulation; (9D) Attributes & [select_switch];
      (9E) Callee block & parameter-copy simulation. *)

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

From CertPasses Require Import InlineSpec InlineSyntaxProof InlineFrameGenv InlineSim.

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
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise; reflexivity
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
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply cfg_inline_sim_raise; reflexivity
    | _ => idtac
    end.

  #[local] Ltac try_mcfg_raise :=
    lazymatch goal with
    | |- mcfg_inline_sim _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply mcfg_inline_sim_raise; reflexivity
    | |- gen_inline_sim _ _ _ _ _ _ _ _ _ _ _ _ (@raise _ _ _ _) (@raise _ _ _ _) => apply mcfg_inline_sim_raise; reflexivity
    | _ => idtac
    end.

  (** ** 9A. Local-Environment Invariants, [ren_exp_id], and Monad Helpers *)

  Definition env_agree_outside (fresh_set : list raw_id) (e1 e2 : @local_env PaV) : Prop :=
    forall x, ~ In x fresh_set -> Maps.lookup x e1 = Maps.lookup x e2.

  Lemma env_agree_outside_refl (fresh_set : list raw_id) (e : @local_env PaV) :
    env_agree_outside fresh_set e e.
  Proof.
    intros x _; reflexivity.
  Qed.

  Lemma env_agree_outside_add_both (fresh_set : list raw_id)
    (x : local_id) (v : @dvalue PaV) (e1 e2 : @local_env PaV) :
    env_agree_outside fresh_set e1 e2 ->
    env_agree_outside fresh_set (Maps.add x v e1) (Maps.add x v e2).
  Proof.
    unfold local_id in *; intros Hagree y Hy.
    destruct (RawIDOrd.eq_dec x y) as [<- | Hne].
    - cbn [Maps.lookup Maps.add Map_rmap]; rewrite !RMF.F.add_eq_o by reflexivity; reflexivity.
    - cbn [Maps.lookup Maps.add Map_rmap]; rewrite !RMF.F.add_neq_o by exact Hne; apply Hagree, Hy.
  Qed.

  Lemma env_agree_outside_add_fresh_r (fresh_set : list raw_id)
    (x : local_id) (v : @dvalue PaV) (e1 e2 : @local_env PaV)
    (Hx : In x fresh_set) :
    env_agree_outside fresh_set e1 e2 ->
    env_agree_outside fresh_set e1 (Maps.add x v e2).
  Proof.
    unfold local_id in *; intros Hagree y Hy.
    assert (Hne : x <> y) by (intros ->; contradiction).
    cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by exact Hne; apply Hagree, Hy.
  Qed.

  Definition callee_defs_bound (ren_l : raw_id -> raw_id) (defs : list raw_id)
    (e1 e2 : @local_env PaV) : Prop :=
    forall x,
      In x defs ->
      exists v, Maps.lookup x e1 = Some v /\ Maps.lookup (ren_l x) e2 = Some v.

  Lemma callee_defs_bound_incl (ren_l : raw_id -> raw_id) (d1 d2 : list raw_id)
    (e1 e2 : @local_env PaV) :
    incl d1 d2 ->
    callee_defs_bound ren_l d2 e1 e2 ->
    callee_defs_bound ren_l d1 e1 e2.
  Proof.
    intros Hincl Hbound x Hx; apply Hbound, Hincl, Hx.
  Qed.

  Lemma callee_defs_bound_add (ren_l : raw_id -> raw_id) (dom defs : list raw_id)
    (x : local_id) (v : @dvalue PaV) (e1 e2 : @local_env PaV)
    (Hinj : forall x1 x2, In x1 dom -> In x2 dom -> ren_l x1 = ren_l x2 -> x1 = x2)
    (Hdefs_dom : incl defs dom)
    (Hx_dom : In x dom) :
    callee_defs_bound ren_l defs e1 e2 ->
    callee_defs_bound ren_l (defs ++ [x]) (Maps.add x v e1) (Maps.add (ren_l x) v e2).
  Proof.
    unfold local_id in *; intros Hbound y Hy.
    destruct (RawIDOrd.eq_dec x y) as [<- | Hne].
    - exists v; cbn [Maps.lookup Maps.add Map_rmap]; rewrite !RMF.F.add_eq_o by reflexivity; split; reflexivity.
    - apply in_app_or in Hy as [Hy | [Heq | []]]; [| congruence].
      assert (Hy_dom : In y dom) by (apply Hdefs_dom, Hy).
      assert (Hren_ne : ren_l x <> ren_l y).
      { intros Heq; apply Hne, (Hinj x y Hx_dom Hy_dom Heq). }
      cbn [Maps.lookup Maps.add Map_rmap];
        rewrite RMF.F.add_neq_o by exact Hne;
        rewrite RMF.F.add_neq_o by exact Hren_ne.
      apply Hbound, Hy.
  Qed.

  Lemma callee_defs_bound_add_other_r (ren_l : raw_id -> raw_id) (defs : list raw_id)
    (z : local_id) (v : @dvalue PaV) (e1 e2 : @local_env PaV)
    (Hother : forall x, In x defs -> ren_l x <> z) :
    callee_defs_bound ren_l defs e1 e2 ->
    callee_defs_bound ren_l defs e1 (Maps.add z v e2).
  Proof.
    unfold local_id in *; intros Hbound x Hx.
    destruct (Hbound x Hx) as (vx & Hlk1 & Hlk2).
    assert (Hne : z <> ren_l x) by (intros ->; exact (Hother x Hx Logic.eq_refl)).
    exists vx; split; [exact Hlk1 | cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by exact Hne; exact Hlk2].
  Qed.

  Lemma ren_exp_id {T : Set} (e : exp T) :
    ren_exp (fun x : raw_id => x) e = e.
  Proof.
    assert (Hlist :
      forall (elts : list (T * exp T)),
        (forall p, In p elts -> ren_exp (fun x => x) (snd p) = snd p) ->
        (fix go (l : list (T * exp T)) : list (T * exp T) :=
           match l with
           | [] => []
           | (t, ex) :: rest => (t, ren_exp (fun x => x) ex) :: go rest
           end) elts = elts).
    { induction elts as [| [t ex] rest IHl]; intros Hall; [reflexivity |].
      pose proof (Hall (t, ex) (or_introl Logic.eq_refl)) as Hhd;
        cbn [snd] in Hhd; rewrite Hhd, IHl; [reflexivity |].
      intros p Hp; apply Hall; right; exact Hp. }
    assert (Hmdlist :
      forall (ms : list (metadata T)),
        (forall m, In m ms -> ren_metadata (fun x => x) m = m) ->
        (fix go_md (l : list (metadata T)) : list (metadata T) :=
           match l with
           | [] => []
           | m :: rest => ren_metadata (fun x => x) m :: go_md rest
           end) ms = ms).
    { induction ms as [| m rest IHm]; intros Hall; [reflexivity |].
      rewrite (Hall m (or_introl Logic.eq_refl)), IHm; [reflexivity |].
      intros m0 Hm0; apply Hall; right; exact Hm0. }
    apply (@AstLib.exp_ind_full T
             (fun v => ren_exp (fun x => x) v = v)
             (fun m => ren_metadata (fun x => x) m = m));
      intros;
      repeat match goal with p : T * exp T |- _ => destruct p as [? ?] end;
      try match goal with i : ident |- _ => destruct i end;
      cbn [ren_exp ren_metadata ren_ident snd] in *;
      try reflexivity;
      try congruence;
      try (f_equal; apply Hlist; assumption);
      try (f_equal; apply Hmdlist; assumption).
    - (* OP_GetElementPtr *)
      rewrite H, (Hlist idxs H0); reflexivity.
  Qed.

  Lemma loop_monad_itree_app {E : Type -> Type} {A : Type}
    (f : A -> itree E unit) (xs ys : list A) :
    loop_monad f (xs ++ ys) ≅
    ITree.bind (loop_monad f xs) (fun _ => loop_monad f ys).
  Proof.
    induction xs as [| x xs' IH]; cbn [app loop_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    - rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_bind.
      apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [] _ _; exact IH.
  Qed.

  Lemma denote_code_app_eq
    (c1 c2 : code dtyp) (va : option (@ptr (@PROV PaV) (@PTR PaV))) :
    @denote_code PaV (c1 ++ c2) va ≅
    ITree.bind (@denote_code PaV c1 va) (fun _ => @denote_code PaV c2 va).
  Proof.
    unfold denote_code; apply loop_monad_itree_app.
  Qed.

  (** ** 9B. Primitive [lread], [lwrite], [stack_push], [stack_pop], and [raiseLLVM] Lemmas *)

  Lemma mcfg_inline_sim_lread_both
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (e1 e2 : @local_env PaV) (x1 x2 : local_id) (v : @dvalue PaV)
    (He1 : ic_env1 ic = Some e1)
    (He2 : ic_env2 ic = Some e2)
    (Hlk1 : Maps.lookup x1 e1 = Some v)
    (Hlk2 : Maps.lookup x2 e2 = Some v) :
    mcfg_inline_sim g0 bf (fun ic' r1 r2 => ic' = ic /\ r1 = v /\ r2 = v)
      ic (lread x1) (lread x2).
  Proof.
    pstep.
    eapply GIS_ReadL with (env1 := e1) (x := x1) (v := v) (k1 := fun z => Ret z);
      [exact He1 | unfold lread; symmetry; apply Eqit.bind_ret_r | exact Hlk1 |].
    eapply GIS_ReadR with (env2 := e2) (x := x2) (v := v) (k2 := fun z => Ret z);
      [exact He2 | unfold lread; symmetry; apply Eqit.bind_ret_r | exact Hlk2 |].
    apply GIS_Step; cbn; auto.
  Qed.

  Lemma mcfg_inline_sim_lread_synced
    (g0 : global_env) (bf : bool)
    stk (e1 e2 : @local_env PaV) (x : local_id)
    (Hlk : Maps.lookup x e1 = Maps.lookup x e2) :
    mcfg_inline_sim g0 bf
      (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
      (IC_Synced stk e1 e2) (lread x) (lread x).
  Proof.
    unfold lread; try unfold trigger; unfold ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body;
      try unfold subevent, resum;
      cbn [observe gis_vis_both as_local_mcfg ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1];
      try unfold resum, ReSum_id, id_, Id_IFun.
    right; right; left.
    split; [reflexivity | split; [exact Hlk |]].
    intros v _; exists (Ret v), (Ret v).
    split; [apply ITS_Refl | split; [apply ITS_Refl |]].
    left; apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma cfg_inline_sim_lwrite_lr
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool)
    (ic ic1 ic2 : inline_ctx) (x1 x2 : local_id) (v : @dvalue PaV)
    (Hw1 : ic_write1 x1 v ic = Some ic1)
    (Hw2 : ic_write2 x2 v ic1 = Some ic2) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic2 /\ r1 = tt /\ r2 = tt)
      ic (lwrite x1 v) (lwrite x2 v).
  Proof.
    pstep.
    eapply GIS_WriteL with (ic' := ic1) (x := x1) (v := v) (k1 := fun z => Ret z);
      [exact Hw1 | unfold lwrite; symmetry; apply Eqit.bind_ret_r |].
    eapply GIS_WriteR with (ic' := ic2) (x := x2) (v := v) (k2 := fun z => Ret z);
      [exact Hw2 | unfold lwrite; symmetry; apply Eqit.bind_ret_r |].
    apply GIS_Step; cbn; auto.
  Qed.

  Lemma cfg_inline_sim_lwrite_r
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool)
    (ic ic' : inline_ctx) (x2 : local_id) (v : @dvalue PaV)
    (Hw2 : ic_write2 x2 v ic = Some ic') :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic0 r1 r2 => ic0 = ic' /\ r1 = tt /\ r2 = tt)
      ic (Ret tt) (lwrite x2 v).
  Proof.
    pstep.
    eapply GIS_WriteR with (ic' := ic') (x := x2) (v := v) (k2 := fun z => Ret z);
      [exact Hw2 | unfold lwrite; symmetry; apply Eqit.bind_ret_r |].
    apply GIS_Step; cbn; auto.
  Qed.

  Lemma cfg_inline_sim_stack_push_sync
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    stk (e1 e2 : @local_env PaV) (bs : list (local_id * @dvalue PaV)) :
    cfg_inline_sim opt_call1 g0 true
      (fun ic' r1 r2 =>
         ic' = IC_Synced ((e1, e2) :: stk) (init_local_env bs) (init_local_env bs) /\
         r1 = tt /\ r2 = tt)
      (IC_Synced stk e1 e2) (stack_push bs) (stack_push bs).
  Proof.
    unfold stack_push; try unfold trigger_cast; try unfold trigger; unfold ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite ?observe_bind;
      norm_subevent; cbn [observe gis_vis_both as_stack_cfg as_stack_mcfg].
    right; right; right; split; [reflexivity | split; [reflexivity |]].
    exists (Ret tt), (Ret tt).
    split; [apply ITS_Refl | split; [apply ITS_Refl |]].
    left; apply gen_inline_sim_ret; auto.
  Qed.

  Lemma cfg_inline_sim_stack_pop_sync
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    stk (p1 p2 e1 e2 : @local_env PaV) :
    cfg_inline_sim opt_call1 g0 true
      (fun ic' r1 r2 => ic' = IC_Synced stk p1 p2 /\ r1 = tt /\ r2 = tt)
      (IC_Synced ((p1, p2) :: stk) e1 e2) stack_pop stack_pop.
  Proof.
    unfold stack_pop; try unfold trigger_cast; try unfold trigger; unfold ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite ?observe_bind;
      norm_subevent; cbn [observe gis_vis_both as_stack_cfg as_stack_mcfg].
    right; right; right; split; [reflexivity |].
    exists (Ret tt), (Ret tt).
    split; [apply ITS_Refl | split; [apply ITS_Refl |]].
    left; apply gen_inline_sim_ret; auto.
  Qed.

  Lemma cfg_inline_sim_raiseLLVM
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    stk (e1 e2 : @local_env PaV) (ex : @exc PaV) :
    cfg_inline_sim opt_call1 g0 bf RR (IC_Synced stk e1 e2) (raiseLLVM ex) (raiseLLVM ex).
  Proof.
    unfold raiseLLVM, trigger_cast, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind; cbn [observe].
    right; left; split; [reflexivity | split; [reflexivity | intros [] [] _ _]].
  Qed.

  (** ** 9C. Expression Denotation Simulation ([denote_exp], [denote_exp']) *)

  Lemma mcfg_inline_sim_freeze
    (g0 : global_env) (bf : bool) (ic : inline_ctx) (dv : @dvalue PaV)
    (Hact : is_ic_active ic = true) :
    forall dt : dtyp,
      mcfg_inline_sim g0 bf (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
        ic (freeze dt dv) (freeze dt dv).
  Proof.
    induction dv as [db | pk fs IHfs | vc es IHes] using dvalue_ind_nested; intros dt;
      unfold freeze.
    - assert (Hfmap_ret :
        forall (b : @dvalue_base PaV),
          mcfg_inline_sim g0 bf (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
            ic (Functor.fmap DVALUE_Base (ExtLib.Structures.Monad.ret b))
               (Functor.fmap DVALUE_Base (ExtLib.Structures.Monad.ret b))).
      { intros b.
        cbn [Functor.fmap Functor_itree Functor_Monad ExtLib.Structures.Monad.bind
             ExtLib.Structures.Monad.ret Monad_itree ITree.map].
        first [apply gen_inline_sim_ret; split; reflexivity
              | eapply gen_inline_sim_bind with (RA := fun ic' r1 r2 => ic' = ic /\ r1 = r2);
                [apply gen_inline_sim_ret; split; reflexivity
                | intros ? ? _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity]]. }
      destruct db as [| | | | | | | sz bv]; unfold freeze_base;
        try first [apply Hfmap_ret
                  | cbn [ExtLib.Structures.Monad.ret Monad_itree];
                    apply gen_inline_sim_ret; split; reflexivity].
      + unfold draw; apply mcfg_inline_sim_trigger_refl.
        destruct ic; try discriminate Hact; reflexivity.
      + destruct bv as [bi | p | bits];
          try first [apply Hfmap_ret
                    | cbn [ExtLib.Structures.Monad.ret Monad_itree];
                      apply gen_inline_sim_ret; split; reflexivity].
        destruct (existsb is_poison_bit bits).
        * eapply gen_inline_sim_bind with (RA := fun ic' r1 r2 => ic' = ic /\ r1 = r2).
          -- unfold draw; apply mcfg_inline_sim_trigger_refl.
             destruct ic; try discriminate Hact; reflexivity.
          -- intros ? x1 x2 [-> <-];
               cbn [ExtLib.Structures.Monad.ret Monad_itree];
               apply gen_inline_sim_ret; split; reflexivity.
        * first [apply Hfmap_ret
                | cbn [ExtLib.Structures.Monad.ret Monad_itree];
                  apply gen_inline_sim_ret; split; reflexivity].
    - destruct dt as [| p dts |]; cbv beta iota zeta;
        lazymatch goal with
        | |- mcfg_inline_sim _ _ _ _ (raise _) (raise _) => apply mcfg_inline_sim_raise, Hact
        | _ => idtac
        end.
      eapply gen_inline_sim_bind with (RA := fun ic' v1 v2 => ic' = ic /\ v1 = v2);
        [| intros ? v1 v2 [-> <-];
           cbn [ExtLib.Structures.Monad.ret Monad_itree];
           apply gen_inline_sim_ret; split; reflexivity].
      lazymatch goal with
      | |- ?Sim ?ic0 (?go fs dts []) (?go fs dts []) =>
          cut (forall acc : list (@dvalue PaV),
                  Sim ic0 (go fs dts acc) (go fs dts acc));
            [intros Hcut; exact (Hcut []) |]
      end.
      revert dts;
      induction IHfs as [| f fs' Hf _ IH]; intros [| t ts] acc; cbv beta iota zeta;
        try (apply mcfg_inline_sim_raise, Hact).
      + cbn [ExtLib.Structures.Monad.ret Monad_itree];
          apply gen_inline_sim_ret; split; reflexivity.
      + eapply gen_inline_sim_bind with (RA := fun ic' v1 v2 => ic' = ic /\ v1 = v2);
          [apply (Hf t) | intros ? v1 v2 [-> <-]; apply IH].
    - destruct dt as [| | v sz t]; cbv beta iota zeta;
        try (apply mcfg_inline_sim_raise, Hact).
      eapply gen_inline_sim_bind with (RA := fun ic' v1 v2 => ic' = ic /\ v1 = v2);
        [| intros ? v1 v2 [-> <-];
           cbn [ExtLib.Structures.Monad.ret Monad_itree];
           apply gen_inline_sim_ret; split; reflexivity].
      lazymatch goal with
      | |- ?Sim ?ic0 (?go es []) (?go es []) =>
          cut (forall acc : list (@dvalue PaV),
                  Sim ic0 (go es acc) (go es acc));
            [intros Hcut; exact (Hcut []) |]
      end.
      induction IHes as [| e es' He _ IH]; intros acc.
      + cbn [ExtLib.Structures.Monad.ret Monad_itree];
          apply gen_inline_sim_ret; split; reflexivity.
      + eapply gen_inline_sim_bind with (RA := fun ic' v1 v2 => ic' = ic /\ v1 = v2);
          [apply (He t) | intros ? v1 v2 [-> <-]; apply IH].
  Qed.

  Lemma mcfg_inline_sim_map_texps
    (g0 : global_env) (ic : inline_ctx) (ren_l : raw_id -> raw_id)
    (es : list (dtyp * exp dtyp))
    (IHes : Forall
              (fun te =>
                 (forall x,
                    In x (full_exp_uses (snd te)) ->
                    mcfg_inline_sim g0 false (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
                      ic (lread x) (lread (ren_l x))) ->
                 forall top,
                   mcfg_inline_sim g0 false (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
                     ic (denote_exp top (snd te)) (denote_exp top (ren_exp ren_l (snd te))))
              es)
    (Hvar : forall x,
              In x ((fix go (l : list (dtyp * exp dtyp)) : list raw_id :=
                       match l with
                       | [] => []
                       | (_, ex) :: rest => full_exp_uses ex ++ go rest
                       end) es) ->
              mcfg_inline_sim g0 false (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
                ic (lread x) (lread (ren_l x))) :
    mcfg_inline_sim g0 false (fun ic' r1 r2 => ic' = ic /\ r1 = r2) ic
      (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex) es)
      (map_monad (fun '(dt, ex) => denote_exp (Some dt) ex)
         ((fix go (l : list (dtyp * exp dtyp)) : list (dtyp * exp dtyp) :=
             match l with
             | [] => []
             | (t, ex) :: rest => (t, ren_exp ren_l ex) :: go rest
             end) es)).
  Proof.
    induction IHes as [| [t ex] rest Hex _ IH]; cbn [map_monad snd] in *.
    - apply gen_inline_sim_ret; split; reflexivity.
    - eapply gen_inline_sim_bind.
      + apply Hex; intros x Hx; apply Hvar, in_or_app; left; exact Hx.
      + intros ? v1 v2 [-> <-].
        eapply gen_inline_sim_bind.
        * apply IH; intros x Hx; apply Hvar, in_or_app; right; exact Hx.
        * intros ? vs1 vs2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma denote_exp_gen_sim
    (g0 : global_env) (ic : inline_ctx) (ren_l : raw_id -> raw_id)
    (Hact : is_ic_active ic = true)
    (e : exp dtyp)
    (Hvar : forall x,
              In x (full_exp_uses e) ->
              mcfg_inline_sim g0 false (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
                ic (lread x) (lread (ren_l x))) :
    forall top : option dtyp,
      mcfg_inline_sim g0 false (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
        ic (denote_exp top e) (denote_exp top (ren_exp ren_l e)).
  Proof.
    revert Hvar; induction e using exp_denote_ind; intros Hvar top;
      cbn [ren_exp ren_metadata denote_exp];
      cbn [full_exp_uses full_metadata_uses] in Hvar;
      lazymatch goal with
      | |- mcfg_inline_sim _ _ _ _ (Ret _) (Ret _) =>
          apply gen_inline_sim_ret; split; reflexivity
      | |- mcfg_inline_sim _ _ _ _ (ExtLib.Structures.Monad.ret _) (ExtLib.Structures.Monad.ret _) =>
          apply gen_inline_sim_ret; split; reflexivity
      | _ => idtac
      end;
      lazymatch goal with
      | |- mcfg_inline_sim _ _ _ _ (raise _) (raise _) =>
          apply mcfg_inline_sim_raise, Hact
      | |- mcfg_inline_sim _ _ _ _
             (match top with Some _ => _ | None => _ end)
             (match top with Some _ => _ | None => _ end) =>
          destruct top; [apply mcfg_inline_sim_EOU, Hact | apply mcfg_inline_sim_raise, Hact]
      | _ => idtac
      end.
    - (* EXP_Ident *)
      destruct id as [gid | lid]; cbn [ren_ident denote_exp lookup_id].
      + unfold gread; apply mcfg_inline_sim_trigger_refl.
        destruct ic; try discriminate Hact; reflexivity.
      + apply Hvar; left; reflexivity.
    - (* EXP_Bool *)
      destruct b; apply gen_inline_sim_ret; split; reflexivity.
    - (* EXP_Cstring *)
      eapply gen_inline_sim_bind;
        [apply (mcfg_inline_sim_map_texps g0 ic ren_l es H Hvar)
        | intros ? vs1 vs2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
    - (* EXP_Struct *)
      eapply gen_inline_sim_bind;
        [apply (mcfg_inline_sim_map_texps g0 ic ren_l es H Hvar)
        | intros ? vs1 vs2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
    - (* EXP_Packed_struct *)
      eapply gen_inline_sim_bind; [apply mcfg_inline_sim_EOU, Hact | intros ? [] _ [-> _]].
      eapply gen_inline_sim_bind;
        [apply (mcfg_inline_sim_map_texps g0 ic ren_l es H Hvar)
        | intros ? vs1 vs2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
    - (* EXP_Array *)
      eapply gen_inline_sim_bind;
        [apply (mcfg_inline_sim_map_texps g0 ic ren_l es H Hvar)
        | intros ? vs1 vs2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
    - (* EXP_Vector *)
      eapply gen_inline_sim_bind;
        [apply (mcfg_inline_sim_map_texps g0 ic ren_l es H Hvar)
        | intros ? vs1 vs2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
    - (* OP_IBinop *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; exact Hx | intros ? v2 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_ICmp *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; exact Hx | intros ? v2 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_FBinop *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; exact Hx | intros ? v2 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_Fneg *)
      eapply gen_inline_sim_bind; [apply IHe, Hvar | intros ? v1 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_FCmp *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; exact Hx | intros ? v2 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_Conversion *)
      eapply gen_inline_sim_bind; [apply IHe, Hvar | intros ? dv _ [-> <-]].
      unfold convert; destruct ct as [| pct | ict].
      + destruct (dtyp_eqb tf tt0); [apply gen_inline_sim_ret; split; reflexivity |].
        destruct (bit_sizeof_dtyp tf =? bit_sizeof_dtyp tt0)%N;
          [apply mcfg_inline_sim_EOU, Hact | apply mcfg_inline_sim_raise, Hact].
      + apply mcfg_inline_sim_EOU, Hact.
      + unfold conv; apply mcfg_inline_sim_trigger_refl.
        destruct ic; try discriminate Hact; reflexivity.
    - (* OP_GetElementPtr *)
      eapply gen_inline_sim_bind;
        [apply IHe; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? vp _ [-> <-]].
      eapply gen_inline_sim_bind.
      + apply (mcfg_inline_sim_map_texps g0 ic ren_l idxs H).
        intros x Hx; apply Hvar, in_or_app; right; exact Hx.
      + intros ? vs _ [-> <-]; apply mcfg_inline_sim_EOU, Hact.
    - (* OP_ExtractElement *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; exact Hx | intros ? v2 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_InsertElement *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind.
      + eapply gen_inline_sim_bind;
          [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; apply in_or_app; left; exact Hx
          | intros ? v2 _ [-> <-]; apply mcfg_inline_sim_EOU, Hact].
      + intros ? b2 _ [-> <-].
        eapply gen_inline_sim_bind;
          [apply IHe3; intros x Hx; apply Hvar, in_or_app; right; apply in_or_app; right; exact Hx
          | intros ? v3 _ [-> <-]; apply mcfg_inline_sim_EOU, Hact].
    - (* OP_ShuffleVector *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; apply in_or_app; left; exact Hx
        | intros ? v2 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe3; intros x Hx; apply Hvar, in_or_app; right; apply in_or_app; right; exact Hx
        | intros ? v3 _ [-> <-]; apply mcfg_inline_sim_EOU, Hact].
    - (* OP_ExtractValue *)
      eapply gen_inline_sim_bind; [apply IHe, Hvar | intros ? v1 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_InsertValue *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; exact Hx | intros ? v2 _ [-> <-]].
      apply mcfg_inline_sim_EOU, Hact.
    - (* OP_Select *)
      eapply gen_inline_sim_bind;
        [apply IHe1; intros x Hx; apply Hvar, in_or_app; left; exact Hx | intros ? v1 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe2; intros x Hx; apply Hvar, in_or_app; right; apply in_or_app; left; exact Hx
        | intros ? v2 _ [-> <-]].
      eapply gen_inline_sim_bind;
        [apply IHe3; intros x Hx; apply Hvar, in_or_app; right; apply in_or_app; right; exact Hx
        | intros ? v3 _ [-> <-]; apply mcfg_inline_sim_EOU, Hact].
    - (* OP_Freeze *)
      eapply gen_inline_sim_bind; [apply IHe, Hvar | intros ? dv _ [-> <-]].
      apply mcfg_inline_sim_freeze, Hact.
    - (* EXP_BlockAddress *)
      unfold gread; apply mcfg_inline_sim_trigger_refl.
      destruct ic; try discriminate Hact; reflexivity.
    - (* EXP_Splat *)
      eapply gen_inline_sim_bind; [apply mcfg_inline_sim_EOU, Hact | intros ? [sz t] _ [-> <-]].
      eapply gen_inline_sim_bind; [apply IHe, Hvar | intros ? v _ [-> <-]].
      apply gen_inline_sim_ret; split; reflexivity.
    - (* EXP_Metadata (METADATA_Const) *)
      apply IHe, Hvar.
    - (* EXP_Metadata (other) *)
      destruct md as [| | [t1 e1] | | | |];
        [| | exfalso; exact (H t1 e1 Logic.eq_refl) | | | |];
        cbn [ren_metadata denote_exp];
        apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma denote_exp'_callee_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (ren_l : raw_id -> raw_id) (d_avail : list raw_id)
    stk (ce1 e1 e2 : @local_env PaV)
    (top : option dtyp) (e : exp dtyp)
    (Huses : incl (full_exp_uses e) d_avail)
    (Hbound : callee_defs_bound ren_l d_avail e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 => ic' = IC_Inlined stk ce1 e1 e2 /\ r1 = r2)
      (IC_Inlined stk ce1 e1 e2)
      (denote_exp' top e)
      (denote_exp' top (ren_exp ren_l e)).
  Proof.
    unfold denote_exp'; apply mcfg_to_cfg_withCall_sim.
    apply denote_exp_gen_sim; [reflexivity |].
    intros x Hx.
    destruct (Hbound x (Huses x Hx)) as (v & Hlk1 & Hlk2).
    eapply gen_inline_sim_weaken;
      [| apply (mcfg_inline_sim_lread_both g0 false (IC_Inlined stk ce1 e1 e2)
                  e1 e2 x (ren_l x) v Logic.eq_refl Logic.eq_refl Hlk1 Hlk2)].
    intros ? ? ? (-> & -> & ->); split; reflexivity.
  Qed.

  Lemma denote_exp'_caller_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (fresh_set : list raw_id)
    stk (e1 e2 : @local_env PaV)
    (top : option dtyp) (e : exp dtyp)
    (Huses : forall x, In x (full_exp_uses e) -> ~ In x fresh_set)
    (Hagree : env_agree_outside fresh_set e1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
      (IC_Synced stk e1 e2)
      (denote_exp' top e)
      (denote_exp' top e).
  Proof.
    unfold denote_exp'; apply mcfg_to_cfg_withCall_sim.
    rewrite <- (ren_exp_id e) at 2.
    apply (denote_exp_gen_sim g0 (IC_Synced stk e1 e2) (fun x => x)); [reflexivity |].
    intros x Hx; apply mcfg_inline_sim_lread_synced, Hagree, Huses, Hx.
  Qed.

  (** ** 9D. Attribute, Dereferenceability, and [select_switch] Lemmas *)

  Lemma cfg_inline_sim_assert_deref
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (or_null : bool) (n : N) (v : @dvalue PaV) (msg1 msg2 : string)
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic /\ r1 = tt /\ r2 = tt)
      ic
      (assert_dereferenceable or_null n v msg1)
      (assert_dereferenceable or_null n v msg2).
  Proof.
    unfold assert_dereferenceable.
    destruct v as [db | |]; [| apply cfg_inline_sim_raise, Hact | apply cfg_inline_sim_raise, Hact].
    destruct db as [p | | | | | | |]; cbv beta iota zeta;
      try_cfg_raise_h Hact.
    - destruct ((or_null && (ptr_to_int p =? ptr_to_int (@null (@PROV PaV) (@PTR PaV)))%Z) || (n =? 0)%N)%bool.
      + apply gen_inline_sim_ret; auto.
      + eapply gen_inline_sim_bind.
        * unfold load; apply cfg_inline_sim_trigger_refl.
          destruct ic; try discriminate Hact; reflexivity.
        * intros ? _ _ [-> _]; apply gen_inline_sim_ret; auto.
    - apply cfg_inline_sim_raiseUB.
  Qed.

  Lemma cfg_inline_sim_assert_load_deref
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (md : list (metadata dtyp)) (v : @dvalue PaV) (msg1 msg2 : string)
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic /\ r1 = tt /\ r2 = tt)
      ic
      (assert_load_dereferenceable md v msg1)
      (assert_load_dereferenceable md v msg2).
  Proof.
    unfold assert_load_dereferenceable.
    destruct (load_metadata_dereferenceable md) as [[or_null n] |].
    - apply cfg_inline_sim_assert_deref, Hact.
    - apply gen_inline_sim_ret; auto.
  Qed.

  Lemma cfg_inline_sim_apply_attrs
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (attrs : list param_attr) (msg1 msg2 : string) (v : @dvalue PaV)
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
      ic
      (apply_attrs attrs msg1 v)
      (apply_attrs attrs msg2 v).
  Proof.
    unfold apply_attrs, apply_value_attrs.
    set (vp := value_attrs_poison attrs v).
    destruct (existsb attr_is_noundef attrs && negb (dvalue_well_defined vp))%bool.
    - cbn [EOU_to_itree ExtLib.Structures.Monad.bind Monad_itree].
      unfold raiseUB, trigger_cast, ITree.trigger.
      pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind; cbn [observe]; left; reflexivity.
    - cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      eapply gen_inline_sim_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      unfold assert_attrs_dereferenceable.
      destruct (find_option attr_dereferenceable attrs) as [[or_null n] |], vp as [db | |];
        try (eapply gen_inline_sim_obs_eq;
             [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |];
             apply gen_inline_sim_ret; split; reflexivity).
      destruct db;
        try (eapply gen_inline_sim_obs_eq;
             [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |];
             apply gen_inline_sim_ret; split; reflexivity).
      eapply gen_inline_sim_bind;
        [apply cfg_inline_sim_assert_deref, Hact
        | intros ? _ _ (-> & _ & _); apply gen_inline_sim_ret; split; reflexivity].
  Qed.

  Lemma cfg_inline_sim_apply_args_attrs
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (attrss : list (list param_attr)) (msg1 msg2 : string) (args : list (@dvalue PaV))
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
      ic
      (apply_args_attrs attrss msg1 args)
      (apply_args_attrs attrss msg2 args).
  Proof.
    revert attrss; induction args as [| v vs IH]; intros attrss; cbn [apply_args_attrs].
    - apply gen_inline_sim_ret; split; reflexivity.
    - destruct attrss as [| a rest].
      + eapply gen_inline_sim_bind; [apply cfg_inline_sim_apply_attrs, Hact | intros ? v1 _ [-> <-]].
        eapply gen_inline_sim_bind; [apply IH | intros ? vs1 _ [-> <-]].
        apply gen_inline_sim_ret; split; reflexivity.
      + eapply gen_inline_sim_bind; [apply cfg_inline_sim_apply_attrs, Hact | intros ? v1 _ [-> <-]].
        eapply gen_inline_sim_bind; [apply IH | intros ? vs1 _ [-> <-]].
        apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma cfg_inline_sim_check_call_return
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (ic : inline_ctx)
    (fattrs : list fn_attr) (ret_attrs : list param_attr)
    (ranges : option (list (int_syntax * int_syntax)))
    (loc1 loc2 : string) (args : list (@dvalue PaV)) (res : @exc PaV + @dvalue PaV)
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf
      (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
      ic
      (check_call_return fattrs ret_attrs ranges loc1 args res)
      (check_call_return fattrs ret_attrs ranges loc2 args res).
  Proof.
    unfold check_call_return, check_call_result.
    destruct res as [ex | v].
    - destruct (existsb fn_attr_is_nounwind fattrs).
      + cbn [EOU_to_itree ExtLib.Structures.Monad.bind Monad_itree].
        unfold raiseUB, trigger_cast, ITree.trigger.
        pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind; cbn [observe]; left; reflexivity.
      + cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        eapply gen_inline_sim_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        apply gen_inline_sim_ret; split; reflexivity.
    - destruct (existsb fn_attr_is_noreturn fattrs).
      + cbn [EOU_to_itree ExtLib.Structures.Monad.bind Monad_itree].
        unfold raiseUB, trigger_cast, ITree.trigger.
        pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind; cbn [observe]; left; reflexivity.
      + destruct (existsb fn_attr_is_nocreateundeforpoison fattrs
                  && forallb dvalue_well_defined args
                  && negb (dvalue_well_defined v))%bool.
        * cbn [EOU_to_itree ExtLib.Structures.Monad.bind Monad_itree].
          unfold raiseUB, trigger_cast, ITree.trigger.
          pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind; cbn [observe]; left; reflexivity.
        * cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
          eapply gen_inline_sim_obs_eq;
            [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
          eapply gen_inline_sim_bind;
            [apply cfg_inline_sim_apply_attrs, Hact
            | intros ? v1 _ [-> <-]; apply gen_inline_sim_ret; split; reflexivity].
  Qed.

  Lemma select_switch_ren_b (ren_b : block_id -> block_id)
    (val : @dvalue PaV) (def_b : block_id) :
    forall (sws : list (@dvalue PaV * block_id)),
      (exists msg,
         select_switch val def_b sws = raise_error msg /\
         select_switch val (ren_b def_b)
           (List.map (fun '(v, b) => (v, ren_b b)) sws) = raise_error msg) \/
      (exists b,
         In b (def_b :: List.map snd sws) /\
         select_switch val def_b sws = raise_ret b /\
         select_switch val (ren_b def_b)
           (List.map (fun '(v, b) => (v, ren_b b)) sws) = raise_ret (ren_b b)).
  Proof.
    induction sws as [| [v id] rest IH]; cbn [List.map select_switch snd].
    - right; exists def_b; split; [left; reflexivity | split; reflexivity].
    - destruct val as [db1 | |];
        [| left; eexists; split; reflexivity | left; eexists; split; reflexivity].
      destruct db1; try (left; eexists; split; reflexivity).
      destruct v as [db2 | |];
        [| left; eexists; split; reflexivity | left; eexists; split; reflexivity].
      destruct db2; try (left; eexists; split; reflexivity).
      destruct (Pos.eq_dec sz sz0) as [<- | _]; [cbn | left; eexists; split; reflexivity].
      match goal with |- context [if ?b then _ else _] => destruct b end.
      + right; exists id; split; [right; left; reflexivity | split; reflexivity].
      + destruct IH as [(msg & E1 & E2) | (b & Hb & E1 & E2)].
        * left; exists msg; split; assumption.
        * right; exists b; split.
          -- destruct Hb as [<- | Hb]; [left; reflexivity | right; right; exact Hb].
          -- split; assumption.
  Qed.

  Lemma switch_elab_ren_b (ren_b : block_id -> block_id)
    (val : @dvalue PaV) (def_b : block_id)
    (dests : list (tint_literal * block_id)) :
    let elab (db : block_id) (ds : list (tint_literal * block_id)) : EOU block_id :=
      ExtLib.Structures.Monad.bind
        (map_monad
           (fun '((TInt_Literal sz x), id) =>
              ExtLib.Structures.Monad.bind (coerce_integer_to_int (Some sz) (denote_int_syntax x))
                (fun s => ExtLib.Structures.Monad.ret (DVALUE_Base s, id)))
           ds)
        (fun switches => select_switch val db switches)
    in
    (exists eou_err,
       (forall b0, eou_err <> raise_ret b0) /\
       elab def_b dests = eou_err /\
       elab (ren_b def_b) (List.map (fun '(lit, b) => (lit, ren_b b)) dests) = eou_err) \/
    (exists b,
       In b (def_b :: List.map snd dests) /\
       elab def_b dests = raise_ret b /\
       elab (ren_b def_b) (List.map (fun '(lit, b) => (lit, ren_b b)) dests) = raise_ret (ren_b b)).
  Proof.
    intros elab.
    assert (Hmap :
      (exists err_sw,
         (forall l0, err_sw <> raise_ret l0) /\
         map_monad
           (fun '((TInt_Literal sz x), id) =>
              ExtLib.Structures.Monad.bind (coerce_integer_to_int (Some sz) (denote_int_syntax x))
                (fun s => ExtLib.Structures.Monad.ret (DVALUE_Base s, id)))
           dests = err_sw /\
         map_monad
           (fun '((TInt_Literal sz x), id) =>
              ExtLib.Structures.Monad.bind (coerce_integer_to_int (Some sz) (denote_int_syntax x))
                (fun s => ExtLib.Structures.Monad.ret (DVALUE_Base s, id)))
           (List.map (fun '(lit, b) => (lit, ren_b b)) dests) = err_sw) \/
      (exists sws,
         List.map snd sws = List.map snd dests /\
         map_monad
           (fun '((TInt_Literal sz x), id) =>
              ExtLib.Structures.Monad.bind (coerce_integer_to_int (Some sz) (denote_int_syntax x))
                (fun s => ExtLib.Structures.Monad.ret (DVALUE_Base s, id)))
           dests = raise_ret sws /\
         map_monad
           (fun '((TInt_Literal sz x), id) =>
              ExtLib.Structures.Monad.bind (coerce_integer_to_int (Some sz) (denote_int_syntax x))
                (fun s => ExtLib.Structures.Monad.ret (DVALUE_Base s, id)))
           (List.map (fun '(lit, b) => (lit, ren_b b)) dests) =
         raise_ret (List.map (fun '(v, b) => (v, ren_b b)) sws))).
    { induction dests as [| [[sz x] id] rest IH]; cbn [List.map map_monad snd].
      - right; exists []; split; [reflexivity | split; reflexivity].
      - destruct (coerce_integer_to_int (Some sz) (denote_int_syntax x)) as [m | m | m | s];
          cbn [EOU_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret].
        + left; exists (raise_error m); split; [intros ?; discriminate | split; reflexivity].
        + left; exists (raise_oom m); split; [intros ?; discriminate | split; reflexivity].
        + left; exists (raise_ub m); split; [intros ?; discriminate | split; reflexivity].
        + destruct IH as [(err_sw & Hnr & E1 & E2) | (sws & Hsnd & E1 & E2)];
            cbn [EOU_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret] in E1, E2.
          * rewrite E1, E2.
            destruct err_sw as [m | m | m | l0]; [| | | exfalso; exact (Hnr l0 Logic.eq_refl)];
              (cbn; left; eexists; split; [| split; reflexivity]; intros ?; discriminate).
          * rewrite E1, E2; cbn [EOU_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret List.map].
            right; exists ((DVALUE_Base s, id) :: sws).
            cbn [List.map snd]; rewrite Hsnd; split; [reflexivity | split; reflexivity]. }
    unfold elab.
    destruct Hmap as [(err_sw & Hnr & E1 & E2) | (sws & Hsnd & E1 & E2)].
    - rewrite E1, E2.
      destruct err_sw as [m | m | m | l0]; [| | | exfalso; exact (Hnr l0 Logic.eq_refl)];
        (cbn; left; eexists; split; [| split; reflexivity]; intros ?; discriminate).
    - rewrite E1, E2; cbn [EOU_monad ExtLib.Structures.Monad.bind].
      destruct (select_switch_ren_b ren_b val def_b sws)
        as [(msg & Es1 & Es2) | (b & Hb & Es1 & Es2)].
      + left; exists (raise_error msg); split; [intros ?; discriminate | split; assumption].
      + right; exists b; rewrite <- Hsnd; split; [exact Hb | split; assumption].
  Qed.

  Lemma map_id_pairs {A B : Type} (xs : list (A * B)) :
    List.map (fun '(a, b) => (a, b)) xs = xs.
  Proof.
    induction xs as [| [a b] rest IH]; [reflexivity | cbn; rewrite IH; reflexivity].
  Qed.

  (** ** 9E. Callee Leaf-Instruction, Code, Phi, Block, and Parameter-Copy Simulations *)

  Lemma denote_instr_callee_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (l_origs all_fresh d_cur : list raw_id)
    (ren_l : raw_id -> raw_id)
    stk (ce1 e1 e2 : @local_env PaV)
    (va1 va2 : option (@ptr (@PROV PaV) (@PTR PaV)))
    (iid : instr_id) (ins : instr dtyp) (md : list (metadata dtyp))
    (Hleaf : is_leaf_instr_entry (iid, ins, md) = true)
    (Hinj_l : forall x1 x2, In x1 l_origs -> In x2 l_origs -> ren_l x1 = ren_l x2 -> x1 = x2)
    (Hfresh_l : forall x, In x l_origs -> In (ren_l x) all_fresh)
    (Hd_dom : incl d_cur l_origs)
    (Hiid_dom : incl (instr_id_defs iid) l_origs)
    (Huses : incl (full_instr_uses ins ++ flat_map full_metadata_uses md) d_cur)
    (Hbound : callee_defs_bound ren_l d_cur e1 e2)
    (Hagree : env_agree_outside all_fresh ce1 e2) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         r1 = tt /\ r2 = tt /\
         exists e1' e2',
           ic' = IC_Inlined stk ce1 e1' e2' /\
           callee_defs_bound ren_l (d_cur ++ instr_id_defs iid) e1' e2' /\
           env_agree_outside all_fresh ce1 e2')
      (IC_Inlined stk ce1 e1 e2)
      (denote_instr (iid, ins, md) va1)
      (denote_instr (ren_code_entry ren_l (iid, ins, md)) va2).
  Proof.
    unfold is_leaf_instr_entry in Hleaf.
    apply andb_prop in Hleaf as [_ Hleaf].
    destruct iid as [x | vn],
             ins as [s_cmt | op | ? ? ? ? | dt anns | dt [du ptr] anns | [dt val] [du ptr] anns
                     | ? ? | ? | ? | s_f1 s_f2 | ? ? ?];
      try discriminate Hleaf.
    - (* IId x, INSTR_Op op *)
      assert (Hx_dom : In x l_origs) by (apply Hiid_dom; left; reflexivity).
      cbn [ren_code_entry ren_instr_id ren_leaf_instr denote_instr].
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_cur stk ce1 e1 e2 None op);
          [intros z Hz; apply Huses, in_or_app; left; exact Hz | exact Hbound].
      + intros ? uv _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                   (IC_Inlined stk ce1 e1 e2)
                   (IC_Inlined stk ce1 (Maps.add x uv e1) e2)
                   (IC_Inlined stk ce1 (Maps.add x uv e1) (Maps.add (ren_l x) uv e2))
                   x (ren_l x) uv Logic.eq_refl Logic.eq_refl).
        * intros ? [] [] (-> & _ & _).
          apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity |]].
          eexists _, _; split; [reflexivity | split].
          -- apply (callee_defs_bound_add ren_l l_origs d_cur x uv e1 e2 Hinj_l Hd_dom Hx_dom Hbound).
          -- apply env_agree_outside_add_fresh_r; [apply Hfresh_l, Hx_dom | exact Hagree].
    - (* IId x, INSTR_Alloca dt anns (0-byte varargs alloca) *)
      unfold is_zero_vararg_alloca in Hleaf; apply andb_prop in Hleaf as [Hdt Hanns].
      apply dtyp_eqb_eq in Hdt; apply is_empty_list_spec in Hanns; subst dt anns.
      assert (Hx_dom : In x l_origs) by (apply Hiid_dom; left; reflexivity).
      cbn [ren_code_entry ren_instr_id ren_leaf_instr denote_instr explicit_alignment find_option].
      eapply gen_inline_sim_obs_eq;
        [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
      eapply gen_inline_sim_bind.
      + unfold alloca; try unfold trigger; apply cfg_inline_sim_trigger_refl.
        norm_subevent;
        cbn [inl_sync_cfg inl_sync_mcfg is_callee_sync_mem];
        norm_subevent.
        rewrite dtyp_eqb_refl; reflexivity.
      + intros ? v _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                   (IC_Inlined stk ce1 e1 e2)
                   (IC_Inlined stk ce1 (Maps.add x v e1) e2)
                   (IC_Inlined stk ce1 (Maps.add x v e1) (Maps.add (ren_l x) v e2))
                   x (ren_l x) v Logic.eq_refl Logic.eq_refl).
        * intros ? [] [] (-> & _ & _).
          apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity |]].
          eexists _, _; split; [reflexivity | split].
          -- apply (callee_defs_bound_add ren_l l_origs d_cur x _ e1 e2 Hinj_l Hd_dom Hx_dom Hbound).
          -- apply env_agree_outside_add_fresh_r; [apply Hfresh_l, Hx_dom | exact Hagree].
    - (* IId x, INSTR_Load dt (du, ptr) anns *)
      assert (Hx_dom : In x l_origs) by (apply Hiid_dom; left; reflexivity).
      cbn [ren_code_entry ren_instr_id ren_leaf_instr denote_instr].
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_cur stk ce1 e1 e2 (Some du) ptr);
          [intros z Hz; apply Huses, in_or_app; left; cbn [full_instr_uses full_texp_uses snd];
           apply in_or_app; left; exact Hz
          | exact Hbound].
      + intros ? a _ [-> <-].
        eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
        eapply gen_inline_sim_bind;
          [unfold load; apply cfg_inline_sim_trigger_refl; reflexivity | intros ? v _ [-> <-]].
        eapply gen_inline_sim_bind; [apply cfg_inline_sim_EOU; reflexivity | intros ? v' _ [-> <-]].
        eapply gen_inline_sim_bind;
          [apply cfg_inline_sim_assert_load_deref; reflexivity | intros ? [] _ (-> & _ & _)].
        eapply gen_inline_sim_weaken;
          [| apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                      (IC_Inlined stk ce1 e1 e2)
                      (IC_Inlined stk ce1 (Maps.add x v' e1) e2)
                      (IC_Inlined stk ce1 (Maps.add x v' e1) (Maps.add (ren_l x) v' e2))
                      x (ren_l x) v' Logic.eq_refl Logic.eq_refl)].
        intros ? [] [] (-> & _ & _).
        split; [reflexivity | split; [reflexivity |]].
        eexists _, _; split; [reflexivity | split].
        * apply (callee_defs_bound_add ren_l l_origs d_cur x v' e1 e2 Hinj_l Hd_dom Hx_dom Hbound).
        * apply env_agree_outside_add_fresh_r; [apply Hfresh_l, Hx_dom | exact Hagree].
    - (* IVoid vn, INSTR_Comment *)
      cbn [ren_code_entry ren_instr_id ren_leaf_instr denote_instr instr_id_defs].
      rewrite app_nil_r; apply gen_inline_sim_ret.
      split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - (* IVoid vn, INSTR_Store (dt, val) (du, ptr) anns *)
      cbn [ren_code_entry ren_instr_id ren_leaf_instr denote_instr instr_id_defs].
      rewrite app_nil_r.
      eapply gen_inline_sim_bind.
      + apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_cur stk ce1 e1 e2 (Some dt) val);
          [intros z Hz; apply Huses, in_or_app; left; cbn [full_instr_uses full_texp_uses snd];
           apply in_or_app; left; exact Hz
          | exact Hbound].
      + intros ? v _ [-> <-].
        eapply gen_inline_sim_bind.
        * apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_cur stk ce1 e1 e2 (Some du) ptr);
            [intros z Hz; apply Huses, in_or_app; left; cbn [full_instr_uses full_texp_uses snd];
             apply in_or_app; right; apply in_or_app; left; exact Hz
            | exact Hbound].
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
    - (* IVoid vn, INSTR_Fence *)
      cbn [ren_code_entry ren_instr_id ren_leaf_instr denote_instr instr_id_defs].
      rewrite app_nil_r; apply gen_inline_sim_ret.
      split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
  Qed.

  Lemma denote_code_callee_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (l_origs all_fresh : list raw_id)
    (ren_l : raw_id -> raw_id)
    (va1 va2 : option (@ptr (@PROV PaV) (@PTR PaV)))
    (Hinj_l : forall x1 x2, In x1 l_origs -> In x2 l_origs -> ren_l x1 = ren_l x2 -> x1 = x2)
    (Hfresh_l : forall x, In x l_origs -> In (ren_l x) all_fresh) :
    forall (cd : code dtyp) (d_cur d_out : list raw_id)
           stk (ce1 e1 e2 : @local_env PaV),
      forallb is_leaf_instr_entry cd = true ->
      check_code_defs d_cur cd = Some d_out ->
      incl d_cur l_origs ->
      incl (flat_map (fun '(iid, _, _) => instr_id_defs iid) cd) l_origs ->
      callee_defs_bound ren_l d_cur e1 e2 ->
      env_agree_outside all_fresh ce1 e2 ->
      cfg_inline_sim opt_call1 g0 false
        (fun ic' r1 r2 =>
           r1 = tt /\ r2 = tt /\
           exists e1' e2',
             ic' = IC_Inlined stk ce1 e1' e2' /\
             callee_defs_bound ren_l d_out e1' e2' /\
             env_agree_outside all_fresh ce1 e2')
        (IC_Inlined stk ce1 e1 e2)
        (denote_code cd va1)
        (denote_code (List.map (ren_code_entry ren_l) cd) va2).
  Proof.
    induction cd as [| [[iid ins] md] rest IH];
      intros d_cur d_out stk ce1 e1 e2 Hleaf Hchk Hd_dom Hcd_dom Hbound Hagree.
    - cbn [check_code_defs] in Hchk; injection Hchk as <-.
      cbn [List.map denote_code loop_monad].
      apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - cbn [forallb] in Hleaf; apply andb_prop in Hleaf as [Hi Hrest_leaf].
      apply check_code_defs_inv in Hchk as [Huses Hchk_rest].
      cbn [flat_map] in Hcd_dom.
      assert (Hiid_dom : incl (instr_id_defs iid) l_origs).
      { intros z Hz; apply Hcd_dom, in_or_app; left; exact Hz. }
      assert (Hrest_dom : incl (flat_map (fun '(iid0, _, _) => instr_id_defs iid0) rest) l_origs).
      { intros z Hz; apply Hcd_dom, in_or_app; right; exact Hz. }
      cbn [List.map denote_code loop_monad].
      eapply gen_inline_sim_bind.
      + apply (denote_instr_callee_sim opt_call1 g0 l_origs all_fresh d_cur ren_l
                 stk ce1 e1 e2 va1 va2 iid ins md
                 Hi Hinj_l Hfresh_l Hd_dom Hiid_dom Huses Hbound Hagree).
      + intros ? [] [] (_ & _ & e1' & e2' & -> & Hbound' & Hagree').
        apply (IH (d_cur ++ instr_id_defs iid) d_out stk ce1 e1' e2' Hrest_leaf Hchk_rest);
          try assumption.
        apply incl_app; assumption.
  Qed.

  Lemma denote_phis_callee_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (l_origs b_origs all_fresh d_in : list raw_id)
    (ren_l ren_b : raw_id -> raw_id)
    stk (ce1 e1 e2 : @local_env PaV)
    (b_from1 b_from2 : block_id)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (Hinj_l : forall x1 x2, In x1 l_origs -> In x2 l_origs -> ren_l x1 = ren_l x2 -> x1 = x2)
    (Hfresh_l : forall x, In x l_origs -> In (ren_l x) all_fresh)
    (Hinj_b : forall b1 b2, In b1 b_origs -> In b2 b_origs -> ren_b b1 = ren_b b2 -> b1 = b2)
    (Hd_dom : incl d_in l_origs)
    (Hp_defs_dom : incl (List.map (fun '(x, _, _) => x) phis) l_origs)
    (Hp_lbls_dom : incl (flat_map (fun '(_, Phi _ _ pargs, _) => List.map fst pargs) phis) b_origs)
    (Hbound : callee_defs_bound ren_l d_in e1 e2)
    (Hagree : env_agree_outside all_fresh ce1 e2)
    (Hentry_or_pred :
       phis = [] \/
       (b_from2 = ren_b b_from1 /\
        In b_from1 b_origs /\
        Forall
          (fun '(_, Phi _ _ pargs, md) =>
             exists op,
               assoc b_from1 pargs = Some op /\
               incl (full_exp_uses op ++ flat_map full_metadata_uses md) d_in)
          phis)) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' r1 r2 =>
         r1 = tt /\ r2 = tt /\
         exists e1' e2',
           ic' = IC_Inlined stk ce1 e1' e2' /\
           callee_defs_bound ren_l (d_in ++ List.map (fun '(x, _, _) => x) phis) e1' e2' /\
           env_agree_outside all_fresh ce1 e2')
      (IC_Inlined stk ce1 e1 e2)
      (denote_phis b_from1 phis)
      (denote_phis b_from2 (List.map (ren_phi_entry ren_l ren_b) phis)).
  Proof.
    destruct Hentry_or_pred as [-> | (Hb_eq & Hfrom_dom & Hall_p)].
    - cbn [List.map denote_phis map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite app_nil_r.
      eapply gen_inline_sim_obs_eq;
        [symmetry; rewrite !Eqit.bind_ret_l; cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree]; rewrite !Eqit.bind_ret_l; reflexivity
        | symmetry; rewrite !Eqit.bind_ret_l; cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree]; rewrite !Eqit.bind_ret_l; reflexivity |].
      apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1, e2; auto]].
    - subst b_from2; unfold denote_phis.
      assert (Heval :
        forall ps,
          incl (flat_map (fun '(_, Phi _ _ pargs, _) => List.map fst pargs) ps) b_origs ->
          Forall
            (fun '(_, Phi _ _ pargs, md) =>
               exists op,
                 assoc b_from1 pargs = Some op /\
                 incl (full_exp_uses op ++ flat_map full_metadata_uses md) d_in)
            ps ->
          cfg_inline_sim opt_call1 g0 false
            (fun ic' dvs1 dvs2 =>
               ic' = IC_Inlined stk ce1 e1 e2 /\
               List.map fst dvs1 = List.map (fun '(x, _, _) => x) ps /\
               dvs2 = List.map (fun '(x, dv) => (ren_l x, dv)) dvs1)
            (IC_Inlined stk ce1 e1 e2)
            (map_monad (denote_phi b_from1) ps)
            (map_monad (denote_phi (ren_b b_from1)) (List.map (ren_phi_entry ren_l ren_b) ps))).
      { intros ps Hlbls Hps.
        induction Hps as [| [[x [fm dt pargs]] md] rest (op & Eop & Hop_uses) _ IH];
          cbn [List.map map_monad].
        - apply gen_inline_sim_ret; auto.
        - cbn [flat_map] in Hlbls.
          assert (Hpargs_dom : incl (List.map fst pargs) b_origs).
          { intros b Hb; apply Hlbls, in_or_app; left; exact Hb. }
          assert (Hrest_lbls : incl (flat_map (fun '(_, Phi _ _ pargs0, _) => List.map fst pargs0) rest) b_origs).
          { intros b Hb; apply Hlbls, in_or_app; right; exact Hb. }
          eapply gen_inline_sim_bind with
            (RA := fun ic' p1 p2 =>
                     ic' = IC_Inlined stk ce1 e1 e2 /\
                     exists uv, p1 = (x, uv) /\ p2 = (ren_l x, uv)).
          + cbn [ren_phi_entry denote_phi].
            lazymatch goal with
            | |- context [@Assoc.assoc ?A ?B ?RD (ren_b b_from1) ?xs] =>
                let t := constr:(@Assoc.assoc A B RD (ren_b b_from1) xs) in
                assert (Hassoc : t = option_map (ren_exp ren_l) (assoc b_from1 pargs))
                  by exact (assoc_ren_phi ren_b (ren_exp ren_l) b_origs b_from1 pargs Hinj_b Hfrom_dom Hpargs_dom);
                rewrite Hassoc; clear Hassoc
            end.
            rewrite Eop; cbn [option_map].
            eapply gen_inline_sim_bind.
            * apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_in stk ce1 e1 e2 (Some dt) op);
                [intros z Hz; apply Hop_uses, in_or_app; left; exact Hz | exact Hbound].
            * intros ? uv _ [-> <-]; apply gen_inline_sim_ret.
              split; [reflexivity | exists uv; split; reflexivity].
          + intros ? [id1 uv1] [id2 uv2] (-> & uv & E1 & E2).
            injection E1 as <- <-; injection E2 as -> ->.
            eapply gen_inline_sim_bind; [apply (IH Hrest_lbls) |].
            intros ? dvs1 dvs2 (-> & Hfst & ->).
            apply gen_inline_sim_ret;
              split; [reflexivity | split; [cbn; f_equal; exact Hfst | cbn; reflexivity]]. }
      assert (Hwrites :
        forall (dvs : list (local_id * @dvalue PaV)) (d_cur : list raw_id) (ea1 ea2 : @local_env PaV),
          incl d_cur l_origs ->
          incl (List.map fst dvs) l_origs ->
          callee_defs_bound ren_l d_cur ea1 ea2 ->
          env_agree_outside all_fresh ce1 ea2 ->
          cfg_inline_sim opt_call1 g0 false
            (fun ic' _ _ =>
               exists ea1' ea2',
                 ic' = IC_Inlined stk ce1 ea1' ea2' /\
                 callee_defs_bound ren_l (d_cur ++ List.map fst dvs) ea1' ea2' /\
                 env_agree_outside all_fresh ce1 ea2')
            (IC_Inlined stk ce1 ea1 ea2)
            (map_monad (fun '(id, dv) => lwrite id dv) dvs)
            (map_monad (fun '(id, dv) => lwrite id dv)
               (List.map (fun '(x, dv) => (ren_l x, dv)) dvs))).
      { induction dvs as [| [x dv] rest IHw];
          intros d_cur ea1 ea2 Hd_cur Hdvs_dom Hb_cur Hag_cur;
          cbn [List.map map_monad fst].
        - rewrite app_nil_r; apply gen_inline_sim_ret; exists ea1, ea2; auto.
        - assert (Hx_dom : In x l_origs) by (apply Hdvs_dom; left; reflexivity).
          assert (Hrest_dom : incl (List.map fst rest) l_origs).
          { intros z Hz; apply Hdvs_dom; right; exact Hz. }
          eapply gen_inline_sim_bind.
          + apply (cfg_inline_sim_lwrite_lr opt_call1 g0 false
                     (IC_Inlined stk ce1 ea1 ea2)
                     (IC_Inlined stk ce1 (Maps.add x dv ea1) ea2)
                     (IC_Inlined stk ce1 (Maps.add x dv ea1) (Maps.add (ren_l x) dv ea2))
                     x (ren_l x) dv Logic.eq_refl Logic.eq_refl).
          + intros ? [] [] (-> & _ & _).
            eapply gen_inline_sim_bind.
            * apply (IHw (d_cur ++ [x]) (Maps.add x dv ea1) (Maps.add (ren_l x) dv ea2)).
              -- apply incl_app; [exact Hd_cur | intros z [<- | []]; exact Hx_dom].
              -- exact Hrest_dom.
              -- apply (callee_defs_bound_add ren_l l_origs d_cur x dv ea1 ea2 Hinj_l Hd_cur Hx_dom Hb_cur).
              -- apply env_agree_outside_add_fresh_r; [apply Hfresh_l, Hx_dom | exact Hag_cur].
            * intros ? r1 r2 (ea1' & ea2' & -> & Hb' & Hag').
              rewrite <- app_assoc in Hb'.
              apply gen_inline_sim_ret; exists ea1', ea2'; auto. }
      eapply gen_inline_sim_bind; [apply (Heval phis Hp_lbls_dom Hall_p) |].
      intros ? dvs1 dvs2 (-> & Hfst & ->).
      assert (Hfst' : List.map (@fst local_id (@dvalue PaV)) dvs1 = List.map (fun '(x, _, _) => x) phis)
        by exact Hfst.
      eapply gen_inline_sim_bind.
      + apply (Hwrites dvs1 d_in e1 e2 Hd_dom); [rewrite Hfst'; exact Hp_defs_dom | exact Hbound | exact Hagree].
      + intros ? _ _ (e1' & e2' & -> & Hb' & Hag').
        rewrite Hfst' in Hb'.
        apply gen_inline_sim_ret; split; [reflexivity | split; [reflexivity | exists e1', e2'; auto]].
  Qed.

  Lemma denote_exp'_mk_copy_exp (ty_i1 dt : dtyp) (ex : exp dtyp) :
    @denote_exp' PaV None (mk_copy_exp ty_i1 dt ex) ≅
    @denote_exp' PaV (Some dt) ex.
  Proof.
    unfold denote_exp'; apply inl_withCall_proper, denote_mk_copy_exp.
  Qed.

  Lemma check_code_defs_dom {T : Set} (dom : list raw_id) :
    forall (cd : list (instr_id * instr T * list (metadata T))) (cur d_out : list raw_id),
      check_code_defs cur cd = Some d_out ->
      incl cur dom ->
      incl (flat_map (fun '(iid, _, _) => instr_id_defs iid) cd) dom ->
      incl d_out dom.
  Proof.
    induction cd as [| [[iid ins] md] rest IH]; intros cur d_out Hchk Hcur Hcd.
    - cbn [check_code_defs] in Hchk; injection Hchk as <-; exact Hcur.
    - apply check_code_defs_inv in Hchk as [_ Hrest].
      cbn [flat_map] in Hcd.
      apply (IH (cur ++ instr_id_defs iid) d_out Hrest).
      + apply incl_app; [exact Hcur | intros x Hx; apply Hcd, in_or_app; left; exact Hx].
      + intros x Hx; apply Hcd, in_or_app; right; exact Hx.
  Qed.

  Lemma denote_block_callee_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (opt_ret_dt : option dtyp)
    (l_origs b_origs all_fresh d_in : list raw_id)
    (in_map : list (block_id * list raw_id))
    (callee_bks : ocfg dtyp)
    (ren_l ren_b : raw_id -> raw_id)
    (post_bid : block_id)
    (va1 va2 : option (@ptr (@PROV PaV) (@PTR PaV)))
    stk (ce1 e1 e2 : @local_env PaV)
    (b_from1 b_from2 : block_id)
    (bk : block dtyp) (rtmp : raw_id)
    (Hinj_l : forall x1 x2, In x1 l_origs -> In x2 l_origs -> ren_l x1 = ren_l x2 -> x1 = x2)
    (Hfresh_l : forall x, In x l_origs -> In (ren_l x) all_fresh)
    (Hinj_b : forall b1 b2, In b1 b_origs -> In b2 b_origs -> ren_b b1 = ren_b b2 -> b1 = b2)
    (Hrtmp_fresh : In rtmp all_fresh)
    (Hleaf : is_leaf_block opt_ret_dt bk = true)
    (Hvblk : verify_block_defs callee_bks in_map bk = true)
    (Hdin_dom : incl d_in l_origs)
    (Hd0_in : incl (lookup_def_set in_map (blk_id bk)) d_in)
    (Hdefs_dom : incl (full_block_defs bk) l_origs)
    (Hlbls_dom : incl (block_all_label_ids bk) b_origs)
    (Hbound : callee_defs_bound ren_l d_in e1 e2)
    (Hagree : env_agree_outside all_fresh ce1 e2)
    (Hentry_or_pred :
       blk_phis bk = [] \/
       (b_from2 = ren_b b_from1 /\
        In b_from1 b_origs /\
        Forall
          (fun '(_, Phi _ _ pargs, md) =>
             exists op,
               assoc b_from1 pargs = Some op /\
               incl (full_exp_uses op ++ flat_map full_metadata_uses md) d_in)
          (blk_phis bk))) :
    cfg_inline_sim opt_call1 g0 false
      (fun ic' bd1 bd2 =>
         (exists succ_bid d_out e1' e2',
            bd1 = inl succ_bid /\
            bd2 = inl (ren_b succ_bid) /\
            In succ_bid (term_succ_bids (snd (fst (blk_term bk)))) /\
            check_succ_edge callee_bks in_map (blk_id bk) d_out succ_bid = true /\
            incl d_out l_origs /\
            ic' = IC_Inlined stk ce1 e1' e2' /\
            callee_defs_bound ren_l d_out e1' e2' /\
            env_agree_outside all_fresh ce1 e2') \/
         (exists dv e1' e2',
            bd1 = inr dv /\
            bd2 = inl post_bid /\
            ic' = IC_Inlined stk ce1 e1' e2' /\
            env_agree_outside all_fresh ce1 e2' /\
            match opt_ret_dt with
            | None => True
            | Some _ =>
                (exists rpair, snd (fst (blk_term bk)) = TERM_Ret rpair) /\
                Maps.lookup rtmp e2' = Some dv
            end))
      (IC_Inlined stk ce1 e1 e2)
      (denote_block bk b_from1 va1)
      (denote_block (transform_callee_block ren_l ren_b post_bid (bk, rtmp)) b_from2 va2).
  Proof.
    unfold is_leaf_block in Hleaf.
    apply andb_prop in Hleaf as [Hleaf1 Hterm_leaf].
    apply andb_prop in Hleaf1 as [_ Hcode_leaf].
    apply verify_block_defs_inv in Hvblk as (d_out & Hchk_cd & Htm_uses & Hsuccs).
    assert (Hd0_dom : incl (lookup_def_set in_map (blk_id bk)) l_origs).
    { intros z Hz; apply Hdin_dom, Hd0_in, Hz. }
    assert (Hp_defs_dom : incl (List.map (fun '(x, _, _) => x) (blk_phis bk)) l_origs).
    { intros z Hz; apply Hdefs_dom; unfold full_block_defs; apply in_or_app; left; exact Hz. }
    assert (Hcd_defs_dom : incl (flat_map (fun '(iid, _, _) => instr_id_defs iid) (blk_code bk)) l_origs).
    { intros z Hz; apply Hdefs_dom; unfold full_block_defs;
        apply in_or_app; right; apply in_or_app; left; exact Hz. }
    assert (Hp_lbls_dom : incl (flat_map (fun '(_, Phi _ _ pargs, _) => List.map fst pargs) (blk_phis bk)) b_origs).
    { intros b Hb; apply Hlbls_dom; unfold block_all_label_ids;
        right; apply in_or_app; left; exact Hb. }
    unfold denote_block, transform_callee_block.
    destruct (blk_term bk) as [[tiid tm] tmd] eqn:Ebt.
    cbn [fst snd] in *.
    assert (Hphis_eq :
      blk_phis
        (let '(new_code, new_term) :=
           match tm with
           | TERM_Ret (dt, op) =>
               (List.map (ren_code_entry ren_l) (blk_code bk) ++
                [(IId rtmp, INSTR_Op (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt (ren_exp ren_l op)), [])],
                (IVoid 0%Z, TERM_Br_1 post_bid, []))
           | TERM_Ret_void =>
               (List.map (ren_code_entry ren_l) (blk_code bk),
                (IVoid 0%Z, TERM_Br_1 post_bid, []))
           | TERM_Br (dt, op) b1 b2 =>
               (List.map (ren_code_entry ren_l) (blk_code bk),
                (tiid, TERM_Br (dt, ren_exp ren_l op) (ren_b b1) (ren_b b2), tmd))
           | TERM_Br_1 b =>
               (List.map (ren_code_entry ren_l) (blk_code bk),
                (tiid, TERM_Br_1 (ren_b b), tmd))
           | TERM_Switch (dt, op) def_b brs =>
               (List.map (ren_code_entry ren_l) (blk_code bk),
                (tiid,
                 TERM_Switch (dt, ren_exp ren_l op) (ren_b def_b)
                   (List.map (fun '(lit, b) => (lit, ren_b b)) brs), tmd))
           | _ =>
               (List.map (ren_code_entry ren_l) (blk_code bk), (tiid, tm, tmd))
           end
         in
         {| blk_id       := ren_b (blk_id bk);
            blk_phis     := List.map (ren_phi_entry ren_l ren_b) (blk_phis bk);
            blk_code     := new_code;
            blk_term     := new_term;
            blk_comments := blk_comments bk |}) =
      List.map (ren_phi_entry ren_l ren_b) (blk_phis bk)).
    { destruct tm as [[? ?] | | [? ?] ? ? | ? | [? ?] ? ? | ? ? ? | ? | ? ? ? ? ? ? | ]; reflexivity. }
    rewrite Hphis_eq; clear Hphis_eq.
    eapply gen_inline_sim_bind.
    - apply (denote_phis_callee_sim opt_call1 g0 l_origs b_origs all_fresh d_in
               ren_l ren_b stk ce1 e1 e2 b_from1 b_from2 (blk_phis bk));
        assumption.
    - intros ? [] [] (_ & _ & e1_p & e2_p & -> & Hbound_p & Hagree_p).
      assert (Hbound_p0 :
        callee_defs_bound ren_l
          (lookup_def_set in_map (blk_id bk) ++ List.map (fun '(x, _, _) => x) (blk_phis bk))
          e1_p e2_p).
      { eapply callee_defs_bound_incl; [| exact Hbound_p].
        intros z Hz; apply in_app_or in Hz as [Hz | Hz]; apply in_or_app;
          [left; apply Hd0_in, Hz | right; exact Hz]. }
      assert (Hd_phi_dom :
        incl (lookup_def_set in_map (blk_id bk) ++ List.map (fun '(x, _, _) => x) (blk_phis bk)) l_origs).
      { apply incl_app; assumption. }
      assert (Hd_out_dom : incl d_out l_origs).
      { exact (check_code_defs_dom l_origs (blk_code bk) _ d_out Hchk_cd Hd_phi_dom Hcd_defs_dom). }
      unfold is_leaf_term_entry in Hterm_leaf.
      apply andb_prop in Hterm_leaf as [_ Htm_ok].
      destruct tm as [[dt op] | | [dt op] b1 b2 | b | [dt op] def_b brs | ? ? ? | ? | ? ? ? ? ? ? | ];
        try discriminate Htm_ok;
        cbn [blk_code blk_term].
      + (* TERM_Ret (dt, op) *)
        eapply gen_inline_sim_obs_eq.
        * reflexivity.
        * symmetry; cbn [ExtLib.Structures.Monad.bind Monad_itree]; rewrite denote_code_app_eq, Eqit.bind_bind; reflexivity.
        * eapply gen_inline_sim_bind.
          -- apply (denote_code_callee_sim opt_call1 g0 l_origs all_fresh ren_l va1 va2
                      Hinj_l Hfresh_l (blk_code bk) _ d_out stk ce1 e1_p e2_p
                      Hcode_leaf Hchk_cd Hd_phi_dom Hcd_defs_dom Hbound_p0 Hagree_p).
          -- intros ? [] [] (_ & _ & e1_c & e2_c & -> & Hbound_c & Hagree_c).
             cbn [denote_code loop_monad denote_instr denote_terminator ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
             eapply gen_inline_sim_obs_eq with
               (t1 := ITree.bind (denote_exp' (Some dt) op) (fun dv => Ret (inr dv)))
               (t2 := ITree.bind (denote_exp' (Some dt) (ren_exp ren_l op))
                        (fun uv => ITree.bind (lwrite rtmp uv) (fun _ => Ret (inl post_bid)))).
             ++ reflexivity.
             ++ symmetry.
                rewrite !Eqit.bind_bind.
                eapply eq_itree_clo_bind with (UU := Logic.eq);
                  [apply denote_exp'_mk_copy_exp | intros uv _ <-].
                rewrite !Eqit.bind_bind.
                eapply eq_itree_clo_bind with (UU := Logic.eq);
                  [reflexivity | intros [] _ _].
                rewrite !Eqit.bind_ret_l; reflexivity.
             ++ eapply gen_inline_sim_bind.
                ** apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_out stk ce1 e1_c e2_c (Some dt) op);
                     [intros z Hz; apply Htm_uses, in_or_app; left; exact Hz | exact Hbound_c].
                ** intros ? dv _ [-> <-].
                   eapply gen_inline_sim_obs_eq with
                     (t1 := ITree.bind (Ret tt) (fun _ : unit => Ret (inr dv)))
                     (t2 := ITree.bind (lwrite rtmp dv) (fun _ : unit => Ret (inl post_bid)));
                     [apply (Eqit.bind_ret_l tt) | reflexivity |].
                   eapply gen_inline_sim_bind.
                   --- apply (cfg_inline_sim_lwrite_r opt_call1 g0 false
                                (IC_Inlined stk ce1 e1_c e2_c)
                                (IC_Inlined stk ce1 e1_c (Maps.add rtmp dv e2_c))
                                rtmp dv Logic.eq_refl).
                   --- intros ? [] [] (-> & _ & _).
                       apply gen_inline_sim_ret; right.
                       exists dv, e1_c, (Maps.add rtmp dv e2_c).
                       split; [reflexivity | split; [reflexivity | split; [reflexivity | split]]].
                       +++ apply env_agree_outside_add_fresh_r; [exact Hrtmp_fresh | exact Hagree_c].
                       +++ destruct opt_ret_dt as [rdt |]; [| exact I].
                           split; [exists (dt, op); reflexivity | cbn [Maps.lookup Maps.add Map_rmap]; apply RMF.F.add_eq_o; reflexivity].
      + (* TERM_Ret_void *)
        destruct opt_ret_dt as [rdt |]; [discriminate Htm_ok |].
        eapply gen_inline_sim_bind.
        * apply (denote_code_callee_sim opt_call1 g0 l_origs all_fresh ren_l va1 va2
                   Hinj_l Hfresh_l (blk_code bk) _ d_out stk ce1 e1_p e2_p
                   Hcode_leaf Hchk_cd Hd_phi_dom Hcd_defs_dom Hbound_p0 Hagree_p).
        * intros ? [] [] (_ & _ & e1_c & e2_c & -> & _ & Hagree_c).
          cbn [denote_terminator].
          apply gen_inline_sim_ret; right.
          exists (DVALUE_Base DVALUE_None), e1_c, e2_c; auto 7.
      + (* TERM_Br (dt, op) b1 b2 *)
        eapply gen_inline_sim_bind.
        * apply (denote_code_callee_sim opt_call1 g0 l_origs all_fresh ren_l va1 va2
                   Hinj_l Hfresh_l (blk_code bk) _ d_out stk ce1 e1_p e2_p
                   Hcode_leaf Hchk_cd Hd_phi_dom Hcd_defs_dom Hbound_p0 Hagree_p).
        * intros ? [] [] (_ & _ & e1_c & e2_c & -> & Hbound_c & Hagree_c).
          cbn [denote_terminator].
          eapply gen_inline_sim_bind.
          -- apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_out stk ce1 e1_c e2_c (Some dt) op);
               [intros z Hz; apply Htm_uses, in_or_app; left; exact Hz | exact Hbound_c].
          -- intros ? v _ [-> <-].
             destruct v as [db | |]; cbv beta iota zeta;
               try_cfg_raise.
             destruct db; cbv beta iota zeta;
               try_cfg_raise.
             ++ destruct sz as [? | ? |]; cbv beta iota zeta;
                  try_cfg_raise.
                lazymatch goal with | |- context [VellvmIntegers.equ ?a ?b] => destruct (VellvmIntegers.equ a b) end.
                ** apply gen_inline_sim_ret; left.
                   assert (Hb1 : In b1 (term_succ_bids (TERM_Br (dt, op) b1 b2))) by (left; reflexivity).
                   exists b1, d_out, e1_c, e2_c; auto 10.
                ** apply gen_inline_sim_ret; left.
                   assert (Hb2 : In b2 (term_succ_bids (TERM_Br (dt, op) b1 b2))) by (right; left; reflexivity).
                   exists b2, d_out, e1_c, e2_c; auto 10.
             ++ apply cfg_inline_sim_raiseUB.
      + (* TERM_Br_1 b *)
        eapply gen_inline_sim_bind.
        * apply (denote_code_callee_sim opt_call1 g0 l_origs all_fresh ren_l va1 va2
                   Hinj_l Hfresh_l (blk_code bk) _ d_out stk ce1 e1_p e2_p
                   Hcode_leaf Hchk_cd Hd_phi_dom Hcd_defs_dom Hbound_p0 Hagree_p).
        * intros ? [] [] (_ & _ & e1_c & e2_c & -> & Hbound_c & Hagree_c).
          cbn [denote_terminator].
          apply gen_inline_sim_ret; left.
          assert (Hb : In b (term_succ_bids (@TERM_Br_1 dtyp b))) by (left; reflexivity).
          exists b, d_out, e1_c, e2_c; auto 10.
      + (* TERM_Switch (dt, op) def_b brs *)
        eapply gen_inline_sim_bind.
        * apply (denote_code_callee_sim opt_call1 g0 l_origs all_fresh ren_l va1 va2
                   Hinj_l Hfresh_l (blk_code bk) _ d_out stk ce1 e1_p e2_p
                   Hcode_leaf Hchk_cd Hd_phi_dom Hcd_defs_dom Hbound_p0 Hagree_p).
        * intros ? [] [] (_ & _ & e1_c & e2_c & -> & Hbound_c & Hagree_c).
          cbn [denote_terminator].
          eapply gen_inline_sim_bind.
          -- apply (denote_exp'_callee_sim opt_call1 g0 ren_l d_out stk ce1 e1_c e2_c (Some dt) op);
               [intros z Hz; apply Htm_uses, in_or_app; left; exact Hz | exact Hbound_c].
          -- intros ? sel _ [-> <-].
             destruct (dvalue_is_poison sel).
             ++ apply cfg_inline_sim_raiseUB.
             ++ destruct (switch_elab_ren_b ren_b sel def_b brs)
                  as [(eou_err & Hnr & E1 & E2) | (b & Hb & E1 & E2)].
                ** rewrite E1;
                   first [rewrite E2
                         | lazymatch goal with
                           | |- _ _ ?rhs =>
                               lazymatch rhs with
                               | context [EOU_to_itree ?t2] =>
                                   assert (HE2' : t2 = eou_err) by exact E2;
                                   rewrite HE2'; clear HE2'
                               end
                           end].
                   destruct eou_err as [m | m | m | b0];
                     [| | | exfalso; exact (Hnr b0 Logic.eq_refl)];
                     cbn [EOU_to_itree].
                   --- eapply gen_inline_sim_bind with (RA := fun _ _ _ => False);
                         [apply cfg_inline_sim_raise; reflexivity | intros ? ? ? []].
                   --- eapply gen_inline_sim_bind with (RA := fun _ _ _ => False);
                         [apply cfg_inline_sim_raiseOOM | intros ? ? ? []].
                   --- eapply gen_inline_sim_bind with (RA := fun _ _ _ => False);
                         [apply cfg_inline_sim_raiseUB | intros ? ? ? []].
                ** rewrite E1;
                   first [rewrite E2
                         | lazymatch goal with
                           | |- _ _ ?rhs =>
                               lazymatch rhs with
                               | context [EOU_to_itree ?t2] =>
                                   assert (HE2' : t2 = raise_ret (ren_b b)) by exact E2;
                                   rewrite HE2'; clear HE2'
                               end
                           end];
                   cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
                   eapply gen_inline_sim_obs_eq;
                     [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
                   apply gen_inline_sim_ret; left.
                   exists b, d_out, e1_c, e2_c; auto 10.
      + (* TERM_Unreachable *)
        eapply gen_inline_sim_bind.
        * apply (denote_code_callee_sim opt_call1 g0 l_origs all_fresh ren_l va1 va2
                   Hinj_l Hfresh_l (blk_code bk) _ d_out stk ce1 e1_p e2_p
                   Hcode_leaf Hchk_cd Hd_phi_dom Hcd_defs_dom Hbound_p0 Hagree_p).
        * intros ? [] [] (_ & _ & e1_c & e2_c & -> & _ & _).
          cbn [denote_terminator]; apply cfg_inline_sim_raiseUB.
  Qed.

  Lemma denote_call_args_param_copies_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env)
    (l_origs all_fresh : list raw_id)
    (ren_l : raw_id -> raw_id)
    (msg : string)
    (caller_va : option (@ptr (@PROV PaV) (@PTR PaV)))
    stk (e1 : @local_env PaV)
    (Hinj_l : forall x1 x2, In x1 l_origs -> In x2 l_origs -> ren_l x1 = ren_l x2 -> x1 = x2)
    (Hfresh_l : forall x, In x l_origs -> In (ren_l x) all_fresh) :
    forall (params : list local_id)
           (call_args : list (texp dtyp * list param_attr))
           (e2 : @local_env PaV),
      List.length call_args = List.length params ->
      NoDup params ->
      incl params l_origs ->
      (forall te pattrs, In (te, pattrs) call_args -> pattrs = []) ->
      (forall te pattrs x,
         In (te, pattrs) call_args ->
         In x (full_texp_uses te) ->
         ~ In x all_fresh) ->
      env_agree_outside all_fresh e1 e2 ->
      cfg_inline_sim opt_call1 g0 false
        (fun ic' vs r2 =>
           r2 = tt /\
           List.length vs = List.length params /\
           exists e2',
             ic' = IC_Synced stk e1 e2' /\
             env_agree_outside all_fresh e1 e2' /\
             (forall z, ~ In z (List.map ren_l params) -> Maps.lookup z e2' = Maps.lookup z e2) /\
             (forall p v, In (p, v) (combine params vs) -> Maps.lookup (ren_l p) e2' = Some v))
        (IC_Synced stk e1 e2)
        (denote_call_args call_args msg)
        (denote_code (build_param_copies ren_l params call_args) caller_va).
  Proof.
    induction params as [| p ps IH];
      intros [| [[arg_dt arg_e] pattrs] rest] e2 Hlen Hnd Hdom Hpattrs Huses Hagree;
      try discriminate Hlen.
    - cbn [denote_call_args build_param_copies denote_code map_monad loop_monad].
      apply gen_inline_sim_ret.
      split; [reflexivity | split; [reflexivity |]].
      exists e2; split; [reflexivity | split; [exact Hagree | split; [reflexivity | intros _ _ []]]].
    - cbn [List.length] in Hlen; injection Hlen as Hlen.
      inversion Hnd as [| ? ? Hnin_p Hnd_ps]; subst.
      assert (Hp_dom : In p l_origs) by (apply Hdom; left; reflexivity).
      assert (Hps_dom : incl ps l_origs) by (intros q Hq; apply Hdom; right; exact Hq).
      assert (Hp_pattrs : pattrs = []) by (eapply Hpattrs; left; reflexivity).
      subst pattrs.
      cbn [denote_call_args build_param_copies denote_code map_monad loop_monad denote_instr
           ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      eapply gen_inline_sim_obs_eq.
      + symmetry.
        rewrite Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros v _ <-].
        rewrite apply_attrs_nil_eq, Eqit.bind_ret_l; reflexivity.
      + symmetry.
        rewrite !Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq);
          [apply denote_exp'_mk_copy_exp | intros uv _ <-].
        rewrite !Eqit.bind_bind; reflexivity.
      + eapply gen_inline_sim_bind.
        * apply (denote_exp'_caller_sim opt_call1 g0 all_fresh stk e1 e2 (Some arg_dt) arg_e);
            [intros x Hx; eapply Huses; [left; reflexivity | exact Hx]
            | exact Hagree].
        * intros ? v _ [-> <-].
          eapply gen_inline_sim_obs_eq with
            (t1 := ITree.bind (Ret tt)
                     (fun _ : unit =>
                        ITree.bind (denote_call_args rest msg) (fun bs => Ret (v :: bs))))
            (t2 := ITree.bind (lwrite (ren_l p) v)
                     (fun _ : unit => denote_code (build_param_copies ren_l ps rest) caller_va));
            [rewrite !Eqit.bind_ret_l; reflexivity
            | symmetry; rewrite Eqit.bind_bind;
              eapply eq_itree_clo_bind with (UU := Logic.eq);
              [reflexivity | intros [] _ _; rewrite Eqit.bind_ret_l; reflexivity] |].
          eapply gen_inline_sim_bind.
          -- apply (cfg_inline_sim_lwrite_r opt_call1 g0 false
                      (IC_Synced stk e1 e2)
                      (IC_Synced stk e1 (Maps.add (ren_l p) v e2))
                      (ren_l p) v Logic.eq_refl).
          -- intros ? [] [] (-> & _ & _).
             assert (Hagree1 : env_agree_outside all_fresh e1 (Maps.add (ren_l p) v e2)).
             { apply env_agree_outside_add_fresh_r; [apply Hfresh_l, Hp_dom | exact Hagree]. }
             eapply gen_inline_sim_obs_eq with
               (t1 := ITree.bind (denote_call_args rest msg) (fun bs => Ret (v :: bs)))
               (t2 := ITree.bind (denote_code (build_param_copies ren_l ps rest) caller_va) (fun u => Ret u));
               [reflexivity
               | rewrite Eqit.bind_ret_r; reflexivity |].
             eapply gen_inline_sim_bind.
             ++ apply (IH rest (Maps.add (ren_l p) v e2) Hlen Hnd_ps Hps_dom).
                ** intros te0 pa0 Hin; eapply Hpattrs; right; exact Hin.
                ** intros te0 pa0 x Hin Hx; eapply Huses; [right; exact Hin | exact Hx].
                ** exact Hagree1.
             ++ intros ? vs [] (_ & Hlen_vs & e2' & -> & Hagree' & Hpres & Hlk_ps).
                apply gen_inline_sim_ret.
                cbn [List.length List.map combine].
                split; [reflexivity | split; [f_equal; exact Hlen_vs |]].
                exists e2'; split; [reflexivity | split; [exact Hagree' | split]].
                ** intros z Hz.
                   assert (Hne_p : ren_l p <> z) by (intros Heq; apply Hz; left; exact Heq).
                   assert (Hnin_ps : ~ In z (List.map ren_l ps)) by (intros Hin; apply Hz; right; exact Hin).
                   unfold local_id in *; rewrite (Hpres z Hnin_ps); cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by exact Hne_p; reflexivity.
                ** intros q w [Heq | Hin].
                   --- injection Heq as <- <-.
                       assert (Hnin_ren_ps : ~ In (ren_l p) (List.map ren_l ps)).
                       { intros Hin; apply in_map_iff in Hin as [q [Heq Hq]].
                         apply Hnin_p; replace p with q; [exact Hq |].
                         apply Hinj_l; [apply Hps_dom, Hq | exact Hp_dom | exact Heq]. }
                       unfold local_id in *; rewrite (Hpres (ren_l p) Hnin_ren_ps); cbn [Maps.lookup Maps.add Map_rmap]; apply RMF.F.add_eq_o; reflexivity.
                   --- apply Hlk_ps, Hin.
  Qed.

End InliningSemantics.
