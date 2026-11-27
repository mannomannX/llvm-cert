(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Stack-Slot to SSA Register Promotion ([CertPasses.Mem2Reg])

    Promotes non-escaping scalar [alloca] stack slots in function entry blocks
    to SSA registers and block-entry [Phi] nodes (Stage 1), followed by
    reverse-order dead scalar [alloca] elimination in leaf functions (Stage 2)
    so inlinable callees become [alloca]-free before [CertPasses.Inline].
    Composed across bounded rounds via [prog_refines_trans]. *)

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

From CertPasses Require Import Mem2RegSpec Mem2RegModel Mem2RegMemBase Mem2RegGhostInv Mem2RegExprLift.

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

  (** ** 3I. Attribute, Block-Lookup & Equal-Memory Synchronization Helpers *)

  Lemma apply_value_attrs_nil_eq (msg : string) (v : @dvalue (@ParamsV IP IPT)) :
    @apply_value_attrs (@ParamsV IP IPT) [] msg v = raise_ret v.
  Proof using.
    unfold apply_value_attrs, value_attrs_poison, value_attr_nofpclass,
           value_attr_range, value_attr_align, value_attr_nonnull.
    cbn [find_option existsb andb].
    destruct v as [db | |]; [destruct db | |]; reflexivity.
  Qed.

  Lemma assert_alignment_ret_or_ub
    (a : @dvalue (@ParamsV IP IPT)) (anns : list (annotation dtyp)) (msg : string) :
    @assert_alignment (@ParamsV IP IPT) a anns msg = raise_ret tt \/
    @assert_alignment (@ParamsV IP IPT) a anns msg = raise_ub msg.
  Proof using.
    unfold assert_alignment, assert_aligned_to.
    destruct a as [db | |]; [destruct db | |];
      destruct (find_option ann_align anns) as [al |];
      cbn; try (left; reflexivity).
    match goal with
    | |- context [if ?c then _ else _] =>
        destruct c; [left; reflexivity | right; reflexivity]
    end.
  Qed.

  Lemma m2r_find_block_some_inv {T : Set} (bks : ocfg T) (bid : block_id) (bk : block T) :
    find_block bks bid = Some bk ->
    In bk bks /\ blk_id bk = bid.
  Proof using.
    induction bks as [| b0 bs IH]; intros Hfind; [cbn in Hfind; discriminate Hfind |].
    destruct (raw_id_eqb (blk_id b0) bid) eqn:Ebid; [apply raw_id_eqb_spec in Ebid; rename Ebid into Heq | apply raw_id_eqb_neq in Ebid; rename Ebid into Hne].
    - rewrite find_block_eq in Hfind by exact Heq.
      inversion Hfind; subst b0; split; [left; reflexivity | exact Heq].
    - rewrite find_block_ineq in Hfind by exact Hne.
      destruct (IH Hfind) as [Hin Hid]; split; [right; exact Hin | exact Hid].
  Qed.

  Lemma m2r_find_block_in_nodup {T : Set} (bks : ocfg T) (bk : block T) :
    NoDup (List.map blk_id bks) ->
    In bk bks ->
    find_block bks (blk_id bk) = Some bk.
  Proof using.
    induction bks as [| b0 bs IH]; intros Hnd Hin; [contradiction Hin |].
    cbn [List.map] in Hnd; inversion Hnd as [| ? ? Hnin Hnd']; subst.
    destruct Hin as [<- | Hin].
    - apply find_block_eq; reflexivity.
    - destruct (raw_id_eqb (blk_id b0) (blk_id bk)) eqn:Ebid; [apply raw_id_eqb_spec in Ebid; rename Ebid into Heq | apply raw_id_eqb_neq in Ebid; rename Ebid into Hne].
      + exfalso; apply Hnin; rewrite Heq; apply in_map, Hin.
      + rewrite find_block_ineq by exact Hne; apply IH; assumption.
  Qed.

  Lemma m2r_find_block_map_id_pres {T : Set}
    (f : block T -> block T) (bks : ocfg T) (bid : block_id)
    (Hid : forall bk, In bk bks -> blk_id (f bk) = blk_id bk) :
    find_block (List.map f bks) bid = option_map f (find_block bks bid).
  Proof using.
    induction bks as [| b0 bs IH]; cbn [List.map]; [reflexivity |].
    pose proof (Hid b0 (or_introl Logic.eq_refl)) as Hid0.
    destruct (raw_id_eqb (blk_id b0) bid) eqn:Ebid; [apply raw_id_eqb_spec in Ebid; rename Ebid into Heq | apply raw_id_eqb_neq in Ebid; rename Ebid into Hne].
    - rewrite find_block_eq by congruence.
      rewrite find_block_eq by exact Heq.
      reflexivity.
    - rewrite find_block_ineq by congruence.
      rewrite find_block_ineq by exact Hne.
      apply IH; intros bk Hbk; apply Hid; right; exact Hbk.
  Qed.

  Lemma refine_prov_refl_incl {A : Type} (U0 : list N) (t : itree ProvBotE A) :
    refine_prov (fun U' a1 a2 => incl U0 U' /\ a1 = a2) U0 t t.
  Proof using.
    assert (Hgen : forall U (tr : itree ProvBotE A),
              incl U0 U ->
              refine_prov (fun U' a1 a2 => incl U0 U' /\ a1 = a2) U tr tr).
    { pcofix CIH; intros U tr Hinc; pstep.
      apply RP_Step; unfold rp_step_body.
      destruct (observe tr) as [a | m | X e k].
      - exact (conj Hinc Logic.eq_refl).
      - right; apply CIH, Hinc.
      - destruct e as [pe | be].
        + destruct pe; right; right; intros pr Hpr; right; apply CIH.
          intros z Hz; right; apply Hinc, Hz.
        + destruct (is_ub_bot be) eqn:Eub.
          * left; exact Eub.
          * right; right; split; [apply EqE_bot_refl |].
            intros a1 a2 Ha; apply EqA_bot_eq in Ha; subst a2.
            right; apply CIH.
            intros z Hz; apply in_app_iff; right; apply Hinc, Hz. }
    apply Hgen, incl_refl.
  Qed.

  Lemma fused_non_mem_equal_sync {A R : Type}
    (t0 : itree ProvBotE A)
    (mk : state -> A -> Res R)
    (U : list N) (σ1 σ2 : state)
    (Hmk : forall a,
             mem_stack_equal (state_memory_stack (fst (fst (mk σ1 a))))
                             (state_memory_stack (fst (fst (mk σ2 a)))) /\
             snd (fst (mk σ1 a)) = snd (fst (mk σ2 a)) /\
             snd (mk σ1 a) = snd (mk σ2 a)) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         incl U U' /\
         mem_stack_equal (state_memory_stack (fst s1')) (state_memory_stack (fst s2')) /\
         snd s1' = snd s2' /\
         r1 = r2)
      U
      (ITree.bind t0 (fun a => Ret (mk σ1 a)))
      (ITree.bind t0 (fun a => Ret (mk σ2 a))).
  Proof using.
    eapply PassCommonModel.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' a1 a2 _ [Hinc <-].
    apply refine_prov_ret.
    destruct (mk σ1 a1) as [[σ1' rest1'] r1] eqn:E1,
             (mk σ2 a1) as [[σ2' rest2'] r2] eqn:E2.
    pose proof (Hmk a1) as Hspec; rewrite E1, E2 in Hspec; cbn in Hspec.
    exact (conj Hinc Hspec).
  Qed.

  Lemma alloca_mem_equal_safe (dt : dtyp) (num : N) (align : option N)
    (U P0 : list N) (σ1 σ2 : state)
    (Hpu : incl P0 U)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov
      (fun U' '(σ1', r1) '(σ2', r2) =>
         exists pr,
           ~ In pr U /\
           U' = pr :: U /\
           r1 = r2 /\
           is_safe_ptr_dvalue (pr :: P0) r2 /\
           mem_stack_equal (state_memory_stack σ1') (state_memory_stack σ2'))
      U
      (memM_interp_prov (handle_memoryM (Alloca dt num align)) σ1)
      (memM_interp_prov (handle_memoryM (Alloca dt num align)) σ2).
  Proof using.
    pose proof (stage1_equal_to_mem_inv U P0 σ1 σ2 Hpu Heq) as Hinv.
    eapply refine_prov_weaken;
      [exact (stage1_alloca_unprom dt num align U P0 [] σ1 σ2 Hinv) |].
    intros U' [σ1' r1] [σ2' r2]
      (pr & ptrs & Hpr & -> & Hr & Hsafe & Hinv' & _ & _).
    exists pr.
    split; [exact Hpr |].
    split; [reflexivity |].
    split; [exact Hr |].
    split; [exact Hsafe |].
    exact (stage1_mem_nil_is_equal (pr :: U) (pr :: P0) σ1' σ2' Hinv').
  Qed.

  Definition mcfg_eq_post {R : Type} (U0 : list N)
    (U' : list N) (x1 x2 : Res R) : Prop :=
    let '(s1', r1) := x1 in
    let '(s2', r2) := x2 in
    incl U0 U' /\
    mem_stack_equal (state_memory_stack (fst s1')) (state_memory_stack (fst s2')) /\
    snd s1' = snd s2' /\
    r1 = r2.

  Lemma on_ls_prov_equal_sync {T : Type}
    (f : Monads.stateT (@stack_frame (@ParamsV IP IPT) * stack)
           (itree (@MCFGEbot (@ParamsV IP IPT))) T)
    (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_post U) U
      (on_ls_prov f (σ1, (ls, g)))
      (on_ls_prov f (σ2, (ls, g))).
  Proof using.
    unfold on_ls_prov.
    eapply PassCommonModel.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' [ls1' r1] [ls2' r2] _ [Hinc Heq_p].
    inversion Heq_p; subst ls2' r2.
    apply refine_prov_ret; exact (conj Hinc (conj Heq (conj Logic.eq_refl Logic.eq_refl))).
  Qed.

  Lemma on_genv_prov_equal_sync {T : Type}
    (f : Monads.stateT global_env (itree (@MCFGEbot (@ParamsV IP IPT))) T)
    (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_post U) U
      (on_genv_prov f (σ1, (ls, g)))
      (on_genv_prov f (σ2, (ls, g))).
  Proof using.
    unfold on_genv_prov.
    eapply PassCommonModel.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' [g1' r1] [g2' r2] _ [Hinc Heq_p].
    inversion Heq_p; subst g2' r2.
    apply refine_prov_ret; exact (conj Hinc (conj Heq (conj Logic.eq_refl Logic.eq_refl))).
  Qed.

  Lemma fused_trigger_prov_equal_sync {F : Type -> Type} `{F -< ProvBotE} {T : Type}
    (e : F T) (U : list N) (σ1 σ2 : state)
    (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_post U) U
      (fused_trigger_prov T e (σ1, rest))
      (fused_trigger_prov T e (σ2, rest)).
  Proof using.
    unfold fused_trigger_prov.
    eapply PassCommonModel.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' r1 r2 _ [Hinc <-].
    apply refine_prov_ret; exact (conj Hinc (conj Heq (conj Logic.eq_refl Logic.eq_refl))).
  Qed.

  Lemma fused_draw_prov_equal_sync {T : Type}
    (e : @DrawE (@ParamsV IP IPT) T) (U : list N) (σ1 σ2 : state)
    (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_post U) U
      (fused_draw_prov T e (σ1, rest))
      (fused_draw_prov T e (σ2, rest)).
  Proof using.
    unfold fused_draw_prov.
    eapply PassCommonModel.refine_prov_bind; [apply refine_prov_refl_incl |].
    intros U' r1 r2 _ [Hinc <-].
    apply refine_prov_ret; exact (conj Hinc (conj Heq (conj Logic.eq_refl Logic.eq_refl))).
  Qed.

  Section InterpStateEqualSync.
    Context {E : Type -> Type}
            (h : E ~> Monads.stateT FusedS (itree ProvBotE))
            (Hh : forall X (e : E X) U σ1 σ2 rest,
                    mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
                    refine_prov (mcfg_eq_post U) U
                      (h X e (σ1, rest))
                      (h X e (σ2, rest))).

    Local Definition k_is_cont {X R : Type} (k : X -> itree E R)
      : Res X -> itree ProvBotE (Res R) :=
      fun '(s', x) => Tau (interp_state h (k x) s').

    Inductive is_eq_rel {R : Type} (U0 : list N)
      : list N -> itree ProvBotE (Res R) -> itree ProvBotE (Res R) -> Prop :=
    | ISE_Tree U (t : itree E R) (σ1 σ2 : state) rest
        (a1 a2 : itree ProvBotE (Res R)) :
        interp_state h t (σ1, rest) ≅ a1 ->
        interp_state h t (σ2, rest) ≅ a2 ->
        incl U0 U ->
        mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
        is_eq_rel U0 U a1 a2
    | ISE_Bind {X : Type} U (u1 u2 : itree ProvBotE (Res X)) (k : X -> itree E R)
        (a1 a2 : itree ProvBotE (Res R)) :
        ITree.bind u1 (k_is_cont k) ≅ a1 ->
        ITree.bind u2 (k_is_cont k) ≅ a2 ->
        refine_prov (mcfg_eq_post U0) U u1 u2 ->
        is_eq_rel U0 U a1 a2.

    Local Lemma is_eq_rel_obs_eq {R : Type} (U0 U : list N)
      (a1 a1' a2 a2' : itree ProvBotE (Res R)) :
      a1 ≅ a1' ->
      a2 ≅ a2' ->
      is_eq_rel U0 U a1 a2 ->
      is_eq_rel U0 U a1' a2'.
    Proof using.
      intros E1 E2 Hst.
      destruct Hst as [U' t σ1 σ2 rest a1_0 a2_0 Et1 Et2 Hinc Heq
                      | X U' u1 u2 k a1_0 a2_0 Eu1 Eu2 Hu].
      - eapply ISE_Tree with (t := t) (σ1 := σ1) (σ2 := σ2) (rest := rest).
        + transitivity a1_0; [exact Et1 | exact E1].
        + transitivity a2_0; [exact Et2 | exact E2].
        + exact Hinc.
        + exact Heq.
      - eapply ISE_Bind with (u1 := u1) (u2 := u2) (k := k).
        + transitivity a1_0; [exact Eu1 | exact E1].
        + transitivity a2_0; [exact Eu2 | exact E2].
        + exact Hu.
    Qed.

    Local Lemma step_is_eq_bind {X R : Type} (U0 U : list N)
      (u1 u2 : itree ProvBotE (Res X)) (k : X -> itree E R) :
      refine_prov (mcfg_eq_post U0) U u1 u2 ->
      refine_prov_ (mcfg_eq_post U0) (@is_eq_rel R U0) U
        (ITree.bind u1 (k_is_cont k))
        (ITree.bind u2 (k_is_cont k)).
    Proof using.
      intros Hu; punfold Hu.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [[[σ1' rest1'] x1] | m1 | Y1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [[[σ2' rest2'] x2] | m2 | Y2 e2 h2] eqn:Hou2;
            try contradiction.
          destruct Hstep as (Hinc & Heq & Hrest & <-).
          cbn [fst snd] in Heq, Hrest; subst rest2'.
          apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2; cbn.
          eapply ISE_Tree; [reflexivity | reflexivity | exact Hinc | exact Heq].
        + destruct (observe u2) as [? | m2 | ? ? ?] eqn:Hou2; try contradiction.
          pclearbot.
          apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2.
          eapply ISE_Bind; [reflexivity | reflexivity | exact Hstep].
        + apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind u1 (k_is_cont k)), Hou1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            eapply ISE_Bind; [reflexivity | reflexivity | exact Hleft].
          * right; right.
            destruct (observe u2) as [? | ? | Y2 e2 h2] eqn:Hou2; try contradiction.
            rewrite (observe_bind u2 (k_is_cont k)), Hou2.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               eapply ISE_Bind; [reflexivity | reflexivity | exact Hboth].
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               eapply ISE_Bind; [reflexivity | reflexivity | exact HA].
      - eapply RP_TauL;
          [rewrite (observe_bind u1 (k_is_cont k)), Hu1; reflexivity | exact IH].
      - eapply RP_TauR;
          [rewrite (observe_bind u2 (k_is_cont k)), Hu2; reflexivity | exact IH].
    Qed.

    Lemma interp_state_equal_sync_gen {R : Type}
      (t : itree E R) (U0 : list N) (σ1 σ2 : state)
      (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
      (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
      refine_prov (mcfg_eq_post U0) U0
        (interp_state h t (σ1, rest))
        (interp_state h t (σ2, rest)).
    Proof using Hh.
      assert (Hvis : forall X (e : E X) (k : X -> itree E R) (s : FusedS),
                ITree.bind (h X e s) (k_is_cont k) ≅ interp_state h (Vis e k) s).
      { intros X e k s; symmetry; rewrite interp_state_vis.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros [s' x] _ <-; reflexivity. }
      assert (Hcore : forall U a1 a2,
                @is_eq_rel R U0 U a1 a2 ->
                refine_prov (mcfg_eq_post U0) U a1 a2).
      { pcofix CIH; intros U a1 a2 Hst; pstep.
        eapply refine_prov__mon with (r := @is_eq_rel R U0);
          [| intros U' x1 x2 Hx; right; apply CIH, Hx].
        destruct Hst as [U t0 s_a s_b rest0 a1_0 a2_0 E1 E2 Hinc Heq0
                        | X U u1 u2 k a1_0 a2_0 E1 E2 Hu].
        - eapply refine_prov__obs_eq;
            [exact (is_eq_rel_obs_eq U0) | exact E1 | exact E2 |].
          destruct (observe t0) as [rv | mt | X e k] eqn:Hot.
          + assert (Et1 : Ret ((s_a, rest0), rv) ≅ interp_state h t0 (s_a, rest0)).
            { symmetry; rewrite (itree_eta t0), Hot; apply interp_state_ret. }
            assert (Et2 : Ret ((s_b, rest0), rv) ≅ interp_state h t0 (s_b, rest0)).
            { symmetry; rewrite (itree_eta t0), Hot; apply interp_state_ret. }
            eapply refine_prov__obs_eq;
              [exact (is_eq_rel_obs_eq U0) | exact Et1 | exact Et2 |].
            apply RP_Step; cbn;
              exact (conj Hinc (conj Heq0 (conj Logic.eq_refl Logic.eq_refl))).
          + assert (Et1 : Tau (interp_state h mt (s_a, rest0)) ≅ interp_state h t0 (s_a, rest0)).
            { symmetry; rewrite (itree_eta t0), Hot; apply interp_state_tau. }
            assert (Et2 : Tau (interp_state h mt (s_b, rest0)) ≅ interp_state h t0 (s_b, rest0)).
            { symmetry; rewrite (itree_eta t0), Hot; apply interp_state_tau. }
            eapply refine_prov__obs_eq;
              [exact (is_eq_rel_obs_eq U0) | exact Et1 | exact Et2 |].
            apply RP_Step; cbn.
            eapply ISE_Tree; [reflexivity | reflexivity | exact Hinc | exact Heq0].
          + assert (Et1 : ITree.bind (h X e (s_a, rest0)) (k_is_cont k) ≅
                          interp_state h t0 (s_a, rest0)).
            { etransitivity; [apply Hvis | symmetry; rewrite (itree_eta t0), Hot; reflexivity]. }
            assert (Et2 : ITree.bind (h X e (s_b, rest0)) (k_is_cont k) ≅
                          interp_state h t0 (s_b, rest0)).
            { etransitivity; [apply Hvis | symmetry; rewrite (itree_eta t0), Hot; reflexivity]. }
            eapply refine_prov__obs_eq;
              [exact (is_eq_rel_obs_eq U0) | exact Et1 | exact Et2 |].
            apply step_is_eq_bind.
            eapply refine_prov_weaken; [apply Hh, Heq0 |].
            intros U' [s1' r1] [s2' r2] (Hinc' & Hm' & Hs' & Hr').
            exact (conj (incl_tran Hinc Hinc') (conj Hm' (conj Hs' Hr'))).
        - eapply refine_prov__obs_eq;
            [exact (is_eq_rel_obs_eq U0) | exact E1 | exact E2 |].
          exact (step_is_eq_bind U0 U u1 u2 k Hu). }
      apply Hcore.
      eapply ISE_Tree; [reflexivity | reflexivity | apply incl_refl | exact Heq].
    Qed.
  End InterpStateEqualSync.

  Section CfgEqualSync.
    Context (Hmcfg : forall R (t : @MCFGtop (@ParamsV IP IPT) R) U σ1 σ2 rest,
                       mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
                       refine_prov (mcfg_eq_post U) U
                         (interp_mcfg_model t (σ1, rest))
                         (interp_mcfg_model t (σ2, rest))).

    Definition ctx_eq_sim
      (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT))) : Prop :=
      forall X (ce : CallE X) U σ1 σ2 rest,
        mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
        refine_prov (mcfg_eq_post U) U
          (interp_cfg_model ctx1 (mrec_ctx ctx1 X ce) (σ1, rest))
          (interp_cfg_model ctx2 (mrec_ctx ctx2 X ce) (σ2, rest)).

    Local Lemma cfg_vis_as_bind {X R : Type}
      (e : @CFGEtop (@ParamsV IP IPT) X) (k : X -> @CFGtop (@ParamsV IP IPT) R) :
      Vis e k ≅ ITree.bind (ITree.trigger e) k.
    Proof using.
      unfold ITree.trigger; rewrite Eqit.bind_vis.
      apply eqit_Vis; intros x; symmetry; apply Eqit.bind_ret_l.
    Qed.

    Local Lemma interp_cfg_model_trigger_call {X : Type}
      (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
      (ce : CallE X) (s : FusedS) :
      interp_cfg_model ctx (ITree.trigger (inl1 ce)) s ≅
      Tau (interp_cfg_model ctx (mrec_ctx ctx X ce) s).
    Proof using.
      assert (Hm : interp_mrec (mrec_ctx ctx) (ITree.trigger (inl1 ce)) ≅
                   Tau (interp_mrec (mrec_ctx ctx) (mrec_ctx ctx X ce))).
      { unfold ITree.trigger; rewrite unfold_interp_mrec.
        transitivity (Tau (interp_mrec (mrec_ctx ctx) (ITree.bind (mrec_ctx ctx X ce) (fun x => Ret x)))).
        - reflexivity.
        - apply eqit_Tau, interp_mrec_proper_eq, Eqit.bind_ret_r. }
      unfold interp_cfg_model.
      rewrite (interp_mcfg_model_obs_eq _ _ s Hm), interp_mcfg_model_tau.
      reflexivity.
    Qed.

    Local Lemma interp_cfg_model_trigger_mcfg {X : Type}
      (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
      (me : @MCFGEtop (@ParamsV IP IPT) X) (s : FusedS) :
      interp_cfg_model ctx (ITree.trigger (inr1 me)) s ≅
      ITree.bind (interp_mcfg_model (ITree.trigger me) s)
        (fun '(s', x) => Tau (Ret (s', x))).
    Proof using.
      assert (Hm : interp_mrec (mrec_ctx ctx) (ITree.trigger (inr1 me)) ≅
                   Vis me (fun x => Tau (interp_mrec (mrec_ctx ctx) (Ret x)))).
      { unfold ITree.trigger; rewrite unfold_interp_mrec; reflexivity. }
      unfold interp_cfg_model.
      rewrite (interp_mcfg_model_obs_eq _ _ s Hm).
      assert (Hvis : Vis me (fun x => Tau (interp_mrec (mrec_ctx ctx) (Ret x))) ≅
                     ITree.bind (Vis me (fun x => Ret x))
                       (fun x => Tau (interp_mrec (mrec_ctx ctx) (Ret x)))).
      { rewrite Eqit.bind_vis; apply eqit_Vis; intros x; rewrite Eqit.bind_ret_l; reflexivity. }
      rewrite (interp_mcfg_model_obs_eq _ _ s Hvis), interp_mcfg_model_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' x] _ <-.
      rewrite interp_mcfg_model_tau.
      rewrite (interp_mcfg_model_obs_eq _ _ s' (interp_mrec_ret (mrec_ctx ctx) x)).
      rewrite interp_mcfg_model_ret; reflexivity.
    Qed.

    Local Definition k_ces_mcfg {X R : Type}
      (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
      (k : X -> @CFGtop (@ParamsV IP IPT) R)
      : Res X -> itree ProvBotE (Res R) :=
      fun '(s', x) => Tau (interp_cfg_model ctx (k x) s').

    Local Definition k_ces_call {X R : Type}
      (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
      (k : X -> @CFGtop (@ParamsV IP IPT) R)
      : Res X -> itree ProvBotE (Res R) :=
      fun '(s', x) => interp_cfg_model ctx (k x) s'.

    Inductive ces_rel {R : Type}
      (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT))) (U0 : list N)
      : list N -> itree ProvBotE (Res R) -> itree ProvBotE (Res R) -> Prop :=
    | CES_Tree U (t : @CFGtop (@ParamsV IP IPT) R) (σ1 σ2 : state) rest
        (a1 a2 : itree ProvBotE (Res R)) :
        interp_cfg_model ctx1 t (σ1, rest) ≅ a1 ->
        interp_cfg_model ctx2 t (σ2, rest) ≅ a2 ->
        incl U0 U ->
        mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
        ces_rel ctx1 ctx2 U0 U a1 a2
    | CES_BindMcfg {X : Type} U (u1 u2 : itree ProvBotE (Res X))
        (k : X -> @CFGtop (@ParamsV IP IPT) R)
        (a1 a2 : itree ProvBotE (Res R)) :
        ITree.bind u1 (k_ces_mcfg ctx1 k) ≅ a1 ->
        ITree.bind u2 (k_ces_mcfg ctx2 k) ≅ a2 ->
        refine_prov (mcfg_eq_post U0) U u1 u2 ->
        ces_rel ctx1 ctx2 U0 U a1 a2
    | CES_BindCall {X : Type} U (u1 u2 : itree ProvBotE (Res X))
        (k : X -> @CFGtop (@ParamsV IP IPT) R)
        (a1 a2 : itree ProvBotE (Res R)) :
        ITree.bind u1 (k_ces_call ctx1 k) ≅ a1 ->
        ITree.bind u2 (k_ces_call ctx2 k) ≅ a2 ->
        refine_prov (mcfg_eq_post U0) U u1 u2 ->
        ces_rel ctx1 ctx2 U0 U a1 a2.

    Local Lemma ces_rel_obs_eq {R : Type}
      (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
      (U0 U : list N) (a1 a1' a2 a2' : itree ProvBotE (Res R)) :
      a1 ≅ a1' ->
      a2 ≅ a2' ->
      @ces_rel R ctx1 ctx2 U0 U a1 a2 ->
      @ces_rel R ctx1 ctx2 U0 U a1' a2'.
    Proof using.
      intros E1 E2 Hc.
      destruct Hc as [U' t σ1 σ2 rest a1_0 a2_0 Et1 Et2 Hinc Heq
                     | X U' u1 u2 k a1_0 a2_0 Eu1 Eu2 Hu
                     | X U' u1 u2 k a1_0 a2_0 Eu1 Eu2 Hu].
      - eapply CES_Tree with (t := t) (σ1 := σ1) (σ2 := σ2) (rest := rest).
        + transitivity a1_0; [exact Et1 | exact E1].
        + transitivity a2_0; [exact Et2 | exact E2].
        + exact Hinc.
        + exact Heq.
      - eapply CES_BindMcfg with (u1 := u1) (u2 := u2) (k := k).
        + transitivity a1_0; [exact Eu1 | exact E1].
        + transitivity a2_0; [exact Eu2 | exact E2].
        + exact Hu.
      - eapply CES_BindCall with (u1 := u1) (u2 := u2) (k := k).
        + transitivity a1_0; [exact Eu1 | exact E1].
        + transitivity a2_0; [exact Eu2 | exact E2].
        + exact Hu.
    Qed.

    Local Lemma step_ces_mcfg_bind {X R : Type}
      (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
      (U0 U : list N) (u1 u2 : itree ProvBotE (Res X))
      (k : X -> @CFGtop (@ParamsV IP IPT) R) :
      refine_prov (mcfg_eq_post U0) U u1 u2 ->
      refine_prov_ (mcfg_eq_post U0) (@ces_rel R ctx1 ctx2 U0) U
        (ITree.bind u1 (k_ces_mcfg ctx1 k))
        (ITree.bind u2 (k_ces_mcfg ctx2 k)).
    Proof using.
      intros Hu; punfold Hu.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [[[σ1' rest1'] x1] | m1 | Y1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [[[σ2' rest2'] x2] | m2 | Y2 e2 h2] eqn:Hou2;
            try contradiction.
          destruct Hstep as (Hinc & Heq & Hrest & <-).
          cbn [fst snd] in Heq, Hrest; subst rest2'.
          apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2; cbn.
          eapply CES_Tree; [reflexivity | reflexivity | exact Hinc | exact Heq].
        + destruct (observe u2) as [? | m2 | ? ? ?] eqn:Hou2; try contradiction.
          pclearbot; apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2.
          eapply CES_BindMcfg; [reflexivity | reflexivity | exact Hstep].
        + apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind u1 (k_ces_mcfg ctx1 k)), Hou1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            eapply CES_BindMcfg; [reflexivity | reflexivity | exact Hleft].
          * right; right.
            destruct (observe u2) as [? | ? | Y2 e2 h2] eqn:Hou2; try contradiction.
            rewrite (observe_bind u2 (k_ces_mcfg ctx2 k)), Hou2.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               eapply CES_BindMcfg; [reflexivity | reflexivity | exact Hboth].
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               eapply CES_BindMcfg; [reflexivity | reflexivity | exact HA].
      - eapply RP_TauL;
          [rewrite (observe_bind u1 (k_ces_mcfg ctx1 k)), Hu1; reflexivity | exact IH].
      - eapply RP_TauR;
          [rewrite (observe_bind u2 (k_ces_mcfg ctx2 k)), Hu2; reflexivity | exact IH].
    Qed.

    Local Lemma step_ces_tree {R : Type}
      (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
      (Hctx : ctx_eq_sim ctx1 ctx2)
      (U0 U : list N) (t : @CFGtop (@ParamsV IP IPT) R)
      (σ1 σ2 : state) (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
      (Hinc : incl U0 U)
      (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
      refine_prov_ (mcfg_eq_post U0) (@ces_rel R ctx1 ctx2 U0) U
        (interp_cfg_model ctx1 t (σ1, rest))
        (interp_cfg_model ctx2 t (σ2, rest)).
    Proof using Hmcfg.
      destruct (observe t) as [rv | mt | X e k] eqn:Hot.
      - assert (Heta : t ≅ Ret rv) by (rewrite (itree_eta t), Hot; reflexivity).
        assert (Et1 : Ret ((σ1, rest), rv) ≅ interp_cfg_model ctx1 t (σ1, rest)).
        { symmetry; rewrite (interp_cfg_model_obs_eq ctx1 _ _ _ Heta); apply interp_cfg_model_ret. }
        assert (Et2 : Ret ((σ2, rest), rv) ≅ interp_cfg_model ctx2 t (σ2, rest)).
        { symmetry; rewrite (interp_cfg_model_obs_eq ctx2 _ _ _ Heta); apply interp_cfg_model_ret. }
        eapply refine_prov__obs_eq;
          [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact Et1 | exact Et2 |].
        apply RP_Step; cbn; exact (conj Hinc (conj Heq (conj Logic.eq_refl Logic.eq_refl))).
      - assert (Heta : t ≅ Tau mt) by (rewrite (itree_eta t), Hot; reflexivity).
        assert (Et1 : Tau (interp_cfg_model ctx1 mt (σ1, rest)) ≅ interp_cfg_model ctx1 t (σ1, rest)).
        { symmetry; rewrite (interp_cfg_model_obs_eq ctx1 _ _ _ Heta); apply interp_cfg_model_tau. }
        assert (Et2 : Tau (interp_cfg_model ctx2 mt (σ2, rest)) ≅ interp_cfg_model ctx2 t (σ2, rest)).
        { symmetry; rewrite (interp_cfg_model_obs_eq ctx2 _ _ _ Heta); apply interp_cfg_model_tau. }
        eapply refine_prov__obs_eq;
          [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact Et1 | exact Et2 |].
        apply RP_Step; cbn; eapply CES_Tree; [reflexivity | reflexivity | exact Hinc | exact Heq].
      - assert (Heta : t ≅ ITree.bind (ITree.trigger e) k).
        { rewrite (itree_eta t), Hot; apply cfg_vis_as_bind. }
        destruct e as [ce | me].
        + assert (Et1 : Tau (ITree.bind (interp_cfg_model ctx1 (mrec_ctx ctx1 X ce) (σ1, rest))
                               (k_ces_call ctx1 k)) ≅
                        interp_cfg_model ctx1 t (σ1, rest)).
          { symmetry; rewrite (interp_cfg_model_obs_eq ctx1 _ _ _ Heta), interp_cfg_model_bind.
            rewrite interp_cfg_model_trigger_call, Eqit.bind_tau; reflexivity. }
          assert (Et2 : Tau (ITree.bind (interp_cfg_model ctx2 (mrec_ctx ctx2 X ce) (σ2, rest))
                               (k_ces_call ctx2 k)) ≅
                        interp_cfg_model ctx2 t (σ2, rest)).
          { symmetry; rewrite (interp_cfg_model_obs_eq ctx2 _ _ _ Heta), interp_cfg_model_bind.
            rewrite interp_cfg_model_trigger_call, Eqit.bind_tau; reflexivity. }
          eapply refine_prov__obs_eq;
            [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact Et1 | exact Et2 |].
          apply RP_Step; cbn.
          eapply CES_BindCall; [reflexivity | reflexivity |].
          eapply refine_prov_weaken; [apply Hctx, Heq |].
          intros U' [s1' r1] [s2' r2] (Hinc' & Hm' & Hs' & Hr').
          exact (conj (incl_tran Hinc Hinc') (conj Hm' (conj Hs' Hr'))).
        + assert (Et1 : ITree.bind (interp_mcfg_model (ITree.trigger me) (σ1, rest))
                          (k_ces_mcfg ctx1 k) ≅
                        interp_cfg_model ctx1 t (σ1, rest)).
          { symmetry; rewrite (interp_cfg_model_obs_eq ctx1 _ _ _ Heta), interp_cfg_model_bind.
            rewrite interp_cfg_model_trigger_mcfg, Eqit.bind_bind.
            eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
            intros [s' x] _ <-; rewrite Eqit.bind_tau, Eqit.bind_ret_l; reflexivity. }
          assert (Et2 : ITree.bind (interp_mcfg_model (ITree.trigger me) (σ2, rest))
                          (k_ces_mcfg ctx2 k) ≅
                        interp_cfg_model ctx2 t (σ2, rest)).
          { symmetry; rewrite (interp_cfg_model_obs_eq ctx2 _ _ _ Heta), interp_cfg_model_bind.
            rewrite interp_cfg_model_trigger_mcfg, Eqit.bind_bind.
            eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
            intros [s' x] _ <-; rewrite Eqit.bind_tau, Eqit.bind_ret_l; reflexivity. }
          eapply refine_prov__obs_eq;
            [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact Et1 | exact Et2 |].
          apply step_ces_mcfg_bind.
          eapply refine_prov_weaken; [apply Hmcfg, Heq |].
          intros U' [s1' r1] [s2' r2] (Hinc' & Hm' & Hs' & Hr').
          exact (conj (incl_tran Hinc Hinc') (conj Hm' (conj Hs' Hr'))).
    Qed.

    Local Lemma step_ces_call_bind {X R : Type}
      (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
      (Hctx : ctx_eq_sim ctx1 ctx2)
      (U0 U : list N) (u1 u2 : itree ProvBotE (Res X))
      (k : X -> @CFGtop (@ParamsV IP IPT) R) :
      refine_prov (mcfg_eq_post U0) U u1 u2 ->
      refine_prov_ (mcfg_eq_post U0) (@ces_rel R ctx1 ctx2 U0) U
        (ITree.bind u1 (k_ces_call ctx1 k))
        (ITree.bind u2 (k_ces_call ctx2 k)).
    Proof using Hmcfg.
      intros Hu; punfold Hu.
      induction Hu as [U u1 u2 Hstep | U u1 m1 u2 Hu1 _ IH | U u1 u2 m2 Hu2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe u1) as [[[σ1' rest1'] x1] | m1 | Y1 e1 h1] eqn:Hou1.
        + destruct (observe u2) as [[[σ2' rest2'] x2] | m2 | Y2 e2 h2] eqn:Hou2;
            try contradiction.
          destruct Hstep as (Hinc & Heq & Hrest & <-).
          cbn [fst snd] in Heq, Hrest; subst rest2'.
          assert (Eb1 : interp_cfg_model ctx1 (k x1) (σ1', rest1') ≅
                        ITree.bind u1 (k_ces_call ctx1 k)).
          { symmetry; rewrite (itree_eta u1), Hou1, Eqit.bind_ret_l; reflexivity. }
          assert (Eb2 : interp_cfg_model ctx2 (k x1) (σ2', rest1') ≅
                        ITree.bind u2 (k_ces_call ctx2 k)).
          { symmetry; rewrite (itree_eta u2), Hou2, Eqit.bind_ret_l; reflexivity. }
          eapply refine_prov__obs_eq;
            [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact Eb1 | exact Eb2 |].
          exact (step_ces_tree ctx1 ctx2 Hctx U0 U (k x1) σ1' σ2' rest1' Hinc Heq).
        + destruct (observe u2) as [? | m2 | ? ? ?] eqn:Hou2; try contradiction.
          pclearbot; apply RP_Step; unfold rp_step_body.
          rewrite !observe_bind, Hou1, Hou2.
          eapply CES_BindCall; [reflexivity | reflexivity | exact Hstep].
        + apply RP_Step; unfold rp_step_body.
          rewrite (observe_bind u1 (k_ces_call ctx1 k)), Hou1.
          destruct Hstep as [Hub | [Hleft | Hboth]].
          * left; exact Hub.
          * right; left; destruct e1 as [p1 | b1']; [| contradiction]; destruct p1.
            intros p Hp; specialize (Hleft p Hp); pclearbot.
            eapply CES_BindCall; [reflexivity | reflexivity | exact Hleft].
          * right; right.
            destruct (observe u2) as [? | ? | Y2 e2 h2] eqn:Hou2; try contradiction.
            rewrite (observe_bind u2 (k_ces_call ctx2 k)), Hou2.
            destruct e1 as [p1 | b1'], e2 as [p2 | b2']; cbn in *; try contradiction.
            -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
               eapply CES_BindCall; [reflexivity | reflexivity | exact Hboth].
            -- destruct Hboth as [HE HA]; split; [exact HE |].
               intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
               eapply CES_BindCall; [reflexivity | reflexivity | exact HA].
      - eapply RP_TauL;
          [rewrite (observe_bind u1 (k_ces_call ctx1 k)), Hu1; reflexivity | exact IH].
      - eapply RP_TauR;
          [rewrite (observe_bind u2 (k_ces_call ctx2 k)), Hu2; reflexivity | exact IH].
    Qed.

    Lemma cfg_equal_sync_gen {R : Type}
      (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
      (Hctx : ctx_eq_sim ctx1 ctx2)
      (t : @CFGtop (@ParamsV IP IPT) R)
      (U0 : list N) (σ1 σ2 : state)
      (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
      (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
      refine_prov (mcfg_eq_post U0) U0
        (interp_cfg_model ctx1 t (σ1, rest))
        (interp_cfg_model ctx2 t (σ2, rest)).
    Proof using Hmcfg.
      assert (Hcore : forall U a1 a2,
                @ces_rel R ctx1 ctx2 U0 U a1 a2 ->
                refine_prov (mcfg_eq_post U0) U a1 a2).
      { pcofix CIH; intros U a1 a2 Hst; pstep.
        eapply refine_prov__mon with (r := @ces_rel R ctx1 ctx2 U0);
          [| intros U' x1 x2 Hx; right; apply CIH, Hx].
        destruct Hst as [U t0 s_a s_b rest0 a1_0 a2_0 E1 E2 Hinc Heq0
                        | X U u1 u2 k a1_0 a2_0 E1 E2 Hu
                        | X U u1 u2 k a1_0 a2_0 E1 E2 Hu].
        - eapply refine_prov__obs_eq;
            [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact E1 | exact E2 |].
          exact (step_ces_tree ctx1 ctx2 Hctx U0 U t0 s_a s_b rest0 Hinc Heq0).
        - eapply refine_prov__obs_eq;
            [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact E1 | exact E2 |].
          exact (step_ces_mcfg_bind ctx1 ctx2 U0 U u1 u2 k Hu).
        - eapply refine_prov__obs_eq;
            [exact (ces_rel_obs_eq ctx1 ctx2 U0) | exact E1 | exact E2 |].
          exact (step_ces_call_bind ctx1 ctx2 Hctx U0 U u1 u2 k Hu). }
      apply Hcore.
      eapply CES_Tree; [reflexivity | reflexivity | apply incl_refl | exact Heq].
    Qed.
  End CfgEqualSync.

  Lemma on_mem_prov_equal_sync {T : Type}
    (m : @memM (@ParamsV IP IPT) _ T)
    (U : list N) (σ1 σ2 : state)
    (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Hm : refine_prov (eq_sync_post U) U
            (memM_interp_prov m σ1)
            (memM_interp_prov m σ2)) :
    refine_prov (mcfg_eq_post U) U
      (on_mem_prov (memM_interp_prov m) (σ1, rest))
      (on_mem_prov (memM_interp_prov m) (σ2, rest)).
  Proof using.
    unfold on_mem_prov.
    eapply refine_prov_bind; [exact Hm |].
    intros U' [σ1' r1] [σ2' r2] (Hinc & Heq & <-).
    apply refine_prov_ret;
      exact (conj Hinc (conj Heq (conj Logic.eq_refl Logic.eq_refl))).
  Qed.

  Lemma interp_vellvm_prov_h_equal_sync {X : Type}
    (e : @MCFGEtop (@ParamsV IP IPT) X)
    (U : list N) (σ1 σ2 : state)
    (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_post U) U
      (interp_vellvm_prov_h e (σ1, rest))
      (interp_vellvm_prov_h e (σ2, rest)).
  Proof using.
    destruct rest as [ls g].
    unfold interp_vellvm_prov_h.
    destruct e as [e1 | [e2 | [e3 | [[e4a | e4b] | [e5 | [e6 | [e7 | [e8 | [e9 | [e10 | e11]]]]]]]]]];
      cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
    - apply fused_trigger_prov_equal_sync, Heq.
    - unfold fused_intrinsic_prov, handle_intrinsic.
      apply on_mem_prov_equal_sync, handle_intrinsicM_equal_sync, Heq.
    - unfold fused_global_prov; apply on_genv_prov_equal_sync, Heq.
    - unfold fused_local_prov; apply on_ls_prov_equal_sync, Heq.
    - unfold fused_stack_prov; apply on_ls_prov_equal_sync, Heq.
    - unfold fused_memory_prov, handle_memory.
      apply on_mem_prov_equal_sync, handle_memoryM_equal_sync, Heq.
    - apply fused_draw_prov_equal_sync, Heq.
    - apply fused_trigger_prov_equal_sync, Heq.
    - apply fused_trigger_prov_equal_sync, Heq.
    - apply fused_trigger_prov_equal_sync, Heq.
    - apply fused_trigger_prov_equal_sync, Heq.
    - apply fused_trigger_prov_equal_sync, Heq.
  Qed.

  Lemma mcfg_equal_sync {R : Type}
    (t : @MCFGtop (@ParamsV IP IPT) R)
    (U : list N) (σ1 σ2 : state)
    (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_post U) U
      (interp_mcfg_model t (σ1, rest))
      (interp_mcfg_model t (σ2, rest)).
  Proof using.
    unfold interp_mcfg_model.
    exact (interp_state_equal_sync_gen interp_vellvm_prov_h
             (@interp_vellvm_prov_h_equal_sync) (interp_intrinsics t) U σ1 σ2 rest Heq).
  Qed.

  Lemma cfg_equal_sync {R : Type}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (Hctx : ctx_eq_sim ctx1 ctx2)
    (t : @CFGtop (@ParamsV IP IPT) R)
    (U : list N) (σ1 σ2 : state)
    (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (mcfg_eq_post U) U
      (interp_cfg_model ctx1 t (σ1, rest))
      (interp_cfg_model ctx2 t (σ2, rest)).
  Proof using.
    exact (cfg_equal_sync_gen (@mcfg_equal_sync) ctx1 ctx2 Hctx t U σ1 σ2 rest Heq).
  Qed.

  Lemma cfg_exc_equal_sync {R : Type}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (Hctx : ctx_eq_sim ctx1 ctx2)
    (t : @CFGtop (@ParamsV IP IPT) R)
    (U : list N) (σ1 σ2 : state)
    (rest : (@stack_frame (@ParamsV IP IPT) * stack) * global_env)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov
      (exc_post
         (fun U' s1' s2' x1 x2 =>
            incl U U' /\
            mem_stack_equal (state_memory_stack (fst s1')) (state_memory_stack (fst s2')) /\
            snd s1' = snd s2' /\
            x1 = x2)
         (fun U' s1' s2' r1 r2 =>
            incl U U' /\
            mem_stack_equal (state_memory_stack (fst s1')) (state_memory_stack (fst s2')) /\
            snd s1' = snd s2' /\
            r1 = r2))
      U
      (interp_cfg_exc ctx1 t (σ1, rest))
      (interp_cfg_exc ctx2 t (σ2, rest)).
  Proof using.
    unfold interp_cfg_exc.
    eapply refine_prov_weaken;
      [exact (cfg_equal_sync ctx1 ctx2 Hctx (run_exc t) U σ1 σ2 rest Heq) |].
    intros U' [s1' [x1 | r1]] [s2' [x2 | r2]] (Hinc & Hm & Hs & Heq_res);
      inversion Heq_res; subst; exact (conj Hinc (conj Hm (conj Hs Logic.eq_refl))).
  Qed.

  (** ** 3J. Global Environment Initialization & Safe-Provenance Preservation *)

  Lemma genv_safe_empty (P0 : list N) :
    genv_safe P0 Maps.empty.
  Proof using.
    intros gid v Hlk; cbn [Maps.lookup Maps.empty Map_rmap] in Hlk; rewrite RMF.F.empty_o in Hlk; discriminate Hlk.
  Qed.

  Lemma genv_safe_add (P0 : list N) (gid : raw_id)
    (v : @dvalue (@ParamsV IP IPT)) (g : @global_env (@ParamsV IP IPT)) :
    genv_safe P0 g ->
    is_safe_ptr_dvalue P0 v ->
    genv_safe P0 (Maps.add gid v g).
  Proof using.
    intros Hg Hv gid' v' Hlk.
    destruct (RawIDOrd.eq_dec gid gid') as [<- | Hne].
    - cbn [Maps.lookup Maps.add Map_rmap] in Hlk; rewrite RMF.F.add_eq_o in Hlk by reflexivity; inversion Hlk; subst v'; exact Hv.
    - cbn [Maps.lookup Maps.add Map_rmap] in Hlk; rewrite RMF.F.add_neq_o in Hlk by exact Hne; exact (Hg gid' v' Hlk).
  Qed.

  Definition genv_init_post
    (P0 : list N) (ls : @stack_frame (@ParamsV IP IPT) * stack)
    (U' : list N) (x1 x2 : Res unit) : Prop :=
    let '(s1', _) := x1 in
    let '(s2', _) := x2 in
    exists P1 g',
      incl P0 P1 /\
      incl P1 U' /\
      snd s1' = (ls, g') /\
      snd s2' = (ls, g') /\
      genv_safe P1 g' /\
      mem_stack_equal (state_memory_stack (fst s1')) (state_memory_stack (fst s2')).

  Lemma genv_init_seq
    (t1 t2 : @MCFGtop (@ParamsV IP IPT) unit)
    (U P0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Ht1 : refine_prov (genv_init_post P0 ls) U
             (interp_mcfg_model t1 (σ1, (ls, g)))
             (interp_mcfg_model t1 (σ2, (ls, g))))
    (Ht2 : forall U1 P1 σ1' σ2' g',
             incl P0 P1 ->
             incl P1 U1 ->
             genv_safe P1 g' ->
             mem_stack_equal (state_memory_stack σ1') (state_memory_stack σ2') ->
             refine_prov (genv_init_post P1 ls) U1
               (interp_mcfg_model t2 (σ1', (ls, g')))
               (interp_mcfg_model t2 (σ2', (ls, g')))) :
    refine_prov (genv_init_post P0 ls) U
      (interp_mcfg_model (ITree.bind t1 (fun _ => t2)) (σ1, (ls, g)))
      (interp_mcfg_model (ITree.bind t1 (fun _ => t2)) (σ2, (ls, g))).
  Proof using.
    eapply refine_mcfg_model_bind; [exact Ht1 |].
    intros U1 [σ1' rest1'] [] [σ2' rest2'] [] _
      (P1 & g1 & Hp01 & Hp1u & Hs1 & Hs2 & Hg1 & Heq1).
    cbn [fst snd] in Hs1, Hs2, Heq1; subst rest1' rest2'.
    eapply refine_prov_weaken; [exact (Ht2 U1 P1 σ1' σ2' g1 Hp01 Hp1u Hg1 Heq1) |].
    intros U2 [s1'' []] [s2'' []] (P2 & g2 & Hp12 & Hp2u & Hsa & Hsb & Hg2 & Heq2).
    exists P2, g2.
    exact (conj (incl_tran Hp01 Hp12)
             (conj Hp2u (conj Hsa (conj Hsb (conj Hg2 Heq2))))).
  Qed.

  Lemma genv_init_loop_monad {A : Type}
    (f : A -> @MCFGtop (@ParamsV IP IPT) unit)
    (xs : list A)
    (Hf : forall a U P0 σ1 σ2 ls g,
            In a xs ->
            incl P0 U ->
            genv_safe P0 g ->
            mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
            refine_prov (genv_init_post P0 ls) U
              (interp_mcfg_model (f a) (σ1, (ls, g)))
              (interp_mcfg_model (f a) (σ2, (ls, g)))) :
    forall U P0 σ1 σ2 ls g,
      incl P0 U ->
      genv_safe P0 g ->
      mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
      refine_prov (genv_init_post P0 ls) U
        (interp_mcfg_model (loop_monad f xs) (σ1, (ls, g)))
        (interp_mcfg_model (loop_monad f xs) (σ2, (ls, g))).
  Proof using.
    induction xs as [| a xs' IH]; intros U P0 σ1 σ2 ls g Hpu Hg Heq;
      cbn [loop_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret; exists P0, g.
      exact (conj (incl_refl P0)
               (conj Hpu (conj Logic.eq_refl (conj Logic.eq_refl (conj Hg Heq))))).
    - eapply genv_init_seq.
      + apply Hf; [left; reflexivity | exact Hpu | exact Hg | exact Heq].
      + intros U1 P1 σ1' σ2' g' _ Hp1u Hg1 Heq1.
        apply IH; [intros a' U' P' s1 s2 ls' g0 Ha'; apply Hf; right; exact Ha'
                  | exact Hp1u | exact Hg1 | exact Heq1].
  Qed.

  Lemma alloca_gwrite_safe_sim
    (dt : dtyp) (al : option N) (gid : raw_id)
    (U P0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hpu : incl P0 U)
    (Hg : genv_safe P0 g)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (genv_init_post P0 ls) U
      (interp_mcfg_model
         (ITree.bind (alloca dt 1%N al) (fun v => gwrite gid v))
         (σ1, (ls, g)))
      (interp_mcfg_model
         (ITree.bind (alloca dt 1%N al) (fun v => gwrite gid v))
         (σ2, (ls, g))).
  Proof using.
    eapply refine_mcfg_model_bind with
      (RA := fun U' '(s1', v1) '(s2', v2) =>
               exists pr,
                 ~ In pr U /\
                 U' = pr :: U /\
                 v1 = v2 /\
                 is_safe_ptr_dvalue (pr :: P0) v2 /\
                 mem_stack_equal (state_memory_stack (fst s1')) (state_memory_stack (fst s2')) /\
                 snd s1' = (ls, g) /\
                 snd s2' = (ls, g)).
    - unfold alloca, Subevent.trigger; try unfold trigger_cast.
      apply refine_mcfg_memory_event.
      eapply refine_prov_weaken;
        [exact (alloca_mem_equal_safe dt 1%N al U P0 σ1 σ2 Hpu Heq) |].
      intros U' [σ1' r1] [σ2' r2] (pr & Hpr & -> & Hr & Hsafe & Heq').
      exists pr; cbn [fst snd];
        exact (conj Hpr (conj Logic.eq_refl (conj Hr (conj Hsafe (conj Heq' (conj Logic.eq_refl Logic.eq_refl)))))).
    - intros U1 [σ1' rest1'] v1 [σ2' rest2'] v2 _
        (pr & Hpr & -> & <- & Hsafe & Heq' & Hrest1 & Hrest2).
      cbn [fst snd] in Heq', Hrest1, Hrest2; subst rest1' rest2'.
      eapply refine_prov_tau_star_l; [apply tau_star_mcfg_gwrite |].
      eapply refine_prov_tau_star_r; [apply tau_star_mcfg_gwrite |].
      apply refine_prov_ret.
      exists (pr :: P0), (Maps.add gid v1 g).
      split; [intros z Hz; right; exact Hz |].
      split; [intros z [<- | Hz]; [left; reflexivity | right; apply Hpu, Hz] |].
      split; [reflexivity |].
      split; [reflexivity |].
      split; [apply genv_safe_add; [| exact Hsafe];
              eapply genv_safe_incl; [intros z Hz; right; exact Hz | exact Hg] |].
      exact Heq'.
  Qed.

  Lemma allocate_declaration_safe_sim (d : declaration dtyp)
    (U P0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hpu : incl P0 U)
    (Hg : genv_safe P0 g)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (genv_init_post P0 ls) U
      (interp_mcfg_model (allocate_declaration d) (σ1, (ls, g)))
      (interp_mcfg_model (allocate_declaration d) (σ2, (ls, g))).
  Proof using.
    unfold allocate_declaration.
    destruct (lookup_intrinsic_declaration (dc_name d)).
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret; exists P0, g.
      exact (conj (incl_refl P0)
               (conj Hpu (conj Logic.eq_refl (conj Logic.eq_refl (conj Hg Heq))))).
    - exact (alloca_gwrite_safe_sim (DTYPE_Base DTYPE_Pointer) None (dc_name d)
               U P0 σ1 σ2 ls g Hpu Hg Heq).
  Qed.

  Lemma allocate_block_address_safe_sim (fb : function_id * block_id)
    (U P0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hpu : incl P0 U)
    (Hg : genv_safe P0 g)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (genv_init_post P0 ls) U
      (interp_mcfg_model (allocate_block_address fb) (σ1, (ls, g)))
      (interp_mcfg_model (allocate_block_address fb) (σ2, (ls, g))).
  Proof using.
    destruct fb as [f b]; unfold allocate_block_address.
    exact (alloca_gwrite_safe_sim (DTYPE_Base (DTYPE_I 8)) None (blockaddress_id f b)
             U P0 σ1 σ2 ls g Hpu Hg Heq).
  Qed.

  Lemma allocate_global_safe_sim (gl : global dtyp)
    (U P0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hpu : incl P0 U)
    (Hg : genv_safe P0 g)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (genv_init_post P0 ls) U
      (interp_mcfg_model (allocate_global gl) (σ1, (ls, g)))
      (interp_mcfg_model (allocate_global gl) (σ2, (ls, g))).
  Proof using.
    unfold allocate_global.
    destruct (g_alias gl).
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret; exists P0, g.
      exact (conj (incl_refl P0)
               (conj Hpu (conj Logic.eq_refl (conj Logic.eq_refl (conj Hg Heq))))).
    - exact (alloca_gwrite_safe_sim (g_typ gl)
               (option_map (fun a => Z.to_N (denote_int_syntax a)) (g_align gl))
               (g_ident gl) U P0 σ1 σ2 ls g Hpu Hg Heq).
  Qed.

  Lemma initialize_global_safe_sim (gl : global dtyp)
    (U P0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hpu : incl P0 U)
    (Hg : genv_safe P0 g)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (genv_init_post P0 ls) U
      (interp_mcfg_model (initialize_global gl) (σ1, (ls, g)))
      (interp_mcfg_model (initialize_global gl) (σ2, (ls, g))).
  Proof using.
    destruct ls as [sf fstk]; unfold initialize_global.
    destruct (g_alias gl).
    - destruct (g_exp gl) as [e |]; [| apply refine_mcfg_raiseUB_l].
      destruct e;
        lazymatch goal with
        | |- refine_prov _ _ (interp_mcfg_model (raiseUB _) _) _ => apply refine_mcfg_raiseUB_l
        | _ => idtac
        end.
      destruct id as [g_source | lid]; [| apply refine_mcfg_raiseUB_l].
      eapply refine_mcfg_model_bind; [apply refine_mcfg_gread_same_g |].
      intros U1 s1' p1 s2' p2 _ (-> & -> & -> & -> & Hsafe).
      eapply refine_prov_tau_star_l; [apply tau_star_mcfg_gwrite |].
      eapply refine_prov_tau_star_r; [apply tau_star_mcfg_gwrite |].
      apply refine_prov_ret.
      exists P0, (Maps.add (g_ident gl) p2 g).
      exact (conj (incl_refl P0)
               (conj Hpu (conj Logic.eq_refl
                  (conj Logic.eq_refl
                     (conj (genv_safe_add P0 (g_ident gl) p2 g Hg (Hsafe P0 Hg)) Heq))))).
    - eapply refine_mcfg_model_bind; [apply refine_mcfg_gread_same_g |].
      intros U1 s1' a1 s2' a2 _ (-> & -> & -> & -> & _).
      eapply refine_mcfg_model_bind with
        (RA := fun U' '(s1', r1) '(s2', r2) =>
                 U' = U /\
                 s1' = (σ1, (sf, fstk, g)) /\
                 s2' = (σ2, (sf, fstk, g)) /\
                 r1 = r2).
      + destruct (g_exp gl) as [e |].
        * eapply refine_prov_weaken;
            [exact (denote_exp_mcfg_sim (Some (g_typ gl)) e U σ1 σ2 sf sf fstk fstk g
                      (fun _ _ => Logic.eq_refl)) |].
          intros U' [sa va] [sb vb] (-> & -> & -> & -> & _).
          exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
        * eapply refine_prov_obs_eq;
            [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
          apply refine_prov_ret;
            exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
      + intros U2 s1'' uv1 s2'' uv2 _ (-> & -> & -> & ->).
        unfold store, Subevent.trigger; try unfold trigger_cast.
        apply refine_mcfg_memory_event.
        eapply refine_prov_weaken;
          [exact (handle_memoryM_equal_sync (Store (g_typ gl) a2 uv2) U σ1 σ2 Heq) |].
        intros U' [σ1' []] [σ2' []] (Hinc & Heq' & _).
        exists P0, g.
        exact (conj (incl_refl P0)
                 (conj (incl_tran Hpu Hinc)
                    (conj Logic.eq_refl (conj Logic.eq_refl (conj Hg Heq'))))).
  Qed.

  Lemma build_global_environment_safe_sim (M : CFG.mcfg dtyp)
    (U P0 : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hpu : incl P0 U)
    (Hg : genv_safe P0 g)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
    refine_prov (genv_init_post P0 ls) U
      (interp_mcfg_model (build_global_environment M) (σ1, (ls, g)))
      (interp_mcfg_model (build_global_environment M) (σ2, (ls, g))).
  Proof using.
    unfold build_global_environment, allocate_declarations,
           allocate_block_addresses, allocate_globals, initialize_globals.
    eapply genv_init_seq.
    - apply genv_init_loop_monad;
        [intros d U' P' s1 s2 ls' g' _; apply allocate_declaration_safe_sim
        | exact Hpu | exact Hg | exact Heq].
    - intros U1 P1 σ1a σ2a g1 _ Hp1u Hg1 Heq1.
      eapply genv_init_seq.
      + apply genv_init_loop_monad;
          [intros fb U' P' s1 s2 ls' g' _; apply allocate_block_address_safe_sim
          | exact Hp1u | exact Hg1 | exact Heq1].
      + intros U2 P2 σ1b σ2b g2 _ Hp2u Hg2 Heq2.
        eapply genv_init_seq.
        * apply genv_init_loop_monad;
            [intros gl U' P' s1 s2 ls' g' _; apply allocate_global_safe_sim
            | exact Hp2u | exact Hg2 | exact Heq2].
        * intros U3 P3 σ1c σ2c g3 _ Hp3u Hg3 Heq3.
          apply genv_init_loop_monad;
            [intros gl U' P' s1 s2 ls' g' _; apply initialize_global_safe_sim
            | exact Hp3u | exact Hg3 | exact Heq3].
  Qed.

  Lemma address_one_function_pair_sim
    (Rfn : @function_denotation (@ParamsV IP IPT) ->
           @function_denotation (@ParamsV IP IPT) -> Prop)
    (df1 df2 : definition dtyp (CFG.cfg dtyp))
    (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hname : dc_name (df_prototype df1) = dc_name (df_prototype df2))
    (Hfn : Rfn (denote_function df1) (denote_function df2)) :
    let s1 := (σ1, (ls, g)) in
    let s2 := (σ2, (ls, g)) in
    refine_prov
      (fun U' '(s1', (z1, f1)) '(s2', (z2, f2)) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\ z1 = z2 /\ Rfn f1 f2)
      U
      (interp_mcfg_model (address_one_function df1) s1)
      (interp_mcfg_model (address_one_function df2) s2).
  Proof using.
    cbv zeta; destruct ls as [sf fstk]; unfold address_one_function.
    rewrite Hname.
    eapply refine_mcfg_model_bind; [apply refine_mcfg_gread_same_g |].
    intros U1 s1' fv1 s2' fv2 _ (-> & -> & -> & -> & _).
    destruct fv2 as [[pt | | | | | | |] | |];
      lazymatch goal with
      | |- refine_prov _ _ (interp_mcfg_model (raise _) _) _ => apply refine_mcfg_raise_both
      | _ => idtac
      end.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
    apply refine_prov_ret;
      exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Hfn)))).
  Qed.

  Lemma address_one_library_pair_sim
    (Rfn : @function_denotation (@ParamsV IP IPT) ->
           @function_denotation (@ParamsV IP IPT) -> Prop)
    (lib : function_id * @function_denotation (@ParamsV IP IPT))
    (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hfn : Rfn (snd lib) (snd lib)) :
    let s1 := (σ1, (ls, g)) in
    let s2 := (σ2, (ls, g)) in
    refine_prov
      (fun U' '(s1', (z1, f1)) '(s2', (z2, f2)) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\ z1 = z2 /\ Rfn f1 f2)
      U
      (interp_mcfg_model (address_one_library_function lib) s1)
      (interp_mcfg_model (address_one_library_function lib) s2).
  Proof using.
    cbv zeta; destruct ls as [sf fstk], lib as [fid den]; cbn [snd] in Hfn.
    unfold address_one_library_function.
    eapply refine_mcfg_model_bind; [apply refine_mcfg_gread_same_g |].
    intros U1 s1' fv1 s2' fv2 _ (-> & -> & -> & -> & _).
    destruct fv2 as [[pt | | | | | | |] | |];
      lazymatch goal with
      | |- refine_prov _ _ (interp_mcfg_model (raise _) _) _ => apply refine_mcfg_raise_both
      | _ => idtac
      end.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
    apply refine_prov_ret;
      exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Hfn)))).
  Qed.

  Lemma map_monad_address_one_function_pair_sim
    (Rfn : @function_denotation (@ParamsV IP IPT) ->
           @function_denotation (@ParamsV IP IPT) -> Prop)
    (defs1 defs2 : list (definition dtyp (CFG.cfg dtyp)))
    (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hrel : Forall2
              (fun d1 d2 =>
                 dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
                 Rfn (denote_function d1) (denote_function d2))
              defs1 defs2) :
    let s1 := (σ1, (ls, g)) in
    let s2 := (σ2, (ls, g)) in
    refine_prov
      (fun U' '(s1', fns1) '(s2', fns2) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\
         Forall2 (fun '(z1, f1) '(z2, f2) => z1 = z2 /\ Rfn f1 f2) fns1 fns2)
      U
      (interp_mcfg_model (map_monad address_one_function defs1) s1)
      (interp_mcfg_model (map_monad address_one_function defs2) s2).
  Proof using.
    cbv zeta; induction Hrel as [| d1 d2 ds1 ds2 [Hnm Hfn] _ IH];
      cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret;
        exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (Forall2_nil _)))).
      - eapply refine_mcfg_model_bind;
        [exact (address_one_function_pair_sim Rfn d1 d2 U σ1 σ2 ls g Hnm Hfn) |].
      intros U1 s1' [z1 f1] s2' [z2 f2] _ (-> & -> & -> & <- & Hf).
      eapply refine_mcfg_model_bind; [exact IH |].
      intros U2 s1'' fns1 s2'' fns2 _ (-> & -> & -> & Hfns).
      eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret;
        exact (conj Logic.eq_refl
                 (conj Logic.eq_refl
                    (conj Logic.eq_refl
                       (Forall2_cons (z1, f1) (z1, f2) (conj Logic.eq_refl Hf) Hfns)))).
  Qed.

  Lemma map_monad_address_one_library_pair_sim
    (Rfn : @function_denotation (@ParamsV IP IPT) ->
           @function_denotation (@ParamsV IP IPT) -> Prop)
    (libs : list (function_id * @function_denotation (@ParamsV IP IPT)))
    (U : list N) (σ1 σ2 : state)
    (ls : @stack_frame (@ParamsV IP IPT) * stack) (g : @global_env (@ParamsV IP IPT))
    (Hrel : Forall (fun lib => Rfn (snd lib) (snd lib)) libs) :
    let s1 := (σ1, (ls, g)) in
    let s2 := (σ2, (ls, g)) in
    refine_prov
      (fun U' '(s1', fns1) '(s2', fns2) =>
         U' = U /\ s1' = s1 /\ s2' = s2 /\
         Forall2 (fun '(z1, f1) '(z2, f2) => z1 = z2 /\ Rfn f1 f2) fns1 fns2)
      U
      (interp_mcfg_model (map_monad address_one_library_function libs) s1)
      (interp_mcfg_model (map_monad address_one_library_function libs) s2).
  Proof using.
    cbv zeta; induction Hrel as [| lib rest Hfn _ IH];
      cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    - eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret;
        exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (Forall2_nil _)))).
    - eapply refine_mcfg_model_bind;
        [exact (address_one_library_pair_sim Rfn lib U σ1 σ2 ls g Hfn) |].
      intros U1 s1' [z1 f1] s2' [z2 f2] _ (-> & -> & -> & <- & Hf).
      eapply refine_mcfg_model_bind; [exact IH |].
      intros U2 s1'' fns1 s2'' fns2 _ (-> & -> & -> & Hfns).
      eapply refine_prov_obs_eq;
        [symmetry; apply interp_mcfg_model_ret | symmetry; apply interp_mcfg_model_ret |].
      apply refine_prov_ret;
        exact (conj Logic.eq_refl
                 (conj Logic.eq_refl
                    (conj Logic.eq_refl
                       (Forall2_cons (z1, f1) (z1, f2) (conj Logic.eq_refl Hf) Hfns)))).
  Qed.

  Lemma convert_bitcast_vec1_scalar_eq
    (dt : dtyp) (db : @dvalue_base (@ParamsV IP IPT))
    (bs : list (@memory_byte (@ParamsV IP IPT)))
    (Hsc : is_scalar_dtyp dt = true)
    (Hser : dvalue_to_memory_bytes dt (DVALUE_Base db) None = raise_ret bs) :
    @convert (@ParamsV IP IPT) CONV_Bitcast (DTYPE_Array true 1%N dt)
      (DVALUE_Array true [DVALUE_Base db]) dt =
    EOU_to_itree (memory_bytes_to_dvalue bs dt).
  Proof using.
    destruct (is_scalar_dtyp_inv dt Hsc) as (dtb & -> & _).
    unfold convert.
    rewrite vec1_neq_base, bit_sizeof_vec1_eq, dvalue_to_memory_bytes_vec1_eq, Hser.
    cbn; reflexivity.
  Qed.

  (** ** 3K. Parameterized CPS Coinduction ([m2r_paco] & [m2r_cps]) *)

  Definition Ans : Type :=
    Res (@dvalue (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT)).

  Definition top_ans_post : list N -> Ans -> Ans -> Prop :=
    fun _ '(_, r1) '(_, r2) => r1 = r2.

  Definition obs_clos
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (b1 b2 : itree ProvBotE Ans) : Prop :=
    exists a1 a2, a1 ≅ b1 /\ a2 ≅ b2 /\ r U a1 a2.

  Lemma obs_clos_eq
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (b1 b1' b2 b2' : itree ProvBotE Ans) :
    b1 ≅ b1' ->
    b2 ≅ b2' ->
    obs_clos r U b1 b2 ->
    obs_clos r U b1' b2'.
  Proof using.
    intros E1 E2 (a1 & a2 & Ea1 & Ea2 & Hr).
    exists a1, a2; split; [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hr]].
  Qed.

  Definition m2r_paco
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (t1 t2 : itree ProvBotE Ans) : Prop :=
    exists R : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop,
      (forall U' a1 a1' a2 a2', a1 ≅ a1' -> a2 ≅ a2' -> R U' a1 a2 -> R U' a1' a2') /\
      (forall U' a1 a2,
         R U' a1 a2 ->
         refine_prov_ top_ans_post
           (fun U'' b1 b2 => R U'' b1 b2 \/ obs_clos r U'' b1 b2) U' a1 a2) /\
      R U t1 t2.

  Lemma m2r_paco_obs_eq
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (t1 t1' t2 t2' : itree ProvBotE Ans) :
    t1 ≅ t1' ->
    t2 ≅ t2' ->
    m2r_paco r U t1 t2 ->
    m2r_paco r U t1' t2'.
  Proof using.
    intros E1 E2 (R & Heq & Hst & HR).
    exists R; exact (conj Heq (conj Hst (Heq U t1 t1' t2 t2' E1 E2 HR))).
  Qed.

  Lemma m2r_paco_mon
    (r1 r2 : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop) :
    (forall U a1 a2, r1 U a1 a2 -> r2 U a1 a2) ->
    forall U t1 t2, m2r_paco r1 U t1 t2 -> m2r_paco r2 U t1 t2.
  Proof using.
    intros Hle U t1 t2 (R & Heq & Hst & HR).
    exists R; split; [exact Heq | split; [| exact HR]].
    intros U' a1 a2 Ha.
    eapply refine_prov__mon; [exact (Hst U' a1 a2 Ha) |].
    intros U'' b1 b2 [Hb | (c1 & c2 & Ec1 & Ec2 & Hc)]; [left; exact Hb |].
    right; exists c1, c2; exact (conj Ec1 (conj Ec2 (Hle U'' c1 c2 Hc))).
  Qed.

  Lemma m2r_paco_to_refine_prov (U0 : list N) (t1_0 t2_0 : itree ProvBotE Ans) :
    m2r_paco (fun _ _ _ => False) U0 t1_0 t2_0 ->
    refine_prov top_ans_post U0 t1_0 t2_0.
  Proof using.
    intros (R & _ & Hst & HR0).
    assert (Hcore : forall U t1 t2, R U t1 t2 -> refine_prov top_ans_post U t1 t2).
    { pcofix CIH; intros U t1 t2 HR; pstep.
      eapply refine_prov__mon; [exact (Hst U t1 t2 HR) |].
      intros U' b1 b2 [Hb | (_ & _ & _ & _ & [])].
      right; apply CIH, Hb. }
    exact (Hcore U0 t1_0 t2_0 HR0).
  Qed.

  Lemma m2r_paco_fold
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (t1 t2 : itree ProvBotE Ans) :
    refine_prov_ top_ans_post
      (fun U' b1 b2 => m2r_paco r U' b1 b2 \/ obs_clos r U' b1 b2) U t1 t2 ->
    m2r_paco r U t1 t2.
  Proof using.
    intros H.
    set (R_fold := fun U' x1 x2 =>
                     m2r_paco r U' x1 x2 \/ (U' = U /\ t1 ≅ x1 /\ t2 ≅ x2)).
    exists R_fold; split; [| split].
    - intros U' a1 a1' a2 a2' E1 E2 [Ha | (-> & Et1 & Et2)].
      + left; exact (m2r_paco_obs_eq r U' a1 a1' a2 a2' E1 E2 Ha).
      + right; split; [reflexivity | split; etransitivity; eassumption].
    - intros U' a1 a2 [Ha | (-> & Et1 & Et2)].
      + destruct Ha as (R0 & Heq0 & Hst0 & HR0).
        eapply refine_prov__mon; [exact (Hst0 U' a1 a2 HR0) |].
        intros U'' b1 b2 [Hb | Hb];
          [left; left; exists R0; exact (conj Heq0 (conj Hst0 Hb)) | right; exact Hb].
      + eapply refine_prov__obs_eq with
          (r := fun U'' b1 b2 => R_fold U'' b1 b2 \/ obs_clos r U'' b1 b2);
          [| exact Et1 | exact Et2
           | eapply refine_prov__mon; [exact H | intros U'' b1 b2 [Hb | Hb]; [left; left; exact Hb | right; exact Hb]]].
        intros U'' x1 x1' x2 x2' Ex1 Ex2 [[Hx | (-> & E1 & E2)] | Hx].
        * left; left; exact (m2r_paco_obs_eq r U'' x1 x1' x2 x2' Ex1 Ex2 Hx).
        * left; right; split; [reflexivity | split; etransitivity; eassumption].
        * right; exact (obs_clos_eq r U'' x1 x1' x2 x2' Ex1 Ex2 Hx).
    - right; split; [reflexivity | split; reflexivity].
  Qed.

  Lemma m2r_paco_unfold
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (t1 t2 : itree ProvBotE Ans) :
    m2r_paco r U t1 t2 ->
    refine_prov_ top_ans_post
      (fun U' b1 b2 => m2r_paco r U' b1 b2 \/ obs_clos r U' b1 b2) U t1 t2.
  Proof using.
    intros (R & Heq & Hst & HR).
    eapply refine_prov__mon; [exact (Hst U t1 t2 HR) |].
    intros U' b1 b2 [Hb | Hb];
      [left; exists R; exact (conj Heq (conj Hst Hb)) | right; exact Hb].
  Qed.

  Lemma m2r_paco_acc
    (r0 l : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop) :
    (forall r,
       (forall U a1 a2, r0 U a1 a2 -> r U a1 a2) ->
       (forall U a1 a2, l U a1 a2 -> r U a1 a2) ->
       forall U a1 a2, l U a1 a2 -> m2r_paco r U a1 a2) ->
    forall U a1 a2, l U a1 a2 -> m2r_paco r0 U a1 a2.
  Proof using.
    intros HOBG.
    set (r_comb := fun U' y1 y2 => r0 U' y1 y2 \/ l U' y1 y2).
    pose proof (HOBG r_comb
                  (fun U' y1 y2 H => or_introl H)
                  (fun U' y1 y2 H => or_intror H)) as Hl_sub.
    set (R_union := m2r_paco r_comb).
    intros U a1 a2 Hl0.
    exists R_union; split; [exact (m2r_paco_obs_eq r_comb) | split; [| exact (Hl_sub U a1 a2 Hl0)]].
    intros U' x1 x2 (R & Heq & Hst & HR).
    eapply refine_prov__mon; [exact (Hst U' x1 x2 HR) |].
    intros U'' z1 z2 [HzR | (w1 & w2 & Ew1 & Ew2 & [Hzr0 | Hzl])].
    - left; exists R; exact (conj Heq (conj Hst HzR)).
    - right; exists w1, w2; exact (conj Ew1 (conj Ew2 Hzr0)).
    - left; exact (m2r_paco_obs_eq r_comb U'' w1 z1 w2 z2 Ew1 Ew2 (Hl_sub U'' w1 w2 Hzl)).
  Qed.

  Lemma m2r_paco_tau_both_r
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (m1 m2 t1 t2 : itree ProvBotE Ans) :
    Tau m1 ≅ t1 ->
    Tau m2 ≅ t2 ->
    r U m1 m2 ->
    m2r_paco r U t1 t2.
  Proof using.
    intros E1 E2 Hr.
    eapply m2r_paco_obs_eq; [exact E1 | exact E2 |].
    apply m2r_paco_fold, RP_Step; cbn.
    right; exists m1, m2; split; [reflexivity | split; [reflexivity | exact Hr]].
  Qed.

  Definition m2r_cps {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U : list N) (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2) : Prop :=
    forall (r' : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop),
      (forall U0 x1 x2, r U0 x1 x2 -> r' U0 x1 x2) ->
      forall (k1 : A1 -> itree ProvBotE Ans) (k2 : A2 -> itree ProvBotE Ans),
        (forall U' a1 a2, incl U U' -> RA U' a1 a2 -> m2r_paco r' U' (k1 a1) (k2 a2)) ->
        m2r_paco r' U (ITree.bind u1 k1) (ITree.bind u2 k2).

  Lemma m2r_cps_mon {A1 A2 : Type}
    (r1 r2 : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (Hle : forall U a1 a2, r1 U a1 a2 -> r2 U a1 a2)
    (U : list N) (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2) :
    m2r_cps r1 RA U u1 u2 ->
    m2r_cps r2 RA U u1 u2.
  Proof using.
    intros Hcps r' Hr' k1 k2 Hk.
    exact (Hcps r' (fun U0 x1 x2 H => Hr' U0 x1 x2 (Hle U0 x1 x2 H)) k1 k2 Hk).
  Qed.

  Lemma m2r_cps_obs_eq {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U : list N) (u1 u1' : itree ProvBotE A1) (u2 u2' : itree ProvBotE A2) :
    u1 ≅ u1' ->
    u2 ≅ u2' ->
    m2r_cps r RA U u1 u2 ->
    m2r_cps r RA U u1' u2'.
  Proof using.
    intros E1 E2 Hcps r' Hr' k1 k2 Hk.
    eapply m2r_paco_obs_eq;
      [eapply eq_itree_clo_bind with (UU := Logic.eq); [exact E1 | intros ? ? <-; reflexivity]
      | eapply eq_itree_clo_bind with (UU := Logic.eq); [exact E2 | intros ? ? <-; reflexivity]
      | exact (Hcps r' Hr' k1 k2 Hk)].
  Qed.

  Lemma m2r_cps_ret {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U : list N) (a1 : A1) (a2 : A2) :
    RA U a1 a2 ->
    m2r_cps r RA U (Ret a1) (Ret a2).
  Proof using.
    intros Hra r' _ k1 k2 Hk.
    eapply m2r_paco_obs_eq;
      [symmetry; apply Eqit.bind_ret_l
      | symmetry; apply Eqit.bind_ret_l
      | exact (Hk U a1 a2 (incl_refl U) Hra)].
  Qed.

  Lemma m2r_cps_bind {A1 A2 B1 B2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (RB : list N -> B1 -> B2 -> Prop)
    (U : list N)
    (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2)
    (f1 : A1 -> itree ProvBotE B1) (f2 : A2 -> itree ProvBotE B2) :
    m2r_cps r RA U u1 u2 ->
    (forall U1 a1 a2, incl U U1 -> RA U1 a1 a2 -> m2r_cps r RB U1 (f1 a1) (f2 a2)) ->
    m2r_cps r RB U (ITree.bind u1 f1) (ITree.bind u2 f2).
  Proof using.
    intros Hu Hf r' Hr' k1 k2 Hk.
    eapply m2r_paco_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    eapply (Hu r' Hr'); intros U1 a1 a2 Hinc1 Ha.
    eapply (Hf U1 a1 a2 Hinc1 Ha r' Hr'); intros U2 b1 b2 Hinc2 Hb.
    exact (Hk U2 b1 b2 (incl_tran Hinc1 Hinc2) Hb).
  Qed.

  Lemma m2r_cps_weaken {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA RB : list N -> A1 -> A2 -> Prop)
    (U : list N) (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2) :
    m2r_cps r RA U u1 u2 ->
    (forall U' a1 a2, incl U U' -> RA U' a1 a2 -> RB U' a1 a2) ->
    m2r_cps r RB U u1 u2.
  Proof using.
    intros Hu Hw r' Hr' k1 k2 Hk.
    eapply (Hu r' Hr'); intros U' a1 a2 Hinc Ha.
    exact (Hk U' a1 a2 Hinc (Hw U' a1 a2 Hinc Ha)).
  Qed.

  Lemma m2r_cps_to_paco
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (t1 t2 : itree ProvBotE Ans) :
    m2r_cps r top_ans_post U t1 t2 ->
    m2r_paco r U t1 t2.
  Proof using.
    intros Hcps.
    eapply m2r_paco_obs_eq; [apply Eqit.bind_ret_r | apply Eqit.bind_ret_r |].
    eapply (Hcps r (fun _ _ _ H => H) (fun x => Ret x) (fun x => Ret x)).
    intros U' [s1 v1] [s2 v2] _ Heq.
    apply m2r_paco_fold, RP_Step; exact Heq.
  Qed.

  Lemma refine_prov_to_cps {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U0 : list N) (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2) :
    refine_prov RA U0 u1 u2 ->
    m2r_cps r RA U0 u1 u2.
  Proof using.
    intros Hu0 r0 _ k1 k2 Hk0.
    set (l := fun U (t1 t2 : itree ProvBotE Ans) =>
                exists u1' u2',
                  ITree.bind u1' k1 ≅ t1 /\
                  ITree.bind u2' k2 ≅ t2 /\
                  incl U0 U /\
                  refine_prov RA U u1' u2').
    eapply (m2r_paco_acc r0 l);
      [| exists u1, u2; split; [reflexivity | split; [reflexivity | exact (conj (incl_refl U0) Hu0)]]].
    intros r' Hr0 Hl U t1 t2 (u1' & u2' & E1 & E2 & Hinc & Hu).
    eapply m2r_paco_obs_eq; [exact E1 | exact E2 |]; clear t1 t2 E1 E2.
    punfold Hu; revert Hinc.
    induction Hu as [U u1' u2' Hstep | U u1' m1 u2' Hu1 _ IH | U u1' u2' m2 Hu2 _ IH];
      intros Hinc.
    - unfold rp_step_body in Hstep.
      destruct (observe u1') as [a1 | m1 | X1 e1 h1] eqn:Hou1.
      + destruct (observe u2') as [a2 | m2 | X2 e2 h2] eqn:Hou2; try contradiction.
        eapply m2r_paco_obs_eq;
          [symmetry; rewrite (itree_eta u1'), Hou1, Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite (itree_eta u2'), Hou2, Eqit.bind_ret_l; reflexivity
          | exact (m2r_paco_mon r0 r' Hr0 U (k1 a1) (k2 a2) (Hk0 U a1 a2 Hinc Hstep))].
      + destruct (observe u2') as [a2 | m2 | X2 e2 h2] eqn:Hou2; try contradiction.
        pclearbot; apply m2r_paco_fold, RP_Step; unfold rp_step_body.
        rewrite (observe_bind u1' k1), Hou1, (observe_bind u2' k2), Hou2.
        right; exists (ITree.bind m1 k1), (ITree.bind m2 k2);
          split; [reflexivity | split; [reflexivity |]].
        apply Hl; exists m1, m2;
          split; [reflexivity | split; [reflexivity | exact (conj Hinc Hstep)]].
      + destruct Hstep as [Hub | [Hleft | Hboth]].
        * apply m2r_paco_fold, RP_Step; unfold rp_step_body;
            rewrite (observe_bind u1' k1), Hou1; left; exact Hub.
        * apply m2r_paco_fold, RP_Step; unfold rp_step_body;
            rewrite (observe_bind u1' k1), Hou1; right; left.
          destruct e1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hleft p Hp); pclearbot.
          right; exists (ITree.bind (h1 p) k1), (ITree.bind u2' k2);
            split; [reflexivity | split; [reflexivity |]].
          apply Hl; exists (h1 p), u2';
            split; [reflexivity | split; [reflexivity |]].
          split; [intros z Hz; right; apply Hinc, Hz | exact Hleft].
        * destruct (observe u2') as [a2 | m2 | X2 e2 h2] eqn:Hou2; try contradiction.
          apply m2r_paco_fold, RP_Step; unfold rp_step_body.
          rewrite (observe_bind u1' k1), Hou1, (observe_bind u2' k2), Hou2; right; right.
          destruct e1 as [p1 | b1], e2 as [p2 | b2]; cbn in *; try contradiction.
          -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
             right; exists (ITree.bind (h1 p) k1), (ITree.bind (h2 p) k2);
               split; [reflexivity | split; [reflexivity |]].
             apply Hl; exists (h1 p), (h2 p);
               split; [reflexivity | split; [reflexivity |]].
             split; [intros z Hz; right; apply Hinc, Hz | exact Hboth].
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
             right; exists (ITree.bind (h1 a1) k1), (ITree.bind (h2 a2) k2);
               split; [reflexivity | split; [reflexivity |]].
             apply Hl; exists (h1 a1), (h2 a2);
               split; [reflexivity | split; [reflexivity |]].
             split; [intros z Hz; apply in_app_iff; right; apply Hinc, Hz | exact HA].
    - specialize (IH Hinc); apply m2r_paco_unfold in IH; apply m2r_paco_fold.
      eapply RP_TauL; [rewrite (observe_bind u1' k1), Hu1; reflexivity | exact IH].
    - specialize (IH Hinc); apply m2r_paco_unfold in IH; apply m2r_paco_fold.
      eapply RP_TauR; [rewrite (observe_bind u2' k2), Hu2; reflexivity | exact IH].
  Qed.

  Lemma m2r_cps_cfg_bind {A1 A2 B1 B2}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RA : list N -> Res A1 -> Res A2 -> Prop)
    (RB : list N -> Res B1 -> Res B2 -> Prop)
    (U : list N)
    (t1 : @CFGtop (@ParamsV IP IPT) A1) (t2 : @CFGtop (@ParamsV IP IPT) A2)
    (k1 : A1 -> @CFGtop (@ParamsV IP IPT) B1) (k2 : A2 -> @CFGtop (@ParamsV IP IPT) B2)
    (s1 s2 : FusedS) :
    m2r_cps r RA U (interp_cfg_model ctx1 t1 s1) (interp_cfg_model ctx2 t2 s2) ->
    (forall U' s1' a1 s2' a2,
       incl U U' ->
       RA U' (s1', a1) (s2', a2) ->
       m2r_cps r RB U'
         (interp_cfg_model ctx1 (k1 a1) s1')
         (interp_cfg_model ctx2 (k2 a2) s2')) ->
    m2r_cps r RB U
      (interp_cfg_model ctx1 (ITree.bind t1 k1) s1)
      (interp_cfg_model ctx2 (ITree.bind t2 k2) s2).
  Proof using.
    intros Ht Hk.
    eapply m2r_cps_obs_eq;
      [symmetry; apply interp_cfg_model_bind | symmetry; apply interp_cfg_model_bind |].
    eapply m2r_cps_bind; [exact Ht |].
    intros U' [s1' a1] [s2' a2] Hinc Ha; exact (Hk U' s1' a1 s2' a2 Hinc Ha).
  Qed.

  Lemma m2r_cps_cfg_exc_bind {A1 A2 B1 B2}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (RB   : list N -> FusedS -> FusedS -> B1 -> B2 -> Prop)
    (U : list N)
    (t1 : @CFGtop (@ParamsV IP IPT) A1) (t2 : @CFGtop (@ParamsV IP IPT) A2)
    (k1 : A1 -> @CFGtop (@ParamsV IP IPT) B1) (k2 : A2 -> @CFGtop (@ParamsV IP IPT) B2)
    (s1 s2 : FusedS) :
    m2r_cps r (exc_post RExc RA) U
      (interp_cfg_exc ctx1 t1 s1) (interp_cfg_exc ctx2 t2 s2) ->
    (forall U' s1' a1 s2' a2,
       incl U U' ->
       RA U' s1' s2' a1 a2 ->
       m2r_cps r (exc_post RExc RB) U'
         (interp_cfg_exc ctx1 (k1 a1) s1')
         (interp_cfg_exc ctx2 (k2 a2) s2')) ->
    m2r_cps r (exc_post RExc RB) U
      (interp_cfg_exc ctx1 (ITree.bind t1 k1) s1)
      (interp_cfg_exc ctx2 (ITree.bind t2 k2) s2).
  Proof using.
    intros Ht Hk.
    eapply m2r_cps_obs_eq;
      [symmetry; apply interp_cfg_exc_bind | symmetry; apply interp_cfg_exc_bind |].
    eapply m2r_cps_bind; [exact Ht |].
    intros U' [s1' [x1 | a1]] [s2' [x2 | a2]] Hinc Hres; try contradiction.
    - apply m2r_cps_ret; exact Hres.
    - exact (Hk U' s1' a1 s2' a2 Hinc Hres).
  Qed.

  Lemma m2r_cps_cfg_exc_iter {I1 I2 R1 R2}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
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
               m2r_cps r
                 (exc_post RExc
                    (fun U' s1' s2' lr1 lr2 =>
                       match lr1, lr2 with
                       | inl j1, inl j2 => RI U' s1' s2' j1 j2
                       | inr v1, inr v2 => RRet U' s1' s2' v1 v2
                       | _, _ => False
                       end))
                 U
                 (interp_cfg_exc ctx1 (b1 i1) s1)
                 (interp_cfg_exc ctx2 (b2 i2) s2)) :
    forall s1 s2 i1 i2,
      RI U0 s1 s2 i1 i2 ->
      m2r_cps r (exc_post RExc RRet) U0
        (interp_cfg_exc ctx1 (ITree.iter b1 i1) s1)
        (interp_cfg_exc ctx2 (ITree.iter b2 i2) s2).
  Proof using.
    set (step_k1 := fun '(s', res) =>
                      match res with
                      | inl x => Ret (s', inl x)
                      | inr (inl j) => Tau (interp_cfg_exc ctx1 (ITree.iter b1 j) s')
                      | inr (inr v) => Ret (s', inr v)
                      end : itree ProvBotE (Res (@exc (@ParamsV IP IPT) + R1))).
    set (step_k2 := fun '(s', res) =>
                      match res with
                      | inl x => Ret (s', inl x)
                      | inr (inl j) => Tau (interp_cfg_exc ctx2 (ITree.iter b2 j) s')
                      | inr (inr v) => Ret (s', inr v)
                      end : itree ProvBotE (Res (@exc (@ParamsV IP IPT) + R2))).
    assert (Hunf1 : forall s i,
              interp_cfg_exc ctx1 (ITree.iter b1 i) s ≅
              ITree.bind (interp_cfg_exc ctx1 (b1 i) s) step_k1).
    { intros s i.
      rewrite (interp_cfg_exc_obs_eq ctx1 _ _ s (unfold_iter b1 i)), interp_cfg_exc_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' [x | [j | v]]] _ <-; cbn [step_k1];
        [reflexivity | apply interp_cfg_exc_tau | apply interp_cfg_exc_ret]. }
    assert (Hunf2 : forall s i,
              interp_cfg_exc ctx2 (ITree.iter b2 i) s ≅
              ITree.bind (interp_cfg_exc ctx2 (b2 i) s) step_k2).
    { intros s i.
      rewrite (interp_cfg_exc_obs_eq ctx2 _ _ s (unfold_iter b2 i)), interp_cfg_exc_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' [x | [j | v]]] _ <-; cbn [step_k2];
        [reflexivity | apply interp_cfg_exc_tau | apply interp_cfg_exc_ret]. }
    intros s1_0 s2_0 i1_0 i2_0 Hinit r0 Hr k_out1 k_out2 Hk_out.
    set (l_it := fun U (t1 t2 : itree ProvBotE Ans) =>
                   exists s1 s2 i1 i2,
                     ITree.bind (interp_cfg_exc ctx1 (ITree.iter b1 i1) s1) k_out1 ≅ t1 /\
                     ITree.bind (interp_cfg_exc ctx2 (ITree.iter b2 i2) s2) k_out2 ≅ t2 /\
                     incl U0 U /\
                     RI U s1 s2 i1 i2).
    eapply (m2r_paco_acc r0 l_it);
      [| exists s1_0, s2_0, i1_0, i2_0;
         split; [reflexivity | split; [reflexivity | exact (conj (incl_refl U0) Hinit)]]].
    intros r' Hr0 Hl U t1 t2 (s1 & s2 & i1 & i2 & E1 & E2 & Hinc & Hri).
    eapply m2r_paco_obs_eq; [exact E1 | exact E2 |]; clear t1 t2 E1 E2.
    assert (Eb1 : ITree.bind (interp_cfg_exc ctx1 (b1 i1) s1)
                    (fun x => ITree.bind (step_k1 x) k_out1) ≅
                  ITree.bind (interp_cfg_exc ctx1 (ITree.iter b1 i1) s1) k_out1).
    { symmetry; rewrite <- Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [apply Hunf1 | intros ? ? <-; reflexivity]. }
    assert (Eb2 : ITree.bind (interp_cfg_exc ctx2 (b2 i2) s2)
                    (fun x => ITree.bind (step_k2 x) k_out2) ≅
                  ITree.bind (interp_cfg_exc ctx2 (ITree.iter b2 i2) s2) k_out2).
    { symmetry; rewrite <- Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [apply Hunf2 | intros ? ? <-; reflexivity]. }
    eapply m2r_paco_obs_eq; [exact Eb1 | exact Eb2 |].
    eapply (Hbody U s1 s2 i1 i2 Hinc Hri r' (fun Ua x1 x2 H => Hr0 Ua x1 x2 (Hr Ua x1 x2 H))).
    intros U' [s1' res1] [s2' res2] Hinc' Hpost.
    destruct res1 as [x1 | [j1 | v1]], res2 as [x2 | [j2 | v2]]; cbn in Hpost; try contradiction.
    - eapply m2r_paco_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      exact (m2r_paco_mon r0 r' Hr0 U' _ _ (Hk_out U' (s1', inl x1) (s2', inl x2) (incl_tran Hinc Hinc') Hpost)).
    - eapply m2r_paco_tau_both_r;
        [symmetry; apply Eqit.bind_tau | symmetry; apply Eqit.bind_tau |].
      apply Hl; exists s1', s2', j1, j2;
        split; [reflexivity | split; [reflexivity | exact (conj (incl_tran Hinc Hinc') Hpost)]].
    - eapply m2r_paco_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      exact (m2r_paco_mon r0 r' Hr0 U' _ _ (Hk_out U' (s1', inr v1) (s2', inr v2) (incl_tran Hinc Hinc') Hpost)).
  Qed.

  Lemma of_list_lookup_pair
    (Rfn : @function_denotation (@ParamsV IP IPT) ->
           @function_denotation (@ParamsV IP IPT) -> Prop)
    (l1 l2 : list (Z * @function_denotation (@ParamsV IP IPT)))
    (Hl : Forall2 (fun '(k1, f1) '(k2, f2) => k1 = k2 /\ Rfn f1 f2) l1 l2) :
    forall z,
      option_rel Rfn
        (lookup z (IntMaps.IP.of_list l1))
        (lookup z (IntMaps.IP.of_list l2)).
  Proof using.
    induction Hl as [| [k1 f1] [k2 f2] l1' l2' [<- Hf] _ IH]; intros z.
    - cbn; constructor.
    - cbn [IntMaps.IP.of_list fold_right]; unfold IntMaps.IP.uncurry, lookup; cbn [fst snd].
      destruct (Z.eq_dec k1 z) as [<- | Hne].
      + rewrite !IntMaps.IP.F.add_eq_o by reflexivity; constructor; exact Hf.
      + rewrite !IntMaps.IP.F.add_neq_o by exact Hne; apply IH.
  Qed.

  Lemma eq_itree_bind_congr_l {E : Type -> Type} {A B : Type}
    {t1 t2 : itree E A} {k : A -> itree E B} (H : t1 ≅ t2) :
    ITree.bind t1 k ≅ ITree.bind t2 k.
  Proof using.
    eapply eq_itree_clo_bind with (UU := Logic.eq);
      [exact H | intros ? ? <-; reflexivity].
  Qed.

  Lemma interp_cfg_exc_call
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (cc : cconv) (fv : @dvalue (@ParamsV IP IPT))
    (vs : list (@dvalue (@ParamsV IP IPT))) (s : FusedS) :
    interp_cfg_exc ctx (call dt cc fv vs) s ≅
    Tau (ITree.bind
           (interp_cfg_model ctx (mrec_ctx ctx _ (Call dt cc fv vs)) s)
           (fun '(s', y) => Tau (Ret (s', inr y)))).
  Proof using.
    assert (Ecall : call dt cc fv vs ≅ ITree.trigger (inl1 (Call dt cc fv vs) : @CFGEtop (@ParamsV IP IPT) _)).
    { unfold call, trigger, ITree.trigger;
        cbn [subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun];
        reflexivity. }
    rewrite (interp_cfg_exc_obs_eq ctx _ _ s Ecall).
    rewrite interp_cfg_exc_trigger_non_exc; [| reflexivity].
    rewrite <- (eq_itree_bind_congr_l (interp_cfg_model_obs_eq ctx _ _ s Ecall)).
    rewrite (eq_itree_bind_congr_l (interp_cfg_model_call ctx dt cc fv vs s)).
    apply Eqit.bind_tau.
  Qed.

  Lemma m2r_cps_call_exc
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (cc : cconv) (fv : @dvalue (@ParamsV IP IPT))
    (vs : list (@dvalue (@ParamsV IP IPT)))
    (U : list N) (s1 s2 : FusedS)
    (k_out1 k_out2 : Res (@exc (@ParamsV IP IPT) +
                          (@dvalue (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT))) ->
                     itree ProvBotE Ans)
    (Hr_call :
       r U
         (ITree.bind
            (interp_cfg_model ctx1 (mrec_ctx ctx1 _ (Call dt cc fv vs)) s1)
            (fun '(s1', y1) => Tau (k_out1 (s1', inr y1))))
         (ITree.bind
            (interp_cfg_model ctx2 (mrec_ctx ctx2 _ (Call dt cc fv vs)) s2)
            (fun '(s2', y2) => Tau (k_out2 (s2', inr y2))))) :
    m2r_paco r U
      (ITree.bind (interp_cfg_exc ctx1 (call dt cc fv vs) s1) k_out1)
      (ITree.bind (interp_cfg_exc ctx2 (call dt cc fv vs) s2) k_out2).
  Proof using.
    assert (E1 :
      Tau (ITree.bind
             (interp_cfg_model ctx1 (mrec_ctx ctx1 _ (Call dt cc fv vs)) s1)
             (fun '(s1', y1) => Tau (k_out1 (s1', inr y1)))) ≅
      ITree.bind (interp_cfg_exc ctx1 (call dt cc fv vs) s1) k_out1).
    { symmetry.
      rewrite (eq_itree_bind_congr_l (interp_cfg_exc_call ctx1 dt cc fv vs s1)).
      rewrite Eqit.bind_tau, Eqit.bind_bind.
      apply eqit_Tau.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s1' y1] _ <-; rewrite Eqit.bind_tau, Eqit.bind_ret_l; reflexivity. }
    assert (E2 :
      Tau (ITree.bind
             (interp_cfg_model ctx2 (mrec_ctx ctx2 _ (Call dt cc fv vs)) s2)
             (fun '(s2', y2) => Tau (k_out2 (s2', inr y2)))) ≅
      ITree.bind (interp_cfg_exc ctx2 (call dt cc fv vs) s2) k_out2).
    { symmetry.
      rewrite (eq_itree_bind_congr_l (interp_cfg_exc_call ctx2 dt cc fv vs s2)).
      rewrite Eqit.bind_tau, Eqit.bind_bind.
      apply eqit_Tau.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s2' y2] _ <-; rewrite Eqit.bind_tau, Eqit.bind_ret_l; reflexivity. }
    exact (m2r_paco_tau_both_r r U _ _ _ _ E1 E2 Hr_call).
  Qed.

  (** ** 3L. Call-Frame Helpers & Promoted SSA Instruction Simulations *)

  Lemma top_frame_unprom_frame_eq
    (fs0 : @Framestack (@ParamsV IP IPT)) (G : list ghost_slot)
    (ms1 ms2 : @Memory_stack (@ParamsV IP IPT)) :
    Memory_stack_frame_stack ms1 = Memory_stack_frame_stack ms2 ->
    top_frame_unprom_from fs0 G ms1 ->
    top_frame_unprom_from fs0 G ms2.
  Proof using.
    intros Heq (f & Hfs & Hout).
    exists f; split; [rewrite <- Heq; exact Hfs | exact Hout].
  Qed.

  Lemma top_frame_prom_frame_eq
    (fs0 : @Framestack (@ParamsV IP IPT)) (gs : ghost_slot) (G : list ghost_slot)
    (ms1 ms2 : @Memory_stack (@ParamsV IP IPT)) :
    Memory_stack_frame_stack ms1 = Memory_stack_frame_stack ms2 ->
    top_frame_prom_from fs0 gs G ms1 ->
    top_frame_prom_from fs0 gs G ms2.
  Proof using.
    intros Heq (f & Hfs & Hin & Hout).
    exists f; split; [rewrite <- Heq; exact Hfs | split; [exact Hin | exact Hout]].
  Qed.

  Lemma m2r_combine_lists_varargs_fst_in {A B : Type}
    (xs : list A) (ys : list B) (bs : list (A * B)) (vs : list B) :
    combine_lists_varargs xs ys = raise_ret (bs, vs) ->
    forall x, In x (List.map fst bs) -> In x xs.
  Proof using.
    revert ys bs vs; induction xs as [| x0 xs' IH]; intros ys bs vs Hcomb x Hin;
      cbn [combine_lists_varargs] in Hcomb.
    - destruct ys; inversion Hcomb; subst; contradiction.
    - destruct ys as [| y0 ys']; [discriminate Hcomb |].
      apply EOU_bind_ret_inv in Hcomb as ([l vargs] & Hrec & Heq).
      inversion Heq; subst bs vs; clear Heq.
      cbn [List.map fst In] in Hin; destruct Hin as [<- | Hin].
      + left; reflexivity.
      + right; eapply IH; eassumption.
  Qed.

  Lemma init_local_env_lookup_none_not_in
    (bs : list (local_id * @dvalue (@ParamsV IP IPT))) (q : local_id) :
    ~ In q (List.map fst bs) ->
    Maps.lookup q (init_local_env bs) = None.
  Proof using.
    induction bs as [| [k dv] rest IH]; intros Hnin; cbn [init_local_env List.fold_right].
    - cbn [Maps.lookup Maps.empty Map_rmap]; apply RMF.F.empty_o.
    - cbn [List.map fst In] in Hnin.
      destruct (RawIDOrd.eq_dec k q) as [-> | Hne].
      + exfalso; apply Hnin; left; reflexivity.
      + cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by exact Hne.
        apply IH; intros Hin; apply Hnin; right; exact Hin.
  Qed.

  Lemma safe_locals_env_init_args
    (P_safe : list N) (fargs : list local_id) (bks : ocfg dtyp)
    (safe_sub : list local_id)
    (args : list (@dvalue (@ParamsV IP IPT)))
    (bs : list (local_id * @dvalue (@ParamsV IP IPT)))
    (vs : list (@dvalue (@ParamsV IP IPT))) :
    combine_lists_varargs fargs args = raise_ret (bs, vs) ->
    (forall q,
       In q safe_sub ->
       In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks)) ->
    (forall q, In q safe_sub -> Maps.lookup q (init_local_env bs) = None) /\
    safe_locals_env P_safe safe_sub (init_local_env bs).
  Proof using.
    intros Hcomb Hsub.
    assert (Hnone : forall q, In q safe_sub -> Maps.lookup q (init_local_env bs) = None).
    { intros q Hq.
      apply init_local_env_lookup_none_not_in.
      intros Hin_bs.
      eapply (unique_alloca_not_in_fargs fargs bks q (Hsub q Hq)).
      eapply m2r_combine_lists_varargs_fst_in; eassumption. }
    split; [exact Hnone |].
    intros q v Hq Hlk; rewrite (Hnone q Hq) in Hlk; discriminate Hlk.
  Qed.

  Lemma safe_locals_env_add_other
    (P_safe : list N) (safe_sub : list local_id)
    (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (env : @local_env (@ParamsV IP IPT)) :
    ~ In x safe_sub ->
    safe_locals_env P_safe safe_sub env ->
    safe_locals_env P_safe safe_sub (Maps.add x v env).
  Proof using.
    intros Hnin Henv q v0 Hq Hlk.
    destruct (RawIDOrd.eq_dec x q) as [-> | Hne]; [contradiction |].
    cbn [Maps.lookup Maps.add Map_rmap] in Hlk; rewrite RMF.F.add_neq_o in Hlk by exact Hne.
    exact (Henv q v0 Hq Hlk).
  Qed.

  Lemma safe_locals_env_add_safe
    (P_safe : list N) (safe_sub : list local_id)
    (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (env : @local_env (@ParamsV IP IPT)) :
    is_safe_ptr_dvalue P_safe v ->
    safe_locals_env P_safe safe_sub env ->
    safe_locals_env P_safe safe_sub (Maps.add x v env).
  Proof using.
    intros Hv Henv q v0 Hq Hlk.
    destruct (RawIDOrd.eq_dec x q) as [<- | Hne].
    - cbn [Maps.lookup Maps.add Map_rmap] in Hlk; rewrite RMF.F.add_eq_o in Hlk by reflexivity; inversion Hlk; subst v0; exact Hv.
    - cbn [Maps.lookup Maps.add Map_rmap] in Hlk; rewrite RMF.F.add_neq_o in Hlk by exact Hne; exact (Henv q v0 Hq Hlk).
  Qed.

  Lemma push_call_frame_stage1_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (df1 df2 : definition dtyp (CFG.cfg dtyp))
    (args : list (@dvalue (@ParamsV IP IPT)))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hargs : df_args df1 = df_args df2)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (fun U' '(s1', varg1) '(s2', varg2) =>
         exists pr_va bs vs σ1' σ2',
           ~ In pr_va U /\
           U' = pr_va :: U /\
           varg1 = varg2 /\
           combine_lists_varargs (df_args df1) args = raise_ret (bs, vs) /\
           s1' = (σ1', (({| stack_vars := init_local_env bs;
                            stack_exc  := None;
                            stack_loc  := Some ""%string |}, sf1 :: fstk1), g)) /\
           s2' = (σ2', (({| stack_vars := init_local_env bs;
                            stack_exc  := None;
                            stack_loc  := Some ""%string |}, sf2 :: fstk2), g)) /\
           stage1_mem_inv (pr_va :: U) (pr_va :: P_unprom) G σ1' σ2' /\
           top_frame_unprom_from
             (Memory_stack_frame_stack (state_memory_stack σ2)) G
             (state_memory_stack σ2'))
      U
      (interp_cfg_model ctx1 (push_call_frame df1 args) (σ1, ((sf1, fstk1), g)))
      (interp_cfg_model ctx2 (push_call_frame df2 args) (σ2, ((sf2, fstk2), g))).
  Proof using.
    unfold push_call_frame; rewrite <- Hargs;
      cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    eapply refine_cfg_model_bind with
      (RA := fun U' '(s1', p1) '(s2', p2) =>
               U' = U /\
               s1' = (σ1, ((sf1, fstk1), g)) /\
               s2' = (σ2, ((sf2, fstk2), g)) /\
               p1 = p2 /\
               combine_lists_varargs (df_args df1) args = raise_ret p1).
    - destruct (combine_lists_varargs (df_args df1) args)
        as [msg | msg | msg | [bs vs]] eqn:Ecomb; cbn [EOU_to_itree].
      + apply refine_cfg_raise_both.
      + apply refine_cfg_raiseOOM_l.
      + apply refine_cfg_raiseUB_l.
      + eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
        apply refine_prov_ret;
          exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
    - intros U0 s1_0 [bs vs] s2_0 _ _ (-> & -> & -> & <- & Ecomb); cbn beta iota.
      eapply refine_cfg_model_bind with
        (RA := fun U' '(s1', d1) '(s2', d2) =>
                 U' = U /\
                 s1' = (σ1, ((sf1, fstk1), g)) /\
                 s2' = (σ2, ((sf2, fstk2), g)) /\
                 d1 = d2).
      + eapply refine_cfg_EOU; [apply refine_EOU_refl |].
        intros d1 d2 <-;
          exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
      + intros U0' s1_0' dts s2_0' _ _ (-> & -> & -> & <-).
        eapply refine_cfg_model_bind with
          (RA := fun U' '(s1', _) '(s2', _) =>
                   exists σ1_mp σ2_mp,
                     U' = U /\
                     s1' = (σ1_mp, ((sf1, fstk1), g)) /\
                     s2' = (σ2_mp, ((sf2, fstk2), g)) /\
                     stage1_mem_inv U P_unprom G σ1_mp σ2_mp /\
                     top_frame_unprom_from
                       (Memory_stack_frame_stack (state_memory_stack σ2)) G
                       (state_memory_stack σ2_mp)).
        * unfold mem_push, Subevent.trigger; try unfold trigger_cast.
          apply refine_cfg_memory_event.
          eapply refine_prov_weaken;
            [exact (stage1_mempush U P_unprom G σ1 σ2 Hinv) |].
          intros U1 [σ1_mp []] [σ2_mp []] (-> & _ & _ & Hinv_mp & Htf_mp).
          exists σ1_mp, σ2_mp;
            exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Hinv_mp Htf_mp)))).
        * intros U1 s1_1 _ s2_1 _ _ (σ1_mp & σ2_mp & -> & -> & -> & Hinv_mp & Htf_mp).
          eapply refine_cfg_model_bind with
            (RA := fun U' '(s1', _) '(s2', _) =>
                     U' = U /\
                     s1' = (σ1_mp, (({| stack_vars := init_local_env bs;
                                         stack_exc  := None;
                                         stack_loc  := Some ""%string |}, sf1 :: fstk1), g)) /\
                     s2' = (σ2_mp, (({| stack_vars := init_local_env bs;
                                         stack_exc  := None;
                                         stack_loc  := Some ""%string |}, sf2 :: fstk2), g))).
          -- eapply refine_prov_tau_star_l; [apply tau_star_cfg_stack_push |].
             eapply refine_prov_tau_star_r; [apply tau_star_cfg_stack_push |].
             apply refine_prov_ret;
               exact (conj (Logic.eq_refl U) (conj Logic.eq_refl Logic.eq_refl)).
          -- intros U2 s1_sp _ s2_sp _ _ (-> & -> & ->).
             eapply refine_cfg_model_bind with
               (RA := fun U' '(s1', va1) '(s2', va2) =>
                        exists pr_va ptrs_va σ1_al σ2_al,
                          ~ In pr_va U /\
                          U' = pr_va :: U /\
                          va1 = va2 /\
                          is_safe_ptr_dvalue (pr_va :: P_unprom) va1 /\
                          stage1_mem_inv (pr_va :: U) (pr_va :: P_unprom) G σ1_al σ2_al /\
                          (forall z, In z (List.map ptr_to_int ptrs_va) -> forall gs, In gs G -> ~ gs_in_range gs z) /\
                          Memory_stack_frame_stack (state_memory_stack σ2_al) =
                            Memory_stack_frame_stack (add_all_to_frame ptrs_va (state_memory_stack σ2_mp)) /\
                          s1' = (σ1_al, (({| stack_vars := init_local_env bs;
                                             stack_exc  := None;
                                             stack_loc  := Some ""%string |}, sf1 :: fstk1), g)) /\
                          s2' = (σ2_al, (({| stack_vars := init_local_env bs;
                                             stack_exc  := None;
                                             stack_loc  := Some ""%string |}, sf2 :: fstk2), g))).
             ++ unfold alloca, Subevent.trigger; try unfold trigger_cast.
                apply refine_cfg_memory_event.
                eapply refine_prov_weaken;
                  [exact (stage1_alloca_unprom (DTYPE_Struct true dts) 1%N None
                            U P_unprom G σ1_mp σ2_mp Hinv_mp) |].
                intros U3 [σ1_al va1] [σ2_al va2]
                  (pr_va & ptrs_va & Hnin_va & -> & <- & Hsafe_va & Hinv_al & Hdisj_va & Hfs_al).
                exists pr_va, ptrs_va, σ1_al, σ2_al;
                  exact (conj Hnin_va (conj Logic.eq_refl (conj Logic.eq_refl
                           (conj Hsafe_va (conj Hinv_al (conj Hdisj_va
                             (conj Hfs_al (conj Logic.eq_refl Logic.eq_refl)))))))).
             ++ intros U3 s1_3 va1 s2_3 _ _
                  (pr_va & ptrs_va & σ1_al & σ2_al & Hnin_va & -> & <- &
                   Hsafe_va & Hinv_al & Hdisj_va & Hfs_al & -> & ->).
                assert (Htf_al :
                          top_frame_unprom_from
                            (Memory_stack_frame_stack (state_memory_stack σ2)) G
                            (state_memory_stack σ2_al)).
                { eapply top_frame_unprom_frame_eq; [symmetry; exact Hfs_al |].
                  exact (top_frame_unprom_add_ptrs _ G ptrs_va _ Htf_mp Hdisj_va). }
                eapply refine_cfg_model_bind with
                  (RA := fun U' '(s1', _) '(s2', _) =>
                           exists σ1_st σ2_st,
                             U' = pr_va :: U /\
                             stage1_mem_inv (pr_va :: U) (pr_va :: P_unprom) G σ1_st σ2_st /\
                             Memory_stack_frame_stack (state_memory_stack σ2_st) =
                               Memory_stack_frame_stack (state_memory_stack σ2_al) /\
                             s1' = (σ1_st, (({| stack_vars := init_local_env bs;
                                                stack_exc  := None;
                                                stack_loc  := Some ""%string |}, sf1 :: fstk1), g)) /\
                             s2' = (σ2_st, (({| stack_vars := init_local_env bs;
                                                stack_exc  := None;
                                                stack_loc  := Some ""%string |}, sf2 :: fstk2), g))).
                ** unfold store, Subevent.trigger; try unfold trigger_cast.
                   apply refine_cfg_memory_event.
                   eapply refine_prov_weaken;
                     [exact (stage1_store_unprom (DTYPE_Struct true dts) va1
                               (DVALUE_Struct true vs)
                               (pr_va :: U) (pr_va :: P_unprom) G σ1_al σ2_al Hinv_al Hsafe_va) |].
                   intros U4 [σ1_st []] [σ2_st []] (-> & _ & _ & Hinv_st & Hfs_st).
                   exists σ1_st, σ2_st;
                     exact (conj Logic.eq_refl (conj Hinv_st (conj Hfs_st (conj Logic.eq_refl Logic.eq_refl)))).
                ** intros U4 s1_4 _ s2_4 _ _ (σ1_st & σ2_st & -> & Hinv_st & Hfs_st & -> & ->).
                   assert (Htf_st :
                             top_frame_unprom_from
                               (Memory_stack_frame_stack (state_memory_stack σ2)) G
                               (state_memory_stack σ2_st)).
                   { eapply top_frame_unprom_frame_eq; [symmetry; exact Hfs_st | exact Htf_al]. }
                   destruct va1 as [[varg | | | | | | |] | |];
                     [| apply refine_cfg_raise_both ..].
                   eapply refine_prov_obs_eq;
                     [symmetry; apply interp_cfg_model_ret
                     | symmetry; apply interp_cfg_model_ret |].
                   apply refine_prov_ret.
                   exists pr_va, bs, vs, σ1_st, σ2_st.
                   exact (conj Hnin_va (conj Logic.eq_refl (conj Logic.eq_refl
                            (conj Ecomb (conj Logic.eq_refl (conj Logic.eq_refl (conj Hinv_st Htf_st))))))).
  Qed.

  Lemma pop_call_frame_stage1_unprom_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf_cur1 sf_prev1 sf_cur2 sf_prev2 : @stack_frame (@ParamsV IP IPT))
    (fstk1 fstk2 : stack) (g : @global_env (@ParamsV IP IPT))
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2)
    (Htf : top_frame_unprom_from fs0 G (state_memory_stack σ2)) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         exists σ1' σ2',
           U' = U /\ r1 = tt /\ r2 = tt /\
           s1' = (σ1', ((sf_prev1, fstk1), g)) /\
           s2' = (σ2', ((sf_prev2, fstk2), g)) /\
           stage1_mem_inv U P_unprom G σ1' σ2' /\
           Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
      U
      (interp_cfg_model ctx1 pop_call_frame (σ1, ((sf_cur1, sf_prev1 :: fstk1), g)))
      (interp_cfg_model ctx2 pop_call_frame (σ2, ((sf_cur2, sf_prev2 :: fstk2), g))).
  Proof using.
    unfold pop_call_frame.
    eapply refine_cfg_model_bind with
      (RA := fun U' '(s1', _) '(s2', _) =>
               U' = U /\
               s1' = (σ1, ((sf_prev1, fstk1), g)) /\
               s2' = (σ2, ((sf_prev2, fstk2), g))).
    - eapply refine_prov_tau_star_l; [apply tau_star_cfg_stack_pop |].
      eapply refine_prov_tau_star_r; [apply tau_star_cfg_stack_pop |].
      apply refine_prov_ret;
        exact (conj (Logic.eq_refl U) (conj Logic.eq_refl Logic.eq_refl)).
    - intros U1 s1_sp _ s2_sp _ _ (-> & -> & ->).
      unfold mem_pop, Subevent.trigger; try unfold trigger_cast.
      apply refine_cfg_memory_event.
      eapply refine_prov_weaken;
        [exact (stage1_mempop_unprom fs0 U P_unprom G σ1 σ2 Hinv Htf) |].
      intros U' [σ1' r1] [σ2' r2] (-> & -> & -> & Hinv' & Hfs').
      exists σ1', σ2';
        exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl
                 (conj Logic.eq_refl (conj Logic.eq_refl (conj Hinv' Hfs')))))).
  Qed.

  Lemma pop_call_frame_stage1_prom_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf_cur1 sf_prev1 sf_cur2 sf_prev2 : @stack_frame (@ParamsV IP IPT))
    (fstk1 fstk2 : stack) (g : @global_env (@ParamsV IP IPT))
    (Hinv : stage1_mem_inv U P_unprom (gs :: G) σ1 σ2)
    (Htf : top_frame_prom_from fs0 gs G (state_memory_stack σ2)) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         exists σ1' σ2',
           U' = U /\ r1 = tt /\ r2 = tt /\
           s1' = (σ1', ((sf_prev1, fstk1), g)) /\
           s2' = (σ2', ((sf_prev2, fstk2), g)) /\
           stage1_mem_inv U P_unprom G σ1' σ2' /\
           Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
      U
      (interp_cfg_model ctx1 pop_call_frame (σ1, ((sf_cur1, sf_prev1 :: fstk1), g)))
      (interp_cfg_model ctx2 pop_call_frame (σ2, ((sf_cur2, sf_prev2 :: fstk2), g))).
  Proof using.
    unfold pop_call_frame.
    eapply refine_cfg_model_bind with
      (RA := fun U' '(s1', _) '(s2', _) =>
               U' = U /\
               s1' = (σ1, ((sf_prev1, fstk1), g)) /\
               s2' = (σ2, ((sf_prev2, fstk2), g))).
    - eapply refine_prov_tau_star_l; [apply tau_star_cfg_stack_pop |].
      eapply refine_prov_tau_star_r; [apply tau_star_cfg_stack_pop |].
      apply refine_prov_ret;
        exact (conj (Logic.eq_refl U) (conj Logic.eq_refl Logic.eq_refl)).
    - intros U1 s1_sp _ s2_sp _ _ (-> & -> & ->).
      unfold mem_pop, Subevent.trigger; try unfold trigger_cast.
      apply refine_cfg_memory_event.
      eapply refine_prov_weaken;
        [exact (stage1_mempop_prom fs0 U P_unprom gs G σ1 σ2 Hinv Htf) |].
      intros U' [σ1' r1] [σ2' r2] (-> & -> & -> & Hinv' & Hfs').
      exists σ1', σ2';
        exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl
                 (conj Logic.eq_refl (conj Logic.eq_refl (conj Hinv' Hfs')))))).
  Qed.

  Lemma pop_call_frame_stage2_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state)
    (sf_cur1 sf_cur2 sf_prev : @stack_frame (@ParamsV IP IPT))
    (fstk : stack) (g : @global_env (@ParamsV IP IPT))
    (Hinv : stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2) :
    refine_prov
      (fun U' '(s1', r1) '(s2', r2) =>
         exists σ1' σ2',
           U' = U /\ r1 = tt /\ r2 = tt /\
           s1' = (σ1', ((sf_prev, fstk), g)) /\
           s2' = (σ2', ((sf_prev, fstk), g)) /\
           mem_stack_equal (state_memory_stack σ1') (state_memory_stack σ2') /\
           Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
      U
      (interp_cfg_model ctx1 pop_call_frame (σ1, ((sf_cur1, sf_prev :: fstk), g)))
      (interp_cfg_model ctx2 pop_call_frame (σ2, ((sf_cur2, sf_prev :: fstk), g))).
  Proof using.
    unfold pop_call_frame.
    eapply refine_cfg_model_bind with
      (RA := fun U' '(s1', _) '(s2', _) =>
               U' = U /\
               s1' = (σ1, ((sf_prev, fstk), g)) /\
               s2' = (σ2, ((sf_prev, fstk), g))).
    - eapply refine_prov_tau_star_l; [apply tau_star_cfg_stack_pop |].
      eapply refine_prov_tau_star_r; [apply tau_star_cfg_stack_pop |].
      apply refine_prov_ret;
        exact (conj (Logic.eq_refl U) (conj Logic.eq_refl Logic.eq_refl)).
    - intros U1 s1_sp _ s2_sp _ _ (-> & -> & ->).
      unfold mem_pop, Subevent.trigger; try unfold trigger_cast.
      apply refine_cfg_memory_event.
      eapply refine_prov_weaken;
        [exact (stage2_mempop_restore U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 Hinv) |].
      intros U' [σ1' r1] [σ2' r2] (-> & -> & -> & Heq' & Hfs').
      exists σ1', σ2';
        exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl
                 (conj Logic.eq_refl (conj Logic.eq_refl (conj Heq' Hfs')))))).
  Qed.

  (** *** Promoted [init_op], [mk_store_vec_exp]/[mk_store_ext_exp], and [mk_load_vec_exp]/[mk_load_cast_exp] Simulations *)

  Lemma denote_init_copy_poison_exc_r {R1 : Type}
    (ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RR : list N -> Res (@exc (@ParamsV IP IPT) + R1) ->
          Res (@exc (@ParamsV IP IPT) + unit) -> Prop)
    (init_reg : local_id) (dt : dtyp)
    (va : option (@ptr ProvenanceV (@PointerV IP)))
    (U : list N) (t1 : itree ProvBotE (Res (@exc (@ParamsV IP IPT) + R1)))
    (σ2 : state) (sf2 : @stack_frame (@ParamsV IP IPT))
    (fstk2 : stack) (g : @global_env (@ParamsV IP IPT))
    (Href :
       refine_prov RR U t1
         (Ret ((σ2, ((upd_local_sf sf2 (Maps.add init_reg (DVALUE_Base DVALUE_Poison) (stack_vars sf2)),
                      fstk2), g)),
               inr tt))) :
    refine_prov RR U t1
      (interp_cfg_exc ctx2
         (denote_instr
            (IId init_reg,
             INSTR_Op (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison),
             []) va)
         (σ2, ((sf2, fstk2), g))).
  Proof using.
    cbn [denote_instr].
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; apply interp_cfg_exc_bind |].
    eapply refine_prov_tau_expand;
      [apply tau_expand_refl
      | apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp |].
    unfold mcfg_inr_exc.
    assert (Eexp :
              interp_mcfg_model
                (denote_exp None (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison))
                (σ2, ((sf2, fstk2), g)) ≅
              Ret ((σ2, ((sf2, fstk2), g)), DVALUE_Base DVALUE_Poison)).
    { rewrite (interp_mcfg_model_obs_eq _ _ _
                 (denote_mk_copy_exp None (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison)).
      cbn [denote_exp]; apply interp_mcfg_model_ret. }
    eapply refine_prov_obs_eq;
      [reflexivity
      | symmetry;
        rewrite Eqit.bind_bind,
          (eq_itree_bind_congr_l Eexp),
          !Eqit.bind_ret_l;
        apply interp_cfg_exc_bind
      |].
    eapply refine_prov_tau_star_r.
    - apply tau_star_bind, tau_star_cfg_exc_lwrite.
    - eapply refine_prov_obs_eq;
        [reflexivity
        | symmetry; rewrite Eqit.bind_ret_l; apply interp_cfg_exc_ret
        | exact Href].
  Qed.

  Lemma tau_star_mcfg_lread_some
    (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (σ : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env)
    (Hlk : Maps.lookup x (stack_vars sf) = Some v) :
    tau_star
      (interp_mcfg_model (lread x) (σ, ((sf, fstk), g)))
      (Ret ((σ, ((sf, fstk), g)), v)).
  Proof using.
    unfold lread, Subevent.trigger; try unfold trigger_cast.
    eapply tau_star_mcfg_det; [reflexivity |].
    unfold interp_vellvm_prov_h;
      cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    exact (fused_local_prov_read_some x v (σ, ((sf, fstk), g)) Hlk).
  Qed.

  Lemma raiseUB_bind_eq {E : Type -> Type} `{UBE -< E} {X Y : Type}
    (msg : string) (k : X -> itree E Y) :
    ITree.bind (raiseUB msg) k ≅ raiseUB msg.
  Proof using.
    unfold raiseUB, trigger_cast; rewrite Eqit.bind_bind.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
  Qed.

  Lemma interp_mcfg_model_raise_bind_eq {A2 R2 : Type}
    (msg : string) (s2 : FusedS) (k2 : Res A2 -> itree ProvBotE R2) :
    ITree.bind (interp_mcfg_model (raise msg) s2) k2 ≅
    ITree.bind
      (ITree.trigger ((inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (Throw (print_msg msg)))))))) : ProvBotE void))
      (fun v : void => match v return itree ProvBotE R2 with end).
  Proof using.
    unfold raise, trigger_cast.
    rewrite interp_mcfg_model_bind, Eqit.bind_bind.
    etransitivity.
    { match goal with
      | |- ITree.bind _ ?k ≅ _ =>
          eapply eq_itree_clo_bind with (UU := Logic.eq) (k2 := k);
          [apply interp_mcfg_model_non_intr; reflexivity | intros ? ? <-; reflexivity]
      end. }
    repeat (progress (try unfold subevent, resum, ReSum_id, ReSum_sum, ReSum_inl, ReSum_inr,
                               cat, Cat_IFun, inl_, inr_, Inl_sum1, Inr_sum1, id_, Id_IFun;
                      cbn beta iota)).
    unfold interp_vellvm_prov_h, case_, Case_sum1, case_sum1, Case_sum1_Handler, Handler.case_; cbn beta iota.
    repeat (progress (try unfold fused_trigger_prov, ITree.trigger, subevent, resum,
                               ReSum_id, ReSum_sum, ReSum_inl, ReSum_inr,
                               cat, Cat_IFun, inl_, inr_, Inl_sum1, Inr_sum1, id_, Id_IFun;
                      cbn beta iota)).
    rewrite !Eqit.bind_bind, !Eqit.bind_vis.
    apply eqit_Vis; intros [].
  Qed.

  Lemma memM_Merr_mcfg_raise_bind_sim {A1 A2 R2 : Type}
    (RR : list N -> (state * A1) -> R2 -> Prop)
    (U : list N) (msg1 msg2 : string) (σ1 : state) (s2 : FusedS)
    (k2 : Res A2 -> itree ProvBotE R2) :
    refine_prov RR U
      (memM_interp_prov (@Merr _ _ _ A1 msg1) σ1)
      (ITree.bind (interp_mcfg_model (raise msg2) s2) k2).
  Proof using.
    cbn [memM_interp_prov].
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; exact (interp_mcfg_model_raise_bind_eq msg2 s2 k2) |].
    unfold raise, trigger_cast, ITree.trigger.
    cbn [subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_vis | symmetry; apply Eqit.bind_vis |].
    pstep; apply RP_Step; cbn; right; right; split; [exact I | intros [] [] _].
  Qed.

  Lemma bind_unit_ret_r {E : Type -> Type} (t : itree E unit) :
    ITree.bind t (fun _ : unit => Ret tt) ≅ t.
  Proof using.
    rewrite <- (Eqit.bind_ret_r t) at 2.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] [] _; reflexivity].
  Qed.

  Lemma memM_void_to_mcfg_raise_bind_eq {A2 R2 : Type}
    (msg : string) (σ2 : state) (s2 : FusedS)
    (k2 : Res A2 -> itree ProvBotE R2) :
    ITree.bind
      (memM_interp_prov (@Merr _ _ _ void msg) σ2)
      (fun '(_, v) => match v with end) ≅
    ITree.bind (interp_mcfg_model (raise msg) s2) k2.
  Proof using.
    rewrite (interp_mcfg_model_raise_bind_eq msg s2 k2).
    cbn [memM_interp_prov].
    unfold raise, trigger_cast, ITree.trigger.
    cbn [subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
    rewrite !Eqit.bind_bind, !Eqit.bind_vis.
    apply eqit_Vis; intros [].
  Qed.

  Lemma denote_mk_store_vec_exp_eq (dt : dtyp) (val_exp : exp dtyp) :
    @denote_exp (@ParamsV IP IPT) None (mk_store_vec_exp dt val_exp) ≅
    ITree.bind (denote_exp (Some dt) val_exp)
      (fun v =>
         match v with
         | DVALUE_Base db => Ret (DVALUE_Array true [DVALUE_Base db])
         | _ => raise "dvalue_to_dvalue_base: non-base dvalue"
         end).
  Proof using.
    unfold mk_store_vec_exp; cbn [denote_exp ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    rewrite !Eqit.bind_ret_l, !Eqit.bind_bind.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [db | pk flds | vec elts] _ <-.
    - cbn [dvalue_to_dvalue_base EOU_monad ExtLib.Structures.Monad.ret EOU_to_itree ExtLib.Structures.Monad.bind Monad_itree].
      rewrite !Eqit.bind_ret_l, ?Eqit.bind_bind, ?Eqit.bind_ret_l.
      unfold insert_element, dvalue_to_Z, VellvmIntegers.signed, VellvmIntegers.zero;
        rewrite ?(@Integers.signed_zero 1);
        try change (N.to_nat 1%N) with 1%nat;
        try change (Pos.to_nat 1%positive) with 1%nat;
        cbn;
        try change (Pos.to_nat 1%positive) with 1%nat;
        cbn;
        rewrite ?Eqit.bind_ret_l; reflexivity.
    - cbn [dvalue_to_dvalue_base EOU_to_itree].
      unfold raise, trigger_cast; rewrite !Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
    - cbn [dvalue_to_dvalue_base EOU_to_itree].
      unfold raise, trigger_cast; rewrite !Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros [] _ _].
  Qed.

  Lemma denote_mk_store_ext_exp_eq (dt : dtyp) (vec_reg : local_id) :
    @denote_exp (@ParamsV IP IPT) None (mk_store_ext_exp dt vec_reg) ≅
    ITree.bind (lread vec_reg)
      (fun vec =>
         EOU_to_itree
           (extract_element vec (DVALUE_Base (DVALUE_I 1 VellvmIntegers.zero)))).
  Proof using.
    unfold mk_store_ext_exp;
      cbn [denote_exp lookup_id ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros vec _ <-; rewrite !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma extract_element_singleton_zero_eq (v : @dvalue (@ParamsV IP IPT)) :
    EOU_to_itree (E := @MCFGEtop (@ParamsV IP IPT))
      (extract_element (DVALUE_Array true [v]) (DVALUE_Base (DVALUE_I 1 VellvmIntegers.zero))) ≅
    Ret v.
  Proof using.
    unfold extract_element, dvalue_to_Z, VellvmIntegers.signed, VellvmIntegers.zero;
      rewrite ?(@Integers.signed_zero 1);
      try change (Pos.to_nat 1%positive) with 1%nat;
      cbn;
      try change (Pos.to_nat 1%positive) with 1%nat;
      cbn;
      rewrite ?Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma denote_mk_load_vec_exp_eq (dt : dtyp) (cur_reg : local_id) :
    @denote_exp (@ParamsV IP IPT) None (mk_load_vec_exp dt cur_reg) ≅
    ITree.bind (lread cur_reg)
      (fun v =>
         match v with
         | DVALUE_Base db => Ret (DVALUE_Array true [DVALUE_Base db])
         | _ => raise "dvalue_to_dvalue_base: non-base dvalue"
         end).
  Proof using.
    exact (denote_mk_store_vec_exp_eq dt (EXP_Ident (ID_Local cur_reg))).
  Qed.

  Lemma denote_mk_load_cast_exp_eq (dt : dtyp) (vec_reg : local_id) :
    @denote_exp (@ParamsV IP IPT) None (mk_load_cast_exp dt vec_reg) ≅
    ITree.bind (lread vec_reg)
      (fun v => convert CONV_Bitcast (DTYPE_Array true 1%N dt) v dt).
  Proof using.
    unfold mk_load_cast_exp;
      cbn [denote_exp lookup_id ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    reflexivity.
  Qed.

  #[local] Lemma denote_mk_store_val_exp_nonbase_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (sv_reg st_reg : local_id) (dt : dtyp) (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (k_succ : @dvalue (@ParamsV IP IPT) -> @CFGtop (@ParamsV IP IPT) unit)
    (v_bad : @dvalue (@ParamsV IP IPT))
    (Hdt : gs_dt gs = dt)
    (Hsc : is_scalar_dtyp dt = true)
    (Hnb : forall db, v_bad <> DVALUE_Base db) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists db' bs' σ1',
              U' = U /\ r1 = tt /\ r2 = tt /\
              dvalue_to_memory_bytes dt (DVALUE_Base db') None = raise_ret bs' /\
              s1' = (σ1', ((sf1, fstk1), g)) /\
              s2' = (σ2, ((upd_local_sf sf2
                             (Maps.add st_reg (DVALUE_Base db')
                                (Maps.add sv_reg (DVALUE_Array true [DVALUE_Base db']) (stack_vars sf2))),
                           fstk2), g)) /\
              stage1_mem_inv U P_unprom (gs_set_val gs db' bs' :: G) σ1' σ2 /\
              top_frame_prom_from fs0 (gs_set_val gs db' bs') G (state_memory_stack σ2)))
      U
      (interp_cfg_exc ctx1
         (store (Pa := @ParamsV IP IPT) dt (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) v_bad)
         (σ1, ((sf1, fstk1), g)))
      (ITree.bind
         (interp_mcfg_model (R := @dvalue (@ParamsV IP IPT))
            (raise "dvalue_to_dvalue_base: non-base dvalue")
            (σ2, ((sf2, fstk2), g)))
         (fun '(s2', x) =>
            ITree.bind (Ret (s2', inr (A := @exc (@ParamsV IP IPT)) x))
              (fun '(s2'', res) =>
                 match res with
                 | inl ex => Ret (s2'', inl ex)
                 | inr uv => interp_cfg_exc ctx2 (k_succ uv) s2''
                 end))).
  Proof using.
    subst dt.
    lazymatch goal with
    | |- refine_prov ?R _ _ (ITree.bind _ ?k) =>
        set (RR_post := R); clearbody RR_post;
        set (k_cont := k); clearbody k_cont
    end.
    destruct (is_scalar_dtyp_inv (gs_dt gs) Hsc) as (dtb & Hdt_eq & _).
    destruct (dvalue_to_memory_bytes_base_err dtb v_bad Hnb) as [msg1 Hser].
    unfold store, Subevent.trigger; try unfold trigger_cast.
    apply refine_cfg_exc_memory_event_l.
    cbn [handle_memoryM]; unfold write_dvalue.
    rewrite Hdt_eq, Hser; cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.bind memS_mon memS_bind memM_interp_prov].
    eapply refine_prov_obs_eq;
      [reflexivity
      | symmetry;
        exact (interp_mcfg_model_raise_bind_eq
                 (A2 := @dvalue (@ParamsV IP IPT))
                 "dvalue_to_dvalue_base: non-base dvalue"
                 (σ2, ((sf2, fstk2), g)) k_cont)
      |].
    unfold raise, trigger_cast, ITree.trigger;
      repeat (progress (try unfold subevent, resum, ReSum_id, ReSum_sum, ReSum_inl, ReSum_inr,
                                   cat, Cat_IFun, inl_, inr_, Inl_sum1, Inr_sum1, id_, Id_IFun;
                        cbn beta iota)).
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_vis | symmetry; apply Eqit.bind_vis |].
    pstep; apply RP_Step; unfold rp_step_body; cbn [observe]; right; right; cbn;
      split; [exact Logic.I | intros [] [] _].
  Qed.

  #[local] Lemma denote_mk_store_pair_base_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (sv_reg st_reg : local_id) (dt : dtyp)
    (va2 : option (@ptr ProvenanceV (@PointerV IP)))
    (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (db' : @dvalue_base (@ParamsV IP IPT))
    (Hdt : gs_dt gs = dt)
    (Hinv : stage1_mem_inv U P_unprom (gs :: G) σ1 σ2)
    (Htf : top_frame_prom_from fs0 gs G (state_memory_stack σ2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists db'0 bs' σ1',
              U' = U /\ r1 = tt /\ r2 = tt /\
              dvalue_to_memory_bytes dt (DVALUE_Base db'0) None = raise_ret bs' /\
              s1' = (σ1', ((sf1, fstk1), g)) /\
              s2' = (σ2, ((upd_local_sf sf2
                             (Maps.add st_reg (DVALUE_Base db'0)
                                (Maps.add sv_reg (DVALUE_Array true [DVALUE_Base db'0]) (stack_vars sf2))),
                           fstk2), g)) /\
              stage1_mem_inv U P_unprom (gs_set_val gs db'0 bs' :: G) σ1' σ2 /\
              top_frame_prom_from fs0 (gs_set_val gs db'0 bs') G (state_memory_stack σ2)))
      U
      (interp_cfg_exc ctx1
         (store (Pa := @ParamsV IP IPT) dt (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) (DVALUE_Base db'))
         (σ1, ((sf1, fstk1), g)))
      (ITree.bind
         (interp_mcfg_model (Ret (DVALUE_Array true [DVALUE_Base db'])) (σ2, ((sf2, fstk2), g)))
         (fun '(s2', x) =>
            ITree.bind (Ret (s2', inr x))
              (fun '(s2'', res) =>
                 match res with
                 | inl ex => Ret (s2'', inl ex)
                 | inr uv =>
                     interp_cfg_exc ctx2
                       (ITree.bind (lwrite sv_reg uv)
                          (fun _ => denote_instr (IId st_reg, INSTR_Op (mk_store_ext_exp dt sv_reg), []) va2))
                       s2''
                 end))).
  Proof using.
    set (sf2_mid := upd_local_sf sf2 (Maps.add sv_reg (DVALUE_Array true [DVALUE_Base db']) (stack_vars sf2))).
    assert (Hlk_sv : Maps.lookup sv_reg (stack_vars sf2_mid) = Some (DVALUE_Array true [DVALUE_Base db']))
      by (cbn [sf2_mid upd_local_sf stack_vars Maps.lookup Maps.add Map_rmap]; apply RMF.F.add_eq_o; reflexivity).
    assert (Er_ok :
              ITree.bind
                (interp_mcfg_model (Ret (DVALUE_Array true [DVALUE_Base db'])) (σ2, ((sf2, fstk2), g)))
                (fun '(s2', x) =>
                   ITree.bind (Ret (s2', inr x))
                     (fun '(s2'', res) =>
                        match res with
                        | inl ex => Ret (s2'', inl ex)
                        | inr uv =>
                            interp_cfg_exc ctx2
                              (ITree.bind (lwrite sv_reg uv)
                                 (fun _ => denote_instr (IId st_reg, INSTR_Op (mk_store_ext_exp dt sv_reg), []) va2))
                              s2''
                        end)) ≅
              ITree.bind
                (interp_cfg_exc ctx2 (lwrite sv_reg (DVALUE_Array true [DVALUE_Base db'])) (σ2, ((sf2, fstk2), g)))
                (fun '(s2''', res2) =>
                   match res2 with
                   | inl ex => Ret (s2''', inl ex)
                   | inr _ =>
                       interp_cfg_exc ctx2 (denote_instr (IId st_reg, INSTR_Op (mk_store_ext_exp dt sv_reg), []) va2) s2'''
                   end)).
    { etransitivity.
      { match goal with
        | |- ITree.bind _ ?k ≅ _ =>
            eapply eq_itree_clo_bind with (UU := Logic.eq) (k2 := k);
              [apply interp_mcfg_model_ret | intros [s2' x] _ <-; reflexivity]
        end. }
      rewrite !Eqit.bind_ret_l.
      apply interp_cfg_exc_bind. }
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; exact Er_ok |]; clear Er_ok.
    eapply refine_prov_tau_star_r;
      [apply tau_star_bind, tau_star_cfg_exc_lwrite |].
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; apply Eqit.bind_ret_l |].
    cbn beta iota; fold sf2_mid.
    cbn [denote_instr].
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; apply interp_cfg_exc_bind |].
    eapply refine_prov_tau_expand;
      [apply tau_expand_refl | apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp |].
    unfold mcfg_inr_exc.
    assert (EexpR :
              interp_mcfg_model (denote_exp None (mk_store_ext_exp dt sv_reg))
                (σ2, ((sf2_mid, fstk2), g)) ≅
              ITree.bind (interp_mcfg_model (lread sv_reg) (σ2, ((sf2_mid, fstk2), g)))
                (fun '(s2', vec) =>
                   interp_mcfg_model
                     (EOU_to_itree
                        (extract_element vec (DVALUE_Base (DVALUE_I 1 VellvmIntegers.zero))))
                     s2')).
    { rewrite (interp_mcfg_model_obs_eq _ _ _ (denote_mk_store_ext_exp_eq dt sv_reg)).
      apply interp_mcfg_model_bind. }
    eapply refine_prov_obs_eq;
      [reflexivity
      | symmetry; rewrite (eq_itree_bind_congr_l EexpR), !Eqit.bind_bind; reflexivity
      |]; clear EexpR.
    eapply refine_prov_tau_star_r;
      [apply tau_star_bind, (tau_star_mcfg_lread_some sv_reg _ σ2 sf2_mid fstk2 g Hlk_sv) |].
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; apply Eqit.bind_ret_l |].
    cbn beta iota.
    eapply refine_prov_obs_eq;
      [reflexivity
      | symmetry;
        rewrite (interp_mcfg_model_obs_eq _ _ _ (extract_element_singleton_zero_eq (DVALUE_Base db'))),
                interp_mcfg_model_ret, Eqit.bind_ret_l;
        cbn beta iota;
        rewrite Eqit.bind_ret_l;
        cbn beta iota;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite (interp_cfg_exc_obs_eq ctx2 _ _ _ (bind_unit_ret_r (lwrite st_reg (DVALUE_Base db'))));
        reflexivity
      |].
    eapply refine_prov_tau_star_r;
      [apply tau_star_cfg_exc_lwrite |].
    subst dt.
    unfold store, Subevent.trigger; try unfold trigger_cast.
    apply refine_cfg_exc_memory_event_l.
    eapply refine_prov_obs_eq;
      [apply Eqit.bind_ret_r
      | apply (Eqit.bind_ret_l (σ2, tt)
                 (fun _ =>
                    Ret ((σ2, ((upd_local_sf sf2_mid (Maps.add st_reg (DVALUE_Base db') (stack_vars sf2_mid)),
                                fstk2), g)),
                         inr tt))) |].
    eapply PassCommonModel.refine_prov_bind;
      [exact (stage1_store_prom_base U P_unprom gs G fs0 db' σ1 σ2 Hinv Htf) |].
    intros U2 [σ1' r1_st] [σ2' r2_st] _ (bs' & -> & -> & _ & Hser' & Hinv' & Htf').
    apply refine_prov_ret.
    exists db', bs', σ1'.
    exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl
             (conj Hser' (conj Logic.eq_refl (conj Logic.eq_refl (conj Hinv' Htf'))))))).
  Qed.

  Lemma denote_mk_store_pair_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (vid : int_ast) (p sv_reg st_reg : local_id) (dt : dtyp) (val_exp : exp dtyp)
    (anns_st : list (annotation dtyp)) (md_st : list (metadata dtyp))
    (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
    (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hdt : gs_dt gs = dt)
    (Hsc : is_scalar_dtyp dt = true)
    (Hlk_p : Maps.lookup p (stack_vars sf1) = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))
    (Hinv : stage1_mem_inv U P_unprom (gs :: G) σ1 σ2)
    (Htf : top_frame_prom_from fs0 gs G (state_memory_stack σ2))
    (Hvars : forall x,
               In x (full_exp_uses val_exp) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists db' bs' σ1',
              U' = U /\ r1 = tt /\ r2 = tt /\
              dvalue_to_memory_bytes dt (DVALUE_Base db') None = raise_ret bs' /\
              s1' = (σ1', ((sf1, fstk1), g)) /\
              s2' = (σ2, ((upd_local_sf sf2
                             (Maps.add st_reg (DVALUE_Base db')
                                (Maps.add sv_reg (DVALUE_Array true [DVALUE_Base db']) (stack_vars sf2))),
                           fstk2), g)) /\
              stage1_mem_inv U P_unprom (gs_set_val gs db' bs' :: G) σ1' σ2 /\
              top_frame_prom_from fs0 (gs_set_val gs db' bs') G (state_memory_stack σ2)))
      U
      (interp_cfg_exc ctx1
         (denote_instr
            (IVoid vid,
             INSTR_Store (dt, val_exp) (DTYPE_Base DTYPE_Pointer, EXP_Ident (ID_Local p)) anns_st,
             md_st) va1)
         (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2
         (ITree.bind
            (denote_instr (IId sv_reg, INSTR_Op (mk_store_vec_exp dt val_exp), []) va2)
            (fun _ => denote_instr (IId st_reg, INSTR_Op (mk_store_ext_exp dt sv_reg), []) va2))
         (σ2, ((sf2, fstk2), g))).
  Proof using.
    set (k_ext := denote_instr (Pa := @ParamsV IP IPT) (IId st_reg, INSTR_Op (mk_store_ext_exp dt sv_reg), []) va2).
    assert (Er_sv :
              interp_cfg_exc ctx2
                (ITree.bind
                   (denote_instr (IId sv_reg, INSTR_Op (mk_store_vec_exp dt val_exp), []) va2)
                   (fun _ => k_ext))
                (σ2, ((sf2, fstk2), g)) ≅
              ITree.bind
                (interp_cfg_exc ctx2
                   (denote_exp' None (mk_store_vec_exp dt val_exp))
                   (σ2, ((sf2, fstk2), g)))
                (fun '(s2'', res) =>
                   match res with
                   | inl ex => Ret (s2'', inl ex)
                   | inr uv =>
                       interp_cfg_exc ctx2
                         (ITree.bind (lwrite sv_reg uv) (fun _ => k_ext))
                         s2''
                   end)).
    { cbn [denote_instr ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)).
      rewrite interp_cfg_exc_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s2'' [ex | uv]] _ <-; [reflexivity |].
      apply interp_cfg_exc_obs_eq.
      rewrite Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [] [] _; rewrite Eqit.bind_ret_l; reflexivity. }
    cbn [denote_instr].
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_exc_bind | symmetry; exact Er_sv |]; clear Er_sv.
    eapply refine_prov_tau_expand;
      [apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp
      | apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp |].
    unfold mcfg_inr_exc.
    assert (EexpR :
              interp_mcfg_model (denote_exp None (mk_store_vec_exp dt val_exp))
                (σ2, ((sf2, fstk2), g)) ≅
              ITree.bind (interp_mcfg_model (denote_exp (Some dt) val_exp) (σ2, ((sf2, fstk2), g)))
                (fun '(s2', v) =>
                   interp_mcfg_model
                     (match v with
                      | DVALUE_Base db => Ret (DVALUE_Array true [DVALUE_Base db])
                      | _ => raise "dvalue_to_dvalue_base: non-base dvalue"
                      end) s2')).
    { rewrite (interp_mcfg_model_obs_eq _ _ _ (denote_mk_store_vec_exp_eq dt val_exp)).
      apply interp_mcfg_model_bind. }
    assert (Er_init :
              ITree.bind
                (interp_mcfg_model (denote_exp None (mk_store_vec_exp dt val_exp))
                   (σ2, ((sf2, fstk2), g)))
                (fun r =>
                   ITree.bind (let '(s2', x) := r in Ret (s2', inr x))
                     (fun '(s2'', res) =>
                        match res with
                        | inl ex => Ret (s2'', inl ex)
                        | inr uv =>
                            interp_cfg_exc ctx2 (ITree.bind (lwrite sv_reg uv) (fun _ => k_ext)) s2''
                        end)) ≅
              ITree.bind (interp_mcfg_model (denote_exp (Some dt) val_exp) (σ2, ((sf2, fstk2), g)))
                (fun '(s2'0, v) =>
                   ITree.bind
                     (interp_mcfg_model
                        (match v with
                         | DVALUE_Base db => Ret (DVALUE_Array true [DVALUE_Base db])
                         | _ => raise "dvalue_to_dvalue_base: non-base dvalue"
                         end) s2'0)
                     (fun '(s2', x) =>
                        ITree.bind (Ret (s2', inr x))
                          (fun '(s2'', res) =>
                             match res with
                             | inl ex => Ret (s2'', inl ex)
                             | inr uv =>
                                 interp_cfg_exc ctx2 (ITree.bind (lwrite sv_reg uv) (fun _ => k_ext)) s2''
                             end)))).
    { rewrite (eq_itree_bind_congr_l EexpR), Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s2'0 v] _ <-; cbn beta iota.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s2' x] _ <-; reflexivity. }
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; exact Er_init |]; clear Er_init EexpR.
    eapply PassCommonModel.refine_prov_bind;
      [exact (denote_exp_mcfg_sim (Some dt) val_exp U σ1 σ2 sf1 sf2 fstk1 fstk2 g Hvars) |].
    intros U1 [s1_v v1] [s2_v v2] _ (-> & -> & -> & <- & _).
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | reflexivity |].
    cbn beta iota.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_exc_bind | reflexivity |].
    eapply refine_prov_tau_expand;
      [apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp
      | apply tau_expand_refl |].
    unfold mcfg_inr_exc; cbn [denote_exp lookup_id].
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind | reflexivity |].
    eapply refine_prov_tau_star_l;
      [apply tau_star_bind, (tau_star_mcfg_lread_some p _ σ1 sf1 fstk1 g Hlk_p) |].
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | reflexivity |].
    cbn beta iota.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | reflexivity |].
    cbn beta iota.
    destruct (assert_alignment_ret_or_ub
                (DVALUE_Base (DVALUE_Pointer (Pa := @ParamsV IP IPT) (gs_pt gs))) anns_st
                ((set_loc (get_file_info md_st) ++ location_error_string md_st) ++
                 ": Store with overestimated alignment.")%string)
      as [Hal_ok | Hal_ub].
    - rewrite Hal_ok; cbn [EOU_to_itree ExtLib.Structures.Monad.ret Monad_itree].
      assert (Est_l :
                ITree.bind (Ret tt)
                  (fun _ : unit =>
                     ITree.bind
                       (store (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT))
                          dt (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) v1)
                       (fun _ : unit => Ret tt)) ≅
                store (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT))
                  dt (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) v1).
      { rewrite Eqit.bind_ret_l; apply bind_unit_ret_r. }
      eapply refine_prov_obs_eq;
        [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ Est_l) | reflexivity |];
        clear Est_l.
      destruct v1 as [db' | pk flds | vec elts].
      + exact (denote_mk_store_pair_base_sim ctx1 ctx2 RExc sv_reg st_reg dt va2 fs0 U P_unprom gs G
                 σ1 σ2 sf1 sf2 fstk1 fstk2 g db' Hdt Hinv Htf).
      + exact (denote_mk_store_val_exp_nonbase_sim ctx1 ctx2 RExc sv_reg st_reg dt fs0 U P_unprom gs G
                 σ1 σ2 sf1 sf2 fstk1 fstk2 g (fun uv => ITree.bind (lwrite sv_reg uv) (fun _ => k_ext))
                 (DVALUE_Struct pk flds) Hdt Hsc (ltac:(intros ? ?; discriminate))).
      + exact (denote_mk_store_val_exp_nonbase_sim ctx1 ctx2 RExc sv_reg st_reg dt fs0 U P_unprom gs G
                 σ1 σ2 sf1 sf2 fstk1 fstk2 g (fun uv => ITree.bind (lwrite sv_reg uv) (fun _ => k_ext))
                 (DVALUE_Array vec elts) Hdt Hsc (ltac:(intros ? ?; discriminate))).
    - rewrite Hal_ub; cbn [EOU_to_itree].
      eapply refine_prov_obs_eq;
        [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (raiseUB_bind_eq _ _)) | reflexivity |].
      apply refine_cfg_exc_raiseUB_l.
  Qed.

  Lemma stage1_load_prom_eq
    (U P_unprom : list N) (G : list ghost_slot)
    (gs : ghost_slot) (σ1 σ2 : state) :
    stage1_mem_inv U P_unprom G σ1 σ2 ->
    In gs G ->
    memM_interp_prov
      (handle_memoryM (Load (gs_dt gs) (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))) σ1 ≅
    memM_interp_prov
      (Interfaces.Memory.lift (memory_bytes_to_dvalue (gs_bytes gs) (gs_dt gs))) σ1.
  Proof using.
    intros Hinv Hin.
    pose proof Hinv as (_ & _ & Hall & _ & _ & _ & _ & _ & Hgs).
    rewrite Forall_forall in Hall.
    destruct (Hall gs Hin) as [(_ & Hpr & Eptrs & _ & Hlen_bs & _) _].
    destruct (get_consecutive_ptrs_spec (gs_pt gs) (@store_size_dtyp SizeofV (gs_dt gs)) (gs_ptrs gs) Eptrs)
      as (Hlen_ptrs & Hinv_ptrs & _).
    cbn [handle_memoryM]; unfold read_dvalue, read_bytes.
    rewrite memM_interp_prov_bind, memM_interp_prov_bind; cbn [SIZE ParamsV]; rewrite Eptrs.
    cbn [Interfaces.Memory.lift ExtLib.Structures.Monad.ret memS_mon memM_interp_prov read_byte MemoryModelPrimitivesV].
    rewrite Eqit.bind_ret_l, memM_interp_prov_map_monad_acc.
    rewrite (map_monad_Read_gs_bytes_eq (gs_ptrs gs) (gs_bytes gs) (gs_addr gs) 0%nat (gs_pr gs) σ1).
    - rewrite Eqit.bind_ret_l; reflexivity.
    - unfold gs_len in Hlen_bs; cbn [SIZE SizeofV ParamsV] in Hlen_ptrs, Hlen_bs |- *; lia.
    - intros i q Hnth; destruct (Hinv_ptrs i q Hnth) as (_ & Hqi & Hqpr).
      rewrite Hpr in Hqpr; unfold gs_addr;
        cbn [ptr_to_int PIV P2I PointerV PTR ParamsV fst] in Hqi |- *;
        split; [lia | exact Hqpr].
    - intros i mb Hnth; destruct (Hgs gs i mb Hin Hnth) as [Hlk1 _]; exact Hlk1.
  Qed.

  Lemma denote_mk_load_val_exp_ok_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (dst : local_id)
    (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hinv : stage1_mem_inv U P_unprom (gs :: G) σ1 σ2) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists dv_ld,
              U' = U /\ r1 = tt /\ r2 = tt /\
              s1' = (σ1, ((upd_local_sf sf1 (Maps.add dst dv_ld (stack_vars sf1)), fstk1), g)) /\
              s2' = (σ2, ((upd_local_sf sf2 (Maps.add dst dv_ld (stack_vars sf2)), fstk2), g))))
      U
      (interp_cfg_exc ctx1
         (ITree.bind (load (Pa := @ParamsV IP IPT) (gs_dt gs) (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))
            (fun v => lwrite dst v))
         (σ1, ((sf1, fstk1), g)))
      (ITree.bind
         (interp_mcfg_model
            (EOU_to_itree (memory_bytes_to_dvalue (gs_bytes gs) (gs_dt gs)))
            (σ2, ((sf2, fstk2), g)))
         (fun '(s2', x) =>
            ITree.bind (Ret (s2', inr x))
              (fun '(s2'', res) =>
                 match res with
                 | inl ex => Ret (s2'', inl ex)
                 | inr uv =>
                     interp_cfg_exc ctx2 (ITree.bind (lwrite dst uv) (fun _ => Ret tt)) s2''
                 end))).
  Proof using.
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_exc_bind | reflexivity |].
    pose proof (stage1_load_prom_eq U P_unprom (gs :: G) gs σ1 σ2 Hinv (or_introl Logic.eq_refl))
      as Hld_eq.
    clear Hinv.
    destruct (memory_bytes_to_dvalue (gs_bytes gs) (gs_dt gs))
      as [msg | msg | msg | dv_ld] eqn:Edeser.
    - cbn [EOU_to_itree]; cbn [Interfaces.Memory.lift] in Hld_eq.
      unfold load, Subevent.trigger; try unfold trigger_cast.
      eapply refine_prov_obs_eq;
        [reflexivity
        | exact (@memM_void_to_mcfg_raise_bind_eq (@dvalue (@ParamsV IP IPT)) _ msg σ2 (σ2, ((sf2, fstk2), g)) _) |].
      eapply PassCommonModel.refine_prov_bind with
        (RR := fun _ _ (p : _ * void) => match snd p with end).
      + apply refine_cfg_exc_memory_event_l.
        eapply refine_prov_obs_eq; [symmetry; exact Hld_eq | reflexivity |].
        apply memM_interp_prov_raise_both.
      + intros _ _ [_ []] _ _.
    - cbn [EOU_to_itree]; cbn [Interfaces.Memory.lift] in Hld_eq.
      unfold load, Subevent.trigger; try unfold trigger_cast.
      eapply refine_prov_obs_eq;
        [reflexivity | apply Eqit.bind_ret_r |].
      eapply PassCommonModel.refine_prov_bind with (RR := fun _ _ _ => False).
      + apply refine_cfg_exc_memory_event_l.
        eapply refine_prov_obs_eq; [symmetry; exact Hld_eq | reflexivity |].
        apply memM_interp_prov_raiseOOM_l.
      + intros _ _ _ _ [].
    - cbn [EOU_to_itree]; cbn [Interfaces.Memory.lift] in Hld_eq.
      unfold load, Subevent.trigger; try unfold trigger_cast.
      eapply refine_prov_obs_eq;
        [reflexivity | apply Eqit.bind_ret_r |].
      eapply PassCommonModel.refine_prov_bind with (RR := fun _ _ _ => False).
      + apply refine_cfg_exc_memory_event_l.
        eapply refine_prov_obs_eq; [symmetry; exact Hld_eq | reflexivity |].
        apply memM_interp_prov_raiseUB_l.
      + intros _ _ _ _ [].
    - cbn [EOU_to_itree]; cbn [Interfaces.Memory.lift] in Hld_eq.
      assert (Er :
                ITree.bind
                  (interp_mcfg_model (Ret dv_ld) (σ2, ((sf2, fstk2), g)))
                  (fun '(s2', x) =>
                     ITree.bind (Ret (s2', inr x))
                       (fun '(s2'', res) =>
                          match res with
                          | inl ex => Ret (s2'', inl ex)
                          | inr uv =>
                              interp_cfg_exc ctx2 (ITree.bind (lwrite dst uv) (fun _ => Ret tt)) s2''
                          end)) ≅
                interp_cfg_exc ctx2 (lwrite dst dv_ld) (σ2, ((sf2, fstk2), g))).
      { etransitivity.
        { match goal with
          | |- ITree.bind _ ?k ≅ _ =>
              eapply eq_itree_clo_bind with (UU := Logic.eq) (k2 := k);
                [apply interp_mcfg_model_ret | intros [s2' x] _ <-; reflexivity]
          end. }
        rewrite !Eqit.bind_ret_l.
        apply interp_cfg_exc_obs_eq, bind_unit_ret_r. }
      eapply refine_prov_obs_eq;
        [reflexivity | symmetry; exact Er |]; clear Er.
      eapply refine_prov_obs_eq;
        [reflexivity | apply Eqit.bind_ret_r |].
      unfold load, Subevent.trigger; try unfold trigger_cast.
      eapply PassCommonModel.refine_prov_bind with
        (RR := fun U' '(s1_ld, res_ld) y2 =>
                   U' = U /\ s1_ld = (σ1, ((sf1, fstk1), g)) /\ res_ld = inr dv_ld /\
                   y2 = ((σ2, ((upd_local_sf sf2 (Maps.add dst dv_ld (stack_vars sf2)), fstk2), g)),
                         inr tt)).
      + apply refine_cfg_exc_memory_event_l.
        eapply refine_prov_obs_eq; [symmetry; exact Hld_eq | reflexivity |].
        cbn [ExtLib.Structures.Monad.ret memS_mon memM_interp_prov].
        eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_lwrite |].
        apply refine_prov_ret;
          exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
      + intros U2 [s1_ld res_ld] y2 _ (-> & -> & -> & ->).
        eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
        apply refine_prov_ret; exists dv_ld;
          exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
  Qed.

  Lemma denote_mk_load_pair_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (dst p lv_reg cur_reg : local_id) (dt : dtyp)
    (anns_ld : list (annotation dtyp)) (md_ld : list (metadata dtyp))
    (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
    (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hdt : gs_dt gs = dt)
    (Hsc : is_scalar_dtyp dt = true)
    (Hmd : is_debug_or_file_md md_ld = true)
    (Hlk_p : Maps.lookup p (stack_vars sf1) = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))
    (Hlk_cur : Maps.lookup cur_reg (stack_vars sf2) = Some (DVALUE_Base (gs_db gs)))
    (Hinv : stage1_mem_inv U P_unprom (gs :: G) σ1 σ2) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists dv_ld,
              U' = U /\ r1 = tt /\ r2 = tt /\
              s1' = (σ1, ((upd_local_sf sf1 (Maps.add dst dv_ld (stack_vars sf1)), fstk1), g)) /\
              s2' = (σ2, ((upd_local_sf sf2
                             (Maps.add dst dv_ld
                                (Maps.add lv_reg (DVALUE_Array true [DVALUE_Base (gs_db gs)]) (stack_vars sf2))),
                           fstk2), g))))
      U
      (interp_cfg_exc ctx1
         (denote_instr
            (IId dst,
             INSTR_Load dt (DTYPE_Base DTYPE_Pointer, EXP_Ident (ID_Local p)) anns_ld,
             md_ld) va1)
         (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2
         (ITree.bind
            (denote_instr (IId lv_reg, INSTR_Op (mk_load_vec_exp dt cur_reg), []) va2)
            (fun _ => denote_instr (IId dst, INSTR_Op (mk_load_cast_exp dt lv_reg), []) va2))
         (σ2, ((sf2, fstk2), g))).
  Proof using.
    destruct (is_debug_or_file_md_props md_ld Hmd)
      as (Hlattrs & Hmrange & Hlderef & _).
    pose proof Hinv as (_ & _ & Hall & _).
    rewrite Forall_forall in Hall.
    destruct (Hall gs (or_introl Logic.eq_refl)) as [(_ & _ & _ & Hser & _) _].
    subst dt.
    set (sf2_mid := upd_local_sf sf2 (Maps.add lv_reg (DVALUE_Array true [DVALUE_Base (gs_db gs)]) (stack_vars sf2))).
    assert (Hlk_lv : Maps.lookup lv_reg (stack_vars sf2_mid) = Some (DVALUE_Array true [DVALUE_Base (gs_db gs)]))
      by (cbn [sf2_mid upd_local_sf stack_vars Maps.lookup Maps.add Map_rmap]; apply RMF.F.add_eq_o; reflexivity).
    set (k_cast := denote_instr (Pa := @ParamsV IP IPT) (IId dst, INSTR_Op (mk_load_cast_exp (gs_dt gs) lv_reg), []) va2).
    assert (Er_lv :
              interp_cfg_exc ctx2
                (ITree.bind (denote_instr (IId lv_reg, INSTR_Op (mk_load_vec_exp (gs_dt gs) cur_reg), []) va2)
                   (fun _ => k_cast))
                (σ2, ((sf2, fstk2), g)) ≅
              ITree.bind
                (interp_cfg_exc ctx2
                   (denote_exp' None (mk_load_vec_exp (gs_dt gs) cur_reg))
                   (σ2, ((sf2, fstk2), g)))
                (fun '(s2'', res) =>
                   match res with
                   | inl ex => Ret (s2'', inl ex)
                   | inr uv =>
                       ITree.bind
                         (interp_cfg_exc ctx2 (lwrite lv_reg uv) s2'')
                         (fun '(s2''', res2) =>
                            match res2 with
                            | inl ex => Ret (s2''', inl ex)
                            | inr _ => interp_cfg_exc ctx2 k_cast s2'''
                            end)
                   end)).
    { cbn [denote_instr ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)).
      rewrite interp_cfg_exc_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s2'' [ex | uv]] _ <-; [reflexivity |].
      rewrite (interp_cfg_exc_obs_eq ctx2 _ _ _ (eq_itree_bind_congr_l (bind_unit_ret_r (lwrite lv_reg uv)))).
      apply interp_cfg_exc_bind. }
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; exact Er_lv |]; clear Er_lv.
    eapply refine_prov_tau_expand;
      [apply tau_expand_refl | apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp |].
    unfold mcfg_inr_exc.
    assert (Elv_m :
              interp_mcfg_model (denote_exp None (mk_load_vec_exp (gs_dt gs) cur_reg)) (σ2, ((sf2, fstk2), g)) ≅
              ITree.bind (interp_mcfg_model (lread cur_reg) (σ2, ((sf2, fstk2), g)))
                (fun '(s2', v) =>
                   interp_mcfg_model
                     (match v with
                      | DVALUE_Base db => Ret (DVALUE_Array true [DVALUE_Base db])
                      | _ => raise "dvalue_to_dvalue_base: non-base dvalue"
                      end) s2')).
    { rewrite (interp_mcfg_model_obs_eq _ _ _ (denote_mk_load_vec_exp_eq (gs_dt gs) cur_reg)).
      apply interp_mcfg_model_bind. }
    eapply refine_prov_obs_eq;
      [reflexivity
      | symmetry; rewrite (eq_itree_bind_congr_l Elv_m), !Eqit.bind_bind; reflexivity
      |]; clear Elv_m.
    eapply refine_prov_tau_star_r;
      [apply tau_star_bind, (tau_star_mcfg_lread_some cur_reg _ σ2 sf2 fstk2 g Hlk_cur) |].
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; apply Eqit.bind_ret_l |].
    cbn beta iota.
    eapply refine_prov_obs_eq;
      [reflexivity
      | symmetry;
        rewrite interp_mcfg_model_ret, Eqit.bind_ret_l;
        cbn beta iota;
        rewrite Eqit.bind_ret_l;
        cbn beta iota;
        reflexivity
      |].
    eapply refine_prov_tau_star_r;
      [apply tau_star_bind, tau_star_cfg_exc_lwrite |].
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; apply Eqit.bind_ret_l |].
    cbn beta iota; fold sf2_mid; unfold k_cast.
    cbn [denote_instr].
    eapply refine_prov_obs_eq;
      [symmetry; apply interp_cfg_exc_bind | symmetry; apply interp_cfg_exc_bind |].
    eapply refine_prov_tau_expand;
      [apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp
      | apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp |].
    unfold mcfg_inr_exc; cbn [denote_exp lookup_id].
    assert (EexpR :
              interp_mcfg_model (denote_exp None (mk_load_cast_exp (gs_dt gs) lv_reg))
                (σ2, ((sf2_mid, fstk2), g)) ≅
              ITree.bind (interp_mcfg_model (lread lv_reg) (σ2, ((sf2_mid, fstk2), g)))
                (fun '(s2', v) =>
                   interp_mcfg_model
                     (convert CONV_Bitcast (DTYPE_Array true 1%N (gs_dt gs)) v (gs_dt gs)) s2')).
    { rewrite (interp_mcfg_model_obs_eq _ _ _ (denote_mk_load_cast_exp_eq (gs_dt gs) lv_reg)).
      apply interp_mcfg_model_bind. }
    assert (Er_init :
              ITree.bind
                (interp_mcfg_model (denote_exp None (mk_load_cast_exp (gs_dt gs) lv_reg))
                   (σ2, ((sf2_mid, fstk2), g)))
                (fun r =>
                   ITree.bind (let '(s2', x) := r in Ret (s2', inr x))
                     (fun '(s2'', res) =>
                        match res with
                        | inl ex => Ret (s2'', inl ex)
                        | inr uv =>
                            interp_cfg_exc ctx2 (ITree.bind (lwrite dst uv) (fun _ => Ret tt)) s2''
                        end)) ≅
              ITree.bind (interp_mcfg_model (lread lv_reg) (σ2, ((sf2_mid, fstk2), g)))
                (fun '(s2'0, v) =>
                   ITree.bind
                     (interp_mcfg_model
                        (convert CONV_Bitcast (DTYPE_Array true 1%N (gs_dt gs)) v (gs_dt gs)) s2'0)
                     (fun '(s2', x) =>
                        ITree.bind (Ret (s2', inr x))
                          (fun '(s2'', res) =>
                             match res with
                             | inl ex => Ret (s2'', inl ex)
                             | inr uv =>
                                 interp_cfg_exc ctx2 (ITree.bind (lwrite dst uv) (fun _ => Ret tt)) s2''
                             end)))).
    { rewrite (eq_itree_bind_congr_l EexpR), Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s2'0 v] _ <-; cbn beta iota.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s2' x] _ <-; reflexivity. }
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; exact Er_init |]; clear Er_init EexpR.
    eapply refine_prov_tau_star_l;
      [apply tau_star_bind, (tau_star_mcfg_lread_some p _ σ1 sf1 fstk1 g Hlk_p) |].
    eapply refine_prov_tau_star_r;
      [apply tau_star_bind, (tau_star_mcfg_lread_some lv_reg _ σ2 sf2_mid fstk2 g Hlk_lv) |].
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
    cbn beta iota.
    eapply refine_prov_obs_eq;
      [symmetry; apply Eqit.bind_ret_l | reflexivity |].
    cbn beta iota.
    rewrite (convert_bitcast_vec1_scalar_eq (gs_dt gs) (gs_db gs) (gs_bytes gs) Hsc Hser).
    destruct (assert_alignment_ret_or_ub
                (DVALUE_Base (DVALUE_Pointer (Pa := @ParamsV IP IPT) (gs_pt gs))) anns_ld
                ((set_loc (get_file_info md_ld) ++ location_error_string md_ld) ++
                 ": Load with overestimated alignment.")%string)
      as [Hal_ok | Hal_ub].
    - rewrite Hal_ok; cbn [EOU_to_itree ExtLib.Structures.Monad.ret Monad_itree].
      assert (Eld_l :
                ITree.bind (Ret tt)
                  (fun _ : unit =>
                     ITree.bind
                       (load (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT))
                          (gs_dt gs) (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))
                       (fun v =>
                          ITree.bind
                            (EOU_to_itree (E := @CFGEtop (@ParamsV IP IPT))
                               (apply_value_attrs (load_metadata_attrs md_ld)
                                  ((set_loc (get_file_info md_ld) ++ location_error_string md_ld) ++
                                   ": Loaded value violates !noundef.")%string
                                  (value_metadata_range (metadata_range md_ld) v)))
                            (fun v0 =>
                               ITree.bind
                                 (assert_load_dereferenceable (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT))
                                    md_ld v0
                                    ((set_loc (get_file_info md_ld) ++ location_error_string md_ld) ++
                                     ": Loaded value violates !dereferenceable.")%string)
                                 (fun _ => lwrite (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT)) dst v0)))) ≅
                ITree.bind
                  (load (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT))
                     (gs_dt gs) (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))
                  (fun v => lwrite (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT)) dst v)).
      { rewrite Eqit.bind_ret_l, Hlattrs, Hmrange.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros v _ <-; cbn [value_metadata_range].
        rewrite apply_value_attrs_nil_eq; cbn [EOU_to_itree ExtLib.Structures.Monad.ret Monad_itree].
        rewrite Eqit.bind_ret_l.
        unfold assert_load_dereferenceable; rewrite Hlderef;
          cbn [EOU_to_itree ExtLib.Structures.Monad.ret Monad_itree];
          rewrite Eqit.bind_ret_l; reflexivity. }
      eapply refine_prov_obs_eq;
        [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ Eld_l) | reflexivity |];
        clear Eld_l.
      exact (denote_mk_load_val_exp_ok_sim ctx1 ctx2 RExc dst U P_unprom gs G
               σ1 σ2 sf1 sf2_mid fstk1 fstk2 g Hinv).
    - rewrite Hal_ub; cbn [EOU_to_itree].
      eapply refine_prov_obs_eq;
        [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (raiseUB_bind_eq _ _)) | reflexivity |].
      apply refine_cfg_exc_raiseUB_l.
  Qed.


End MemoryAndSerialization.
