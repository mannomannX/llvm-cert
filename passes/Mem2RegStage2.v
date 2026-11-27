(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Mem2Reg Stage 2 Dead-Alloca Elimination Soundness ([CertPasses.Mem2RegStage2])

    Purpose:
      Proves CFG-level simulation for non-invoke terminators, [Phi] writes
      ([write_phi_dvs]), Stage 1 no-call blocks, and Stage 2 reverse-order
      dead scalar [alloca] elimination ([try_elim_dead_alloca_denote_function_sim]).

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml. Establishes per-function
      refinement for dead [alloca] removal on guarded leaf functions.

    Assumptions:
      Parametric over [IP : IPtr] and [IPT : @IPtrTheory IP] (with
      [IPtrWellBehaved IP] for Stage 2 [alloca] deletion); depends on
      [PassCommon] and [Mem2RegSpec]..[Mem2RegLeafKnot]; zero custom axioms.

    Section Outline:
      - [MemoryAndSerialization]: terminator/[Phi] sims, Stage 1 no-call code
        sim ([stage1_no_call_code_exc_sim]), and Stage 2 function sim. *)

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

From CertPasses Require Import
  Mem2RegSpec Mem2RegModel Mem2RegMemBase Mem2RegGhostInv
  Mem2RegExprLift Mem2RegCpsSSA Mem2RegLeafKnot.

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
  #[local] Hint Resolve ev_ok__mon : paco.


  Lemma m2r_collect_unique_allocas_intro
    (all_defs : list raw_id) (bks : ocfg dtyp)
    (bk : block dtyp) (q : local_id) (dt_q : dtyp)
    (anns_q : list (annotation dtyp)) (md_q : list (metadata dtyp)) :
    In bk bks ->
    In (IId q, INSTR_Alloca dt_q anns_q, md_q) (blk_code bk) ->
    m2r_count_id q all_defs = 1%nat ->
    In q (m2r_collect_unique_allocas all_defs bks).
  Proof using.
    intros Hbk Him Hcnt; unfold m2r_collect_unique_allocas.
    apply in_flat_map; exists bk; split; [exact Hbk |].
    apply in_flat_map; exists (IId q, INSTR_Alloca dt_q anns_q, md_q); split; [exact Him |].
    rewrite Hcnt; cbn; left; reflexivity.
  Qed.

  Lemma unique_def_code_split
    (fargs : list local_id) (bks : ocfg dtyp) (b_init : block dtyp)
    (pre_al : code dtyp) (p : local_id) (ins_p : instr dtyp)
    (md_p : list (metadata dtyp)) (post_al : code dtyp) :
    NoDup (List.map blk_id bks) ->
    In b_init bks ->
    blk_code b_init = pre_al ++ (IId p, ins_p, md_p) :: post_al ->
    m2r_count_id p (fargs ++ flat_map full_block_defs bks) = 1%nat ->
    ~ In p fargs /\
    ~ In p (List.map (fun '(x, _, _) => x) (blk_phis b_init)) /\
    ~ In p (flat_map (fun '(iid, _, _) => instr_id_defs iid) pre_al) /\
    ~ In p (flat_map (fun '(iid, _, _) => instr_id_defs iid) post_al) /\
    ~ In p (instr_id_defs (fst (fst (blk_term b_init)))) /\
    (forall bk, In bk bks -> blk_id bk <> blk_id b_init -> ~ In p (full_block_defs bk)).
  Proof using IP IPT.
    intros Hnd_ids Hin_init Hsplit Hcnt.
    pose proof (m2r_nodup_map_inv blk_id bks Hnd_ids) as Hnd_bks.
    assert (Hge_init :
              (m2r_count_id p (full_block_defs b_init) <=
               m2r_count_id p (flat_map full_block_defs bks))%nat).
    { clear -Hin_init; induction bks as [| b bs IH]; cbn [In flat_map] in *; [contradiction |].
      rewrite m2r_count_id_app; destruct Hin_init as [<- | Hin_init]; [lia | specialize (IH Hin_init); lia]. }
    rewrite m2r_count_id_app in Hcnt.
    assert (Hdefs_init :
              m2r_count_id p (List.map (fun '(x, _, _) => x) (blk_phis b_init)) = 0%nat /\
              m2r_count_id p (flat_map (fun '(iid, _, _) => instr_id_defs iid) pre_al) = 0%nat /\
              m2r_count_id p (flat_map (fun '(iid, _, _) => instr_id_defs iid) post_al) = 0%nat /\
              m2r_count_id p (instr_id_defs (fst (fst (blk_term b_init)))) = 0%nat /\
              m2r_count_id p fargs = 0%nat).
    { assert (Hsum : (1 +
                      m2r_count_id p (List.map (fun '(x, _, _) => x) (blk_phis b_init)) +
                      m2r_count_id p (flat_map (fun '(iid, _, _) => instr_id_defs iid) pre_al) +
                      m2r_count_id p (flat_map (fun '(iid, _, _) => instr_id_defs iid) post_al) +
                      m2r_count_id p (instr_id_defs (fst (fst (blk_term b_init)))) <=
                      m2r_count_id p (full_block_defs b_init))%nat).
      { unfold full_block_defs; rewrite Hsplit, m2r_flat_map_app.
        replace (flat_map (fun '(iid, _, _) => instr_id_defs iid) ((IId p, ins_p, md_p) :: post_al))
          with ([p] ++ flat_map (fun '(iid, _, _) => instr_id_defs iid) post_al) by reflexivity.
        rewrite !m2r_count_id_app.
        replace (m2r_count_id p [p]) with 1%nat
          by (cbn [m2r_count_id]; rewrite raw_id_eqb_refl; reflexivity).
        destruct (blk_term b_init) as [[tiid tm] tmd]; cbn [fst]; lia. }
      lia. }
    destruct Hdefs_init as (Hc_phi & Hc_pre & Hc_post & Hc_tm & Hc_fargs).
    rewrite m2r_count_id_zero in Hc_phi, Hc_pre, Hc_post, Hc_tm, Hc_fargs.
    refine (conj Hc_fargs (conj Hc_phi (conj Hc_pre (conj Hc_post (conj Hc_tm _))))).
    intros bk Hbk Hne_id Hdef_bk.
    assert (Hne_bk : bk <> b_init) by (intros ->; exact (Hne_id Logic.eq_refl)).
    assert (Hdef_init : In p (full_block_defs b_init)).
    { unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
      rewrite Hsplit; apply in_flat_map; exists (IId p, ins_p, md_p);
        split;
          [ apply in_app_iff; right; left; reflexivity
          | left; reflexivity ]. }
    pose proof (m2r_count_id_in_two_elems full_block_defs bks bk b_init p
                  Hnd_bks Hbk Hin_init Hne_bk Hdef_bk Hdef_init).
    lia.
  Qed.

  Lemma refine_cfg_exc_gread_same_g
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (gid : raw_id) (U : list N)
    (σ1 σ2 : state)
    (ls1 ls2 : @stack_frame (@ParamsV IP IPT) * stack)
    (g : @global_env (@ParamsV IP IPT)) :
    let s1 := (σ1, (ls1, g)) in
    let s2 := (σ2, (ls2, g)) in
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' v1 v2 =>
            U' = U /\ s1' = s1 /\ s2' = s2 /\ v1 = v2))
      U
      (interp_cfg_exc ctx1 (gread gid) s1)
      (interp_cfg_exc ctx2 (gread gid) s2).
  Proof using.
    intros s1 s2; unfold gread, Subevent.trigger.
    apply refine_cfg_exc_trigger; [reflexivity | reflexivity |].
    eapply refine_prov_tau_expand;
      [eapply tau_expand_obs_eq;
         [apply (interp_cfg_model_obs_eq ctx1 _ _ s1
                   (withCall_trigger_eq (subevent _ (GlobalRead gid))))
         | reflexivity
         | apply tau_expand_cfg_withCall_trigger]
      | eapply tau_expand_obs_eq;
          [apply (interp_cfg_model_obs_eq ctx2 _ _ s2
                    (withCall_trigger_eq (subevent _ (GlobalRead gid))))
          | reflexivity
          | apply tau_expand_cfg_withCall_trigger] |].
    eapply refine_prov_weaken; [apply (refine_mcfg_gread_same_g gid U σ1 σ2 ls1 ls2 g) |].
    intros U' [s1' v1] [s2' v2] (-> & -> & -> & <- & _);
      exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
  Qed.

  Lemma map_monad_indirectbr_addrs_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (f : function_id) (brs : list block_id) (U : list N)
    (σ1 σ2 : state)
    (ls1 ls2 : @stack_frame (@ParamsV IP IPT) * stack)
    (g : @global_env (@ParamsV IP IPT)) :
    let s1 := (σ1, (ls1, g)) in
    let s2 := (σ2, (ls2, g)) in
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' a1 a2 =>
            U' = U /\ s1' = s1 /\ s2' = s2 /\ a1 = a2))
      U
      (interp_cfg_exc ctx1
         (map_monad (fun b => ITree.bind (gread (blockaddress_id f b))
                                (fun ba => Ret (dvalue_ptr_address ba))) brs) s1)
      (interp_cfg_exc ctx2
         (map_monad (fun b => ITree.bind (gread (blockaddress_id f b))
                                (fun ba => Ret (dvalue_ptr_address ba))) brs) s2).
  Proof using.
    intros s1 s2; induction brs as [| b brs' IH];
      cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    - apply refine_cfg_exc_ret;
        exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
    - eapply refine_cfg_exc_bind
        with (RA := fun U' s1' s2' z1 z2 => U' = U /\ s1' = s1 /\ s2' = s2 /\ z1 = z2).
      + eapply refine_cfg_exc_bind; [apply refine_cfg_exc_gread_same_g |].
        intros U1 s1' ba1 s2' ba2 _ (-> & -> & -> & <-).
        apply refine_cfg_exc_ret;
          exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
      + intros U1 s1' oz1 s2' oz2 _ (-> & -> & -> & <-).
        eapply refine_cfg_exc_bind; [exact IH |].
        intros U2 s1'' ozs1 s2'' ozs2 _ (-> & -> & -> & <-).
        apply refine_cfg_exc_ret;
          exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
  Qed.

  Lemma denote_non_invoke_term_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (iid1 iid2 : instr_id) (tm : terminator dtyp) (md1 md2 : list (metadata dtyp))
    (U : list N) (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hni : m2r_non_invoke_term tm = true)
    (Hvars : forall x,
               In x (full_term_uses tm) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2))
    (Hexc : forall ex,
              RExc U (σ1, ((sf1, fstk1), g)) (σ2, ((sf2, fstk2), g)) ex ex) :
    let s1 := (σ1, ((sf1, fstk1), g)) in
    let s2 := (σ2, ((sf2, fstk2), g)) in
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            U' = U /\ s1' = s1 /\ s2' = s2 /\ r1 = r2 /\
            match r2 with
            | inl bid_target => In bid_target (m2r_term_succs tm)
            | inr _ => True
            end))
      U
      (interp_cfg_exc ctx1 (denote_terminator (iid1, tm, md1)) s1)
      (interp_cfg_exc ctx2 (denote_terminator (iid2, tm, md2)) s2).
  Proof using.
    intros s1 s2; cbn [denote_terminator].
    destruct tm as [[dt op] | | [dt op] br1 br2 | br | [dt e] default_br dests
                   | [t addr] brs fn | [t expr]
                   | [dt fnptrval] args to_label unwind_label anns obs |].
    - eapply refine_cfg_exc_bind; [apply denote_exp_cfg_exc_sim, Hvars |].
      intros U1 s1' dv1 s2' dv2 _ (-> & -> & -> & <- & _).
      apply refine_cfg_exc_ret;
        exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl I)))).
    - apply refine_cfg_exc_ret;
        exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl I)))).
    - eapply refine_cfg_exc_bind; [apply denote_exp_cfg_exc_sim, Hvars |].
      intros U1 s1' v1 s2' v2 _ (-> & -> & -> & <- & _).
      destruct v1 as [db | |];
        [| apply refine_cfg_exc_raise_both | apply refine_cfg_exc_raise_both].
      destruct db as [? | sz x | ? | ? | ? | | | ? ?]; cbv beta iota;
        lazymatch goal with
        | |- refine_prov _ _ (interp_cfg_exc _ (raise _) _) _ => apply refine_cfg_exc_raise_both
        | _ => idtac
        end.
      + destruct sz as [? | ? |];
          [apply refine_cfg_exc_raise_both | apply refine_cfg_exc_raise_both |].
        destruct (VellvmIntegers.equ x VellvmIntegers.one).
        * apply refine_cfg_exc_ret; cbn [m2r_term_succs];
            refine (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl _))));
            left; reflexivity.
        * apply refine_cfg_exc_ret; cbn [m2r_term_succs];
            refine (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl _))));
            right; left; reflexivity.
      + apply refine_cfg_exc_raiseUB_l.
    - apply refine_cfg_exc_ret; cbn [m2r_term_succs];
        refine (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl _))));
        left; reflexivity.
    - eapply refine_cfg_exc_bind; [apply denote_exp_cfg_exc_sim, Hvars |].
      intros U1 s1' sel1 s2' sel2 _ (-> & -> & -> & <- & _).
      destruct (dvalue_is_poison sel1); [apply refine_cfg_exc_raiseUB_l |].
      set (sw_eou :=
             ExtLib.Structures.Monad.bind
               (map_monad
                  (fun '((TInt_Literal sz x), id) =>
                     ExtLib.Structures.Monad.bind (coerce_integer_to_int (Some sz) (denote_int_syntax x))
                       (fun s => ExtLib.Structures.Monad.ret (@DVALUE_Base (@ParamsV IP IPT) s, id)))
                  dests)
               (fun switches => select_switch sel1 default_br switches)).
      destruct sw_eou as [msg | msg | msg | bid] eqn:Esw; cbn [EOU_to_itree].
      + eapply refine_cfg_exc_bind with (RA := fun _ _ _ _ _ => False);
          [apply refine_cfg_exc_raise_both | intros _ _ _ _ _ _ []].
      + eapply refine_prov_obs_eq; [symmetry; apply interp_cfg_exc_bind | symmetry; apply interp_cfg_exc_bind |].
        eapply PassCommonModel.refine_prov_bind with (RR := fun _ _ _ => False);
          [apply refine_cfg_exc_raiseOOM_l | intros _ _ _ _ []].
      + eapply refine_prov_obs_eq; [symmetry; apply interp_cfg_exc_bind | symmetry; apply interp_cfg_exc_bind |].
        eapply PassCommonModel.refine_prov_bind with (RR := fun _ _ _ => False);
          [apply refine_cfg_exc_raiseUB_l | intros _ _ _ _ []].
      + eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_exc_obs_eq, Eqit.bind_ret_l
          | symmetry; apply interp_cfg_exc_obs_eq, Eqit.bind_ret_l |].
        apply refine_cfg_exc_ret;
          refine (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl _)))).
        unfold sw_eou in Esw.
        destruct (map_monad _ dests) as [? | ? | ? | switches] eqn:Emm;
          cbn [ExtLib.Structures.Monad.bind EOU_monad] in Esw; try discriminate Esw.
        pose proof (switch_dests_map_snd dests switches Emm) as Hmap_eq.
        apply select_switch_in in Esw as [-> | Hin_sw]; cbn [m2r_term_succs].
        * left; reflexivity.
        * right; rewrite <- Hmap_eq; exact Hin_sw.
    - eapply refine_cfg_exc_bind; [apply denote_exp_cfg_exc_sim, Hvars |].
      intros U1 s1' a1 s2' a2 _ (-> & -> & -> & <- & _).
      destruct (dvalue_is_poison a1); [apply refine_cfg_exc_raiseUB_l |].
      destruct fn as [f |]; [| apply refine_cfg_exc_raise_both].
      eapply refine_cfg_exc_bind; [apply map_monad_indirectbr_addrs_exc_sim |].
      intros U2 s1'' addrs1 s2'' addrs2 _ (-> & -> & -> & <-).
      destruct (dvalue_ptr_address a1) as [z |]; [| apply refine_cfg_exc_raise_both].
      destruct (indirectbr_target z (List.combine brs addrs1)) as [b |] eqn:Eib;
        [| apply refine_cfg_exc_raiseUB_l].
      apply refine_cfg_exc_ret;
        refine (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl _)))).
      cbn [m2r_term_succs]; eapply indirectbr_target_In; exact Eib.
    - eapply refine_cfg_exc_bind; [apply denote_exp_cfg_exc_sim, Hvars |].
      intros U1 s1' ex1 s2' ex2 _ (-> & -> & -> & <- & _).
      apply refine_cfg_exc_raiseLLVM_both, Hexc.
    - discriminate Hni.
    - apply refine_cfg_exc_raiseUB_l.
  Qed.

  Fixpoint write_phi_dvs
    (dvs : list (local_id * @dvalue (@ParamsV IP IPT)))
    (env : @local_env (@ParamsV IP IPT)) : @local_env (@ParamsV IP IPT) :=
    match dvs with
    | [] => env
    | (id, dv) :: rest => write_phi_dvs rest (Maps.add id dv env)
    end.

  Lemma write_phi_dvs_lookup_not_in
    (dvs : list (local_id * @dvalue (@ParamsV IP IPT)))
    (env : @local_env (@ParamsV IP IPT)) (x : local_id) :
    ~ In x (List.map fst dvs) ->
    Maps.lookup x (write_phi_dvs dvs env) = Maps.lookup x env.
  Proof using.
    revert env; induction dvs as [| [id dv] rest IH]; intros env Hnin; cbn [write_phi_dvs List.map fst] in *.
    - reflexivity.
    - rewrite IH by (intros H; apply Hnin; right; exact H).
      cbn [Maps.lookup Maps.add Map_rmap]; apply RMF.F.add_neq_o;
        intros ->; apply Hnin; left; reflexivity.
  Qed.

  Lemma write_phi_dvs_lookup_agree
    (dvs : list (local_id * @dvalue (@ParamsV IP IPT)))
    (env1 env2 : @local_env (@ParamsV IP IPT)) (x : local_id) :
    Maps.lookup x env1 = Maps.lookup x env2 ->
    Maps.lookup x (write_phi_dvs dvs env1) = Maps.lookup x (write_phi_dvs dvs env2).
  Proof using.
    revert env1 env2; induction dvs as [| [id dv] rest IH]; intros env1 env2 Heq; cbn [write_phi_dvs].
    - exact Heq.
    - apply IH.
      cbn [Maps.lookup Maps.add Map_rmap].
      destruct (raw_id_eqb x id) eqn:Ex_id;
        [ apply raw_id_eqb_spec in Ex_id; subst x
        | apply raw_id_eqb_neq in Ex_id; rename Ex_id into Hne ].
      + rewrite !RMF.F.add_eq_o by reflexivity; reflexivity.
      + rewrite !RMF.F.add_neq_o by (intros Heq'; exact (Hne (Logic.eq_sym Heq'))); exact Heq.
  Qed.

  Lemma write_phi_dvs_safe_locals
    (P_safe : list N) (safe_sub : list local_id)
    (dvs : list (local_id * @dvalue (@ParamsV IP IPT)))
    (env : @local_env (@ParamsV IP IPT)) :
    (forall q, In q safe_sub -> ~ In q (List.map fst dvs)) ->
    safe_locals_env P_safe safe_sub env ->
    safe_locals_env P_safe safe_sub (write_phi_dvs dvs env).
  Proof using.
    revert env; induction dvs as [| [id dv] rest IH]; intros env Hdisj Hsafe; cbn [write_phi_dvs].
    - exact Hsafe.
    - apply IH.
      + intros q Hq H; eapply Hdisj; [exact Hq | right; exact H].
      + apply safe_locals_env_add_other; [| exact Hsafe].
        intros Hid; eapply Hdisj; [exact Hid | left; reflexivity].
  Qed.

  Lemma tau_star_cfg_exc_write_phi_dvs
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dvs : list (local_id * @dvalue (@ParamsV IP IPT)))
    (σ : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env) :
    tau_star
      (interp_cfg_exc ctx
         (ITree.bind (map_monad (fun '(id, dv) => lwrite id dv) dvs) (fun _ => Ret tt))
         (σ, ((sf, fstk), g)))
      (Ret ((σ, ((upd_local_sf sf (write_phi_dvs dvs (stack_vars sf)), fstk), g)), inr tt)).
  Proof using.
    revert sf; induction dvs as [| [id dv] rest IH]; intros sf;
      cbn [map_monad write_phi_dvs ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    - eapply tau_star_trans.
      + eapply TS_Eq;
          [rewrite (interp_cfg_exc_obs_eq ctx _ _ _ (Eqit.bind_ret_l _ _)),
                   interp_cfg_exc_ret; reflexivity
          | apply TS_Refl].
      + destruct sf as [sv se sl]; cbn; apply TS_Refl.
    - eapply tau_star_trans.
      + eapply TS_Eq;
          [rewrite (interp_cfg_exc_obs_eq ctx _ _ _ (Eqit.bind_bind _ _ _)),
                   interp_cfg_exc_bind; reflexivity
          | apply tau_star_bind, tau_star_cfg_exc_lwrite].
      + eapply tau_star_trans.
        * eapply TS_Eq; [rewrite Eqit.bind_ret_l; reflexivity |].
          eapply TS_Eq;
            [apply interp_cfg_exc_obs_eq;
             rewrite Eqit.bind_bind;
             eapply eq_itree_clo_bind with (UU := Logic.eq) (k2 := fun _ : list unit => Ret tt);
               [reflexivity | intros bs _ _; rewrite Eqit.bind_ret_l; reflexivity]
            | apply IH].
        * destruct sf as [sv se sl]; cbn; apply TS_Refl.
  Qed.

  Lemma find_option_ann_num_elements_uses {T : Set}
    (anns : list (annotation T)) (t : T) (num_exp : exp T) :
    find_option ann_num_elements anns = Some (t, num_exp) ->
    forall x, In x (full_exp_uses num_exp) -> In x (flat_map full_ann_uses anns).
  Proof using.
    induction anns as [| a rest IH]; cbn [find_option flat_map]; [intros H; discriminate H |].
    destruct a; cbn [ann_num_elements full_ann_uses];
      try (intros H x Hx; apply in_app_iff; right; exact (IH H x Hx)).
    intros H x Hx; inversion H; subst;
      apply in_app_iff; left; exact Hx.
  Qed.

  Lemma map_monad_denote_phi_same_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (bid_from : block_id)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (U : list N) (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hvars : forall x,
               In x (flat_map m2r_phi_entry_uses phis) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    let s1 := (σ1, ((sf1, fstk1), g)) in
    let s2 := (σ2, ((sf2, fstk2), g)) in
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' dvs1 dvs2 =>
            U' = U /\ s1' = s1 /\ s2' = s2 /\ dvs1 = dvs2 /\
            List.map fst dvs2 = List.map (fun '(id, _, _) => id) phis))
      U
      (interp_cfg_exc ctx1 (map_monad (denote_phi bid_from) phis) s1)
      (interp_cfg_exc ctx2 (map_monad (denote_phi bid_from) phis) s2).
  Proof using.
    intros s1 s2; induction phis as [| [[id [fmf dt p_args]] md] rest IH];
      cbn [map_monad denote_phi ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree List.map].
    - apply refine_cfg_exc_ret; repeat split; reflexivity.
    - destruct (assoc bid_from p_args) as [op |] eqn:Eassoc.
      + destruct (m2r_assoc_in bid_from p_args op Eassoc) as [k0 Hin_op].
        eapply refine_cfg_exc_bind with
          (RA := fun U' s1' s2' p1 p2 =>
                   U' = U /\ s1' = s1 /\ s2' = s2 /\ p1 = p2 /\ fst p2 = id).
        * eapply refine_cfg_exc_bind.
          -- apply denote_exp_cfg_exc_sim.
             intros x Hx; apply Hvars.
             cbn [flat_map m2r_phi_entry_uses full_phi_uses].
             apply in_app_iff; left; apply in_app_iff; left.
             apply in_flat_map; exists (k0, op); split; [exact Hin_op | exact Hx].
          -- intros U1 s1' uv1 s2' uv2 _ (-> & -> & -> & <- & _).
             apply refine_cfg_exc_ret;
               repeat match goal with |- _ /\ _ => split end; reflexivity.
        * intros U1 s1' p1 s2' p2 _ (-> & -> & -> & <- & Hfst_p).
          eapply refine_cfg_exc_bind.
          -- apply IH; intros x Hx; apply Hvars; cbn [flat_map];
               apply in_app_iff; right; exact Hx.
          -- intros U2 s1'' dvs1 s2'' dvs2 _ (-> & -> & -> & <- & Hfst).
             apply refine_cfg_exc_ret;
               repeat match goal with |- _ /\ _ => split end;
               try reflexivity; cbn [List.map]; rewrite Hfst_p, Hfst; reflexivity.
      + eapply refine_cfg_exc_bind with (RA := fun _ _ _ _ _ => False);
          [apply refine_cfg_exc_raise_both | intros _ _ _ _ _ _ []].
  Qed.

  Lemma denote_phis_same_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (bid_from : block_id)
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (U : list N) (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hvars : forall x,
               In x (flat_map m2r_phi_entry_uses phis) ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists dvs,
              U' = U /\ r1 = tt /\ r2 = tt /\
              List.map fst dvs = List.map (fun '(id, _, _) => id) phis /\
              s1' = (σ1, ((upd_local_sf sf1 (write_phi_dvs dvs (stack_vars sf1)), fstk1), g)) /\
              s2' = (σ2, ((upd_local_sf sf2 (write_phi_dvs dvs (stack_vars sf2)), fstk2), g))))
      U
      (interp_cfg_exc ctx1 (denote_phis bid_from phis) (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2 (denote_phis bid_from phis) (σ2, ((sf2, fstk2), g))).
  Proof using.
    unfold denote_phis.
    eapply refine_cfg_exc_bind; [apply map_monad_denote_phi_same_exc_sim, Hvars |].
    intros U1 s1' dvs1 s2' dvs2 _ (-> & -> & -> & <- & Hfst).
    eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_write_phi_dvs |].
    eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_write_phi_dvs |].
    apply refine_prov_ret; exists dvs1; repeat (first [exact Hfst | reflexivity | split]).
  Qed.

  Lemma stage1_alloca_lwrite_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (id0 : local_id) (dt_a : dtyp) (num : N) (align : option N)
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists pr ptrs v σ1' σ2',
              ~ In pr U /\
              U' = pr :: U /\ r1 = tt /\ r2 = tt /\
              is_safe_ptr_dvalue (pr :: P_unprom) v /\
              stage1_mem_inv (pr :: U) (pr :: P_unprom) G σ1' σ2' /\
              (forall z, In z (List.map ptr_to_int ptrs) -> forall gs, In gs G -> ~ gs_in_range gs z) /\
              Memory_stack_frame_stack (state_memory_stack σ2') =
                Memory_stack_frame_stack (add_all_to_frame ptrs (state_memory_stack σ2)) /\
              s1' = (σ1', ((upd_local_sf sf1 (Maps.add id0 v (stack_vars sf1)), fstk1), g)) /\
              s2' = (σ2', ((upd_local_sf sf2 (Maps.add id0 v (stack_vars sf2)), fstk2), g))))
      U
      (interp_cfg_exc ctx1 (ITree.bind (alloca dt_a num align) (fun v => lwrite id0 v))
         (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2 (ITree.bind (alloca dt_a num align) (fun v => lwrite id0 v))
         (σ2, ((sf2, fstk2), g))).
  Proof using.
    eapply refine_cfg_exc_bind with
      (RA := fun U' s1' s2' v1 v2 =>
               exists pr ptrs σ1' σ2',
                 ~ In pr U /\
                 U' = pr :: U /\
                 v1 = v2 /\
                 is_safe_ptr_dvalue (pr :: P_unprom) v1 /\
                 stage1_mem_inv (pr :: U) (pr :: P_unprom) G σ1' σ2' /\
                 (forall z, In z (List.map ptr_to_int ptrs) -> forall gs, In gs G -> ~ gs_in_range gs z) /\
                 Memory_stack_frame_stack (state_memory_stack σ2') =
                   Memory_stack_frame_stack (add_all_to_frame ptrs (state_memory_stack σ2)) /\
                 s1' = (σ1', ((sf1, fstk1), g)) /\
                 s2' = (σ2', ((sf2, fstk2), g))).
    - unfold alloca, Subevent.trigger; try unfold trigger_cast.
      apply refine_cfg_exc_memory_event.
      eapply refine_prov_weaken;
        [exact (stage1_alloca_unprom dt_a num align U P_unprom G σ1 σ2 Hinv) |].
      intros U1 [σ1' v1] [σ2' v2]
        (pr & ptrs & Hnin & -> & <- & Hsafe_v & Hinv' & Hdisj & Hfs').
      exists pr, ptrs, σ1', σ2';
        exact (conj Hnin (conj Logic.eq_refl (conj Logic.eq_refl
                 (conj Hsafe_v (conj Hinv' (conj Hdisj (conj Hfs' (conj Logic.eq_refl Logic.eq_refl)))))))).
    - intros U1 s1' v1 s2' _ _
        (pr & ptrs & σ1' & σ2' & Hnin & -> & <- & Hsafe_v & Hinv' & Hdisj & Hfs' & -> & ->).
      eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
      eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_lwrite |].
      apply refine_prov_ret.
      exists pr, ptrs, v1, σ1', σ2'; repeat match goal with |- _ /\ _ => split end; try reflexivity; assumption.
  Qed.

  Lemma stage1_no_call_instr_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (TF : state -> Prop)
    (fargs : list local_id) (bks : ocfg dtyp) (bk : block dtyp)
    (pre_c post_c : code dtyp)
    (safe_sub : list local_id) (p : local_id)
    (im : instr_id * instr dtyp * list (metadata dtyp))
    (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hnd_bks : NoDup (List.map blk_id bks))
    (Hbk : In bk bks)
    (Hsplit : blk_code bk = pre_c ++ im :: post_c)
    (Hsub : forall q,
              In q safe_sub ->
              In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
    (Hchk : check_other_instr_for_slot false safe_sub p im = true)
    (HTF_eq : forall s_a s_b,
                Memory_stack_frame_stack (state_memory_stack s_b) =
                  Memory_stack_frame_stack (state_memory_stack s_a) ->
                TF s_a -> TF s_b)
    (HTF_add : forall s_a s_b ptrs,
                 (forall z, In z (List.map ptr_to_int ptrs) -> forall gs0, In gs0 G -> ~ gs_in_range gs0 z) ->
                 Memory_stack_frame_stack (state_memory_stack s_b) =
                   Memory_stack_frame_stack (add_all_to_frame ptrs (state_memory_stack s_a)) ->
                 TF s_a -> TF s_b)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2)
    (HTF : TF σ2)
    (Hgenv : genv_safe P_unprom g)
    (Hsafe_loc : safe_locals_env P_unprom safe_sub (stack_vars sf2))
    (Huse_vars : forall x,
                   In x (m2r_code_entry_uses im) ->
                   Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists P_unprom' σ1' σ2' sf1' sf2',
              incl U U' /\
              incl P_unprom P_unprom' /\
              r1 = tt /\ r2 = tt /\
              s1' = (σ1', ((sf1', fstk1), g)) /\
              s2' = (σ2', ((sf2', fstk2), g)) /\
              stage1_mem_inv U' P_unprom' G σ1' σ2' /\
              TF σ2' /\
              genv_safe P_unprom' g /\
              safe_locals_env P_unprom' safe_sub (stack_vars sf2') /\
              ((sf1' = sf1 /\ sf2' = sf2) \/
               (exists id0 v,
                  fst (fst im) = IId id0 /\
                  sf1' = upd_local_sf sf1 (Maps.add id0 v (stack_vars sf1)) /\
                  sf2' = upd_local_sf sf2 (Maps.add id0 v (stack_vars sf2))))))
      U
      (interp_cfg_exc ctx1 (denote_instr im va1) (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2 (denote_instr im va2) (σ2, ((sf2, fstk2), g))).
  Proof using.
    destruct (check_other_instr_for_slot_inv false safe_sub p im Hchk)
      as (_ & Hsafe_im & Hnocall).
    destruct im as [[iid ins] md].
    destruct iid as [id0 | vid0], ins; cbn [m2r_safe_mem_instr_any] in Hsafe_im;
      try discriminate Hsafe_im.
    - (* IId id0, INSTR_Op op *)
      assert (Hnid_safe : ~ In id0 safe_sub).
      { intros Hin_s.
        destruct (unique_alloca_code_def_is_alloca fargs bks id0 Hnd_bks (Hsub id0 Hin_s)
                    bk pre_c (INSTR_Op op) md post_c Hbk Hsplit) as (? & ? & Hbad);
          discriminate Hbad. }
      cbn [denote_instr].
      eapply refine_cfg_exc_bind.
      + apply denote_exp_cfg_exc_sim.
        intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses];
          apply in_app_iff; left; exact Hx.
      + intros U1 s1' uv1 s2' uv2 _ (-> & -> & -> & <- & _).
        eapply refine_prov_obs_eq;
          [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (bind_unit_ret_r _))
          | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (bind_unit_ret_r _)) |].
        eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
        eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_lwrite |].
        apply refine_prov_ret.
        exists P_unprom, σ1, σ2,
               (upd_local_sf sf1 (Maps.add id0 uv1 (stack_vars sf1))),
               (upd_local_sf sf2 (Maps.add id0 uv1 (stack_vars sf2))).
        refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Logic.eq_refl (conj Logic.eq_refl
                      (conj Hinv (conj HTF (conj Hgenv (conj _ _)))))))))).
        * apply safe_locals_env_add_other; [exact Hnid_safe | exact Hsafe_loc].
        * right; exists id0, uv1; repeat split; reflexivity.
    - (* IId id0, INSTR_Call -> impossible since allow_calls = false *)
      exfalso; exact (Hnocall Logic.eq_refl (IId id0) fn args anns obs md Logic.eq_refl).
    - (* IId id0, INSTR_Alloca dt anns *)
      cbn [denote_instr].
      eapply refine_cfg_exc_bind.
      + destruct (find_option ann_num_elements anns) as [[t_num num_exp] |] eqn:Enum.
        * eapply refine_cfg_exc_bind.
          -- apply denote_exp_cfg_exc_sim.
             intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses].
             apply in_app_iff; left.
             exact (find_option_ann_num_elements_uses anns t_num num_exp Enum x Hx).
          -- intros U1 s1' n1 s2' n2 _ (-> & -> & -> & <- & _).
             destruct (dvalue_is_poison n1); [apply refine_cfg_exc_raiseUB_l |].
             eapply refine_cfg_exc_bind with
               (RA := fun U' s1' s2' nb1 nb2 =>
                        U' = U /\
                        s1' = (σ1, ((sf1, fstk1), g)) /\
                        s2' = (σ2, ((sf2, fstk2), g)) /\
                        nb1 = nb2).
             ++ eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
                intros nb1 nb2 <-; repeat split; reflexivity.
             ++ intros U2 s1'' nb1 s2'' nb2 _ (-> & -> & -> & <-).
                exact (stage1_alloca_lwrite_exc_sim ctx1 ctx2 RExc id0 t
                         (Z.to_N (dvalue_base_int_unsigned nb1))
                         (explicit_alignment anns)
                         U P_unprom G σ1 σ2 sf1 sf2 fstk1 fstk2 g Hinv).
        * exact (stage1_alloca_lwrite_exc_sim ctx1 ctx2 RExc id0 t 1%N
                   (explicit_alignment anns)
                   U P_unprom G σ1 σ2 sf1 sf2 fstk1 fstk2 g Hinv).
      + intros U1 s1' _ s2' _ _
          (pr & ptrs & v & σ1' & σ2' & Hnin & -> & _ & _ & Hsafe_v & Hinv' & Hdisj & Hfs' & -> & ->).
        apply refine_cfg_exc_ret.
        assert (HincP : incl P_unprom (pr :: P_unprom)) by (intros x Hx; right; exact Hx).
        exists (pr :: P_unprom), σ1', σ2',
               (upd_local_sf sf1 (Maps.add id0 v (stack_vars sf1))),
               (upd_local_sf sf2 (Maps.add id0 v (stack_vars sf2))).
        refine (conj (fun x Hx => or_intror Hx) (conj HincP
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Logic.eq_refl (conj Logic.eq_refl
                      (conj Hinv' (conj (HTF_add σ2 σ2' ptrs Hdisj Hfs' HTF)
                        (conj (genv_safe_incl P_unprom (pr :: P_unprom) g HincP Hgenv)
                          (conj _ _)))))))))).
        * apply safe_locals_env_add_safe; [exact Hsafe_v |].
          exact (safe_locals_env_incl P_unprom (pr :: P_unprom) safe_sub (stack_vars sf2) HincP Hsafe_loc).
        * right; exists id0, v; repeat split; reflexivity.
    - (* IId id0, INSTR_Load t ptr anns *)
      destruct ptr as [du_l ptr_e].
      assert (Hnid_safe : ~ In id0 safe_sub).
      { intros Hin_s.
        destruct (unique_alloca_code_def_is_alloca fargs bks id0 Hnd_bks (Hsub id0 Hin_s)
                    bk pre_c (INSTR_Load t (du_l, ptr_e) anns) md post_c Hbk Hsplit)
          as (? & ? & Hbad); discriminate Hbad. }
      cbn [denote_instr].
      eapply refine_cfg_exc_bind.
      + apply denote_exp_cfg_exc_sim.
        intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
          apply in_app_iff; left; apply in_app_iff; left; exact Hx.
      + intros U1 s1' a1 s2' a2 _ (-> & -> & -> & <- & Hptr_safe).
        pose proof (Hptr_safe P_unprom safe_sub Hgenv Hsafe_loc Hsafe_im) as Ha_safe.
        eapply refine_cfg_exc_bind with
          (RA := fun U' s1' s2' (_ _ : unit) =>
                   U' = U /\
                   s1' = (σ1, ((sf1, fstk1), g)) /\
                   s2' = (σ2, ((sf2, fstk2), g))).
        * eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
          intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
        * intros U2 s1'' _ s2'' _ _ (-> & -> & ->).
          eapply refine_cfg_exc_bind with
            (RA := fun U' s1' s2' v1 v2 =>
                     U' = U /\
                     s1' = (σ1, ((sf1, fstk1), g)) /\
                     s2' = (σ2, ((sf2, fstk2), g)) /\
                     v1 = v2).
          -- unfold load, Subevent.trigger; try unfold trigger_cast.
             apply refine_cfg_exc_memory_event.
             eapply refine_prov_weaken;
               [exact (stage1_load_unprom t a1 U P_unprom G σ1 σ2 Hinv Ha_safe) |].
             intros U3 [σ1_l v1] [σ2_l v2] (-> & -> & -> & ->);
               exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
          -- intros U3 s1_l v1 s2_l _ _ (-> & -> & -> & <-).
             eapply refine_cfg_exc_bind with
               (RA := fun U' s1' s2' w1 w2 =>
                        U' = U /\
                        s1' = (σ1, ((sf1, fstk1), g)) /\
                        s2' = (σ2, ((sf2, fstk2), g)) /\
                        w1 = w2).
             ++ eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
                intros w1 w2 <-; repeat split; reflexivity.
             ++ intros U4 s1_a w1 s2_a w2 _ (-> & -> & -> & <-).
                eapply refine_cfg_exc_bind.
                ** exact (assert_load_dereferenceable_stage1_exc_sim ctx1 ctx2 RExc md w1 _ _
                            U P_unprom G σ1 σ2 ((sf1, fstk1), g) ((sf2, fstk2), g) Hinv).
                ** intros U5 s1_d _ s2_d _ _ (-> & -> & -> & _ & _).
                   eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
                   eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_lwrite |].
                   apply refine_prov_ret.
                   exists P_unprom, σ1, σ2,
                          (upd_local_sf sf1 (Maps.add id0 w1 (stack_vars sf1))),
                          (upd_local_sf sf2 (Maps.add id0 w1 (stack_vars sf2))).
                   refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                             (conj Logic.eq_refl (conj Logic.eq_refl
                               (conj Logic.eq_refl (conj Logic.eq_refl
                                 (conj Hinv (conj HTF (conj Hgenv (conj _ _)))))))))).
                   --- apply safe_locals_env_add_other; [exact Hnid_safe | exact Hsafe_loc].
                   --- right; exists id0, w1; repeat split; reflexivity.
    - (* IId id0, INSTR_Fence *)
      cbn [denote_instr]; apply refine_cfg_exc_ret.
      exists P_unprom, σ1, σ2, sf1, sf2.
      refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                (conj Logic.eq_refl (conj Logic.eq_refl
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Hinv (conj HTF (conj Hgenv (conj Hsafe_loc _)))))))))).
      left; split; reflexivity.
    - (* IVoid vid0, INSTR_Comment *)
      cbn [denote_instr]; apply refine_cfg_exc_ret.
      exists P_unprom, σ1, σ2, sf1, sf2.
      refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                (conj Logic.eq_refl (conj Logic.eq_refl
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Hinv (conj HTF (conj Hgenv (conj Hsafe_loc _)))))))))).
      left; split; reflexivity.
    - (* IVoid vid0, INSTR_Call -> impossible since allow_calls = false *)
      exfalso; exact (Hnocall Logic.eq_refl (IVoid vid0) fn args anns obs md Logic.eq_refl).
    - (* IVoid vid0, INSTR_Store val ptr anns *)
      destruct val as [dt_s val_e], ptr as [du_s ptr_e].
      cbn [denote_instr].
      eapply refine_cfg_exc_bind.
      + apply denote_exp_cfg_exc_sim.
        intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
          apply in_app_iff; left; apply in_app_iff; left; exact Hx.
      + intros U1 s1' v1 s2' v2 _ (-> & -> & -> & <- & _).
        eapply refine_cfg_exc_bind.
        * apply denote_exp_cfg_exc_sim.
          intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
            apply in_app_iff; left; apply in_app_iff;
            right; apply in_app_iff; left; exact Hx.
        * intros U2 s1'' a1 s2'' a2 _ (-> & -> & -> & <- & Hptr_safe).
          pose proof (Hptr_safe P_unprom safe_sub Hgenv Hsafe_loc Hsafe_im) as Ha_safe.
          eapply refine_cfg_exc_bind with
            (RA := fun U' s1' s2' (_ _ : unit) =>
                     U' = U /\
                     s1' = (σ1, ((sf1, fstk1), g)) /\
                     s2' = (σ2, ((sf2, fstk2), g))).
          -- eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
             intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
          -- intros U3 s1_a _ s2_a _ _ (-> & -> & ->).
             assert (Hdo_store :
                       forall a_st : @dvalue (@ParamsV IP IPT),
                         is_safe_ptr_dvalue P_unprom a_st ->
                         refine_prov
                           (exc_post RExc
                              (fun U' s1' s2' r1 r2 =>
                                 exists P_unprom' σ1' σ2' sf1' sf2',
                                   incl U U' /\
                                   incl P_unprom P_unprom' /\
                                   r1 = tt /\ r2 = tt /\
                                   s1' = (σ1', ((sf1', fstk1), g)) /\
                                   s2' = (σ2', ((sf2', fstk2), g)) /\
                                   stage1_mem_inv U' P_unprom' G σ1' σ2' /\
                                   TF σ2' /\
                                   genv_safe P_unprom' g /\
                                   safe_locals_env P_unprom' safe_sub (stack_vars sf2') /\
                                   ((sf1' = sf1 /\ sf2' = sf2) \/
                                    (exists id0 v,
                                       IVoid vid0 = IId id0 /\
                                       sf1' = upd_local_sf sf1 (Maps.add id0 v (stack_vars sf1)) /\
                                       sf2' = upd_local_sf sf2 (Maps.add id0 v (stack_vars sf2))))))
                           U
                           (interp_cfg_exc ctx1 (ITree.bind (store dt_s a_st v1) (fun _ => Ret tt))
                              (σ1, ((sf1, fstk1), g)))
                           (interp_cfg_exc ctx2 (ITree.bind (store dt_s a_st v1) (fun _ => Ret tt))
                              (σ2, ((sf2, fstk2), g)))).
             { intros a_st Ha_st.
               eapply refine_cfg_exc_bind with
                 (RA := fun U' s1' s2' _ _ =>
                          exists σ1' σ2',
                            U' = U /\
                            stage1_mem_inv U P_unprom G σ1' σ2' /\
                            Memory_stack_frame_stack (state_memory_stack σ2') =
                              Memory_stack_frame_stack (state_memory_stack σ2) /\
                            s1' = (σ1', ((sf1, fstk1), g)) /\
                            s2' = (σ2', ((sf2, fstk2), g))).
               - unfold store, Subevent.trigger; try unfold trigger_cast.
                 apply refine_cfg_exc_memory_event.
                 eapply refine_prov_weaken;
                   [exact (stage1_store_unprom dt_s a_st v1 U P_unprom G σ1 σ2 Hinv Ha_st) |].
                 intros U4 [σ1' []] [σ2' []] (-> & _ & _ & Hinv' & Hfs').
                 exists σ1', σ2';
                   exact (conj Logic.eq_refl (conj Hinv' (conj Hfs' (conj Logic.eq_refl Logic.eq_refl)))).
               - intros U4 s1' _ s2' _ _ (σ1' & σ2' & -> & Hinv' & Hfs' & -> & ->).
                 apply refine_cfg_exc_ret.
                 exists P_unprom, σ1', σ2', sf1, sf2.
                 refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                           (conj Logic.eq_refl (conj Logic.eq_refl
                             (conj Logic.eq_refl (conj Logic.eq_refl
                               (conj Hinv' (conj (HTF_eq σ2 σ2' Hfs' HTF)
                                 (conj Hgenv (conj Hsafe_loc _)))))))))).
                 left; split; reflexivity. }
             destruct a1 as [[? | ? ? | ? | ? | ? | | | ? ?] | |];
               try (apply Hdo_store, Ha_safe).
             eapply refine_prov_obs_eq;
               [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (raiseUB_bind_eq _ _)) | reflexivity |].
             apply refine_cfg_exc_raiseUB_l.
    - (* IVoid vid0, INSTR_Fence *)
      cbn [denote_instr]; apply refine_cfg_exc_ret.
      exists P_unprom, σ1, σ2, sf1, sf2.
      refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                (conj Logic.eq_refl (conj Logic.eq_refl
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Hinv (conj HTF (conj Hgenv (conj Hsafe_loc _)))))))))).
      left; split; reflexivity.
  Qed.

  Lemma stage1_no_call_code_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (TF : state -> Prop)
    (fargs : list local_id) (bks : ocfg dtyp) (bk : block dtyp)
    (pre_c cd post_c : code dtyp)
    (safe_sub : list local_id) (p : local_id)
    (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hnd_bks : NoDup (List.map blk_id bks))
    (Hbk : In bk bks)
    (Hsplit : blk_code bk = pre_c ++ cd ++ post_c)
    (Hsub : forall q,
              In q safe_sub ->
              In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
    (Hchk : forallb (check_other_instr_for_slot false safe_sub p) cd = true)
    (HTF_eq : forall s_a s_b,
                Memory_stack_frame_stack (state_memory_stack s_b) =
                  Memory_stack_frame_stack (state_memory_stack s_a) ->
                TF s_a -> TF s_b)
    (HTF_add : forall s_a s_b ptrs,
                 (forall z, In z (List.map ptr_to_int ptrs) -> forall gs0, In gs0 G -> ~ gs_in_range gs0 z) ->
                 Memory_stack_frame_stack (state_memory_stack s_b) =
                   Memory_stack_frame_stack (add_all_to_frame ptrs (state_memory_stack s_a)) ->
                 TF s_a -> TF s_b)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2)
    (HTF : TF σ2)
    (Hgenv : genv_safe P_unprom g)
    (Hsafe_loc : safe_locals_env P_unprom safe_sub (stack_vars sf2))
    (Hvars : forall x,
               x <> p ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists P_unprom' σ1' σ2' sf1' sf2',
              incl U U' /\
              incl P_unprom P_unprom' /\
              r1 = tt /\ r2 = tt /\
              s1' = (σ1', ((sf1', fstk1), g)) /\
              s2' = (σ2', ((sf2', fstk2), g)) /\
              stage1_mem_inv U' P_unprom' G σ1' σ2' /\
              TF σ2' /\
              genv_safe P_unprom' g /\
              safe_locals_env P_unprom' safe_sub (stack_vars sf2') /\
              (forall x, x <> p -> Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf2')) /\
              (forall x,
                 ~ In x (flat_map (fun '(iid, _, _) => instr_id_defs iid) cd) ->
                 Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf1) /\
                 Maps.lookup x (stack_vars sf2') = Maps.lookup x (stack_vars sf2)) /\
              (sf1 = sf2 -> sf1' = sf2')))
      U
      (interp_cfg_exc ctx1 (denote_code cd va1) (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2 (denote_code cd va2) (σ2, ((sf2, fstk2), g))).
  Proof using.
    revert pre_c U P_unprom σ1 σ2 sf1 sf2 Hsplit Hchk Hinv HTF Hgenv Hsafe_loc Hvars.
    induction cd as [| im rest IH];
      intros pre_c U P_unprom σ1 σ2 sf1 sf2 Hsplit Hchk Hinv HTF Hgenv Hsafe_loc Hvars;
      unfold denote_code; cbn [forallb] in Hchk; cbn [loop_monad flat_map].
    - apply refine_cfg_exc_ret.
      exists P_unprom, σ1, σ2, sf1, sf2.
      refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                (conj Logic.eq_refl (conj Logic.eq_refl
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Hinv (conj HTF (conj Hgenv (conj Hsafe_loc
                      (conj Hvars (conj (fun _ _ => conj Logic.eq_refl Logic.eq_refl)
                                        (fun Heq => Heq))))))))))))).
    - rewrite andb_true_iff in Hchk; destruct Hchk as [Hchk_im Hchk_rest].
      assert (Huse_im : forall x,
                In x (m2r_code_entry_uses im) ->
                Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)).
      { intros x Hx; apply Hvars; intros ->.
        exact (proj1 (check_other_instr_for_slot_inv false safe_sub p im Hchk_im) Hx). }
      eapply refine_cfg_exc_bind.
      + exact (stage1_no_call_instr_exc_sim ctx1 ctx2 RExc TF fargs bks bk pre_c (rest ++ post_c)
                 safe_sub p im va1 va2 U P_unprom G σ1 σ2 sf1 sf2 fstk1 fstk2 g
                 Hnd_bks Hbk Hsplit Hsub Hchk_im HTF_eq HTF_add Hinv HTF Hgenv Hsafe_loc Huse_im).
      + intros U1 s1_m _ s2_m _ _
          (P1 & σ1_m & σ2_m & sf1_m & sf2_m &
           HincU1 & HincP1 & _ & _ & -> & -> & Hinv1 & HTF1 & Hgenv1 & Hsafe1 & Hsf_step).
        assert (Hvars1 : forall x, x <> p -> Maps.lookup x (stack_vars sf1_m) = Maps.lookup x (stack_vars sf2_m)).
        { intros x Hne.
          destruct Hsf_step as [[-> ->] | (id0 & v & _ & -> & ->)].
          - exact (Hvars x Hne).
          - cbn [stack_vars upd_local_sf Maps.lookup Maps.add Map_rmap].
            destruct (raw_id_eqb x id0) eqn:Ex_id;
              [ apply raw_id_eqb_spec in Ex_id; subst x
              | apply raw_id_eqb_neq in Ex_id; rename Ex_id into Hne_id ].
            + rewrite !RMF.F.add_eq_o by reflexivity; reflexivity.
            + rewrite !RMF.F.add_neq_o by (intros Heq'; exact (Hne_id (Logic.eq_sym Heq'))); exact (Hvars x Hne). }
        assert (Hsplit_rest : blk_code bk = (pre_c ++ [im]) ++ rest ++ post_c).
        { rewrite <- app_assoc; exact Hsplit. }
        eapply refine_prov_weaken.
        * exact (IH (pre_c ++ [im]) U1 P1 σ1_m σ2_m sf1_m sf2_m
                   Hsplit_rest Hchk_rest Hinv1 HTF1 Hgenv1 Hsafe1 Hvars1).
        * intros U2 [s1_f res1] [s2_f res2].
          destruct res1 as [ex1 | u1], res2 as [ex2 | u2]; cbn [exc_post];
            try (intros H; exact H).
          intros (P2 & σ1_f & σ2_f & sf1_f & sf2_f &
                  HincU2 & HincP2 & -> & -> & -> & -> & Hinv2 & HTF2 & Hgenv2 & Hsafe2 &
                  Hvars2 & Hpres2 & Heq2).
          exists P2, σ1_f, σ2_f, sf1_f, sf2_f.
          refine (conj (incl_tran HincU1 HincU2) (conj (incl_tran HincP1 HincP2)
                    (conj Logic.eq_refl (conj Logic.eq_refl
                      (conj Logic.eq_refl (conj Logic.eq_refl
                        (conj Hinv2 (conj HTF2 (conj Hgenv2 (conj Hsafe2
                          (conj Hvars2 (conj _ _)))))))))))).
          -- intros x Hnin_all.
             destruct im as [[iid_im ins_im] md_im]; cbn [fst] in Hsf_step.
             assert (Hnin_im : ~ In x (instr_id_defs iid_im))
               by (intros Hx; apply Hnin_all, in_app_iff; left; exact Hx).
             assert (Hnin_rest : ~ In x (flat_map (fun '(iid, _, _) => instr_id_defs iid) rest))
               by (intros Hx; apply Hnin_all, in_app_iff; right; exact Hx).
             destruct (Hpres2 x Hnin_rest) as [Hp1 Hp2]; rewrite Hp1, Hp2.
             destruct Hsf_step as [[-> ->] | (id0 & v & Heq_iid & -> & ->)];
               [split; reflexivity |].
             subst iid_im; cbn [instr_id_defs] in Hnin_im.
             assert (Hne_id : x <> id0) by (intros ->; apply Hnin_im; left; reflexivity).
             cbn [stack_vars upd_local_sf Maps.lookup Maps.add Map_rmap];
               rewrite !RMF.F.add_neq_o by (intros Heq'; exact (Hne_id (Logic.eq_sym Heq')));
               split; reflexivity.
          -- intros Heq_sf; apply Heq2.
             destruct Hsf_step as [[-> ->] | (id0 & v & _ & -> & ->)]; [exact Heq_sf |].
             subst sf2; reflexivity.
  Qed.

  Lemma denote_phis_nil_eq (bid : block_id) :
    @denote_phis (@ParamsV IP IPT) bid [] ≅ Ret tt.
  Proof using.
    unfold denote_phis; cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    rewrite Eqit.bind_ret_l.
    cbn [map_monad ExtLib.Structures.Monad.ret Monad_itree].
    rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma interp_cfg_exc_unfold_iter {I R : Type}
    (ctx : IntMap (@function_denotation (@ParamsV IP IPT)))
    (body : I -> @CFGtop (@ParamsV IP IPT) (I + R))
    (i : I) (s : FusedS) :
    interp_cfg_exc ctx (ITree.iter body i) s ≅
    ITree.bind (interp_cfg_exc ctx (body i) s)
      (fun '(s', res) =>
         match res with
         | inl x => Ret (s', inl x)
         | inr (inl j) => Tau (interp_cfg_exc ctx (ITree.iter body j) s')
         | inr (inr r) => Ret (s', inr r)
         end).
  Proof using.
    rewrite (interp_cfg_exc_obs_eq ctx _ _ s (unfold_iter body i)).
    rewrite interp_cfg_exc_bind.
    eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
    intros [s' [x | [j | r]]] _ <-.
    - reflexivity.
    - apply interp_cfg_exc_tau.
    - apply interp_cfg_exc_ret.
  Qed.

  Lemma stage2_alloca_dead_instr_exc_l {IPWB : IPtrWellBehaved IP}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (p : local_id) (dt : dtyp)
    (anns_al : list (annotation dtyp)) (md_al : list (metadata dtyp))
    (va : option (@ptr ProvenanceV (@PointerV IP)))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (σ1 σ2 : state)
    (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hsc : is_scalar_dtyp dt = true)
    (Hanns : is_only_align_anns anns_al = true)
    (Hpu : incl P_safe U)
    (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2))
    (Hfs2 : Memory_stack_frame_stack (state_memory_stack σ2) = Snoc fs0 f2) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists pr pt σ1',
              ~ In pr U /\
              U' = pr :: U /\ r1 = tt /\ r2 = tt /\
              s1' = (σ1', ((upd_local_sf sf (Maps.add p (DVALUE_Base (DVALUE_Pointer pt)) (stack_vars sf)),
                            fstk), g)) /\
              s2' = (σ2, ((sf, fstk), g)) /\
              stage2_mem_inv (pr :: U) P_safe fs0 f2 (ptr_to_int pt) pr
                (N.to_nat (@store_size_dtyp SizeofV dt)) σ1' σ2))
      U
      (interp_cfg_exc ctx1 (denote_instr (IId p, INSTR_Alloca dt anns_al, md_al) va)
         (σ1, ((sf, fstk), g)))
      (interp_cfg_exc ctx2 (Ret tt) (σ2, ((sf, fstk), g))).
  Proof using.
    destruct (is_only_align_anns_num_elts anns_al Hanns) as [Hnum _].
    cbn [denote_instr]; rewrite Hnum.
    assert (Eal :
              ITree.bind
                (ITree.bind
                   (alloca (Pa := @ParamsV IP IPT)
                      (E := @CFGEtop (@ParamsV IP IPT))
                      dt 1%N (explicit_alignment anns_al))
                   (fun v => lwrite (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT)) p v))
                (fun _ => Ret tt) ≅
              ITree.bind
                (alloca (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT)) dt 1%N (explicit_alignment anns_al))
                (fun v => lwrite (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT)) p v)).
    { rewrite Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros v _ <-; apply bind_unit_ret_r. }
    assert (Elhs :
              interp_cfg_exc ctx1
                (ITree.bind
                   (ITree.bind (alloca dt 1%N (explicit_alignment anns_al)) (fun v => lwrite p v))
                   (fun _ => Ret tt))
                (σ1, ((sf, fstk), g)) ≅
              ITree.bind
                (interp_cfg_exc ctx1 (alloca dt 1%N (explicit_alignment anns_al))
                   (σ1, ((sf, fstk), g)))
                (fun '(s1_a, res_a) =>
                   match res_a with
                   | inl ex => Ret (s1_a, inl ex)
                   | inr v => interp_cfg_exc ctx1 (lwrite p v) s1_a
                   end)).
    { rewrite (interp_cfg_exc_obs_eq ctx1 _ _ _ Eal); apply interp_cfg_exc_bind. }
    assert (Erhs :
              interp_cfg_exc ctx2 (Ret tt) (σ2, ((sf, fstk), g)) ≅
              ITree.bind (Ret ((σ2, ((sf, fstk), g)), inr tt)) (fun x => Ret x)).
    { rewrite interp_cfg_exc_ret; symmetry; apply Eqit.bind_ret_r. }
    eapply refine_prov_obs_eq;
      [symmetry; exact Elhs | symmetry; exact Erhs |];
      clear Eal Elhs Erhs.
    unfold alloca, Subevent.trigger; try unfold trigger_cast.
    eapply PassCommonModel.refine_prov_bind with
      (RR := fun U1 '(s1_a, res_a) y2 =>
               exists pr pt σ1',
                 ~ In pr U /\
                 U1 = pr :: U /\
                 s1_a = (σ1', ((sf, fstk), g)) /\
                 res_a = inr (DVALUE_Base (DVALUE_Pointer pt)) /\
                 y2 = ((σ2, ((sf, fstk), g)), inr tt) /\
                 stage2_mem_inv (pr :: U) P_safe fs0 f2 (ptr_to_int pt) pr
                   (N.to_nat (@store_size_dtyp SizeofV dt)) σ1' σ2).
    - apply refine_cfg_exc_memory_event_l.
      eapply refine_prov_weaken;
        [exact (stage2_alloca_dead_l
                  ((σ2, ((sf, fstk), g)), inr tt)
                  dt (explicit_alignment anns_al) U P_safe fs0 f2 σ1 σ2 Hsc Hpu Heq Hfs2) |].
      intros U1 [σ1' r1] y2 (pr & pt & Hnin & -> & -> & -> & Hinv').
      exists pr, pt, σ1';
        exact (conj Hnin (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Hinv'))))).
    - intros U1 [s1_a res_a] y2 _
        (pr & pt & σ1' & Hnin & -> & -> & -> & -> & Hinv').
      eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
      apply refine_prov_ret.
      exists pr, pt, σ1';
        exact (conj Hnin (conj Logic.eq_refl (conj Logic.eq_refl
                 (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Hinv')))))).
  Qed.

  Lemma stage2_instr_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (fargs : list local_id) (bks : ocfg dtyp) (bk : block dtyp)
    (pre_c post_c : code dtyp)
    (safe_no_p : list local_id) (p : local_id)
    (im : instr_id * instr dtyp * list (metadata dtyp))
    (va : option (@ptr ProvenanceV (@PointerV IP)))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hnd_bks : NoDup (List.map blk_id bks))
    (Hbk : In bk bks)
    (Hsplit : blk_code bk = pre_c ++ im :: post_c)
    (Hsub : forall q,
              In q safe_no_p ->
              In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
    (Hnin_p_use : ~ In p (m2r_code_entry_uses im))
    (Hchk : check_no_alloca_or_call_instr safe_no_p im = true)
    (Hinv : stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2)
    (Hgenv : genv_safe P_safe g)
    (Hsafe_loc : safe_locals_env P_safe safe_no_p (stack_vars sf2))
    (Hvars : forall x,
               x <> p ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists σ1' σ2' sf1' sf2',
              U' = U /\ r1 = tt /\ r2 = tt /\
              s1' = (σ1', ((sf1', fstk), g)) /\
              s2' = (σ2', ((sf2', fstk), g)) /\
              stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1' σ2' /\
              safe_locals_env P_safe safe_no_p (stack_vars sf2') /\
              (forall x, x <> p -> Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf2'))))
      U
      (interp_cfg_exc ctx1 (denote_instr im va) (σ1, ((sf1, fstk), g)))
      (interp_cfg_exc ctx2 (denote_instr im va) (σ2, ((sf2, fstk), g))).
  Proof using.
    assert (Huse_vars : forall x,
              In x (m2r_code_entry_uses im) ->
              Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)).
    { intros x Hx; apply Hvars; intros ->; exact (Hnin_p_use Hx). }
    destruct (check_no_alloca_or_call_instr_inv safe_no_p im Hchk)
      as [(id0 & op & md & ->)
         | [(id0 & dt_l & du_l & ptr_e & anns_l & md & -> & Hsafe_ptr & Hderef_none)
         | [(vid0 & dt_s & val_e & du_s & ptr_e & anns_s & md & -> & Hsafe_ptr)
         | [(vid0 & msg_c & md & ->)
         | (iid0 & sync & ord & md & ->)]]]].
    - assert (Hnid_safe : ~ In id0 safe_no_p).
      { intros Hin_s.
        destruct (unique_alloca_code_def_is_alloca fargs bks id0 Hnd_bks (Hsub id0 Hin_s)
                    bk pre_c (INSTR_Op op) md post_c Hbk Hsplit) as (? & ? & Hbad);
          discriminate Hbad. }
      cbn [denote_instr].
      eapply refine_cfg_exc_bind.
      + apply denote_exp_cfg_exc_sim.
        intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses];
          apply in_app_iff; left; exact Hx.
      + intros U1 s1' uv1 s2' uv2 _ (-> & -> & -> & <- & _).
        eapply refine_prov_obs_eq;
          [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (bind_unit_ret_r _))
          | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (bind_unit_ret_r _)) |].
        eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
        eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_lwrite |].
        apply refine_prov_ret.
        exists σ1, σ2,
               (upd_local_sf sf1 (Maps.add id0 uv1 (stack_vars sf1))),
               (upd_local_sf sf2 (Maps.add id0 uv1 (stack_vars sf2))).
        refine (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Hinv
                      (conj (safe_locals_env_add_other P_safe safe_no_p id0 uv1 _ Hnid_safe Hsafe_loc) _))))))).
        intros x Hne; cbn [stack_vars upd_local_sf Maps.lookup Maps.add Map_rmap].
        destruct (raw_id_eqb x id0) eqn:Ex_id;
          [ apply raw_id_eqb_spec in Ex_id; subst x
          | apply raw_id_eqb_neq in Ex_id; rename Ex_id into Hne_id ];
          [ rewrite !RMF.F.add_eq_o by reflexivity; reflexivity
          | rewrite !RMF.F.add_neq_o by (intros Heq'; exact (Hne_id (Logic.eq_sym Heq')));
            exact (Hvars x Hne) ].
    - assert (Hnid_safe : ~ In id0 safe_no_p).
      { intros Hin_s.
        destruct (unique_alloca_code_def_is_alloca fargs bks id0 Hnd_bks (Hsub id0 Hin_s)
                    bk pre_c (INSTR_Load dt_l (du_l, ptr_e) anns_l) md post_c Hbk Hsplit)
          as (? & ? & Hbad); discriminate Hbad. }
      cbn [denote_instr].
      eapply refine_cfg_exc_bind.
      + apply denote_exp_cfg_exc_sim.
        intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
          apply in_app_iff; left; apply in_app_iff; left; exact Hx.
      + intros U1 s1' a1 s2' a2 _ (-> & -> & -> & <- & Hptr_safe).
        pose proof (Hptr_safe P_safe safe_no_p Hgenv Hsafe_loc Hsafe_ptr) as Ha_safe.
        eapply refine_cfg_exc_bind with
          (RA := fun U' s1' s2' (_ _ : unit) =>
                   U' = U /\
                   s1' = (σ1, ((sf1, fstk), g)) /\
                   s2' = (σ2, ((sf2, fstk), g))).
        * eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
          intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
        * intros U2 s1'' _ s2'' _ _ (-> & -> & ->).
          eapply refine_cfg_exc_bind with
            (RA := fun U' s1' s2' v1 v2 =>
                     U' = U /\
                     s1' = (σ1, ((sf1, fstk), g)) /\
                     s2' = (σ2, ((sf2, fstk), g)) /\
                     v1 = v2).
          -- unfold load, Subevent.trigger; try unfold trigger_cast.
             apply refine_cfg_exc_memory_event.
             eapply refine_prov_weaken;
               [exact (stage2_load_safe dt_l a1 U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2 Hinv Ha_safe) |].
             intros U3 [σ1_l v1] [σ2_l v2] (-> & -> & -> & ->);
               exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
          -- intros U3 s1_l v1 s2_l _ _ (-> & -> & -> & <-).
             eapply refine_cfg_exc_bind with
               (RA := fun U' s1' s2' w1 w2 =>
                        U' = U /\
                        s1' = (σ1, ((sf1, fstk), g)) /\
                        s2' = (σ2, ((sf2, fstk), g)) /\
                        w1 = w2).
             ++ eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
                intros w1 w2 <-; repeat split; reflexivity.
             ++ intros U4 s1_a w1 s2_a w2 _ (-> & -> & -> & <-).
                unfold assert_load_dereferenceable; rewrite Hderef_none.
                eapply refine_prov_obs_eq;
                  [symmetry; apply interp_cfg_exc_obs_eq, Eqit.bind_ret_l
                  | symmetry; apply interp_cfg_exc_obs_eq, Eqit.bind_ret_l |].
                eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
                eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_lwrite |].
                apply refine_prov_ret.
                exists σ1, σ2,
                       (upd_local_sf sf1 (Maps.add id0 w1 (stack_vars sf1))),
                       (upd_local_sf sf2 (Maps.add id0 w1 (stack_vars sf2))).
                refine (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl
                          (conj Logic.eq_refl (conj Logic.eq_refl
                            (conj Hinv
                              (conj (safe_locals_env_add_other P_safe safe_no_p id0 w1 _ Hnid_safe Hsafe_loc) _))))))).
                intros x Hne; cbn [stack_vars upd_local_sf Maps.lookup Maps.add Map_rmap].
                destruct (raw_id_eqb x id0) eqn:Ex_id;
                  [ apply raw_id_eqb_spec in Ex_id; subst x
                  | apply raw_id_eqb_neq in Ex_id; rename Ex_id into Hne_id ];
                  [ rewrite !RMF.F.add_eq_o by reflexivity; reflexivity
                  | rewrite !RMF.F.add_neq_o by (intros Heq'; exact (Hne_id (Logic.eq_sym Heq')));
                    exact (Hvars x Hne) ].
    - cbn [denote_instr].
      eapply refine_cfg_exc_bind.
      + apply denote_exp_cfg_exc_sim.
        intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
          apply in_app_iff; left; apply in_app_iff; left; exact Hx.
      + intros U1 s1' v1 s2' v2 _ (-> & -> & -> & <- & _).
        eapply refine_cfg_exc_bind.
        * apply denote_exp_cfg_exc_sim.
          intros x Hx; apply Huse_vars; cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
            apply in_app_iff; left; apply in_app_iff;
            right; apply in_app_iff; left; exact Hx.
        * intros U2 s1'' a1 s2'' a2 _ (-> & -> & -> & <- & Hptr_safe).
          pose proof (Hptr_safe P_safe safe_no_p Hgenv Hsafe_loc Hsafe_ptr) as Ha_safe.
          eapply refine_cfg_exc_bind with
            (RA := fun U' s1' s2' (_ _ : unit) =>
                     U' = U /\
                     s1' = (σ1, ((sf1, fstk), g)) /\
                     s2' = (σ2, ((sf2, fstk), g))).
          -- eapply refine_cfg_exc_EOU; [apply refine_EOU_refl |].
             intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
          -- intros U3 s1_a _ s2_a _ _ (-> & -> & ->).
             assert (Hdo_store :
                       forall a_st : @dvalue (@ParamsV IP IPT),
                         is_safe_ptr_dvalue P_safe a_st ->
                         refine_prov
                           (exc_post RExc
                              (fun U' s1' s2' r1 r2 =>
                                 exists σ1' σ2' sf1' sf2',
                                   U' = U /\ r1 = tt /\ r2 = tt /\
                                   s1' = (σ1', ((sf1', fstk), g)) /\
                                   s2' = (σ2', ((sf2', fstk), g)) /\
                                   stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1' σ2' /\
                                   safe_locals_env P_safe safe_no_p (stack_vars sf2') /\
                                   (forall x, x <> p ->
                                      Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf2'))))
                           U
                           (interp_cfg_exc ctx1 (ITree.bind (store dt_s a_st v1) (fun _ => Ret tt))
                              (σ1, ((sf1, fstk), g)))
                           (interp_cfg_exc ctx2 (ITree.bind (store dt_s a_st v1) (fun _ => Ret tt))
                              (σ2, ((sf2, fstk), g)))).
             { intros a_st Ha_st.
               eapply refine_cfg_exc_bind with
                 (RA := fun U' s1' s2' _ _ =>
                          exists σ1' σ2',
                            U' = U /\
                            stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1' σ2' /\
                            s1' = (σ1', ((sf1, fstk), g)) /\
                            s2' = (σ2', ((sf2, fstk), g))).
               - unfold store, Subevent.trigger; try unfold trigger_cast.
                 apply refine_cfg_exc_memory_event.
                 eapply refine_prov_weaken;
                   [ exact (stage2_store_safe dt_s a_st v1 U P_safe
                              fs0 f2 base_dead pr_dead sz_dead σ1 σ2 Hinv Ha_st) | ].
                 intros U4 [σ1' []] [σ2' []] (-> & _ & _ & Hinv').
                 exists σ1', σ2';
                   exact (conj Logic.eq_refl (conj Hinv' (conj Logic.eq_refl Logic.eq_refl))).
               - intros U4 s1' _ s2' _ _ (σ1' & σ2' & -> & Hinv' & -> & ->).
                 apply refine_cfg_exc_ret.
                 exists σ1', σ2', sf1, sf2;
                   repeat match goal with |- _ /\ _ => split end; try reflexivity; assumption. }
             destruct a1 as [[? | ? ? | ? | ? | ? | | | ? ?] | |];
               try (apply Hdo_store, Ha_safe).
             eapply refine_prov_obs_eq;
               [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (raiseUB_bind_eq _ _)) | reflexivity |].
             apply refine_cfg_exc_raiseUB_l.
    - cbn [denote_instr]; apply refine_cfg_exc_ret.
      exists σ1, σ2, sf1, sf2;
        repeat match goal with |- _ /\ _ => split end; try reflexivity; assumption.
    - destruct iid0; cbn [denote_instr]; apply refine_cfg_exc_ret;
        exists σ1, σ2, sf1, sf2;
        repeat match goal with |- _ /\ _ => split end; try reflexivity; assumption.
  Qed.

  Lemma stage2_code_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (fargs : list local_id) (bks : ocfg dtyp) (bk : block dtyp)
    (pre_c cd post_c : code dtyp)
    (safe_no_p : list local_id) (p : local_id)
    (va : option (@ptr ProvenanceV (@PointerV IP)))
    (U P_safe : list N)
    (fs0 : @Framestack (@ParamsV IP IPT)) (f2 : @Frame (@ParamsV IP IPT))
    (base_dead : Z) (pr_dead : N) (sz_dead : nat)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hnd_bks : NoDup (List.map blk_id bks))
    (Hbk : In bk bks)
    (Hsplit : blk_code bk = pre_c ++ cd ++ post_c)
    (Hsub : forall q,
              In q safe_no_p ->
              In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
    (Hnin_p_blk : ~ In p (full_block_uses bk))
    (Hchk : forallb (check_no_alloca_or_call_instr safe_no_p) cd = true)
    (Hinv : stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1 σ2)
    (Hgenv : genv_safe P_safe g)
    (Hsafe_loc : safe_locals_env P_safe safe_no_p (stack_vars sf2))
    (Hvars : forall x,
               x <> p ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists σ1' σ2' sf1' sf2',
              U' = U /\ r1 = tt /\ r2 = tt /\
              s1' = (σ1', ((sf1', fstk), g)) /\
              s2' = (σ2', ((sf2', fstk), g)) /\
              stage2_mem_inv U P_safe fs0 f2 base_dead pr_dead sz_dead σ1' σ2' /\
              safe_locals_env P_safe safe_no_p (stack_vars sf2') /\
              (forall x, x <> p -> Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf2'))))
      U
      (interp_cfg_exc ctx1 (denote_code cd va) (σ1, ((sf1, fstk), g)))
      (interp_cfg_exc ctx2 (denote_code cd va) (σ2, ((sf2, fstk), g))).
  Proof using.
    revert pre_c σ1 σ2 sf1 sf2 Hsplit Hchk Hinv Hsafe_loc Hvars.
    induction cd as [| im rest IH];
      intros pre_c σ1 σ2 sf1 sf2 Hsplit Hchk Hinv Hsafe_loc Hvars;
      unfold denote_code; cbn [forallb] in Hchk; cbn [loop_monad].
    - apply refine_cfg_exc_ret; exists σ1, σ2, sf1, sf2;
        repeat match goal with |- _ /\ _ => split end; try reflexivity; assumption.
    - rewrite andb_true_iff in Hchk; destruct Hchk as [Hchk_im Hchk_rest].
      assert (Hnin_p_im : ~ In p (m2r_code_entry_uses im)).
      { intros Hp; apply Hnin_p_blk; eapply m2r_code_entry_uses_in_block; [| exact Hp].
        rewrite Hsplit; apply in_app_iff; right; left; reflexivity. }
      eapply refine_cfg_exc_bind.
      + exact (stage2_instr_exc_sim ctx1 ctx2 RExc fargs bks bk pre_c (rest ++ post_c)
                 safe_no_p p im va U P_safe fs0 f2 base_dead pr_dead sz_dead
                 σ1 σ2 sf1 sf2 fstk g
                 Hnd_bks Hbk Hsplit Hsub Hnin_p_im Hchk_im Hinv Hgenv Hsafe_loc Hvars).
      + intros U1 s1_m _ s2_m _ _
          (σ1_m & σ2_m & sf1_m & sf2_m & -> & _ & _ & -> & -> & Hinv1 & Hsafe1 & Hvars1).
        assert (Hsplit_rest : blk_code bk = (pre_c ++ [im]) ++ rest ++ post_c)
          by (rewrite <- app_assoc; exact Hsplit).
        exact (IH (pre_c ++ [im]) σ1_m σ2_m sf1_m sf2_m Hsplit_rest Hchk_rest Hinv1 Hsafe1 Hvars1).
  Qed.

  Local Lemma stage2_elim_entry_block_sim {IPWB : IPtrWellBehaved IP}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (fargs : list local_id) (bks : ocfg dtyp) (b_init : block dtyp)
    (pre_al post_al : code dtyp) (p : local_id) (dt : dtyp)
    (anns_al : list (annotation dtyp)) (md_al : list (metadata dtyp))
    (safe_no_p : list local_id) (bid_from : block_id)
    (varg1 : @ptr ProvenanceV (@PointerV IP))
    (U0 P0 : list N) (pr_va : N) (fs0 : @Framestack (@ParamsV IP IPT))
    (σ1_pf σ2_pf : state) (sf0 : @stack_frame (@ParamsV IP IPT))
    (fstk : stack) (g0 : @global_env (@ParamsV IP IPT))
    (Hnd_bks : NoDup (List.map blk_id bks))
    (Hin_init : In b_init bks)
    (Hsplit_init : blk_code b_init = pre_al ++ (IId p, INSTR_Alloca dt anns_al, md_al) :: post_al)
    (Hphis_init : blk_phis b_init = [])
    (Hni_init : m2r_non_invoke_term (snd (fst (blk_term b_init))) = true)
    (Hsc : is_scalar_dtyp dt = true)
    (Hanns_al : is_only_align_anns anns_al = true)
    (Hsub_safe : forall q,
                   In q safe_no_p ->
                   In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
    (Hp_nuse : ~ In p (full_block_uses b_init))
    (Hpre_chk : forallb (check_other_instr_for_slot false safe_no_p p) pre_al = true)
    (Hpost_chk : forallb (check_no_alloca_or_call_instr safe_no_p) post_al = true)
    (Hinv_pf : stage1_mem_inv (pr_va :: U0) (pr_va :: P0) [] σ1_pf σ2_pf)
    (Htf_pf : top_frame_unprom_from fs0 [] (state_memory_stack σ2_pf))
    (Hgenv_pf : genv_safe (pr_va :: P0) g0)
    (Hsafe_sf0 : safe_locals_env (pr_va :: P0) safe_no_p (stack_vars sf0))
    (Hrexc : forall U_x P_x f2 base_dead pr_dead σ1_x σ2_x sf1_x sf2_x ex,
               incl (pr_va :: U0) U_x ->
               stage2_mem_inv U_x P_x fs0 f2 base_dead pr_dead
                 (N.to_nat (@store_size_dtyp SizeofV dt)) σ1_x σ2_x ->
               RExc U_x (σ1_x, ((sf1_x, fstk), g0)) (σ2_x, ((sf2_x, fstk), g0)) ex ex) :
    let sz_dead := N.to_nat (@store_size_dtyp SizeofV dt) in
    let b_init' :=
      {| blk_id       := blk_id b_init;
         blk_phis     := blk_phis b_init;
         blk_code     := pre_al ++ post_al;
         blk_term     := blk_term b_init;
         blk_comments := blk_comments b_init |} in
    refine_prov
      (exc_post RExc
         (fun U_b1 s1_b1 s2_b1 bd1 bd2 =>
            exists (P_pre : list N) f2 base_dead pr_dead σ1_b1 σ2_b1
                   (sf1_b1 sf2_b1 : @stack_frame (@ParamsV IP IPT)),
              incl (pr_va :: U0) U_b1 /\
              bd1 = bd2 /\
              s1_b1 = (σ1_b1, ((sf1_b1, fstk), g0)) /\
              s2_b1 = (σ2_b1, ((sf2_b1, fstk), g0)) /\
              stage2_mem_inv U_b1 P_pre fs0 f2 base_dead pr_dead sz_dead σ1_b1 σ2_b1 /\
              genv_safe P_pre g0 /\
              safe_locals_env P_pre safe_no_p (stack_vars sf2_b1) /\
              (forall x, x <> p ->
                 Maps.lookup x (stack_vars sf1_b1) = Maps.lookup x (stack_vars sf2_b1)) /\
              match bd1 with
              | inl bid_target => In bid_target (m2r_block_succs b_init)
              | inr _ => True
              end))
      (pr_va :: U0)
      (interp_cfg_exc ctx1 (denote_block b_init bid_from (Some varg1)) (σ1_pf, ((sf0, fstk), g0)))
      (interp_cfg_exc ctx2 (denote_block b_init' bid_from (Some varg1)) (σ2_pf, ((sf0, fstk), g0))).
  Proof using.
    intros sz_dead b_init'.
    unfold denote_block, b_init'; cbn [blk_phis blk_code blk_term]; rewrite Hphis_init.
    eapply refine_prov_obs_eq;
      [ symmetry;
        apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (eq_itree_bind_congr_l (denote_phis_nil_eq bid_from)))
      | symmetry;
        apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (eq_itree_bind_congr_l (denote_phis_nil_eq bid_from))) |].
    eapply refine_prov_obs_eq;
      [ symmetry; apply interp_cfg_exc_obs_eq, Eqit.bind_ret_l
      | symmetry; apply interp_cfg_exc_obs_eq, Eqit.bind_ret_l |].
    rewrite Hsplit_init.
    eapply refine_prov_obs_eq;
      [ symmetry;
        apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                 (eq_itree_bind_congr_l (denote_code_app_eq pre_al _ (Some varg1))))
      | symmetry;
        apply (interp_cfg_exc_obs_eq ctx2 _ _ _
                 (eq_itree_bind_congr_l (denote_code_app_eq pre_al post_al (Some varg1)))) |].
    eapply refine_prov_obs_eq;
      [ symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_bind _ _ _))
      | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
    eapply refine_cfg_exc_bind.
    - assert (Hsplit_pre :
                blk_code b_init = [] ++ pre_al ++ (IId p, INSTR_Alloca dt anns_al, md_al) :: post_al)
        by exact Hsplit_init.
      exact (stage1_no_call_code_exc_sim ctx1 ctx2 RExc
               (fun s => top_frame_unprom_from fs0 [] (state_memory_stack s))
               fargs bks b_init [] pre_al
               ((IId p, INSTR_Alloca dt anns_al, md_al) :: post_al)
               safe_no_p p (Some varg1) (Some varg1)
               (pr_va :: U0) (pr_va :: P0) [] σ1_pf σ2_pf sf0 sf0 fstk fstk g0
               Hnd_bks Hin_init Hsplit_pre Hsub_safe Hpre_chk
               (fun s_a s_b Heq_fs HT => top_frame_unprom_frame_eq fs0 [] _ _ (eq_sym Heq_fs) HT)
               (fun s_a s_b ptrs Hdisj Heq_fs HT =>
                  top_frame_unprom_frame_eq fs0 [] _ _ (eq_sym Heq_fs)
                    (top_frame_unprom_add_ptrs fs0 [] ptrs _ HT Hdisj))
               Hinv_pf Htf_pf Hgenv_pf Hsafe_sf0 (fun _ _ => Logic.eq_refl)).
    - intros U_pre s1_pre _ s2_pre _ _
        (P_pre & σ1_pre & σ2_pre & sf1_pre & sf2_pre &
         HincU_pre & HincP_pre & _ & _ & -> & -> &
         Hinv_pre & Htf_pre & Hgenv_pre & Hsafe_pre & _ & _ & Heq_sf_pre).
      pose proof (Heq_sf_pre Logic.eq_refl) as ->.
      destruct Htf_pre as (f2 & Hfs2_pre & _).
      pose proof (proj1 Hinv_pre) as Hpu_pre.
      pose proof (stage1_mem_nil_is_equal U_pre P_pre σ1_pre σ2_pre Hinv_pre) as Heq_pre.
      assert (Econs_l :
                @denote_code (@ParamsV IP IPT)
                  ((IId p, INSTR_Alloca dt anns_al, md_al) :: post_al) (Some varg1) ≅
                ITree.bind (denote_instr (IId p, INSTR_Alloca dt anns_al, md_al) (Some varg1))
                  (fun _ => denote_code post_al (Some varg1)))
        by reflexivity.
      eapply refine_prov_obs_eq;
        [ symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (eq_itree_bind_congr_l Econs_l))
        | symmetry;
          apply (interp_cfg_exc_obs_eq ctx2 _ _ _
                   (eq_itree_bind_congr_l
                      (symmetry (Eqit.bind_ret_l tt
                                   (fun _ => @denote_code (@ParamsV IP IPT) post_al (Some varg1)))))) |].
      eapply refine_prov_obs_eq;
        [ symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_bind _ _ _))
        | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
      eapply refine_cfg_exc_bind.
      + exact (stage2_alloca_dead_instr_exc_l ctx1 ctx2 RExc
                 p dt anns_al md_al (Some varg1) U_pre P_pre fs0 f2
                 σ1_pre σ2_pre sf2_pre fstk g0
                 Hsc Hanns_al Hpu_pre Heq_pre Hfs2_pre).
      + intros U_al s1_al _ s2_al _ _
          (pr_dead & pt_dead & σ1_al & Hnin_dead & -> & _ & _ & -> & -> & Hinv_al).
        fold sz_dead in Hinv_al.
        assert (HincU_al : incl (pr_va :: U0) (pr_dead :: U_pre))
          by (intros x Hx; right; apply HincU_pre, Hx).
        assert (Hvars_al : forall x,
                  x <> p ->
                  Maps.lookup x
                    (stack_vars
                       (upd_local_sf sf2_pre
                          (Maps.add p (DVALUE_Base (DVALUE_Pointer pt_dead)) (stack_vars sf2_pre)))) =
                  Maps.lookup x (stack_vars sf2_pre)).
        { intros x Hne; cbn [stack_vars upd_local_sf Maps.lookup Maps.add Map_rmap].
          apply RMF.F.add_neq_o; intros Heq'; exact (Hne (Logic.eq_sym Heq')). }
        assert (Hsplit_post :
                  blk_code b_init =
                  (pre_al ++ [(IId p, INSTR_Alloca dt anns_al, md_al)]) ++ post_al ++ []).
        { rewrite <- app_assoc, app_nil_r; exact Hsplit_init. }
        eapply refine_cfg_exc_bind.
        * exact (stage2_code_exc_sim ctx1 ctx2 RExc
                   fargs bks b_init
                   (pre_al ++ [(IId p, INSTR_Alloca dt anns_al, md_al)]) post_al []
                   safe_no_p p (Some varg1) (pr_dead :: U_pre) P_pre fs0 f2
                   (ptr_to_int pt_dead) pr_dead sz_dead
                   σ1_al σ2_pre _ sf2_pre fstk g0
                   Hnd_bks Hin_init Hsplit_post Hsub_safe
                   Hp_nuse Hpost_chk
                   Hinv_al Hgenv_pre Hsafe_pre Hvars_al).
        * intros U_post s1_post _ s2_post _ _
            (σ1_post & σ2_post & sf1_post & sf2_post &
             -> & _ & _ & -> & -> & Hinv_post & Hsafe_post & Hvars_post).
          destruct (blk_term b_init) as [[iid_tm tm_init] md_tm] eqn:Etm_init.
          cbn [fst snd] in Hni_init.
          assert (Htm_vars : forall x,
                    In x (full_term_uses tm_init) ->
                    Maps.lookup x (stack_vars sf1_post) = Maps.lookup x (stack_vars sf2_post)).
          { intros x Hx; apply Hvars_post; intros ->.
            apply Hp_nuse, m2r_term_entry_uses_in_block.
            rewrite Etm_init; cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx. }
          eapply refine_prov_weaken.
          -- apply (denote_non_invoke_term_exc_sim ctx1 ctx2 RExc
                      iid_tm iid_tm tm_init md_tm md_tm
                      (pr_dead :: U_pre) σ1_post σ2_post sf1_post sf2_post fstk fstk g0
                      Hni_init Htm_vars).
             intros ex; exact (Hrexc _ P_pre f2 (ptr_to_int pt_dead) pr_dead
                                 σ1_post σ2_post sf1_post sf2_post ex HincU_al Hinv_post).
          -- intros U_t [s1_t res1_t] [s2_t res2_t].
             destruct res1_t as [ex1 | bd1], res2_t as [ex2 | bd2]; cbn [exc_post];
               try (intros H; exact H).
             intros (-> & -> & -> & <- & Hsucc).
             destruct bd1 as [bid_t | dv_t];
               [cbn in Hsucc |- *; unfold m2r_block_succs; rewrite Etm_init |];
             exists P_pre, f2, (ptr_to_int pt_dead), pr_dead,
                    σ1_post, σ2_post, sf1_post, sf2_post;
             exact (conj HincU_al (conj Logic.eq_refl (conj Logic.eq_refl
                      (conj Logic.eq_refl (conj Hinv_post
                        (conj Hgenv_pre (conj Hsafe_post (conj Hvars_post Hsucc)))))))).
  Qed.

  Local Lemma stage2_elim_non_entry_loop_sim {IPWB : IPtrWellBehaved IP}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (fargs : list local_id) (c : CFG.cfg dtyp) (f_blk : block dtyp -> block dtyp)
    (safe_no_p : list local_id) (p : local_id) (dt : dtyp)
    (varg1 : @ptr ProvenanceV (@PointerV IP))
    (U0 P_pre : list N) (pr_va : N) (fs0 : @Framestack (@ParamsV IP IPT))
    (f2 : @Frame (@ParamsV IP IPT)) (base_dead : Z) (pr_dead : N)
    (σ1_s σ2_s : state) (sf1_s sf2_s : @stack_frame (@ParamsV IP IPT))
    (fstk : stack) (g0 : @global_env (@ParamsV IP IPT))
    (U_s : list N) (j1 : block_id * block_id)
    (Hnd_bks : NoDup (List.map blk_id (blks c)))
    (Hno_entry_pred : ~ In (init c) (m2r_all_succs c))
    (Hsub_safe : forall q,
                   In q safe_no_p ->
                   In q (m2r_collect_unique_allocas
                           (fargs ++ flat_map full_block_defs (blks c)) (blks c)))
    (Hp_blk_nuse : forall bk, In bk (blks c) -> ~ In p (full_block_uses bk))
    (Ebks_chk : forallb
                  (fun bk =>
                     if raw_id_eqb (blk_id bk) (init c) then true
                     else
                       forallb (check_no_alloca_or_call_instr safe_no_p) (blk_code bk) &&
                       m2r_non_invoke_term (snd (fst (blk_term bk))))
                  (blks c) = true)
    (Hf_id : forall bk, In bk (blks c) -> blk_id (f_blk bk) = blk_id bk)
    (Hf_non_entry : forall bk, In bk (blks c) -> blk_id bk <> init c -> f_blk bk = bk)
    (HincU_s : incl (pr_va :: U0) U_s)
    (Hne_s : snd j1 <> init c)
    (Hinv_s : stage2_mem_inv U_s P_pre fs0 f2 base_dead pr_dead
                (N.to_nat (@store_size_dtyp SizeofV dt)) σ1_s σ2_s)
    (Hgenv_pre : genv_safe P_pre g0)
    (Hsafe_s : safe_locals_env P_pre safe_no_p (stack_vars sf2_s))
    (Hvars_s : forall x, x <> p -> Maps.lookup x (stack_vars sf1_s) = Maps.lookup x (stack_vars sf2_s))
    (Hrexc : forall U_x σ1_x σ2_x sf1_x sf2_x ex,
               incl (pr_va :: U0) U_x ->
               stage2_mem_inv U_x P_pre fs0 f2 base_dead pr_dead
                 (N.to_nat (@store_size_dtyp SizeofV dt)) σ1_x σ2_x ->
               RExc U_x (σ1_x, ((sf1_x, fstk), g0)) (σ2_x, ((sf2_x, fstk), g0)) ex ex) :
    let sz_dead := N.to_nat (@store_size_dtyp SizeofV dt) in
    refine_prov
      (exc_post RExc
         (fun U_e s1_e s2_e r1 r2 =>
            r1 = r2 /\
            incl (pr_va :: U0) U_e /\
            exists P_e f2' base_dead' pr_dead' σ1_e σ2_e sf1_e sf2_e,
              s1_e = (σ1_e, ((sf1_e, fstk), g0)) /\
              s2_e = (σ2_e, ((sf2_e, fstk), g0)) /\
              stage2_mem_inv U_e P_e fs0 f2' base_dead' pr_dead' sz_dead σ1_e σ2_e))
      U_s
      (Tau (interp_cfg_exc ctx1 (denote_ocfg_map (ocfg_map (blks c)) (Some varg1) j1)
              (σ1_s, ((sf1_s, fstk), g0))))
      (Tau (interp_cfg_exc ctx2 (denote_ocfg_map (ocfg_map (List.map f_blk (blks c))) (Some varg1) j1)
              (σ2_s, ((sf2_s, fstk), g0)))).
  Proof using.
    intros sz_dead.
    unfold denote_ocfg_map; apply refine_prov_tau_both.
    set (RI_loop :=
           fun U_l (s1_l s2_l : FusedS) (i1 i2 : block_id * block_id) =>
             i1 = i2 /\
             snd i2 <> init c /\
             incl (pr_va :: U0) U_l /\
             exists σ1_l σ2_l sf1_l sf2_l,
               s1_l = (σ1_l, ((sf1_l, fstk), g0)) /\
               s2_l = (σ2_l, ((sf2_l, fstk), g0)) /\
               stage2_mem_inv U_l P_pre fs0 f2 base_dead pr_dead sz_dead σ1_l σ2_l /\
               safe_locals_env P_pre safe_no_p (stack_vars sf2_l) /\
               (forall x, x <> p -> Maps.lookup x (stack_vars sf1_l) = Maps.lookup x (stack_vars sf2_l))).
    eapply (refine_cfg_exc_iter ctx1 ctx2 RI_loop RExc _ _ _ U_s).
    - intros U_l s1_l s2_l [bf1 bs1] [bf2 bs2] Hinc_step
        (Heq_ij & Hne_bs & HincU_l & σ1_l & σ2_l & sf1_l & sf2_l &
         -> & -> & Hinv_l & Hsafe_l & Hvars_l).
      inversion Heq_ij; subst bf1 bs1; clear Heq_ij; cbn [snd] in Hne_bs.
      cbn beta iota.
      rewrite !ScopeTheory.ocfg_map_find_block.
      rewrite (m2r_find_block_map_id_pres f_blk (blks c) bs2 Hf_id).
      destruct (find_block (blks c) bs2) as [bk_cur |] eqn:Efind_cur; cbn [option_map].
      + destruct (m2r_find_block_some_inv (blks c) bs2 bk_cur Efind_cur)
          as [Hin_cur Hid_cur].
        rewrite (Hf_non_entry bk_cur Hin_cur) by congruence.
        pose proof Ebks_chk as Hbk_cur_chk.
        rewrite forallb_forall in Hbk_cur_chk.
        specialize (Hbk_cur_chk bk_cur Hin_cur).
        destruct (raw_id_eqb (blk_id bk_cur) (init c)) eqn:Ebad;
          [apply raw_id_eqb_spec in Ebad; exfalso; congruence | clear Ebad].
        rewrite andb_true_iff in Hbk_cur_chk.
        destruct Hbk_cur_chk as [Hcd_cur Hni_cur].
        unfold denote_block.
        eapply refine_cfg_exc_bind with
          (RA := fun U_bd s1_bd s2_bd bd1 bd2 =>
                   exists σ1_cd σ2_cd (sf1_cd sf2_cd : @stack_frame (@ParamsV IP IPT)),
                     U_bd = U_l /\
                     bd1 = bd2 /\
                     s1_bd = (σ1_cd, ((sf1_cd, fstk), g0)) /\
                     s2_bd = (σ2_cd, ((sf2_cd, fstk), g0)) /\
                     stage2_mem_inv U_l P_pre fs0 f2 base_dead pr_dead sz_dead σ1_cd σ2_cd /\
                     safe_locals_env P_pre safe_no_p (stack_vars sf2_cd) /\
                     (forall x, x <> p ->
                        Maps.lookup x (stack_vars sf1_cd) = Maps.lookup x (stack_vars sf2_cd)) /\
                     match bd1 with
                     | inl bid_target => In bid_target (m2r_block_succs bk_cur)
                     | inr _ => True
                     end).
        * eapply refine_cfg_exc_bind.
          -- apply denote_phis_same_exc_sim.
             intros x Hx; apply Hvars_l; intros ->.
             apply (Hp_blk_nuse bk_cur Hin_cur).
             apply in_flat_map in Hx as (pe & Hpe & Hx_pe).
             exact (m2r_phi_entry_uses_in_block bk_cur pe p Hpe Hx_pe).
          -- intros U_ph s1_ph _ s2_ph _ _ (dvs & -> & _ & _ & Hfst_dvs & -> & ->).
             assert (Hsafe_ph :
                       safe_locals_env P_pre safe_no_p (write_phi_dvs dvs (stack_vars sf2_l))).
             { apply write_phi_dvs_safe_locals; [| exact Hsafe_l].
               intros q Hq Hin_dvs; rewrite Hfst_dvs in Hin_dvs.
               apply in_map_iff in Hin_dvs as ([[x_ph ph_q] md_q] & <- & Hpe_in).
               exact (unique_alloca_not_phi_def fargs (blks c) x_ph Hnd_bks
                        (Hsub_safe x_ph Hq) bk_cur x_ph ph_q md_q Hin_cur Hpe_in Logic.eq_refl). }
             assert (Hvars_ph :
                       forall x, x <> p ->
                         Maps.lookup x (write_phi_dvs dvs (stack_vars sf1_l)) =
                         Maps.lookup x (write_phi_dvs dvs (stack_vars sf2_l))).
             { intros x Hne; apply write_phi_dvs_lookup_agree, Hvars_l, Hne. }
             assert (Hsplit_cur : blk_code bk_cur = [] ++ blk_code bk_cur ++ [])
               by (rewrite app_nil_r; reflexivity).
             eapply refine_cfg_exc_bind.
             ++ exact (stage2_code_exc_sim ctx1 ctx2 RExc
                         fargs (blks c) bk_cur [] (blk_code bk_cur) []
                         safe_no_p p (Some varg1) U_l P_pre fs0 f2
                         base_dead pr_dead sz_dead
                         σ1_l σ2_l
                         (upd_local_sf sf1_l (write_phi_dvs dvs (stack_vars sf1_l)))
                         (upd_local_sf sf2_l (write_phi_dvs dvs (stack_vars sf2_l)))
                         fstk g0
                         Hnd_bks Hin_cur Hsplit_cur Hsub_safe
                         (Hp_blk_nuse bk_cur Hin_cur) Hcd_cur
                         Hinv_l Hgenv_pre Hsafe_ph Hvars_ph).
             ++ intros U_cd s1_cd _ s2_cd _ _
                  (σ1_cd & σ2_cd & sf1_cd & sf2_cd &
                   -> & _ & _ & -> & -> & Hinv_cd & Hsafe_cd & Hvars_cd).
                destruct (blk_term bk_cur) as [[iid_tc tm_cur] md_tc] eqn:Etm_cur.
                cbn [fst snd] in Hni_cur.
                assert (Htm_vars :
                          forall x,
                            In x (full_term_uses tm_cur) ->
                            Maps.lookup x (stack_vars sf1_cd) = Maps.lookup x (stack_vars sf2_cd)).
                { intros x Hx; apply Hvars_cd; intros ->.
                  apply (Hp_blk_nuse bk_cur Hin_cur), m2r_term_entry_uses_in_block.
                  rewrite Etm_cur; cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx. }
                eapply refine_prov_weaken.
                ** apply (denote_non_invoke_term_exc_sim ctx1 ctx2 RExc
                            iid_tc iid_tc tm_cur md_tc md_tc
                            U_l σ1_cd σ2_cd sf1_cd sf2_cd fstk fstk g0
                            Hni_cur Htm_vars).
                   intros ex; exact (Hrexc U_l σ1_cd σ2_cd sf1_cd sf2_cd ex HincU_l Hinv_cd).
                ** intros U_t [s1_t res1_t] [s2_t res2_t].
                   destruct res1_t as [ex1 | bd1], res2_t as [ex2 | bd2]; cbn [exc_post];
                     try (intros H; exact H).
                   intros (-> & -> & -> & <- & Hsucc_cur).
                   destruct bd1 as [bid_t | dv_t];
                     [cbn in Hsucc_cur |- *; unfold m2r_block_succs; rewrite Etm_cur |];
                   exists σ1_cd, σ2_cd, sf1_cd, sf2_cd;
                   exact (conj Logic.eq_refl (conj Logic.eq_refl
                            (conj Logic.eq_refl (conj Logic.eq_refl
                              (conj Hinv_cd (conj Hsafe_cd (conj Hvars_cd Hsucc_cur))))))).
        * intros U_bd s1_bd bd1 s2_bd bd2 _
            (σ1_cd & σ2_cd & sf1_cd & sf2_cd &
             -> & <- & -> & -> & Hinv_cd & Hsafe_cd & Hvars_cd & Hsucc_cur).
          destruct bd1 as [bid_tgt | dv_cur].
          -- apply refine_cfg_exc_ret.
             assert (Hne_tgt : bid_tgt <> init c).
             { intros Heq_t; apply Hno_entry_pred; rewrite <- Heq_t.
               unfold m2r_all_succs; apply in_flat_map; exists bk_cur;
                 split; [exact Hin_cur | exact Hsucc_cur]. }
             refine (conj Logic.eq_refl (conj Hne_tgt (conj HincU_l _))).
             exists σ1_cd, σ2_cd, sf1_cd, sf2_cd;
               exact (conj Logic.eq_refl (conj Logic.eq_refl
                        (conj Hinv_cd (conj Hsafe_cd Hvars_cd)))).
          -- apply refine_cfg_exc_ret.
             refine (conj Logic.eq_refl (conj HincU_l _)).
             exists P_pre, f2, base_dead, pr_dead, σ1_cd, σ2_cd, sf1_cd, sf2_cd;
               exact (conj Logic.eq_refl (conj Logic.eq_refl Hinv_cd)).
      + apply refine_cfg_exc_ret.
        refine (conj Logic.eq_refl (conj HincU_l _)).
        exists P_pre, f2, base_dead, pr_dead, σ1_l, σ2_l, sf1_l, sf2_l;
          exact (conj Logic.eq_refl (conj Logic.eq_refl Hinv_l)).
    - refine (conj Logic.eq_refl (conj Hne_s (conj HincU_s _))).
      exists σ1_s, σ2_s, sf1_s, sf2_s;
        exact (conj Logic.eq_refl (conj Logic.eq_refl (conj Hinv_s (conj Hsafe_s Hvars_s)))).
  Qed.

  Local Lemma stage2_elim_cfg_sim {IPWB : IPtrWellBehaved IP}
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (fargs : list local_id) (c : CFG.cfg dtyp) (b_init : block dtyp)
    (pre_al post_al : code dtyp) (p : local_id) (dt : dtyp)
    (anns_al : list (annotation dtyp)) (md_al : list (metadata dtyp))
    (safe_no_p : list local_id) (f_blk : block dtyp -> block dtyp)
    (varg1 : @ptr ProvenanceV (@PointerV IP))
    (U0 P0 : list N) (pr_va : N) (fs0 : @Framestack (@ParamsV IP IPT))
    (σ1_pf σ2_pf : state) (sf0 : @stack_frame (@ParamsV IP IPT))
    (fstk : stack) (g0 : @global_env (@ParamsV IP IPT))
    (Hnd_bks : NoDup (List.map blk_id (blks c)))
    (Hno_entry_pred : ~ In (init c) (m2r_all_succs c))
    (Efind_init : find_block (blks c) (init c) = Some b_init)
    (Hin_init : In b_init (blks c))
    (Hid_init : blk_id b_init = init c)
    (Hphis_init : blk_phis b_init = [])
    (Hni_init : m2r_non_invoke_term (snd (fst (blk_term b_init))) = true)
    (Hsplit_init : blk_code b_init = pre_al ++ (IId p, INSTR_Alloca dt anns_al, md_al) :: post_al)
    (Hsc : is_scalar_dtyp dt = true)
    (Hanns_al : is_only_align_anns anns_al = true)
    (Hsub_safe : forall q,
                   In q safe_no_p ->
                   In q (m2r_collect_unique_allocas
                           (fargs ++ flat_map full_block_defs (blks c)) (blks c)))
    (Hp_blk_nuse : forall bk, In bk (blks c) -> ~ In p (full_block_uses bk))
    (Hpre_chk : forallb (check_other_instr_for_slot false safe_no_p p) pre_al = true)
    (Hpost_chk : forallb (check_no_alloca_or_call_instr safe_no_p) post_al = true)
    (Ebks_chk : forallb
                  (fun bk =>
                     if raw_id_eqb (blk_id bk) (init c) then true
                     else
                       forallb (check_no_alloca_or_call_instr safe_no_p) (blk_code bk) &&
                       m2r_non_invoke_term (snd (fst (blk_term bk))))
                  (blks c) = true)
    (Hf_id : forall bk, In bk (blks c) -> blk_id (f_blk bk) = blk_id bk)
    (Hf_entry : f_blk b_init =
                  {| blk_id       := blk_id b_init;
                     blk_phis     := blk_phis b_init;
                     blk_code     := pre_al ++ post_al;
                     blk_term     := blk_term b_init;
                     blk_comments := blk_comments b_init |})
    (Hf_non_entry : forall bk, In bk (blks c) -> blk_id bk <> init c -> f_blk bk = bk)
    (Hinv_pf : stage1_mem_inv (pr_va :: U0) (pr_va :: P0) [] σ1_pf σ2_pf)
    (Htf_pf : top_frame_unprom_from fs0 [] (state_memory_stack σ2_pf))
    (Hgenv_pf : genv_safe (pr_va :: P0) g0)
    (Hsafe_sf0 : safe_locals_env (pr_va :: P0) safe_no_p (stack_vars sf0)) :
    let sz_dead := N.to_nat (@store_size_dtyp SizeofV dt) in
    let c' := {| init := init c; blks := List.map f_blk (blks c); args := args c |} in
    let ExitRel :=
      fun U_e (s1_e s2_e : FusedS) =>
        incl (pr_va :: U0) U_e /\
        exists P_e f2 base_dead pr_dead σ1_e σ2_e sf1_e sf2_e,
          s1_e = (σ1_e, ((sf1_e, fstk), g0)) /\
          s2_e = (σ2_e, ((sf2_e, fstk), g0)) /\
          stage2_mem_inv U_e P_e fs0 f2 base_dead pr_dead sz_dead σ1_e σ2_e in
    refine_prov
      (exc_post
         (fun U_e s1_e s2_e (ex1 ex2 : @exc (@ParamsV IP IPT)) => ex1 = ex2 /\ ExitRel U_e s1_e s2_e)
         (fun U_e s1_e s2_e (v1 v2 : @dvalue (@ParamsV IP IPT)) => v1 = v2 /\ ExitRel U_e s1_e s2_e))
      (pr_va :: U0)
      (interp_cfg_exc ctx1 (denote_cfg_map (ocfg_map (blks c)) c (Some varg1)) (σ1_pf, ((sf0, fstk), g0)))
      (interp_cfg_exc ctx2 (denote_cfg_map (ocfg_map (blks c')) c' (Some varg1)) (σ2_pf, ((sf0, fstk), g0))).
  Proof using.
    intros sz_dead c' ExitRel.
    set (RExc_s2 := fun U_e s1_e s2_e (ex1 ex2 : @exc (@ParamsV IP IPT)) => ex1 = ex2 /\ ExitRel U_e s1_e s2_e).
    assert (Hrexc :
              forall U_x P_x f2 base_dead pr_dead σ1_x σ2_x sf1_x sf2_x ex,
                incl (pr_va :: U0) U_x ->
                stage2_mem_inv U_x P_x fs0 f2 base_dead pr_dead sz_dead σ1_x σ2_x ->
                RExc_s2 U_x (σ1_x, ((sf1_x, fstk), g0)) (σ2_x, ((sf2_x, fstk), g0)) ex ex).
    { intros U_x P_x f2 base_dead pr_dead σ1_x σ2_x sf1_x sf2_x ex Hinc Hinv.
      refine (conj Logic.eq_refl (conj Hinc _)).
      exists P_x, f2, base_dead, pr_dead, σ1_x, σ2_x, sf1_x, sf2_x;
        exact (conj Logic.eq_refl (conj Logic.eq_refl Hinv)). }
    unfold denote_cfg_map; cbn [init].
    eapply refine_cfg_exc_bind with
      (RA := fun U_e s1_e s2_e (r1 r2 : (block_id * block_id) + @dvalue (@ParamsV IP IPT)) =>
               r1 = r2 /\ ExitRel U_e s1_e s2_e).
    - unfold denote_ocfg_map.
      eapply refine_prov_obs_eq;
        [symmetry; apply interp_cfg_exc_unfold_iter | symmetry; apply interp_cfg_exc_unfold_iter |].
      cbn beta iota.
      rewrite ScopeTheory.ocfg_map_find_block, Efind_init.
      rewrite ScopeTheory.ocfg_map_find_block; unfold c'; cbn [init blks].
      rewrite (m2r_find_block_map_id_pres f_blk (blks c) (init c) Hf_id), Efind_init.
      cbn [option_map]; rewrite Hf_entry.
      eapply PassCommonModel.refine_prov_bind with
        (RR := exc_post RExc_s2
                   (fun U_s s1_s s2_s
                      (lr1 lr2 : (block_id * block_id) + ((block_id * block_id) + @dvalue (@ParamsV IP IPT))) =>
                      exists P_pre f2 base_dead pr_dead σ1_b1 σ2_b1 sf1_b1 sf2_b1,
                        incl (pr_va :: U0) U_s /\
                        lr1 = lr2 /\
                        s1_s = (σ1_b1, ((sf1_b1, fstk), g0)) /\
                        s2_s = (σ2_b1, ((sf2_b1, fstk), g0)) /\
                        stage2_mem_inv U_s P_pre fs0 f2 base_dead pr_dead sz_dead σ1_b1 σ2_b1 /\
                        genv_safe P_pre g0 /\
                        safe_locals_env P_pre safe_no_p (stack_vars sf2_b1) /\
                        (forall x, x <> p ->
                           Maps.lookup x (stack_vars sf1_b1) = Maps.lookup x (stack_vars sf2_b1)) /\
                        match lr1 with
                        | inl j => snd j <> init c
                        | inr _ => True
                        end)).
      + eapply refine_cfg_exc_bind.
        * exact (stage2_elim_entry_block_sim ctx1 ctx2 RExc_s2 fargs (blks c) b_init
                   pre_al post_al p dt anns_al md_al safe_no_p (init c) varg1
                   U0 P0 pr_va fs0 σ1_pf σ2_pf sf0 fstk g0
                   Hnd_bks Hin_init Hsplit_init Hphis_init Hni_init Hsc Hanns_al
                   Hsub_safe (Hp_blk_nuse b_init Hin_init) Hpre_chk Hpost_chk
                   Hinv_pf Htf_pf Hgenv_pf Hsafe_sf0 Hrexc).
        * intros U_b1 s1_b1 bd1 s2_b1 bd2 _
            (P_pre & f2 & base_dead & pr_dead & σ1_b1 & σ2_b1 & sf1_b1 & sf2_b1 &
             HincU_b1 & <- & -> & -> & Hinv_b1 & Hgenv_pre & Hsafe_b1 & Hvars_b1 & Hsucc_b1).
          destruct bd1 as [bid_next | dv_ret].
          -- assert (Hne_init : bid_next <> init c).
             { intros Heq_n; apply Hno_entry_pred; rewrite <- Heq_n.
               unfold m2r_all_succs; apply in_flat_map; exists b_init;
                 split; [exact Hin_init | exact Hsucc_b1]. }
             apply refine_cfg_exc_ret.
             exists P_pre, f2, base_dead, pr_dead, σ1_b1, σ2_b1, sf1_b1, sf2_b1.
             exact (conj HincU_b1 (conj Logic.eq_refl (conj Logic.eq_refl
                      (conj Logic.eq_refl (conj Hinv_b1
                        (conj Hgenv_pre (conj Hsafe_b1 (conj Hvars_b1 Hne_init)))))))).
          -- apply refine_cfg_exc_ret.
             exists P_pre, f2, base_dead, pr_dead, σ1_b1, σ2_b1, sf1_b1, sf2_b1.
             exact (conj HincU_b1 (conj Logic.eq_refl (conj Logic.eq_refl
                      (conj Logic.eq_refl (conj Hinv_b1
                        (conj Hgenv_pre (conj Hsafe_b1 (conj Hvars_b1 I)))))))).
      + intros U_step [s1_step res1_s] [s2_step res2_s] _.
        destruct res1_s as [ex1 | [j1 | r1]], res2_s as [ex2 | [j2 | r2]]; cbn [exc_post];
          try contradiction;
          try (let H := fresh in intros H;
               repeat match goal with
                      | H0 : _ /\ _ |- _ => destruct H0
                      | H0 : exists _, _ |- _ => destruct H0
                      end;
               discriminate).
        * intros Hex; apply refine_prov_ret; exact Hex.
        * intros (P_pre & f2 & base_dead & pr_dead & σ1_s & σ2_s & sf1_s & sf2_s &
                  HincU_s & Hjeq & -> & -> & Hinv_s & Hgenv_pre & Hsafe_s & Hvars_s & Hne_s).
          inversion Hjeq; subst j2; clear Hjeq.
          exact (stage2_elim_non_entry_loop_sim ctx1 ctx2 RExc_s2 fargs c f_blk safe_no_p p dt
                   varg1 U0 P_pre pr_va fs0 f2 base_dead pr_dead σ1_s σ2_s sf1_s sf2_s fstk g0
                   U_step j1 Hnd_bks Hno_entry_pred Hsub_safe Hp_blk_nuse Ebks_chk
                   Hf_id Hf_non_entry HincU_s Hne_s Hinv_s Hgenv_pre Hsafe_s Hvars_s
                   (fun U_x σ1_x σ2_x sf1_x sf2_x ex Hinc Hinv =>
                      Hrexc U_x P_pre f2 base_dead pr_dead σ1_x σ2_x sf1_x sf2_x ex Hinc Hinv)).
        * intros (P_pre & f2 & base_dead & pr_dead & σ1_s & σ2_s & sf1_s & sf2_s &
                  HincU_s & Hreq & -> & -> & Hinv_s & _).
          inversion Hreq; subst r2; clear Hreq.
          apply refine_prov_ret.
          refine (conj Logic.eq_refl (conj HincU_s _)).
          exists P_pre, f2, base_dead, pr_dead, σ1_s, σ2_s, sf1_s, sf2_s;
            exact (conj Logic.eq_refl (conj Logic.eq_refl Hinv_s)).
    - intros U_ocfg s1_ocfg r_ocfg1 s2_ocfg r_ocfg2 _
        (<- & HincU_ocfg & P_e & f2 & base_dead & pr_dead & σ1_e & σ2_e & sf1_e & sf2_e &
         -> & -> & Hinv_e).
      destruct r_ocfg1 as [bid_miss | uv_ret].
      + apply refine_cfg_exc_raise_both.
      + apply refine_cfg_exc_ret.
        refine (conj Logic.eq_refl (conj HincU_ocfg _)).
        exists P_e, f2, base_dead, pr_dead, σ1_e, σ2_e, sf1_e, sf2_e;
          exact (conj Logic.eq_refl (conj Logic.eq_refl Hinv_e)).
  Qed.

  Lemma try_elim_dead_alloca_denote_function_sim {IPWB : IPtrWellBehaved IP}
    (P0 : list N) (g0 : @global_env (@ParamsV IP IPT))
    (df df' : definition dtyp (CFG.cfg dtyp)) :
    genv_safe P0 g0 ->
    try_elim_dead_alloca_in_defn df = Some df' ->
    leaf_ctx_fn_rel P0 g0 (denote_function df) (denote_function df').
  Proof using.
    intros Hgenv0 Htry.
    unfold try_elim_dead_alloca_in_defn in Htry; cbn zeta in Htry.
    set (fargs := df_args df) in *.
    set (c := df_instrs df) in *.
    destruct (m2r_nodup_ids (List.map blk_id (blks c))
              && negb (in_raw_ids (init c) (m2r_all_succs c))
              && cfg_no_block_addresses c) eqn:Eg1; [| discriminate Htry].
    rewrite !andb_true_iff, negb_true_iff in Eg1.
    destruct Eg1 as [[Hnd_bks Hno_entry_pred] _].
    apply m2r_nodup_ids_spec in Hnd_bks.
    apply in_raw_ids_false in Hno_entry_pred.
    destruct (find_block (blks c) (init c)) as [b_init |] eqn:Efind_init;
      [| discriminate Htry].
    destruct (m2r_find_block_some_inv (blks c) (init c) b_init Efind_init)
      as [Hin_init Hid_init].
    destruct (m2r_is_empty (blk_phis b_init)
              && m2r_non_invoke_term (snd (fst (blk_term b_init)))) eqn:Eg2;
      [| discriminate Htry].
    rewrite andb_true_iff in Eg2; destruct Eg2 as [Hphis_init Hni_init].
    apply m2r_is_empty_spec in Hphis_init.
    set (all_defs := fargs ++ flat_map full_block_defs (blks c)) in *.
    set (all_uses := flat_map full_block_uses (blks c)) in *.
    set (safe_locals := m2r_collect_unique_allocas all_defs (blks c)) in *.
    destruct (find_trailing_dead_alloca_in_code all_defs all_uses safe_locals [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |] eqn:Efind_al;
      [| discriminate Htry].
    pose proof (find_trailing_dead_alloca_in_code_inv
                  all_defs all_uses safe_locals [] (blk_code b_init)
                  pre_al al_ins post_al p dt Efind_al) as Hal_inv.
    cbv zeta in Hal_inv; cbn [List.rev app] in Hal_inv.
    set (safe_no_p := List.filter (fun q => negb (raw_id_eqb q p)) safe_locals) in *.
    destruct Hal_inv as (Hsplit_init & (anns_al & md_al & -> & Hanns_al & _) &
                         Hsc & Hcnt_p & Hp_nuse & Hpre_chk & Hpost_chk).
    apply in_raw_ids_false in Hp_nuse.
    destruct (forallb
                (fun bk =>
                   if raw_id_eqb (blk_id bk) (init c) then true
                   else
                     forallb (check_no_alloca_or_call_instr safe_no_p) (blk_code bk) &&
                     m2r_non_invoke_term (snd (fst (blk_term bk))))
                (blks c)) eqn:Ebks_chk; [| discriminate Htry].
    inversion Htry; subst df'; clear Htry.
    assert (Hsub_safe : forall q, In q safe_no_p -> In q safe_locals).
    { intros q Hq; apply filter_In in Hq as [Hq _]; exact Hq. }
    assert (Hp_blk_nuse : forall bk, In bk (blks c) -> ~ In p (full_block_uses bk)).
    { intros bk Hbk Hp; apply Hp_nuse, in_flat_map; exists bk; split; assumption. }
    set (f_blk := fun bk : block dtyp =>
                    if raw_id_eqb (blk_id bk) (init c) then
                      {| blk_id       := blk_id bk;
                         blk_phis     := blk_phis bk;
                         blk_code     := pre_al ++ post_al;
                         blk_term     := blk_term bk;
                         blk_comments := blk_comments bk |}
                    else bk).
    set (c' := {| init := init c; blks := List.map f_blk (blks c); args := args c |}).
    assert (Hf_id : forall bk, In bk (blks c) -> blk_id (f_blk bk) = blk_id bk).
    { intros bk _; unfold f_blk; destruct (raw_id_eqb (blk_id bk) (init c)); reflexivity. }
    assert (Hf_entry :
              f_blk b_init =
              {| blk_id       := blk_id b_init;
                 blk_phis     := blk_phis b_init;
                 blk_code     := pre_al ++ post_al;
                 blk_term     := blk_term b_init;
                 blk_comments := blk_comments b_init |}).
    { unfold f_blk; rewrite Hid_init, raw_id_eqb_refl; reflexivity. }
    assert (Hf_non_entry : forall bk, In bk (blks c) -> blk_id bk <> init c -> f_blk bk = bk).
    { intros bk _ Hne; unfold f_blk; destruct (raw_id_eqb (blk_id bk) (init c)) eqn:Eeq;
        [apply raw_id_eqb_spec in Eeq; contradiction | reflexivity]. }
    right.
    intros ctx1 ctx2 cc args U0 σ1_in σ2_in [sf_caller fstk_caller] Hpu0 Heq_in.
    unfold denote_function; cbn [df_prototype df_args df_instrs].
    fold fargs c c'.
    destruct (dc_param_attrs (df_prototype df)) as [ret_attrs args_attrs].
    set (fname := show_raw_id (dc_name (df_prototype df))).
    set (fcc := anns_cconv (dc_annotations (df_prototype df))).
    set (fs0 := Memory_stack_frame_stack (state_memory_stack σ2_in)).
    pose proof (stage1_equal_to_mem_inv U0 P0 σ1_in σ2_in Hpu0 Heq_in) as Hinv0.
    eapply refine_cfg_model_bind with
      (RA := fun U' '(s1', _) '(s2', _) =>
               U' = U0 /\
               s1' = (σ1_in, ((sf_caller, fstk_caller), g0)) /\
               s2' = (σ2_in, ((sf_caller, fstk_caller), g0))).
    - eapply refine_cfg_EOU; [apply refine_EOU_refl |].
      intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
    - intros U_cc s1_cc _ s2_cc _ _ (-> & -> & ->).
      eapply refine_cfg_model_bind.
      + exact (apply_args_attrs_stage1_cfg_sim ctx1 ctx2 args_attrs
                 ("Argument of " ++ fname ++ " violates noundef.")%string
                 args U0 P0 [] σ1_in σ2_in ((sf_caller, fstk_caller), g0) ((sf_caller, fstk_caller), g0) Hinv0).
      + intros U_aa s1_aa args1 s2_aa args2 _ (-> & -> & -> & <-).
        eapply refine_cfg_model_bind.
        * exact (push_call_frame_stage1_sim ctx1 ctx2 df
                   {| df_prototype := df_prototype df; df_args := fargs; df_instrs := c' |}
                   args1 U0 P0 [] σ1_in σ2_in sf_caller sf_caller fstk_caller fstk_caller g0
                   Logic.eq_refl Hinv0).
        * intros U_pf s1_pf varg1 s2_pf varg2 _
            (pr_va & bs & vs & σ1_pf & σ2_pf & Hnin_va & -> & <- & Ecomb & -> & -> & Hinv_pf & Htf_pf).
          fold fs0 in Htf_pf.
          set (sf0 := {| stack_vars := init_local_env bs;
                         stack_exc  := None;
                         stack_loc  := Some ""%string |}).
          set (fstk := sf_caller :: fstk_caller).
          assert (Hgenv_pf : genv_safe (pr_va :: P0) g0)
            by (apply (genv_safe_incl P0 (pr_va :: P0) g0 (fun x Hx => or_intror Hx) Hgenv0)).
          assert (Hsafe_sf0 : safe_locals_env (pr_va :: P0) safe_no_p (stack_vars sf0))
            by (exact (proj2 (safe_locals_env_init_args (pr_va :: P0) fargs (blks c) safe_no_p
                                args1 bs vs Ecomb Hsub_safe))).
          set (sz_dead := N.to_nat (@store_size_dtyp SizeofV dt)).
          set (RExc_s2 :=
                 fun U_e (s1_e s2_e : FusedS) (ex1 ex2 : @exc (@ParamsV IP IPT)) =>
                   ex1 = ex2 /\
                   incl (pr_va :: U0) U_e /\
                   exists P_e f2 base_dead pr_dead σ1_e σ2_e sf1_e sf2_e,
                     s1_e = (σ1_e, ((sf1_e, fstk), g0)) /\
                     s2_e = (σ2_e, ((sf2_e, fstk), g0)) /\
                     stage2_mem_inv U_e P_e fs0 f2 base_dead pr_dead sz_dead σ1_e σ2_e).
          set (RA_s2 :=
                 fun U_e (s1_e s2_e : FusedS) (v1 v2 : @dvalue (@ParamsV IP IPT)) =>
                   v1 = v2 /\
                   incl (pr_va :: U0) U_e /\
                   exists P_e f2 base_dead pr_dead σ1_e σ2_e sf1_e sf2_e,
                     s1_e = (σ1_e, ((sf1_e, fstk), g0)) /\
                     s2_e = (σ2_e, ((sf2_e, fstk), g0)) /\
                     stage2_mem_inv U_e P_e fs0 f2 base_dead pr_dead sz_dead σ1_e σ2_e).
          eapply refine_cfg_model_bind with (RA := exc_post RExc_s2 RA_s2).
          -- change (interp_cfg_model ctx1 (run_exc (denote_cfg_map (ocfg_map (blks c)) c (Some varg1)))
                       (σ1_pf, ((sf0, fstk), g0)))
               with (interp_cfg_exc ctx1 (denote_cfg_map (ocfg_map (blks c)) c (Some varg1))
                       (σ1_pf, ((sf0, fstk), g0))).
             change (interp_cfg_model ctx2 (run_exc (denote_cfg_map (ocfg_map (blks c')) c' (Some varg1)))
                       (σ2_pf, ((sf0, fstk), g0)))
               with (interp_cfg_exc ctx2 (denote_cfg_map (ocfg_map (blks c')) c' (Some varg1))
                       (σ2_pf, ((sf0, fstk), g0))).
             exact (stage2_elim_cfg_sim ctx1 ctx2 fargs c b_init pre_al post_al p dt anns_al md_al
                      safe_no_p f_blk varg1 U0 P0 pr_va fs0 σ1_pf σ2_pf sf0 fstk g0
                      Hnd_bks Hno_entry_pred Efind_init Hin_init Hid_init Hphis_init Hni_init
                      Hsplit_init Hsc Hanns_al Hsub_safe Hp_blk_nuse Hpre_chk Hpost_chk Ebks_chk
                      Hf_id Hf_entry Hf_non_entry Hinv_pf Htf_pf Hgenv_pf Hsafe_sf0).
          -- intros U_rv s1_rv rv1 s2_rv rv2 _ Hrv_post.
             assert (Hrv_unif :
                       rv1 = rv2 /\
                       incl (pr_va :: U0) U_rv /\
                       exists P_e f2 base_dead pr_dead σ1_e σ2_e sf1_e sf2_e,
                         s1_rv = (σ1_e, ((sf1_e, fstk), g0)) /\
                         s2_rv = (σ2_e, ((sf2_e, fstk), g0)) /\
                         stage2_mem_inv U_rv P_e fs0 f2 base_dead pr_dead sz_dead σ1_e σ2_e).
             { destruct rv1 as [ex1 | v1], rv2 as [ex2 | v2]; cbn [exc_post] in Hrv_post;
                 try contradiction; destruct Hrv_post as [<- Hrest]; (split; [reflexivity | exact Hrest]). }
             clear Hrv_post.
             destruct Hrv_unif as (<- & HincU_rv & P_e & f2 & base_dead & pr_dead &
                                   σ1_e & σ2_e & sf1_e & sf2_e & -> & -> & Hinv_e).
             eapply refine_cfg_model_bind.
             ++ exact (pop_call_frame_stage2_sim ctx1 ctx2 U_rv P_e fs0 f2 base_dead pr_dead sz_dead
                         σ1_e σ2_e sf1_e sf2_e sf_caller fstk_caller g0 Hinv_e).
             ++ intros U_pop s1_pop _ s2_pop _ _
                  (σ1_pop & σ2_pop & -> & _ & _ & -> & -> & Heq_pop & _).
                pose proof (stage1_equal_to_mem_inv U_rv [] σ1_pop σ2_pop
                              (fun _ H => match H with end) Heq_pop) as Hinv_pop.
                eapply refine_prov_weaken.
                ** exact (check_call_return_stage1_cfg_sim ctx1 ctx2
                            (dc_attrs (df_prototype df)) ret_attrs None fname args1 rv1
                            U_rv [] [] σ1_pop σ2_pop
                            ((sf_caller, fstk_caller), g0) ((sf_caller, fstk_caller), g0) Hinv_pop).
                ** intros U_f [s1_f rf1] [s2_f rf2] (-> & -> & -> & <-).
                   exact (conj (fun x Hx => HincU_rv x (or_intror Hx))
                            (conj Heq_pop (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
  Qed.


End MemoryAndSerialization.
