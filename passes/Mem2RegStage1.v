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

From CertPasses Require Import Mem2RegSpec Mem2RegModel Mem2RegMemBase Mem2RegGhostInv Mem2RegExprLift Mem2RegCpsSSA Mem2RegLeafKnot Mem2RegStage2.

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

  (** ** 3N. Stage 1 SSA Promotion Helpers, Block Lookup & Block-Address Preservation *)

  Lemma stage1_prom_alloca_init_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (p init_reg : local_id) (dt : dtyp)
    (anns_al : list (annotation dtyp)) (md_al : list (metadata dtyp))
    (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
    (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hsc : is_scalar_dtyp dt = true)
    (Hanns : is_only_align_anns anns_al = true)
    (Hinv : stage1_mem_inv U P_unprom G σ1 σ2)
    (Htf : top_frame_unprom_from fs0 G (state_memory_stack σ2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists gs0 σ1' σ2',
              ~ In (gs_pr gs0) U /\
              U' = gs_pr gs0 :: U /\
              r1 = tt /\ r2 = tt /\
              gs_dt gs0 = dt /\
              gs_db gs0 = DVALUE_Poison /\
              s1' = (σ1', ((upd_local_sf sf1
                              (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf1)),
                            fstk1), g)) /\
              s2' = (σ2', ((upd_local_sf sf2
                              (Maps.add init_reg (DVALUE_Base DVALUE_Poison)
                                 (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2))),
                            fstk2), g)) /\
              stage1_mem_inv (gs_pr gs0 :: U) P_unprom (gs0 :: G) σ1' σ2' /\
              top_frame_prom_from fs0 gs0 G (state_memory_stack σ2')))
      U
      (interp_cfg_exc ctx1
         (denote_instr (IId p, INSTR_Alloca dt anns_al, md_al) va1)
         (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2
         (ITree.bind
            (denote_instr (IId p, INSTR_Alloca dt anns_al, md_al) va2)
            (fun _ =>
               denote_instr
                 (IId init_reg,
                  INSTR_Op (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison),
                  []) va2))
         (σ2, ((sf2, fstk2), g))).
  Proof using.
    destruct (is_only_align_anns_num_elts anns_al Hanns) as [Hnum _].
    eapply refine_prov_obs_eq;
      [apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                (bind_unit_ret_r (denote_instr (Pa := @ParamsV IP IPT) (IId p, INSTR_Alloca dt anns_al, md_al) va1)))
      | reflexivity |].
    eapply refine_cfg_exc_bind with
      (RA := fun U' s1' s2' r1 r2 =>
               exists gs0 σ1' σ2',
                 ~ In (gs_pr gs0) U /\
                 U' = gs_pr gs0 :: U /\
                 r1 = tt /\ r2 = tt /\
                 gs_dt gs0 = dt /\
                 gs_db gs0 = DVALUE_Poison /\
                 s1' = (σ1', ((upd_local_sf sf1
                                 (Maps.add p (DVALUE_Base (DVALUE_Pointer (Pa := @ParamsV IP IPT) (gs_pt gs0))) (stack_vars sf1)),
                               fstk1), g)) /\
                 s2' = (σ2', ((upd_local_sf sf2
                                 (Maps.add p (DVALUE_Base (DVALUE_Pointer (Pa := @ParamsV IP IPT) (gs_pt gs0))) (stack_vars sf2)),
                               fstk2), g)) /\
                 stage1_mem_inv (gs_pr gs0 :: U) P_unprom (gs0 :: G) σ1' σ2' /\
                 top_frame_prom_from fs0 gs0 G (state_memory_stack σ2')).
    - cbn [denote_instr]; rewrite Hnum.
      assert (Eal :
                ITree.bind
                  (ITree.bind
                     (alloca (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT)) dt 1%N (explicit_alignment anns_al))
                     (fun v => lwrite (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT)) p v))
                  (fun _ => Ret tt) ≅
                ITree.bind
                  (alloca (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT)) dt 1%N (explicit_alignment anns_al))
                  (fun v => lwrite (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT)) p v)).
      { rewrite Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros v _ <-; apply bind_unit_ret_r. }
      eapply refine_prov_obs_eq;
        [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ Eal)
        | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ Eal) |].
      eapply refine_cfg_exc_bind with
        (RA := fun U' s1' s2' v1 v2 =>
                 exists gs0 σ1' σ2',
                   ~ In (gs_pr gs0) U /\
                   U' = gs_pr gs0 :: U /\
                   gs_dt gs0 = dt /\
                   gs_db gs0 = DVALUE_Poison /\
                   v1 = DVALUE_Base (DVALUE_Pointer (Pa := @ParamsV IP IPT) (gs_pt gs0)) /\
                   v2 = DVALUE_Base (DVALUE_Pointer (Pa := @ParamsV IP IPT) (gs_pt gs0)) /\
                   stage1_mem_inv (gs_pr gs0 :: U) P_unprom (gs0 :: G) σ1' σ2' /\
                   top_frame_prom_from fs0 gs0 G (state_memory_stack σ2') /\
                   s1' = (σ1', ((sf1, fstk1), g)) /\
                   s2' = (σ2', ((sf2, fstk2), g))).
      + unfold alloca, Subevent.trigger; try unfold trigger_cast.
        apply refine_cfg_exc_memory_event.
        eapply refine_prov_weaken;
          [exact (stage1_alloca_prom dt (explicit_alignment anns_al) fs0 U P_unprom G σ1 σ2 Hsc Hinv Htf) |].
        intros U1 [σ1' v1] [σ2' v2]
          (gs0 & Hnin & -> & Hdt0 & Hdb0 & -> & -> & Hinv' & Htf').
        exists gs0, σ1', σ2';
          exact (conj Hnin (conj Logic.eq_refl (conj Hdt0 (conj Hdb0 (conj Logic.eq_refl
                   (conj Logic.eq_refl (conj Hinv' (conj Htf' (conj Logic.eq_refl Logic.eq_refl))))))))).
      + intros U1 s1' _ s2' _ _
          (gs0 & σ1' & σ2' & Hnin & -> & Hdt0 & Hdb0 & -> & -> & Hinv' & Htf' & -> & ->).
        eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |].
        eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_lwrite |].
        apply refine_prov_ret.
        exists gs0, σ1', σ2';
          exact (conj Hnin (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl
                   (conj Hdt0 (conj Hdb0 (conj Logic.eq_refl (conj Logic.eq_refl (conj Hinv' Htf'))))))))).
    - intros U1 s1_m _ s2_m _ _
        (gs0 & σ1' & σ2' & Hnin & -> & _ & _ & Hdt0 & Hdb0 & -> & -> & Hinv' & Htf').
      apply denote_init_copy_poison_exc_r.
      eapply refine_prov_obs_eq; [symmetry; apply interp_cfg_exc_ret | reflexivity |].
      destruct sf2 as [sv2 se2 sl2]; cbn [upd_local_sf stack_vars].
      apply refine_prov_ret.
      exists gs0, σ1', σ2'; repeat match goal with |- _ /\ _ => split end; try reflexivity; assumption.
  Qed.

  Lemma m2r_assoc_nodup {K V : Type} {Heq : ExtLib.Core.RelDec.RelDec (@Logic.eq K)}
    {Hcorr : ExtLib.Core.RelDec.RelDec_Correct Heq}
    (k : K) (l : list (K * V)) (v : V) :
    NoDup (List.map fst l) ->
    In (k, v) l ->
    assoc k l = Some v.
  Proof using.
    induction l as [| [k0 v0] rest IH]; cbn [List.map fst In assoc]; [intros _ [] |].
    intros Hnd [Heq_p | Hin].
    - inversion Heq_p; subst k0 v0.
      destruct (ExtLib.Core.RelDec.rel_dec k k) eqn:Er; [reflexivity |].
      exfalso; pose proof (proj2 (ExtLib.Core.RelDec.rel_dec_correct k k) Logic.eq_refl) as Htr; congruence.
    - inversion Hnd as [| ? ? Hnin Hnd']; subst.
      destruct (ExtLib.Core.RelDec.rel_dec k k0) eqn:Er.
      + exfalso; pose proof (proj1 (ExtLib.Core.RelDec.rel_dec_correct k k0) Er) as ->.
        exact (Hnin (in_map fst rest (k0, v) Hin)).
      + exact (IH Hnd' Hin).
  Qed.

  Lemma denote_phis_stage1_prom_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (bid_from : block_id) (phi_reg src_reg : local_id) (dt : dtyp)
    (incoming : list (block_id * exp dtyp))
    (phis : list (local_id * phi dtyp * list (metadata dtyp)))
    (dv0 : @dvalue (@ParamsV IP IPT))
    (U : list N) (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hassoc : assoc bid_from incoming = Some (EXP_Ident (ID_Local src_reg)))
    (Hlk_src : Maps.lookup src_reg (stack_vars sf2) = Some dv0)
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
              s2' = (σ2, ((upd_local_sf sf2 (write_phi_dvs ((phi_reg, dv0) :: dvs) (stack_vars sf2)),
                           fstk2), g))))
      U
      (interp_cfg_exc ctx1 (denote_phis bid_from phis) (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2
         (denote_phis bid_from ((phi_reg, Phi [] dt incoming, []) :: phis))
         (σ2, ((sf2, fstk2), g))).
  Proof using.
    unfold denote_phis.
    cbn [map_monad denote_phi ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree]; rewrite Hassoc.
    assert (Er_assoc :
      ITree.bind
        (ITree.bind
           (ITree.bind (denote_exp' (Pa := @ParamsV IP IPT) (Some dt) (EXP_Ident (ID_Local src_reg)))
              (fun dv => Ret (phi_reg, dv)))
           (fun y =>
              ITree.bind (map_monad (denote_phi (Pa := @ParamsV IP IPT) bid_from) phis)
                (fun ys => Ret (y :: ys))))
        (fun dvs =>
           ITree.bind
             (map_monad (fun '(id, dv) => lwrite (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT)) id dv) dvs)
             (fun _ => Ret tt)) ≅
      ITree.bind (denote_exp' (Pa := @ParamsV IP IPT) (Some dt) (EXP_Ident (ID_Local src_reg)))
        (fun dv0' =>
           ITree.bind (map_monad (denote_phi (Pa := @ParamsV IP IPT) bid_from) phis)
             (fun dvs =>
                ITree.bind
                  (map_monad (fun '(id, dv) => lwrite (Pa := @ParamsV IP IPT) (E := @CFGEtop (@ParamsV IP IPT)) id dv)
                     ((phi_reg, dv0') :: dvs))
                  (fun _ => Ret tt)))).
    { rewrite !Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros dv0' _ <-; rewrite Eqit.bind_ret_l, Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros dvs _ <-; rewrite Eqit.bind_ret_l; reflexivity. }
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ Er_assoc) |];
      clear Er_assoc.
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; apply interp_cfg_exc_bind |].
    eapply refine_prov_tau_expand_r;
      [apply tau_expand_bind_l, tau_expand_exc_withCall_denote_exp |].
    unfold mcfg_inr_exc; cbn [denote_exp lookup_id].
    eapply refine_prov_obs_eq; [reflexivity | symmetry; apply Eqit.bind_bind |].
    eapply refine_prov_tau_star_r;
      [apply tau_star_bind, (tau_star_mcfg_lread_some src_reg dv0 σ2 sf2 fstk2 g Hlk_src) |].
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; apply Eqit.bind_ret_l |].
    cbn beta iota.
    eapply refine_prov_obs_eq;
      [reflexivity | symmetry; apply Eqit.bind_ret_l |].
    cbn beta iota.
    eapply refine_cfg_exc_bind; [apply map_monad_denote_phi_same_exc_sim, Hvars |].
    intros U1 s1' dvs1 s2' dvs2 _ (-> & -> & -> & <- & Hfst).
    eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_write_phi_dvs |].
    eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_write_phi_dvs |].
    apply refine_prov_ret; exists dvs1; repeat (first [exact Hfst | reflexivity | split]).
  Qed.

  Lemma pass1_end_map_fst
    (pass1_out : list (block dtyp * local_id * code dtyp * local_id)) :
    List.map fst (List.map (fun '(bk, _, _, end_r) => (blk_id bk, end_r)) pass1_out) =
    List.map blk_id (List.map (fun '(bk, _, _, _) => bk) pass1_out).
  Proof using.
    induction pass1_out as [| [[[bk pr] cd] er] rest IH]; cbn; [reflexivity | f_equal; exact IH].
  Qed.

  Lemma pass1_find_block_gen
    (f : block dtyp * local_id * code dtyp * local_id -> block dtyp)
    (ps : list (block dtyp * local_id * code dtyp * local_id))
    (Hf_id : forall bk pr cd er, blk_id (f (bk, pr, cd, er)) = blk_id bk) :
    (forall bid,
       find_block (List.map (fun '(bk, _, _, _) => bk) ps) bid = None ->
       find_block (List.map f ps) bid = None) /\
    (forall bid bk,
       find_block (List.map (fun '(bk, _, _, _) => bk) ps) bid = Some bk ->
       exists pr cd er,
         In (bk, pr, cd, er) ps /\
         find_block (List.map f ps) bid = Some (f (bk, pr, cd, er))).
  Proof using.
    induction ps as [| [[[bk0 pr0] cd0] er0] rest [IH_none IH_some]]; cbn [List.map].
    - split; [intros bid0 Hnone; exact Hnone | intros ? ? H; cbn in H; discriminate H].
    - pose proof (Hf_id bk0 pr0 cd0 er0) as Hid0.
      split.
      + intros bid Hnone.
        destruct (raw_id_eqb (blk_id bk0) bid) eqn:Ebid; [apply raw_id_eqb_spec in Ebid; rename Ebid into Heq | apply raw_id_eqb_neq in Ebid; rename Ebid into Hne].
        * rewrite find_block_eq in Hnone by exact Heq; discriminate Hnone.
        * rewrite find_block_ineq in Hnone by exact Hne.
          rewrite find_block_ineq by congruence.
          exact (IH_none bid Hnone).
      + intros bid bk Hsome.
        destruct (raw_id_eqb (blk_id bk0) bid) eqn:Ebid; [apply raw_id_eqb_spec in Ebid; rename Ebid into Heq | apply raw_id_eqb_neq in Ebid; rename Ebid into Hne].
        * rewrite find_block_eq in Hsome by exact Heq; inversion Hsome; subst bk0.
          rewrite find_block_eq by congruence.
          exists pr0, cd0, er0; split; [left; reflexivity | reflexivity].
        * rewrite find_block_ineq in Hsome by exact Hne.
          rewrite find_block_ineq by congruence.
          destruct (IH_some bid bk Hsome) as (pr & cd & er & Hin & Hfb).
          exists pr, cd, er; split; [right; exact Hin | exact Hfb].
  Qed.

  Lemma pass1_find_block_spec
    (init_bid : block_id) (dt : dtyp) (init_reg : local_id)
    (all_bks : ocfg dtyp)
    (pass1_out : list (block dtyp * local_id * code dtyp * local_id))
    (Hbks : List.map (fun '(bk, _, _, _) => bk) pass1_out = all_bks) :
    let end_map := List.map (fun '(bk, _, _, end_r) => (blk_id bk, end_r)) pass1_out in
    let bks' := build_promoted_blocks init_bid dt init_reg all_bks pass1_out in
    (forall bid, find_block all_bks bid = None -> find_block bks' bid = None) /\
    (forall bid bk,
       find_block all_bks bid = Some bk ->
       exists phi_r cd' end_r,
         In (bk, phi_r, cd', end_r) pass1_out /\
         find_block bks' bid =
           Some (if raw_id_eqb (blk_id bk) init_bid then
                   {| blk_id := blk_id bk; blk_phis := blk_phis bk; blk_code := cd';
                      blk_term := blk_term bk; blk_comments := blk_comments bk |}
                 else
                   let preds := List.filter (fun b_pred => in_raw_ids (blk_id bk) (m2r_block_succs b_pred)) all_bks in
                   let incoming := List.map (fun b_pred => (blk_id b_pred, EXP_Ident (ID_Local (lookup_end_reg end_map (blk_id b_pred) init_reg)))) preds in
                   {| blk_id := blk_id bk; blk_phis := (phi_r, Phi [] dt incoming, []) :: blk_phis bk;
                      blk_code := cd'; blk_term := blk_term bk; blk_comments := blk_comments bk |})).
  Proof using.
    intros end_map bks'; subst bks'; unfold build_promoted_blocks; fold end_map.
    replace (find_block all_bks)
      with (find_block (List.map (fun '(bk, _, _, _) => bk) pass1_out))
      by (rewrite Hbks; reflexivity).
    apply (pass1_find_block_gen
             (fun '(bk, phi_r, cd', _) =>
                if raw_id_eqb (blk_id bk) init_bid then
                  {| blk_id := blk_id bk; blk_phis := blk_phis bk; blk_code := cd';
                     blk_term := blk_term bk; blk_comments := blk_comments bk |}
                else
                  let preds := List.filter (fun b_pred => in_raw_ids (blk_id bk) (m2r_block_succs b_pred)) all_bks in
                  let incoming := List.map (fun b_pred => (blk_id b_pred, EXP_Ident (ID_Local (lookup_end_reg end_map (blk_id b_pred) init_reg)))) preds in
                  {| blk_id := blk_id bk; blk_phis := (phi_r, Phi [] dt incoming, []) :: blk_phis bk;
                     blk_code := cd'; blk_term := blk_term bk; blk_comments := blk_comments bk |})
             pass1_out).
    intros bk pr cd er; destruct (raw_id_eqb (blk_id bk) init_bid); reflexivity.
  Qed.

  Lemma rewrite_code_for_slot_block_addresses_nil
    (p : local_id) (dt : dtyp) (cur_reg : local_id) (avoid : list raw_id)
    (cd cd' : code dtyp) (end_reg : local_id) (avoid' : list raw_id) :
    flat_map (fun '(_, i, _) => instr_block_addresses i) cd = [] ->
    rewrite_code_for_slot p dt cur_reg avoid cd = (cd', end_reg, avoid') ->
    flat_map (fun '(_, i, _) => instr_block_addresses i) cd' = [].
  Proof using.
    revert cur_reg avoid cd' end_reg avoid';
      induction cd as [| [[iid ins] md] rest IH];
      intros cur_reg avoid cd' end_reg avoid' Hba Hrw;
      cbn [rewrite_code_for_slot] in Hrw; cbn [flat_map] in Hba.
    - inversion Hrw; subst; reflexivity.
    - apply app_eq_nil in Hba as [Him_ba Hrest_ba].
      destruct (is_promotable_load_of p dt (iid, ins, md)) as [dst |].
      + set (lv_reg := fresh_name "mlv" (p :: cur_reg :: avoid)) in *.
        destruct (rewrite_code_for_slot p dt cur_reg (lv_reg :: avoid) rest) as [[rest' er] av'] eqn:E.
        inversion Hrw; subst; cbn; rewrite ?app_nil_r.
        exact (IH cur_reg (lv_reg :: avoid) rest' end_reg avoid' Hrest_ba E).
      + destruct (is_promotable_store_of p dt (iid, ins, md)) as [val_exp |] eqn:Est.
        * destruct (is_promotable_store_of_inv p dt (iid, ins, md) val_exp Est)
            as (_ & vid & anns_st & md_st & Heq_im & _).
          inversion Heq_im; subst iid ins md; clear Heq_im.
          cbn in Him_ba; rewrite !app_nil_r in Him_ba.
          set (sv_reg := fresh_name "msv" (p :: avoid)) in *.
          set (st_reg := fresh_name "mst" (p :: sv_reg :: avoid)) in *.
          destruct (rewrite_code_for_slot p dt st_reg (st_reg :: sv_reg :: avoid) rest)
            as [[rest' er] av'] eqn:E.
          inversion Hrw; subst; cbn; rewrite ?app_nil_r, Him_ba; cbn.
          exact (IH _ _ rest' end_reg avoid' Hrest_ba E).
        * destruct (rewrite_code_for_slot p dt cur_reg avoid rest) as [[rest' er] av'] eqn:E.
          inversion Hrw; subst; cbn; rewrite Him_ba; cbn.
          exact (IH cur_reg avoid rest' end_reg avoid' Hrest_ba E).
  Qed.

  Lemma flat_map_nil_in {A B : Type} (f : A -> list B) (xs : list A) :
    (forall x, In x xs -> f x = []) <-> flat_map f xs = [].
  Proof using.
    induction xs as [| x xs' IH]; cbn [flat_map In].
    - split; [intros _; reflexivity | intros _ ? []].
    - split.
      + intros Hall; rewrite (Hall x (or_introl Logic.eq_refl)); cbn.
        apply IH; intros y Hy; exact (Hall y (or_intror Hy)).
      + intros Hnil; apply app_eq_nil in Hnil as [Hx Hxs].
        intros y [<- | Hy]; [exact Hx | exact (proj2 IH Hxs y Hy)].
  Qed.

  Lemma promote_slot_in_defn_block_addresses
    (interproc_safe : bool) (df df' : definition dtyp (CFG.cfg dtyp)) :
    try_promote_slot_in_defn interproc_safe df = Some df' ->
    df_prototype df' = df_prototype df /\
    flat_map block_block_addresses (blks (df_instrs df')) =
    flat_map block_block_addresses (blks (df_instrs df)).
  Proof using.
    unfold try_promote_slot_in_defn; cbn zeta; intros Htry.
    set (fargs := df_args df) in *; set (c := df_instrs df) in *.
    destruct (m2r_nodup_ids (List.map blk_id (blks c))
              && negb (in_raw_ids (init c) (m2r_all_succs c))
              && cfg_no_block_addresses c) eqn:Eg1; [| discriminate Htry].
    rewrite !andb_true_iff in Eg1; destruct Eg1 as [[_ _] Hnba].
    apply cfg_no_block_addresses_nil in Hnba.
    destruct (find_block (blks c) (init c)) as [b_init |] eqn:Ef; [| discriminate Htry].
    destruct (m2r_find_block_some_inv (blks c) (init c) b_init Ef) as [Hin_init _].
    destruct (m2r_is_empty (blk_phis b_init)); [| discriminate Htry].
    destruct (find_promotable_in_init_code interproc_safe
                (fargs ++ flat_map full_block_defs (blks c))
                (flat_map full_block_uses (blks c))
                (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs (blks c)) (blks c))
                (init c) (blks c) b_init [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |] eqn:Efind; [| discriminate Htry].
    pose proof (find_promotable_in_init_code_inv interproc_safe
                  (fargs ++ flat_map full_block_defs (blks c))
                  (flat_map full_block_uses (blks c))
                  (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs (blks c)) (blks c))
                  (init c) (blks c) b_init [] (blk_code b_init)
                  pre_al al_ins post_al p dt Efind) as Hal_inv.
    cbv zeta in Hal_inv; cbn [List.rev app] in Hal_inv.
    destruct Hal_inv as (Hsplit_init & (anns_al & md_al & -> & _) & _).
    inversion Htry; subst df'; clear Htry.
    split; [reflexivity |].
    rewrite Hnba; apply (proj1 (flat_map_nil_in block_block_addresses _)).
    pose proof (proj2 (flat_map_nil_in block_block_addresses (blks c)) Hnba) as Hbk_nil.
    unfold promote_slot_in_cfg; cbn [blks].
    set (avoid0 := fargs ++ cfg_all_ids c).
    set (init_reg := fresh_name "m2r_init" avoid0).
    set (avoid1 := init_reg :: avoid0).
    set (phi_regs := fresh_names "m2r_phi" (List.length (blks c)) avoid1).
    set (avoid2 := phi_regs ++ avoid1).
    destruct (rewrite_code_for_slot p dt init_reg avoid2 post_al)
      as [[post_al' init_end_reg] avoid3] eqn:Erw_post.
    set (init_op := (IId init_reg, INSTR_Op (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison), @nil (metadata dtyp))).
    set (init_code' := pre_al ++ (IId p, INSTR_Alloca dt anns_al, md_al) :: init_op :: post_al').
    set (bk_phis := List.combine (blks c) phi_regs).
    destruct (rewrite_non_entry_blocks_pass1 (init c) p dt init_end_reg init_code' avoid3 bk_phis)
      as [pass1_out avoid_out] eqn:Epass1.
    assert (Hinit_ba : flat_map (fun '(_, i, _) => instr_block_addresses i) init_code' = []).
    { pose proof (Hbk_nil b_init Hin_init) as Hb0; unfold block_block_addresses in Hb0.
      apply app_eq_nil in Hb0 as [_ Hb0a]; apply app_eq_nil in Hb0a as [Hb0_cd _].
      rewrite Hsplit_init, flat_map_app in Hb0_cd; cbn [flat_map instr_block_addresses] in Hb0_cd.
      apply app_eq_nil in Hb0_cd as [Hpre_ba Hpost_ba].
      pose proof (rewrite_code_for_slot_block_addresses_nil p dt init_reg avoid2
                    post_al post_al' init_end_reg avoid3 Hpost_ba Erw_post) as Hpost'_ba.
      unfold init_code', init_op; rewrite flat_map_app; cbn; rewrite Hpre_ba, Hpost'_ba; reflexivity. }
    assert (Hinc2 : incl avoid0 avoid2).
    { intros z Hz; unfold avoid2, avoid1; apply in_app_iff; right; right; exact Hz. }
    assert (Hinit_nin0 : ~ In init_reg avoid0) by apply fresh_name_not_in.
    destruct (rewrite_code_for_slot_fresh_inv avoid0 p dt init_reg avoid2 post_al
                post_al' init_end_reg avoid3 Erw_post Hinc2 Hinit_nin0) as [Hav3 Hinit_er_nin0].
    assert (Hinc3 : incl avoid0 avoid3) by (eapply incl_tran; eassumption).
    assert (Hlen_pr : List.length (blks c) = List.length phi_regs)
      by (symmetry; apply fresh_names_length).
    assert (Hphis_nin0 : forall r, In r (List.map snd bk_phis) -> ~ In r avoid0).
    { unfold bk_phis; rewrite (combine_snd_eq _ _ Hlen_pr).
      intros r Hr Hin0; eapply (fresh_names_disjoint "m2r_phi" _ avoid1 r Hr); right; exact Hin0. }
    destruct (rewrite_non_entry_blocks_pass1_spec avoid0 (init c) p dt init_end_reg init_code'
                avoid3 bk_phis pass1_out avoid_out Epass1 Hinc3 Hinit_er_nin0 Hphis_nin0)
      as (Hbks_p1 & _ & _ & Hall_p1).
    assert (Hbks_eq : List.map (fun '(bk, _, _, _) => bk) pass1_out = blks c)
      by (etransitivity; [exact Hbks_p1 | exact (combine_fst_eq _ _ Hlen_pr)]);
      clear Hbks_p1; rename Hbks_eq into Hbks_p1.
    unfold build_promoted_blocks; intros b' Hb'.
    apply in_map_iff in Hb' as [[[[bk phi_r] cd'] end_r] [<- Hin_p1]].
    assert (Hin_bk : In bk (blks c)).
    { rewrite <- Hbks_p1; exact (in_map (fun '(b0, _, _, _) => b0) _ _ Hin_p1). }
    pose proof (Hbk_nil bk Hin_bk) as Hbk_ba; unfold block_block_addresses in Hbk_ba.
    apply app_eq_nil in Hbk_ba as [Hbk_ph Hbk_ba1]; apply app_eq_nil in Hbk_ba1 as [Hbk_cd Hbk_tm].
    pose proof (Hall_p1 bk phi_r cd' end_r Hin_p1) as (_ & _ & Hcd_spec).
    destruct (raw_id_eqb (blk_id bk) (init c)).
    - destruct Hcd_spec as [-> _]; unfold block_block_addresses; cbn.
      rewrite Hbk_ph, Hinit_ba, Hbk_tm; reflexivity.
    - destruct Hcd_spec as (av_in & av_out & _ & Erw_bk).
      pose proof (rewrite_code_for_slot_block_addresses_nil p dt phi_r av_in
                    (blk_code bk) cd' end_r av_out Hbk_cd Erw_bk) as Hcd'_ba.
      unfold block_block_addresses; cbn [blk_phis blk_code blk_term flat_map].
      assert (Hinc_ba :
        forall preds0,
          flat_map (fun x : block_id * exp dtyp => exp_block_addresses (snd x))
            (List.map
               (fun b_pred : block dtyp =>
                  (blk_id b_pred,
                   EXP_Ident (ID_Local (lookup_end_reg
                     (List.map (fun '(bk0, _, _, end_r0) => (blk_id bk0, end_r0)) pass1_out)
                     (blk_id b_pred) init_reg))))
               preds0) = []).
      { induction preds0 as [| bp rest_p IHp]; cbn; [reflexivity | exact IHp]. }
      rewrite Hinc_ba, Hbk_ph, Hcd'_ba, Hbk_tm; reflexivity.
  Qed.

  Lemma elim_dead_alloca_in_defn_block_addresses
    (df df' : definition dtyp (CFG.cfg dtyp)) :
    try_elim_dead_alloca_in_defn df = Some df' ->
    df_prototype df' = df_prototype df /\
    flat_map block_block_addresses (blks (df_instrs df')) =
    flat_map block_block_addresses (blks (df_instrs df)).
  Proof using.
    unfold try_elim_dead_alloca_in_defn; cbn zeta; intros Htry.
    set (c := df_instrs df) in *.
    destruct (m2r_nodup_ids (List.map blk_id (blks c))
              && negb (in_raw_ids (init c) (m2r_all_succs c))
              && cfg_no_block_addresses c) eqn:Eg1; [| discriminate Htry].
    rewrite !andb_true_iff in Eg1; destruct Eg1 as [[_ _] Hnba].
    apply cfg_no_block_addresses_nil in Hnba.
    destruct (find_block (blks c) (init c)) as [b_init |] eqn:Ef; [| discriminate Htry].
    destruct (m2r_find_block_some_inv (blks c) (init c) b_init Ef) as [Hin_init _].
    destruct (m2r_is_empty (blk_phis b_init) && m2r_non_invoke_term (snd (fst (blk_term b_init))));
      [| discriminate Htry].
    destruct (find_trailing_dead_alloca_in_code _ _ _ [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |] eqn:Efind; [| discriminate Htry].
    pose proof (find_trailing_dead_alloca_in_code_inv _ _ _ [] (blk_code b_init)
                  pre_al al_ins post_al p dt Efind) as Hal_inv.
    cbv zeta in Hal_inv; cbn [List.rev app] in Hal_inv.
    destruct Hal_inv as (Hsplit_init & (anns_al & md_al & -> & _) & _).
    destruct (forallb _ (blks c)); [| discriminate Htry].
    inversion Htry; subst df'; clear Htry; split; [reflexivity |].
    rewrite Hnba; apply (proj1 (flat_map_nil_in block_block_addresses _)).
    pose proof (proj2 (flat_map_nil_in block_block_addresses (blks c)) Hnba) as Hbk_nil.
    cbn [blks]; intros b' Hb'; apply in_map_iff in Hb' as [bk [<- Hin_bk]].
    pose proof (Hbk_nil bk Hin_bk) as Hbk_ba.
    destruct (raw_id_eqb (blk_id bk) (init c)); [| exact Hbk_ba].
    pose proof (Hbk_nil b_init Hin_init) as Hb0; unfold block_block_addresses in Hb0.
    apply app_eq_nil in Hb0 as [_ Hb0a]; apply app_eq_nil in Hb0a as [Hb0_cd _].
    rewrite Hsplit_init, flat_map_app in Hb0_cd; cbn [flat_map instr_block_addresses] in Hb0_cd.
    apply app_eq_nil in Hb0_cd as [Hpre_ba Hpost_ba].
    unfold block_block_addresses in Hbk_ba |- *; cbn [blk_phis blk_code blk_term].
    apply app_eq_nil in Hbk_ba as [Hbk_ph Hbk_ba1]; apply app_eq_nil in Hbk_ba1 as [_ Hbk_tm].
    rewrite flat_map_app, Hbk_ph, Hpre_ba, Hpost_ba, Hbk_tm; reflexivity.
  Qed.

  (** ** 3O. Stage 1 Leaf Slot Promotion Simulation *)

  Lemma m2r_nodup_map_filter {A B : Type} (f : A -> B) (pred : A -> bool) (xs : list A) :
    NoDup (List.map f xs) ->
    NoDup (List.map f (List.filter pred xs)).
  Proof using.
    induction xs as [| x xs' IH]; cbn [List.map List.filter]; [intros _; constructor |].
    intros Hnd; inversion Hnd as [| ? ? Hnin Hnd']; subst.
    destruct (pred x); cbn [List.map].
    - constructor; [| exact (IH Hnd')].
      intros Hin; apply in_map_iff in Hin as (y & Heq & Hy).
      apply filter_In in Hy as [Hy _].
      apply Hnin; rewrite <- Heq; exact (in_map f xs' y Hy).
    - exact (IH Hnd').
  Qed.

  Lemma safe_locals_in_avoid0 (fargs : list local_id) (c : CFG.cfg dtyp) (q : local_id) :
    In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs (blks c)) (blks c)) ->
    In q (fargs ++ cfg_all_ids c).
  Proof using.
    unfold m2r_collect_unique_allocas; intros Hq.
    apply in_flat_map in Hq as (bk & Hbk & Hq_bk).
    apply in_flat_map in Hq_bk as ([[iid ins] md] & Him & Hq_im).
    destruct iid as [id0 |]; [| contradiction Hq_im].
    destruct ins; try contradiction Hq_im.
    destruct (Nat.eqb (m2r_count_id id0 (fargs ++ flat_map full_block_defs (blks c))) 1%nat);
      cbn in Hq_im; [| contradiction Hq_im].
    destruct Hq_im as [<- | []].
    apply in_app_iff; right; eapply in_defs_in_cfg_all_ids; [exact Hbk |].
    unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
    apply in_flat_map; exists (IId id0, INSTR_Alloca t anns, md);
      split; [exact Him | left; reflexivity].
  Qed.

  Lemma rewrite_code_for_slot_no_call_exc_sim
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (avoid0 : list raw_id) (fargs : list local_id) (bks : ocfg dtyp) (bk : block dtyp)
    (pre_c cd post_c : code dtyp)
    (safe_no_p : list local_id) (p : local_id) (dt : dtyp)
    (cur_reg : local_id) (avoid : list raw_id)
    (cd' : code dtyp) (end_reg : local_id) (avoid' : list raw_id)
    (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
    (fs0 : @Framestack (@ParamsV IP IPT))
    (U P_unprom : list N) (gs : ghost_slot) (G : list ghost_slot)
    (σ1 σ2 : state)
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
    (g : @global_env (@ParamsV IP IPT))
    (Hnd_bks : NoDup (List.map blk_id bks))
    (Hbk : In bk bks)
    (Hsplit : blk_code bk = pre_c ++ cd ++ post_c)
    (Hsub : forall q,
              In q safe_no_p ->
              In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
    (Hsafe_av0 : incl safe_no_p avoid0)
    (Huses_av0 : forall im x, In im cd -> In x (m2r_code_entry_uses im) -> In x avoid0)
    (Hdefs_av0 : forall im x, In im cd -> In x (instr_id_defs (fst (fst im))) -> In x avoid0)
    (Hp_nd_cd : ~ In p (flat_map (fun '(iid, _, _) => instr_id_defs iid) cd))
    (Hchk : forallb (check_code_entry_for_slot false safe_no_p p dt) cd = true)
    (Hrw : rewrite_code_for_slot p dt cur_reg avoid cd = (cd', end_reg, avoid'))
    (Hinc_av : incl avoid0 avoid)
    (Hcur_nin0 : ~ In cur_reg avoid0)
    (Hsc : is_scalar_dtyp dt = true)
    (Hdt : gs_dt gs = dt)
    (Hlk_p : Maps.lookup p (stack_vars sf1) = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))
    (Hlk_cur : Maps.lookup cur_reg (stack_vars sf2) = Some (DVALUE_Base (gs_db gs)))
    (Hinv : stage1_mem_inv U P_unprom (gs :: G) σ1 σ2)
    (Htf : top_frame_prom_from fs0 gs G (state_memory_stack σ2))
    (Hgenv : genv_safe P_unprom g)
    (Hsafe_loc : safe_locals_env P_unprom safe_no_p (stack_vars sf2))
    (Hvars : forall x,
               In x avoid0 -> x <> p ->
               Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
    refine_prov
      (exc_post RExc
         (fun U' s1' s2' r1 r2 =>
            exists P_unprom' gs' σ1' σ2' sf1' sf2',
              incl U U' /\
              incl P_unprom P_unprom' /\
              r1 = tt /\ r2 = tt /\
              gs_dt gs' = dt /\
              Maps.lookup p (stack_vars sf1') = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs'))) /\
              Maps.lookup end_reg (stack_vars sf2') = Some (DVALUE_Base (gs_db gs')) /\
              s1' = (σ1', ((sf1', fstk1), g)) /\
              s2' = (σ2', ((sf2', fstk2), g)) /\
              stage1_mem_inv U' P_unprom' (gs' :: G) σ1' σ2' /\
              top_frame_prom_from fs0 gs' G (state_memory_stack σ2') /\
              genv_safe P_unprom' g /\
              safe_locals_env P_unprom' safe_no_p (stack_vars sf2') /\
              (forall x,
                 In x avoid0 -> x <> p ->
                 Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf2'))))
      U
      (interp_cfg_exc ctx1 (denote_code cd va1) (σ1, ((sf1, fstk1), g)))
      (interp_cfg_exc ctx2 (denote_code cd' va2) (σ2, ((sf2, fstk2), g))).
  Proof using.
    revert pre_c cur_reg avoid cd' end_reg avoid' U P_unprom gs σ1 σ2 sf1 sf2
      Hsplit Huses_av0 Hdefs_av0 Hp_nd_cd Hchk Hrw Hinc_av Hcur_nin0
      Hdt Hlk_p Hlk_cur Hinv Htf Hgenv Hsafe_loc Hvars.
    induction cd as [| im rest IH];
      intros pre_c cur_reg avoid cd' end_reg avoid' U P_unprom gs σ1 σ2 sf1 sf2
        Hsplit Huses_av0 Hdefs_av0 Hp_nd_cd Hchk Hrw Hinc_av Hcur_nin0
        Hdt Hlk_p Hlk_cur Hinv Htf Hgenv Hsafe_loc Hvars;
      cbn [rewrite_code_for_slot forallb flat_map] in *.
    - inversion Hrw; subst cd' end_reg avoid'; clear Hrw.
      unfold denote_code; cbn [loop_monad].
      apply refine_cfg_exc_ret.
      exists P_unprom, gs, σ1, σ2, sf1, sf2;
        repeat match goal with |- _ /\ _ => split end; try apply incl_refl; try reflexivity; assumption.
    - rewrite andb_true_iff in Hchk; destruct Hchk as [Hchk_im Hchk_rest].
      assert (Hp_nd_im : ~ In p (instr_id_defs (fst (fst im)))).
      { destruct im as [[iid_i ?] ?]; intros Hp; apply Hp_nd_cd, in_app_iff; left; exact Hp. }
      assert (Hp_nd_rest : ~ In p (flat_map (fun '(iid, _, _) => instr_id_defs iid) rest)).
      { intros Hp; apply Hp_nd_cd, in_app_iff; right; exact Hp. }
      assert (Huses_rest : forall im0 x, In im0 rest -> In x (m2r_code_entry_uses im0) -> In x avoid0)
        by (intros im0 x Him0 Hx; exact (Huses_av0 im0 x (or_intror Him0) Hx)).
      assert (Hdefs_rest : forall im0 x, In im0 rest -> In x (instr_id_defs (fst (fst im0))) -> In x avoid0)
        by (intros im0 x Him0 Hx; exact (Hdefs_av0 im0 x (or_intror Him0) Hx)).
      assert (Hsplit_rest : blk_code bk = (pre_c ++ [im]) ++ rest ++ post_c)
        by (rewrite <- app_assoc; exact Hsplit).
      unfold check_code_entry_for_slot in Hchk_im.
      destruct (is_promotable_load_of p dt im) as [dst |] eqn:Eld.
      + set (lv_reg := fresh_name "mlv" (p :: cur_reg :: avoid)) in *.
        destruct (rewrite_code_for_slot p dt cur_reg (lv_reg :: avoid) rest) as [[rest' er] av'] eqn:Erest.
        inversion Hrw; subst cd' end_reg avoid'; clear Hrw.
        pose proof (Hdefs_av0 im dst (or_introl Logic.eq_refl)) as Hdst_av0_fn.
        destruct (is_promotable_load_of_inv p dt im dst Eld)
          as (Hdst_ne_p & anns_ld & md_ld & -> & _ & Hmd_ld).
        assert (Hdst_av0 : In dst avoid0) by (apply Hdst_av0_fn; left; reflexivity).
        assert (Hcur_ne_dst : cur_reg <> dst) by (intros ->; exact (Hcur_nin0 Hdst_av0)).
        assert (Hlv_ne_p : p <> lv_reg)
          by (intros Heq; exact (fresh_name_not_in "mlv" (p :: cur_reg :: avoid) (or_introl Heq))).
        assert (Hlv_ne_cur : cur_reg <> lv_reg)
          by (intros Heq; exact (fresh_name_not_in "mlv" (p :: cur_reg :: avoid) (or_intror (or_introl Heq)))).
        assert (Hlv_nin0 : ~ In lv_reg avoid0)
          by (intros Hin0; exact (fresh_name_not_in "mlv" (p :: cur_reg :: avoid) (or_intror (or_intror (Hinc_av _ Hin0))))).
        assert (Hdst_nsafe : ~ In dst safe_no_p).
        { intros Hin_s.
          destruct (unique_alloca_code_def_is_alloca fargs bks dst Hnd_bks (Hsub dst Hin_s)
                      bk pre_c
                      (INSTR_Load dt (DTYPE_Base DTYPE_Pointer, EXP_Ident (ID_Local p)) anns_ld)
                      md_ld (rest ++ post_c) Hbk Hsplit) as (? & ? & Hbad);
            discriminate Hbad. }
        assert (Hlv_nsafe : ~ In lv_reg safe_no_p)
          by (intros Hin_s; exact (Hlv_nin0 (Hsafe_av0 lv_reg Hin_s))).
        unfold denote_code; cbn [loop_monad ExtLib.Structures.Monad.bind Monad_itree].
        eapply refine_prov_obs_eq;
          [reflexivity
          | apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
        eapply refine_cfg_exc_bind.
        * exact (denote_mk_load_pair_exc_sim ctx1 ctx2 RExc dst p lv_reg cur_reg dt anns_ld md_ld
                   va1 va2 U P_unprom gs G σ1 σ2 sf1 sf2 fstk1 fstk2 g
                   Hdt Hsc Hmd_ld Hlk_p Hlk_cur Hinv).
        * intros U1 s1_m _ s2_m _ _ (dv_ld & -> & _ & _ & -> & ->).
          assert (Hlk_p1 : Maps.lookup p (Maps.add dst dv_ld (stack_vars sf1)) =
                           Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))
            by (cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by (intros ->; exact (Hdst_ne_p Logic.eq_refl)); exact Hlk_p).
          assert (Hlk_cur1 : Maps.lookup cur_reg
                               (Maps.add dst dv_ld
                                  (Maps.add lv_reg (DVALUE_Array true [DVALUE_Base (gs_db gs)]) (stack_vars sf2))) =
                             Some (DVALUE_Base (gs_db gs)))
            by (cbn [Maps.lookup Maps.add Map_rmap];
                rewrite !RMF.F.add_neq_o
                  by (first [intros Heq'; exact (Hcur_ne_dst (Logic.eq_sym Heq'))
                            | intros Heq'; exact (Hlv_ne_cur (Logic.eq_sym Heq'))]);
                exact Hlk_cur).
          assert (Hsafe1 : safe_locals_env P_unprom safe_no_p
                             (Maps.add dst dv_ld
                                (Maps.add lv_reg (DVALUE_Array true [DVALUE_Base (gs_db gs)]) (stack_vars sf2))))
            by (apply safe_locals_env_add_other; [assumption | apply safe_locals_env_add_other; assumption]).
          assert (Hvars1 : forall x, In x avoid0 -> x <> p ->
                             Maps.lookup x (Maps.add dst dv_ld (stack_vars sf1)) =
                             Maps.lookup x
                               (Maps.add dst dv_ld
                                  (Maps.add lv_reg (DVALUE_Array true [DVALUE_Base (gs_db gs)]) (stack_vars sf2)))).
          { intros x Hx Hne; cbn [Maps.lookup Maps.add Map_rmap]; destruct (raw_id_eqb x dst) eqn:Exd; [apply raw_id_eqb_spec in Exd; subst x | apply raw_id_eqb_neq in Exd; rename Exd into Hxd];
              [rewrite !RMF.F.add_eq_o by reflexivity; reflexivity
              | rewrite !RMF.F.add_neq_o
                  by (first [intros Heq'; exact (Hxd (Logic.eq_sym Heq'))
                            | intros ->; exact (Hlv_nin0 Hx)]);
                exact (Hvars x Hx Hne)]. }
          assert (Hinc_av1 : incl avoid0 (lv_reg :: avoid))
            by (intros z Hz; right; exact (Hinc_av z Hz)).
          exact (IH (pre_c ++ [_]) cur_reg (lv_reg :: avoid) rest' er av' U P_unprom gs σ1 σ2
                   (upd_local_sf sf1 (Maps.add dst dv_ld (stack_vars sf1)))
                   (upd_local_sf sf2
                      (Maps.add dst dv_ld
                         (Maps.add lv_reg (DVALUE_Array true [DVALUE_Base (gs_db gs)]) (stack_vars sf2))))
                   Hsplit_rest Huses_rest Hdefs_rest Hp_nd_rest Hchk_rest Erest
                   Hinc_av1 Hcur_nin0 Hdt Hlk_p1 Hlk_cur1 Hinv Htf Hgenv Hsafe1 Hvars1).
      + destruct (is_promotable_store_of p dt im) as [val_exp |] eqn:Est.
        * set (sv_reg := fresh_name "msv" (p :: avoid)) in *.
          set (st_reg := fresh_name "mst" (p :: sv_reg :: avoid)) in *.
          destruct (rewrite_code_for_slot p dt st_reg (st_reg :: sv_reg :: avoid) rest) as [[rest' er] av'] eqn:Erest.
          inversion Hrw; subst cd' end_reg avoid'; clear Hrw.
          pose proof (Huses_av0 im) as Hval_av0_fn.
          destruct (is_promotable_store_of_inv p dt im val_exp Est)
            as (Hnin_p_val & vid & anns_st & md_st & -> & _ & _).
          assert (Hsv_nin0 : ~ In sv_reg avoid0)
            by (intros Hin0; exact (fresh_name_not_in "msv" (p :: avoid) (or_intror (Hinc_av _ Hin0)))).
          assert (Hst_nin0 : ~ In st_reg avoid0)
            by (intros Hin0; exact (fresh_name_not_in "mst" (p :: sv_reg :: avoid) (or_intror (or_intror (Hinc_av _ Hin0))))).
          assert (Hsv_nsafe : ~ In sv_reg safe_no_p)
            by (intros Hin_s; exact (Hsv_nin0 (Hsafe_av0 sv_reg Hin_s))).
          assert (Hst_nsafe : ~ In st_reg safe_no_p)
            by (intros Hin_s; exact (Hst_nin0 (Hsafe_av0 st_reg Hin_s))).
          assert (Hval_vars : forall x,
                    In x (full_exp_uses val_exp) ->
                    Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)).
          { intros x Hx; apply Hvars.
            - apply (Hval_av0_fn x (or_introl Logic.eq_refl)); cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
                apply in_app_iff; left; apply in_app_iff; left; exact Hx.
            - intros ->; exact (Hnin_p_val Hx). }
          unfold denote_code; cbn [loop_monad ExtLib.Structures.Monad.bind Monad_itree].
          eapply refine_prov_obs_eq;
            [reflexivity
            | apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
          eapply refine_cfg_exc_bind.
          -- exact (denote_mk_store_pair_exc_sim ctx1 ctx2 RExc vid p sv_reg st_reg dt val_exp
                      anns_st md_st va1 va2 fs0 U P_unprom gs G σ1 σ2 sf1 sf2 fstk1 fstk2 g
                      Hdt Hsc Hlk_p Hinv Htf Hval_vars).
          -- intros U1 s1_m _ s2_m _ _ (db' & bs' & σ1' & -> & _ & _ & _ & -> & -> & Hinv1 & Htf1).
             assert (Hinc_av1 : incl avoid0 (st_reg :: sv_reg :: avoid))
               by (intros z Hz; right; right; exact (Hinc_av z Hz)).
             assert (Hlk_st : Maps.lookup st_reg
                                (Maps.add st_reg (DVALUE_Base db')
                                   (Maps.add sv_reg (DVALUE_Array true [DVALUE_Base db']) (stack_vars sf2))) =
                              Some (DVALUE_Base (gs_db (gs_set_val gs db' bs'))))
               by (cbn [gs_db gs_set_val Maps.lookup Maps.add Map_rmap]; apply RMF.F.add_eq_o; reflexivity).
             assert (Hsafe1 : safe_locals_env P_unprom safe_no_p
                                (Maps.add st_reg (DVALUE_Base db')
                                   (Maps.add sv_reg (DVALUE_Array true [DVALUE_Base db']) (stack_vars sf2))))
               by (apply safe_locals_env_add_other; [assumption | apply safe_locals_env_add_other; assumption]).
             assert (Hvars1 : forall x, In x avoid0 -> x <> p ->
                                Maps.lookup x (stack_vars sf1) =
                                Maps.lookup x
                                  (Maps.add st_reg (DVALUE_Base db')
                                     (Maps.add sv_reg (DVALUE_Array true [DVALUE_Base db']) (stack_vars sf2)))).
             { intros x Hx Hne; cbn [Maps.lookup Maps.add Map_rmap];
               rewrite !RMF.F.add_neq_o
                 by (first [intros ->; exact (Hst_nin0 Hx)
                           | intros ->; exact (Hsv_nin0 Hx)]);
               exact (Hvars x Hx Hne). }
             exact (IH (pre_c ++ [_]) st_reg (st_reg :: sv_reg :: avoid) rest' er av'
                      U P_unprom (gs_set_val gs db' bs') σ1' σ2 sf1
                      (upd_local_sf sf2
                         (Maps.add st_reg (DVALUE_Base db')
                            (Maps.add sv_reg (DVALUE_Array true [DVALUE_Base db']) (stack_vars sf2))))
                      Hsplit_rest Huses_rest Hdefs_rest Hp_nd_rest Hchk_rest Erest
                      Hinc_av1 Hst_nin0 Hdt Hlk_p Hlk_st Hinv1 Htf1 Hgenv Hsafe1 Hvars1).
        * destruct (rewrite_code_for_slot p dt cur_reg avoid rest) as [[rest' er] av'] eqn:Erest.
          inversion Hrw; subst cd' end_reg avoid'; clear Hrw.
          assert (Huse_im : forall x,
                    In x (m2r_code_entry_uses im) ->
                    Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)).
          { intros x Hx; apply Hvars;
              [exact (Huses_av0 im x (or_introl Logic.eq_refl) Hx)
              | intros ->; exact (proj1 (check_other_instr_for_slot_inv false safe_no_p p im Hchk_im) Hx)]. }
          unfold denote_code; cbn [loop_monad].
          eapply refine_cfg_exc_bind.
          -- exact (stage1_no_call_instr_exc_sim ctx1 ctx2 RExc
                      (fun s => top_frame_prom_from fs0 gs G (state_memory_stack s))
                      fargs bks bk pre_c (rest ++ post_c)
                      safe_no_p p im va1 va2 U P_unprom (gs :: G) σ1 σ2 sf1 sf2 fstk1 fstk2 g
                      Hnd_bks Hbk Hsplit Hsub Hchk_im
                      (fun s_a s_b Heq_fs HT => top_frame_prom_frame_eq fs0 gs G _ _ (eq_sym Heq_fs) HT)
                      (fun s_a s_b ptrs Hdisj Heq_fs HT =>
                         top_frame_prom_frame_eq fs0 gs G _ _ (eq_sym Heq_fs)
                           (top_frame_prom_add_ptrs fs0 gs G ptrs _ HT Hdisj))
                      Hinv Htf Hgenv Hsafe_loc Huse_im).
          -- intros U1 s1_m _ s2_m _ _
               (P1 & σ1_m & σ2_m & sf1_m & sf2_m &
                HincU1 & HincP1 & _ & _ & -> & -> & Hinv1 & Htf1 & Hgenv1 & Hsafe1 & Hsf_step).
             assert (Hstep_env :
                       Maps.lookup p (stack_vars sf1_m) = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) /\
                       Maps.lookup cur_reg (stack_vars sf2_m) = Some (DVALUE_Base (gs_db gs)) /\
                       (forall x, In x avoid0 -> x <> p ->
                          Maps.lookup x (stack_vars sf1_m) = Maps.lookup x (stack_vars sf2_m))).
             { destruct Hsf_step as [[-> ->] | (id0 & v & Heq_iid & -> & ->)];
                 [exact (conj Hlk_p (conj Hlk_cur Hvars)) |].
               assert (Hid_av0 : In id0 avoid0).
               { apply (Hdefs_av0 im id0 (or_introl Logic.eq_refl)); rewrite Heq_iid; left; reflexivity. }
               assert (Hp_ne_id : p <> id0)
                 by (intros ->; apply Hp_nd_im; rewrite Heq_iid; left; reflexivity).
               assert (Hcur_ne_id : cur_reg <> id0)
                 by (intros ->; exact (Hcur_nin0 Hid_av0)).
               cbn [stack_vars upd_local_sf Maps.lookup Maps.add Map_rmap]; split;
                 [rewrite RMF.F.add_neq_o by (intros Heq'; exact (Hp_ne_id (Logic.eq_sym Heq'))); exact Hlk_p | split;
                 [rewrite RMF.F.add_neq_o by (intros Heq'; exact (Hcur_ne_id (Logic.eq_sym Heq'))); exact Hlk_cur |]].
               intros x Hx Hne; destruct (raw_id_eqb x id0) eqn:Ex_id; [apply raw_id_eqb_spec in Ex_id; subst x | apply raw_id_eqb_neq in Ex_id; rename Ex_id into Hx_id];
                 [rewrite !RMF.F.add_eq_o by reflexivity; reflexivity
                 | rewrite !RMF.F.add_neq_o by (intros Heq'; exact (Hx_id (Logic.eq_sym Heq'))); exact (Hvars x Hx Hne)]. }
             destruct Hstep_env as (Hlk_p1 & Hlk_cur1 & Hvars1).
             eapply refine_prov_weaken.
             ++ exact (IH (pre_c ++ [im]) cur_reg avoid rest' er av' U1 P1 gs σ1_m σ2_m sf1_m sf2_m
                         Hsplit_rest Huses_rest Hdefs_rest Hp_nd_rest Hchk_rest Erest
                         Hinc_av Hcur_nin0 Hdt Hlk_p1 Hlk_cur1 Hinv1 Htf1 Hgenv1 Hsafe1 Hvars1).
             ++ intros U2 [s1_f res1] [s2_f res2].
                destruct res1 as [ex1 | u1], res2 as [ex2 | u2]; cbn [exc_post];
                  try (intros H; exact H).
                intros (P2 & gs2 & σ1_f & σ2_f & sf1_f & sf2_f &
                        HincU2 & HincP2 & -> & -> & Hdt2 & Hlk_p2 & Hlk_er2 &
                        -> & -> & Hinv2 & Htf2 & Hgenv2 & Hsafe2 & Hvars2).
                exists P2, gs2, σ1_f, σ2_f, sf1_f, sf2_f.
                exact (conj (incl_tran HincU1 HincU2) (conj (incl_tran HincP1 HincP2)
                         (conj Logic.eq_refl (conj Logic.eq_refl
                           (conj Hdt2 (conj Hlk_p2 (conj Hlk_er2
                             (conj Logic.eq_refl (conj Logic.eq_refl
                               (conj Hinv2 (conj Htf2 (conj Hgenv2 (conj Hsafe2 Hvars2))))))))))))).
  Qed.

  Lemma try_promote_slot_leaf_denote_function_sim
    (P0 : list N) (g0 : @global_env (@ParamsV IP IPT))
    (df df' : definition dtyp (CFG.cfg dtyp)) :
    genv_safe P0 g0 ->
    try_promote_slot_in_defn false df = Some df' ->
    leaf_ctx_fn_rel P0 g0 (denote_function df) (denote_function df').
  Proof using.
    intros Hgenv0 Htry.
    unfold try_promote_slot_in_defn in Htry; cbn zeta in Htry.
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
    destruct (m2r_is_empty (blk_phis b_init)) eqn:Ephis_init; [| discriminate Htry].
    apply m2r_is_empty_spec in Ephis_init.
    set (all_defs := fargs ++ flat_map full_block_defs (blks c)) in *.
    set (all_uses := flat_map full_block_uses (blks c)) in *.
    set (safe_locals := m2r_collect_unique_allocas all_defs (blks c)) in *.
    destruct (find_promotable_in_init_code false all_defs all_uses safe_locals
                (init c) (blks c) b_init [] (blk_code b_init))
      as [[[[[pre_al al_ins] post_al] p] dt] |] eqn:Efind_al;
      [| discriminate Htry].
    pose proof (find_promotable_in_init_code_inv false all_defs all_uses safe_locals
                  (init c) (blks c) b_init [] (blk_code b_init)
                  pre_al al_ins post_al p dt Efind_al) as Hal_inv.
    cbv zeta in Hal_inv; cbn [List.rev app] in Hal_inv.
    set (safe_no_p := List.filter (fun q => negb (raw_id_eqb q p)) safe_locals) in *.
    destruct Hal_inv as (Hsplit_init & (anns_al & md_al & -> & Hanns_al & _) &
                         Hsc & Hcnt_p & _ & Hpre_chk & Hpost_chk & Hterm_p & Hni_init & Ebks_chk).
    apply in_raw_ids_false in Hterm_p.
    inversion Htry; subst df'; clear Htry.
    destruct (unique_def_code_split fargs (blks c) b_init pre_al p
                (INSTR_Alloca dt anns_al) md_al post_al Hnd_bks Hin_init Hsplit_init Hcnt_p)
      as (_ & _ & _ & Hp_nd_post & _ & Hp_nd_other).
    assert (Hsub_safe : forall q, In q safe_no_p -> In q safe_locals)
      by (intros q Hq; apply filter_In in Hq as [Hq _]; exact Hq).
    assert (Hp_nin_safe : ~ In p safe_no_p).
    { intros Hp; apply filter_In in Hp as [_ Hp]; rewrite raw_id_eqb_refl in Hp; discriminate Hp. }
    set (avoid0 := fargs ++ cfg_all_ids c).
    assert (Hsafe_av0 : incl safe_no_p avoid0)
      by (intros q Hq; apply safe_locals_in_avoid0, Hsub_safe, Hq).
    assert (Hblk_uses_av0 : forall bk x, In bk (blks c) -> In x (full_block_uses bk) -> In x avoid0)
      by (intros bk x Hbk Hx; unfold avoid0; apply in_app_iff; right; exact (in_uses_in_cfg_all_ids c bk x Hbk Hx)).
    assert (Hblk_defs_av0 : forall bk x, In bk (blks c) -> In x (full_block_defs bk) -> In x avoid0)
      by (intros bk x Hbk Hx; unfold avoid0; apply in_app_iff; right; exact (in_defs_in_cfg_all_ids c bk x Hbk Hx)).
    set (c' := promote_slot_in_cfg fargs c b_init pre_al (IId p, INSTR_Alloca dt anns_al, md_al) post_al p dt).
    set (init_reg := fresh_name "m2r_init" avoid0).
    set (avoid1 := init_reg :: avoid0).
    set (phi_regs := fresh_names "m2r_phi" (List.length (blks c)) avoid1).
    set (avoid2 := phi_regs ++ avoid1).
    destruct (rewrite_code_for_slot p dt init_reg avoid2 post_al)
      as [[post_al' init_end_reg] avoid3] eqn:Erw_post.
    set (init_op := (IId init_reg, INSTR_Op (mk_copy_exp (DTYPE_Base (DTYPE_I 1)) dt EXP_Poison), @nil (metadata dtyp))).
    set (init_code' := pre_al ++ (IId p, INSTR_Alloca dt anns_al, md_al) :: init_op :: post_al').
    set (bk_phis := List.combine (blks c) phi_regs).
    destruct (rewrite_non_entry_blocks_pass1 (init c) p dt init_end_reg init_code' avoid3 bk_phis)
      as [pass1_out avoid_out] eqn:Epass1.
    assert (Hc'_eq :
      c' = {| init := init c;
              blks := build_promoted_blocks (init c) dt init_reg (blks c) pass1_out;
              args := args c |}).
    { unfold c', promote_slot_in_cfg; cbn zeta.
      fold avoid0 init_reg avoid1 phi_regs avoid2.
      rewrite Erw_post; fold init_op init_code' bk_phis.
      rewrite Epass1; reflexivity. }
    assert (Hinit_nin0 : ~ In init_reg avoid0) by apply fresh_name_not_in.
    assert (Hinc_av2 : incl avoid0 avoid2)
      by (intros z Hz; unfold avoid2, avoid1; apply in_app_iff; right; right; exact Hz).
    destruct (rewrite_code_for_slot_fresh_inv avoid0 p dt init_reg avoid2 post_al
                post_al' init_end_reg avoid3 Erw_post Hinc_av2 Hinit_nin0)
      as [Hav3 Hinit_er_nin0].
    assert (Hinc_av3 : incl avoid0 avoid3) by (eapply incl_tran; eassumption).
    assert (Hlen_pr : List.length (blks c) = List.length phi_regs)
      by (symmetry; apply fresh_names_length).
    assert (Hphis_nin0 : forall r, In r (List.map snd bk_phis) -> ~ In r avoid0).
    { unfold bk_phis; rewrite (combine_snd_eq _ _ Hlen_pr).
      intros r Hr Hin0; eapply (fresh_names_disjoint "m2r_phi" _ avoid1 r Hr); right; exact Hin0. }
    destruct (rewrite_non_entry_blocks_pass1_spec avoid0 (init c) p dt init_end_reg init_code'
                avoid3 bk_phis pass1_out avoid_out Epass1 Hinc_av3 Hinit_er_nin0 Hphis_nin0)
      as (Hbks_p1 & _ & _ & Hall_p1).
    assert (Hbks_eq : List.map (fun '(bk, _, _, _) => bk) pass1_out = blks c)
      by (etransitivity; [exact Hbks_p1 | exact (combine_fst_eq _ _ Hlen_pr)]);
      clear Hbks_p1; rename Hbks_eq into Hbks_p1.
    set (end_map := List.map (fun '(bk, _, _, end_r) => (blk_id bk, end_r)) pass1_out).
    assert (Hnd_end_map : NoDup (List.map fst end_map)).
    { unfold end_map; rewrite pass1_end_map_fst, Hbks_p1; exact Hnd_bks. }
    pose proof (pass1_find_block_spec (init c) dt init_reg (blks c) pass1_out Hbks_p1)
      as [Hfb_none Hfb_some]; cbv zeta in Hfb_none, Hfb_some; fold end_map in Hfb_some.
    right.
    intros ctx1 ctx2 cc args U0 σ1_in σ2_in [sf_caller fstk_caller] Hpu0 Heq_in.
    unfold denote_function; cbn [df_prototype df_args df_instrs]; fold fargs c c'.
    destruct (dc_param_attrs (df_prototype df)) as [ret_attrs args_attrs].
    set (fname := show_raw_id (dc_name (df_prototype df))).
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
          set (sf0 := {| stack_vars := init_local_env bs; stack_exc := None; stack_loc := Some ""%string |}).
          set (fstk := sf_caller :: fstk_caller).
          assert (Hgenv_pf : genv_safe (pr_va :: P0) g0)
            by (apply (genv_safe_incl P0 (pr_va :: P0) g0 (fun x Hx => or_intror Hx) Hgenv0)).
          assert (Hsafe_sf0 : safe_locals_env (pr_va :: P0) safe_no_p (stack_vars sf0))
            by (exact (proj2 (safe_locals_env_init_args (pr_va :: P0) fargs (blks c) safe_no_p
                                args1 bs vs Ecomb Hsub_safe))).
          set (ExitRel :=
                 fun U_e (s1_e s2_e : FusedS) =>
                   incl (pr_va :: U0) U_e /\
                   (exists P_e σ1_e σ2_e sf1_e sf2_e,
                      s1_e = (σ1_e, ((sf1_e, fstk), g0)) /\
                      s2_e = (σ2_e, ((sf2_e, fstk), g0)) /\
                      ((stage1_mem_inv U_e P_e [] σ1_e σ2_e /\
                        top_frame_unprom_from fs0 [] (state_memory_stack σ2_e)) \/
                       (exists gs_e,
                          stage1_mem_inv U_e P_e (gs_e :: []) σ1_e σ2_e /\
                          top_frame_prom_from fs0 gs_e [] (state_memory_stack σ2_e))))).
          set (RExc_s1 := fun U_e s1_e s2_e (ex1 ex2 : @exc (@ParamsV IP IPT)) => ex1 = ex2 /\ ExitRel U_e s1_e s2_e).
          set (RA_s1   := fun U_e s1_e s2_e (v1 v2 : @dvalue (@ParamsV IP IPT)) => v1 = v2 /\ ExitRel U_e s1_e s2_e).
          eapply refine_cfg_model_bind with (RA := exc_post RExc_s1 RA_s1).
          -- change (interp_cfg_model ctx1 (run_exc (denote_cfg_map (ocfg_map (blks c)) c (Some varg1)))
                       (σ1_pf, ((sf0, fstk), g0)))
               with (interp_cfg_exc ctx1 (denote_cfg_map (ocfg_map (blks c)) c (Some varg1))
                       (σ1_pf, ((sf0, fstk), g0))).
             change (interp_cfg_model ctx2 (run_exc (denote_cfg_map (ocfg_map (blks c')) c' (Some varg1)))
                       (σ2_pf, ((sf0, fstk), g0)))
               with (interp_cfg_exc ctx2 (denote_cfg_map (ocfg_map (blks c')) c' (Some varg1))
                       (σ2_pf, ((sf0, fstk), g0))).
             unfold denote_cfg_map; rewrite Hc'_eq; cbn [init blks].
             eapply refine_cfg_exc_bind with
               (RA := fun U_e s1_e s2_e (r1 r2 : (block_id * block_id) + @dvalue (@ParamsV IP IPT)) =>
                        r1 = r2 /\ ExitRel U_e s1_e s2_e).
             ++ unfold denote_ocfg_map.
                eapply refine_prov_obs_eq;
                  [symmetry; apply interp_cfg_exc_unfold_iter
                  | symmetry; apply interp_cfg_exc_unfold_iter |].
                destruct (Hfb_some (init c) b_init Efind_init)
                  as (phi_init & cd_init & end_init & Hin_p1_init & Efind_init').
                pose proof (Hall_p1 b_init phi_init cd_init end_init Hin_p1_init)
                  as (_ & _ & Hinit_p1_spec).
                rewrite Hid_init, raw_id_eqb_refl in Hinit_p1_spec, Efind_init'.
                destruct Hinit_p1_spec as [-> ->].
                assert (Hlk_end_init : lookup_end_reg end_map (init c) init_reg = init_end_reg).
                { apply lookup_end_reg_in_nodup; [exact Hnd_end_map |].
                  unfold end_map; rewrite <- Hid_init.
                  exact (in_map (fun '(bk, _, _, er) => (blk_id bk, er)) _ _ Hin_p1_init). }
                cbn beta iota.
                rewrite ScopeTheory.ocfg_map_find_block, Efind_init.
                rewrite ScopeTheory.ocfg_map_find_block, Efind_init'.
                unfold denote_block; cbn [blk_phis blk_code blk_term]; rewrite Ephis_init.
                eapply PassCommonModel.refine_prov_bind with
                  (RR := exc_post RExc_s1
                             (fun U_s s1_s s2_s
                                (lr1 lr2 : (block_id * block_id) + ((block_id * block_id) + @dvalue (@ParamsV IP IPT))) =>
                                exists (P_b1 : list N) gs_b1 σ1_b1 σ2_b1
                                       (sf1_b1 sf2_b1 : @stack_frame (@ParamsV IP IPT)),
                                  incl (pr_va :: U0) U_s /\
                                  lr1 = lr2 /\
                                  s1_s = (σ1_b1, ((sf1_b1, fstk), g0)) /\
                                  s2_s = (σ2_b1, ((sf2_b1, fstk), g0)) /\
                                  gs_dt gs_b1 = dt /\
                                  Maps.lookup p (stack_vars sf1_b1) =
                                    Some (@DVALUE_Base (@ParamsV IP IPT) (@DVALUE_Pointer (@ParamsV IP IPT) (gs_pt gs_b1))) /\
                                  Maps.lookup init_end_reg (stack_vars sf2_b1) =
                                    Some (@DVALUE_Base (@ParamsV IP IPT) (gs_db gs_b1)) /\
                                  stage1_mem_inv U_s P_b1 (gs_b1 :: []) σ1_b1 σ2_b1 /\
                                  top_frame_prom_from fs0 gs_b1 [] (state_memory_stack σ2_b1) /\
                                  genv_safe P_b1 g0 /\
                                  safe_locals_env P_b1 safe_no_p (stack_vars sf2_b1) /\
                                  (forall x, In x avoid0 -> x <> p ->
                                     Maps.lookup x (stack_vars sf1_b1) = Maps.lookup x (stack_vars sf2_b1)) /\
                                  match lr1 with
                                  | inl j => fst j = init c /\ In (snd j) (m2r_block_succs b_init) /\ snd j <> init c
                                  | inr _ => True
                                  end)).
                ** eapply refine_prov_obs_eq;
                     [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                                         (eq_itree_bind_congr_l
                                            (eq_itree_bind_congr_l (denote_phis_nil_eq (init c)))))
                     | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _
                                          (eq_itree_bind_congr_l
                                             (eq_itree_bind_congr_l (denote_phis_nil_eq (init c))))) |].
                   eapply refine_prov_obs_eq;
                     [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_bind _ _ _))
                     | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
                   eapply refine_prov_obs_eq;
                     [symmetry; apply interp_cfg_exc_obs_eq, Eqit.bind_ret_l
                     | symmetry; apply interp_cfg_exc_obs_eq, Eqit.bind_ret_l |].
                   rewrite Hsplit_init; unfold init_code'.
                   eapply refine_cfg_exc_bind with
                     (RA := fun U_b1 s1_b1 s2_b1 bd1 bd2 =>
                              exists (P_b1 : list N) gs_b1 σ1_b1 σ2_b1
                                     (sf1_b1 sf2_b1 : @stack_frame (@ParamsV IP IPT)),
                                incl (pr_va :: U0) U_b1 /\
                                bd1 = bd2 /\
                                s1_b1 = (σ1_b1, ((sf1_b1, fstk), g0)) /\
                                s2_b1 = (σ2_b1, ((sf2_b1, fstk), g0)) /\
                                gs_dt gs_b1 = dt /\
                                Maps.lookup p (stack_vars sf1_b1) =
                                  Some (@DVALUE_Base (@ParamsV IP IPT) (@DVALUE_Pointer (@ParamsV IP IPT) (gs_pt gs_b1))) /\
                                Maps.lookup init_end_reg (stack_vars sf2_b1) =
                                  Some (@DVALUE_Base (@ParamsV IP IPT) (gs_db gs_b1)) /\
                                stage1_mem_inv U_b1 P_b1 (gs_b1 :: []) σ1_b1 σ2_b1 /\
                                top_frame_prom_from fs0 gs_b1 [] (state_memory_stack σ2_b1) /\
                                genv_safe P_b1 g0 /\
                                safe_locals_env P_b1 safe_no_p (stack_vars sf2_b1) /\
                                (forall x, In x avoid0 -> x <> p ->
                                   Maps.lookup x (stack_vars sf1_b1) = Maps.lookup x (stack_vars sf2_b1)) /\
                                match bd1 with
                                | inl bid_target => In bid_target (m2r_block_succs b_init)
                                | inr _ => True
                                end).
                   --- eapply refine_prov_obs_eq;
                         [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                                             (eq_itree_bind_congr_l (denote_code_app_eq pre_al _ (Some varg1))))
                         | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _
                                              (eq_itree_bind_congr_l (denote_code_app_eq pre_al _ (Some varg1)))) |].
                       eapply refine_prov_obs_eq;
                         [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_bind _ _ _))
                         | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
                       eapply refine_cfg_exc_bind.
                       +++ assert (Hsplit_pre :
                                     blk_code b_init = [] ++ pre_al ++ (IId p, INSTR_Alloca dt anns_al, md_al) :: post_al)
                             by exact Hsplit_init.
                           exact (stage1_no_call_code_exc_sim ctx1 ctx2 RExc_s1
                                    (fun s => top_frame_unprom_from fs0 [] (state_memory_stack s))
                                    fargs (blks c) b_init [] pre_al
                                    ((IId p, INSTR_Alloca dt anns_al, md_al) :: post_al)
                                    safe_no_p p (Some varg1) (Some varg1)
                                    (pr_va :: U0) (pr_va :: P0) [] σ1_pf σ2_pf sf0 sf0 fstk fstk g0
                                    Hnd_bks Hin_init Hsplit_pre Hsub_safe Hpre_chk
                                    (fun s_a s_b Heq_fs HT => top_frame_unprom_frame_eq fs0 [] _ _ (eq_sym Heq_fs) HT)
                                    (fun s_a s_b ptrs Hdisj Heq_fs HT =>
                                       top_frame_unprom_frame_eq fs0 [] _ _ (eq_sym Heq_fs)
                                         (top_frame_unprom_add_ptrs fs0 [] ptrs _ HT Hdisj))
                                    Hinv_pf Htf_pf Hgenv_pf Hsafe_sf0 (fun _ _ => Logic.eq_refl)).
                       +++ intros U_pre s1_pre _ s2_pre _ _
                             (P_pre & σ1_pre & σ2_pre & sf1_pre & sf2_pre &
                              HincU_pre & HincP_pre & _ & _ & -> & -> &
                              Hinv_pre & Htf_pre & Hgenv_pre & Hsafe_pre & _ & _ & Heq_sf_pre).
                           pose proof (Heq_sf_pre Logic.eq_refl) as ->.
                           assert (Econs_l :
                                     @denote_code (@ParamsV IP IPT)
                                       ((IId p, INSTR_Alloca dt anns_al, md_al) :: post_al) (Some varg1) ≅
                                     ITree.bind (denote_instr (IId p, INSTR_Alloca dt anns_al, md_al) (Some varg1))
                                       (fun _ => denote_code post_al (Some varg1)))
                             by reflexivity.
                           assert (Econs_r :
                                     @denote_code (@ParamsV IP IPT)
                                       ((IId p, INSTR_Alloca dt anns_al, md_al) :: init_op :: post_al') (Some varg1) ≅
                                     ITree.bind
                                       (ITree.bind (denote_instr (IId p, INSTR_Alloca dt anns_al, md_al) (Some varg1))
                                          (fun _ => denote_instr init_op (Some varg1)))
                                       (fun _ => denote_code post_al' (Some varg1))).
                           { unfold denote_code; cbn [loop_monad]; symmetry; apply Eqit.bind_bind. }
                           eapply refine_prov_obs_eq;
                             [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (eq_itree_bind_congr_l Econs_l))
                             | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (eq_itree_bind_congr_l Econs_r)) |].
                           eapply refine_prov_obs_eq;
                             [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_bind _ _ _))
                             | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
                           eapply refine_cfg_exc_bind.
                           *** exact (stage1_prom_alloca_init_exc_sim ctx1 ctx2 RExc_s1
                                        p init_reg dt anns_al md_al (Some varg1) (Some varg1)
                                        fs0 U_pre P_pre [] σ1_pre σ2_pre sf2_pre sf2_pre fstk fstk g0
                                        Hsc Hanns_al Hinv_pre Htf_pre).
                           *** intros U_al s1_al _ s2_al _ _
                                 (gs0 & σ1_al & σ2_al & _ & -> & _ & _ & Hdt0 & Hdb0 &
                                  -> & -> & Hinv_al & Htf_al).
                               assert (HincU_al : incl (pr_va :: U0) (gs_pr gs0 :: U_pre))
                                 by (intros x Hx; right; exact (HincU_pre x Hx)).
                               assert (Hlk_p_al :
                                         Maps.lookup p (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre)) =
                                         Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))))
                                 by (cbn [Maps.lookup Maps.add Map_rmap]; apply RMF.F.add_eq_o; reflexivity).
                               assert (Hlk_init_al :
                                         Maps.lookup init_reg
                                           (Maps.add init_reg (DVALUE_Base DVALUE_Poison)
                                              (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre))) =
                                         Some (DVALUE_Base (gs_db gs0))).
                               { rewrite Hdb0; cbn [Maps.lookup Maps.add Map_rmap]; apply RMF.F.add_eq_o; reflexivity. }
                               assert (Hsafe_al :
                                         safe_locals_env P_pre safe_no_p
                                           (Maps.add init_reg (DVALUE_Base DVALUE_Poison)
                                              (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre)))).
                               { apply safe_locals_env_add_other;
                                   [intros Hs; exact (Hinit_nin0 (Hsafe_av0 _ Hs)) |].
                                 apply safe_locals_env_add_other; [exact Hp_nin_safe | exact Hsafe_pre]. }
                               assert (Hvars_al :
                                         forall x, In x avoid0 -> x <> p ->
                                           Maps.lookup x (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre)) =
                                           Maps.lookup x (Maps.add init_reg (DVALUE_Base DVALUE_Poison)
                                                            (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre)))).
                               { intros x Hx _; cbn [Maps.lookup Maps.add Map_rmap]; symmetry;
                                 rewrite RMF.F.add_neq_o by (intros ->; exact (Hinit_nin0 Hx)); reflexivity. }
                               assert (Hsplit_post :
                                         blk_code b_init = (pre_al ++ [(IId p, INSTR_Alloca dt anns_al, md_al)]) ++ post_al ++ [])
                                 by (rewrite <- app_assoc, app_nil_r; exact Hsplit_init).
                               assert (Huses_post : forall im0 x, In im0 post_al -> In x (m2r_code_entry_uses im0) -> In x avoid0).
                               { intros im0 x Him0 Hx; apply (Hblk_uses_av0 b_init x Hin_init).
                                 eapply m2r_code_entry_uses_in_block; [| exact Hx].
                                 rewrite Hsplit_init; apply in_app_iff; right; right; exact Him0. }
                               assert (Hdefs_post : forall im0 x, In im0 post_al -> In x (instr_id_defs (fst (fst im0))) -> In x avoid0).
                               { intros im0 x Him0 Hx; apply (Hblk_defs_av0 b_init x Hin_init).
                                 unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
                                 rewrite Hsplit_init; apply in_flat_map; exists im0; split;
                                   [apply in_app_iff; right; right; exact Him0
                                   | destruct im0 as [[? ?] ?]; exact Hx]. }
                               eapply refine_cfg_exc_bind.
                               ---- exact (rewrite_code_for_slot_no_call_exc_sim ctx1 ctx2 RExc_s1
                                             avoid0 fargs (blks c) b_init
                                             (pre_al ++ [(IId p, INSTR_Alloca dt anns_al, md_al)]) post_al []
                                             safe_no_p p dt init_reg avoid2 post_al' init_end_reg avoid3
                                             (Some varg1) (Some varg1) fs0 (gs_pr gs0 :: U_pre) P_pre gs0 []
                                             σ1_al σ2_al
                                             (upd_local_sf sf2_pre
                                                (Maps.add p (@DVALUE_Base (@ParamsV IP IPT) (@DVALUE_Pointer (@ParamsV IP IPT) (gs_pt gs0))) (stack_vars sf2_pre)))
                                             (upd_local_sf sf2_pre
                                                (Maps.add init_reg (@DVALUE_Base (@ParamsV IP IPT) DVALUE_Poison)
                                                   (Maps.add p (@DVALUE_Base (@ParamsV IP IPT) (@DVALUE_Pointer (@ParamsV IP IPT) (gs_pt gs0))) (stack_vars sf2_pre))))
                                             fstk fstk g0
                                             Hnd_bks Hin_init Hsplit_post Hsub_safe Hsafe_av0
                                             Huses_post Hdefs_post Hp_nd_post Hpost_chk Erw_post
                                             Hinc_av2 Hinit_nin0 Hsc Hdt0 Hlk_p_al Hlk_init_al
                                             Hinv_al Htf_al Hgenv_pre Hsafe_al Hvars_al).
                               ---- intros U_post s1_post _ s2_post _ _
                                      (P_post & gs_post & σ1_post & σ2_post & sf1_post & sf2_post &
                                       HincU_post & _ & _ & _ & Hdt_post & Hlk_p_post & Hlk_er_post &
                                       -> & -> & Hinv_post & Htf_post & Hgenv_post & Hsafe_post & Hvars_post).
                                    assert (HincU_p : incl (pr_va :: U0) U_post)
                                      by (eapply incl_tran; [exact HincU_al | exact HincU_post]).
                                    destruct (blk_term b_init) as [[iid_tm tm_init] md_tm] eqn:Etm_init.
                                    cbn [fst snd] in Hni_init.
                                    assert (Htm_vars : forall x,
                                              In x (full_term_uses tm_init) ->
                                              Maps.lookup x (stack_vars sf1_post) = Maps.lookup x (stack_vars sf2_post)).
                                    { intros x Hx; apply Hvars_post.
                                      - apply (Hblk_uses_av0 b_init x Hin_init), m2r_term_entry_uses_in_block.
                                        rewrite Etm_init; cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx.
                                      - intros ->; apply Hterm_p; try rewrite Etm_init;
                                          cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx. }
                                    eapply refine_prov_weaken.
                                    ++++ apply (denote_non_invoke_term_exc_sim ctx1 ctx2 RExc_s1
                                                  iid_tm iid_tm tm_init md_tm md_tm
                                                  U_post σ1_post σ2_post sf1_post sf2_post fstk fstk g0
                                                  Hni_init Htm_vars).
                                         intros ex; refine (conj Logic.eq_refl (conj HincU_p _)).
                                         exists P_post, σ1_post, σ2_post, sf1_post, sf2_post;
                                           split; [reflexivity | split; [reflexivity | right; exists gs_post; split; assumption]].
                                    ++++ intros U_t [s1_t res1_t] [s2_t res2_t].
                                         destruct res1_t as [ex1 | bd1], res2_t as [ex2 | bd2]; cbn [exc_post];
                                           try (intros H; exact H).
                                         intros (-> & -> & -> & <- & Hsucc).
                                         destruct bd1 as [bid_t | dv_t];
                                           [cbn in Hsucc |- *; unfold m2r_block_succs; rewrite Etm_init |];
                                         exists P_post, gs_post, σ1_post, σ2_post, sf1_post, sf2_post;
                                         exact (conj HincU_p (conj Logic.eq_refl (conj Logic.eq_refl
                                                  (conj Logic.eq_refl (conj Hdt_post (conj Hlk_p_post
                                                    (conj Hlk_er_post (conj Hinv_post (conj Htf_post
                                                      (conj Hgenv_post (conj Hsafe_post (conj Hvars_post Hsucc)))))))))))).
                   --- intros U_b1 s1_b1 bd1 s2_b1 bd2 _
                         (P_b1 & gs_b1 & σ1_b1 & σ2_b1 & sf1_b1 & sf2_b1 &
                          HincU_b1 & <- & -> & -> & Hdt_b1 & Hlk_p_b1 & Hlk_er_b1 &
                          Hinv_b1 & Htf_b1 & Hgenv_b1 & Hsafe_b1 & Hvars_b1 & Hsucc_b1).
                       destruct bd1 as [bid_next | dv_ret].
                       +++ assert (Hsucc_init : In bid_next (m2r_block_succs b_init))
                             by exact Hsucc_b1.
                           assert (Hne_init : bid_next <> init c).
                           { intros Heq_n; apply Hno_entry_pred; rewrite <- Heq_n.
                             unfold m2r_all_succs; apply in_flat_map; exists b_init; split; assumption. }
                           apply refine_cfg_exc_ret.
                           exists P_b1, gs_b1, σ1_b1, σ2_b1, sf1_b1, sf2_b1.
                           exact (conj HincU_b1 (conj Logic.eq_refl (conj Logic.eq_refl
                                    (conj Logic.eq_refl (conj Hdt_b1 (conj Hlk_p_b1
                                      (conj Hlk_er_b1 (conj Hinv_b1 (conj Htf_b1
                                        (conj Hgenv_b1 (conj Hsafe_b1 (conj Hvars_b1
                                          (conj Logic.eq_refl (conj Hsucc_init Hne_init)))))))))))))).
                       +++ apply refine_cfg_exc_ret.
                           exists P_b1, gs_b1, σ1_b1, σ2_b1, sf1_b1, sf2_b1.
                           exact (conj HincU_b1 (conj Logic.eq_refl (conj Logic.eq_refl
                                    (conj Logic.eq_refl (conj Hdt_b1 (conj Hlk_p_b1
                                      (conj Hlk_er_b1 (conj Hinv_b1 (conj Htf_b1
                                        (conj Hgenv_b1 (conj Hsafe_b1 (conj Hvars_b1 I)))))))))))).
                ** intros U_step [s1_step res1_s] [s2_step res2_s] _.
                   destruct res1_s as [ex1 | [j1 | r1]], res2_s as [ex2 | [j2 | r2]]; cbn [exc_post];
                     try contradiction;
                     try (let H := fresh in intros H;
                          repeat match goal with
                                 | H0 : _ /\ _ |- _ => destruct H0
                                 | H0 : exists _, _ |- _ => destruct H0
                                 end;
                          discriminate).
                   --- intros Hex; apply refine_prov_ret; exact Hex.
                   --- intros (P_s & gs_s & σ1_s & σ2_s & sf1_s & sf2_s &
                               HincU_s & Hjeq & -> & -> & Hdt_s & Hlk_p_s & Hlk_er_s &
                               Hinv_s & Htf_s & Hgenv_s & Hsafe_s & Hvars_s &
                               Hjid_s & Hsucc_s & Hne_s).
                       inversion Hjeq; subst j2; clear Hjeq.
                       apply refine_prov_tau_both.
                       set (RI_loop :=
                              fun U_l (s1_l s2_l : FusedS) (i1 i2 : block_id * block_id) =>
                                i1 = i2 /\
                                snd i2 <> init c /\
                                incl (pr_va :: U0) U_l /\
                                (exists b_pred,
                                   In b_pred (blks c) /\
                                   blk_id b_pred = fst i2 /\
                                   In (snd i2) (m2r_block_succs b_pred)) /\
                                exists (P_l : list N) gs_l σ1_l σ2_l
                                       (sf1_l sf2_l : @stack_frame (@ParamsV IP IPT)),
                                  gs_dt gs_l = dt /\
                                  Maps.lookup p (stack_vars sf1_l) =
                                    Some (@DVALUE_Base (@ParamsV IP IPT) (@DVALUE_Pointer (@ParamsV IP IPT) (gs_pt gs_l))) /\
                                  Maps.lookup (lookup_end_reg end_map (fst i2) init_reg) (stack_vars sf2_l) =
                                    Some (@DVALUE_Base (@ParamsV IP IPT) (gs_db gs_l)) /\
                                  s1_l = (σ1_l, ((sf1_l, fstk), g0)) /\
                                  s2_l = (σ2_l, ((sf2_l, fstk), g0)) /\
                                  stage1_mem_inv U_l P_l (gs_l :: []) σ1_l σ2_l /\
                                  top_frame_prom_from fs0 gs_l [] (state_memory_stack σ2_l) /\
                                  genv_safe P_l g0 /\
                                  safe_locals_env P_l safe_no_p (stack_vars sf2_l) /\
                                  (forall x, In x avoid0 -> x <> p ->
                                     Maps.lookup x (stack_vars sf1_l) = Maps.lookup x (stack_vars sf2_l))).
                       eapply (refine_cfg_exc_iter ctx1 ctx2 RI_loop RExc_s1 _ _ _ U_step).
                       +++ intros U_l s1_l s2_l [bf1 bs1] [bf2 bs2] _
                             (Heq_ij & Hne_bs & HincU_l & (b_pred & Hin_pred & Hid_pred & Hsucc_pred) &
                              P_l & gs_l & σ1_l & σ2_l & sf1_l & sf2_l &
                              Hdt_l & Hlk_p_l & Hlk_end_l & -> & -> &
                              Hinv_l & Htf_l & Hgenv_l & Hsafe_l & Hvars_l).
                           inversion Heq_ij; subst bf1 bs1; clear Heq_ij; cbn [fst snd] in *.
                           cbn beta iota.
                           rewrite !ScopeTheory.ocfg_map_find_block.
                           destruct (find_block (blks c) bs2) as [bk_cur |] eqn:Efind_cur.
                           *** destruct (m2r_find_block_some_inv (blks c) bs2 bk_cur Efind_cur)
                                 as [Hin_cur Hid_cur].
                               destruct (Hfb_some bs2 bk_cur Efind_cur)
                                 as (phi_r & cd_cur' & end_r & Hin_p1_cur & Efind_cur').
                               rewrite Efind_cur'.
                               pose proof (Hall_p1 bk_cur phi_r cd_cur' end_r Hin_p1_cur)
                                 as (Hphi_nin0 & Hend_nin0 & Hcur_p1_spec).
                               destruct (raw_id_eqb (blk_id bk_cur) (init c)) eqn:Ecur_id; [apply raw_id_eqb_spec in Ecur_id; rename Ecur_id into Hbad | apply raw_id_eqb_neq in Ecur_id; rename Ecur_id into Hne_cur_id];
                                 [exfalso; congruence |].
                               destruct Hcur_p1_spec as (av_in & av_out & Hinc_avin & Erw_cur).
                               pose proof Ebks_chk as Hbk_cur_chk.
                               rewrite forallb_forall in Hbk_cur_chk.
                               specialize (Hbk_cur_chk bk_cur Hin_cur).
                               destruct (raw_id_eqb (blk_id bk_cur) (init c)) eqn:Ebad; [apply raw_id_eqb_spec in Ebad; rename Ebad into Hbad | clear Ebad];
                                 [exfalso; congruence |].
                               unfold check_block_non_entry_for_slot in Hbk_cur_chk.
                               rewrite !andb_true_iff, !negb_true_iff in Hbk_cur_chk.
                               destruct Hbk_cur_chk as (((Hphi_np & Hcd_cur) & Htm_np) & Hni_cur).
                               apply in_raw_ids_false in Hphi_np; apply in_raw_ids_false in Htm_np.
                               pose proof (Hp_nd_other bk_cur Hin_cur (fun Heq => Hne_cur_id (eq_trans Heq Hid_init)))
                                 as Hp_nd_bk_cur.
                               set (preds_cur := List.filter (fun b_p => in_raw_ids (blk_id bk_cur) (m2r_block_succs b_p)) (blks c)).
                               set (inc_cur := List.map (fun b_p => (blk_id b_p, EXP_Ident (ID_Local (lookup_end_reg end_map (blk_id b_p) init_reg)))) preds_cur).
                               assert (Hassoc_cur :
                                         assoc bf2 inc_cur =
                                         Some (EXP_Ident (ID_Local (lookup_end_reg end_map bf2 init_reg)))).
                               { apply m2r_assoc_nodup.
                                 - unfold inc_cur; rewrite map_map; cbn [fst].
                                   exact (m2r_nodup_map_filter blk_id _ (blks c) Hnd_bks).
                                 - unfold inc_cur; rewrite <- Hid_pred at 1 2.
                                   apply (in_map (fun b_p => (blk_id b_p, EXP_Ident (ID_Local (lookup_end_reg end_map (blk_id b_p) init_reg))))).
                                   unfold preds_cur; apply filter_In; split; [exact Hin_pred |].
                                   rewrite Hid_cur; apply in_raw_ids_spec, Hsucc_pred. }
                               assert (Hphi_vars :
                                         forall x, In x (flat_map m2r_phi_entry_uses (blk_phis bk_cur)) ->
                                           Maps.lookup x (stack_vars sf1_l) = Maps.lookup x (stack_vars sf2_l)).
                               { intros x Hx; apply Hvars_l;
                                   [apply (Hblk_uses_av0 bk_cur x Hin_cur);
                                    apply in_flat_map in Hx as (pe & Hpe & Hx_pe);
                                    exact (m2r_phi_entry_uses_in_block bk_cur pe x Hpe Hx_pe)
                                   | intros ->; exact (Hphi_np Hx)]. }
                               unfold denote_block; cbn [blk_phis blk_code blk_term]; fold preds_cur inc_cur.
                               eapply refine_cfg_exc_bind with
                                 (RA := fun U_bd s1_bd s2_bd bd1 bd2 =>
                                          exists (P_cd : list N) gs_cd σ1_cd σ2_cd
                                                 (sf1_cd sf2_cd : @stack_frame (@ParamsV IP IPT)),
                                            incl (pr_va :: U0) U_bd /\
                                            bd1 = bd2 /\
                                            s1_bd = (σ1_cd, ((sf1_cd, fstk), g0)) /\
                                            s2_bd = (σ2_cd, ((sf2_cd, fstk), g0)) /\
                                            gs_dt gs_cd = dt /\
                                            Maps.lookup p (stack_vars sf1_cd) =
                                              Some (@DVALUE_Base (@ParamsV IP IPT) (@DVALUE_Pointer (@ParamsV IP IPT) (gs_pt gs_cd))) /\
                                            lookup_end_reg end_map bs2 init_reg = end_r /\
                                            Maps.lookup end_r (stack_vars sf2_cd) =
                                              Some (@DVALUE_Base (@ParamsV IP IPT) (gs_db gs_cd)) /\
                                            stage1_mem_inv U_bd P_cd (gs_cd :: []) σ1_cd σ2_cd /\
                                            top_frame_prom_from fs0 gs_cd [] (state_memory_stack σ2_cd) /\
                                            genv_safe P_cd g0 /\
                                            safe_locals_env P_cd safe_no_p (stack_vars sf2_cd) /\
                                            (forall x, In x avoid0 -> x <> p ->
                                               Maps.lookup x (stack_vars sf1_cd) = Maps.lookup x (stack_vars sf2_cd)) /\
                                            match bd1 with
                                            | inl bid_target => In bid_target (m2r_block_succs bk_cur)
                                            | inr _ => True
                                            end).
                               ---- eapply refine_cfg_exc_bind.
                                    ++++ exact (denote_phis_stage1_prom_sim ctx1 ctx2 RExc_s1
                                                  bf2 phi_r (lookup_end_reg end_map bf2 init_reg)
                                                  dt inc_cur (blk_phis bk_cur) (DVALUE_Base (gs_db gs_l))
                                                  U_l σ1_l σ2_l sf1_l sf2_l fstk fstk g0
                                                  Hassoc_cur Hlk_end_l Hphi_vars).
                                    ++++ intros U_ph s1_ph _ s2_ph _ _
                                           (dvs & -> & _ & _ & Hfst_dvs & -> & ->).
                                         assert (Hp_nin_dvs : ~ In p (List.map fst dvs)).
                                         { rewrite Hfst_dvs; intros Hp_in; apply Hp_nd_bk_cur.
                                           unfold full_block_defs; apply in_app_iff; left; exact Hp_in. }
                                         assert (Hphi_nin_dvs : ~ In phi_r (List.map fst dvs)).
                                         { rewrite Hfst_dvs; intros Hpr_in; apply Hphi_nin0.
                                           apply (Hblk_defs_av0 bk_cur phi_r Hin_cur).
                                           unfold full_block_defs; apply in_app_iff; left; exact Hpr_in. }
                                         assert (Hlk_p_ph :
                                                   Maps.lookup p (write_phi_dvs dvs (stack_vars sf1_l)) =
                                                   Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs_l)))).
                                         { rewrite (write_phi_dvs_lookup_not_in dvs _ p Hp_nin_dvs); exact Hlk_p_l. }
                                         assert (Hlk_phi_ph :
                                                   Maps.lookup phi_r
                                                     (write_phi_dvs ((phi_r, DVALUE_Base (gs_db gs_l)) :: dvs) (stack_vars sf2_l)) =
                                                   Some (DVALUE_Base (gs_db gs_l))).
                                         { cbn [write_phi_dvs];
                                             rewrite (write_phi_dvs_lookup_not_in dvs _ phi_r Hphi_nin_dvs);
                                             cbn [Maps.lookup Maps.add Map_rmap]; apply RMF.F.add_eq_o; reflexivity. }
                                         assert (Hsafe_ph :
                                                   safe_locals_env P_l safe_no_p
                                                     (write_phi_dvs ((phi_r, DVALUE_Base (gs_db gs_l)) :: dvs) (stack_vars sf2_l))).
                                         { apply write_phi_dvs_safe_locals; [| exact Hsafe_l].
                                           intros q Hq [Heq_q | Hin_dvs].
                                           - subst q; exact (Hphi_nin0 (Hsafe_av0 _ Hq)).
                                           - rewrite Hfst_dvs in Hin_dvs.
                                             apply in_map_iff in Hin_dvs as ([[x_ph ph_q] md_q] & <- & Hpe_in).
                                             exact (unique_alloca_not_phi_def fargs (blks c) x_ph Hnd_bks
                                                      (Hsub_safe x_ph Hq) bk_cur x_ph ph_q md_q Hin_cur Hpe_in Logic.eq_refl). }
                                         assert (Hvars_ph :
                                                   forall x, In x avoid0 -> x <> p ->
                                                     Maps.lookup x (write_phi_dvs dvs (stack_vars sf1_l)) =
                                                     Maps.lookup x (write_phi_dvs ((phi_r, DVALUE_Base (gs_db gs_l)) :: dvs) (stack_vars sf2_l))).
                                         { intros x Hx Hne; cbn [write_phi_dvs]; apply write_phi_dvs_lookup_agree.
                                           cbn [Maps.lookup Maps.add Map_rmap];
                                           rewrite RMF.F.add_neq_o by (intros ->; exact (Hphi_nin0 Hx)).
                                           exact (Hvars_l x Hx Hne). }
                                         assert (Hsplit_cur : blk_code bk_cur = [] ++ blk_code bk_cur ++ [])
                                           by (rewrite app_nil_r; reflexivity).
                                         assert (Huses_cur : forall im0 x, In im0 (blk_code bk_cur) -> In x (m2r_code_entry_uses im0) -> In x avoid0)
                                           by (intros im0 x Him0 Hx; apply (Hblk_uses_av0 bk_cur x Hin_cur);
                                               eapply m2r_code_entry_uses_in_block; eassumption).
                                         assert (Hdefs_cur : forall im0 x, In im0 (blk_code bk_cur) -> In x (instr_id_defs (fst (fst im0))) -> In x avoid0).
                                         { intros im0 x Him0 Hx; apply (Hblk_defs_av0 bk_cur x Hin_cur).
                                           unfold full_block_defs; apply in_app_iff; right; apply in_app_iff; left.
                                           apply in_flat_map; exists im0; split; [exact Him0 | destruct im0 as [[? ?] ?]; exact Hx]. }
                                         assert (Hp_nd_cd_cur : ~ In p (flat_map (fun '(iid, _, _) => instr_id_defs iid) (blk_code bk_cur))).
                                         { intros Hp_in; apply Hp_nd_bk_cur; unfold full_block_defs;
                                             apply in_app_iff; right; apply in_app_iff; left; exact Hp_in. }
                                         eapply refine_cfg_exc_bind.
                                         **** exact (rewrite_code_for_slot_no_call_exc_sim ctx1 ctx2 RExc_s1
                                                       avoid0 fargs (blks c) bk_cur [] (blk_code bk_cur) []
                                                       safe_no_p p dt phi_r av_in cd_cur' end_r av_out
                                                       (Some varg1) (Some varg1) fs0 U_l P_l gs_l []
                                                       σ1_l σ2_l
                                                       (upd_local_sf sf1_l (write_phi_dvs dvs (stack_vars sf1_l)))
                                                       (upd_local_sf sf2_l
                                                          (write_phi_dvs ((phi_r, @DVALUE_Base (@ParamsV IP IPT) (gs_db gs_l)) :: dvs) (stack_vars sf2_l)))
                                                       fstk fstk g0
                                                       Hnd_bks Hin_cur Hsplit_cur Hsub_safe Hsafe_av0
                                                       Huses_cur Hdefs_cur Hp_nd_cd_cur Hcd_cur Erw_cur
                                                       Hinc_avin Hphi_nin0 Hsc Hdt_l Hlk_p_ph Hlk_phi_ph
                                                       Hinv_l Htf_l Hgenv_l Hsafe_ph Hvars_ph).
                                         **** intros U_cd s1_cd _ s2_cd _ _
                                                (P_cd & gs_cd & σ1_cd & σ2_cd & sf1_cd & sf2_cd &
                                                 HincU_cd & _ & _ & _ & Hdt_cd & Hlk_p_cd & Hlk_er_cd &
                                                 -> & -> & Hinv_cd & Htf_cd & Hgenv_cd & Hsafe_cd & Hvars_cd).
                                              assert (HincU_c : incl (pr_va :: U0) U_cd)
                                                by (eapply incl_tran; [exact HincU_l | exact HincU_cd]).
                                              assert (Hlk_end_cur : lookup_end_reg end_map bs2 init_reg = end_r).
                                              { apply lookup_end_reg_in_nodup; [exact Hnd_end_map |].
                                                unfold end_map; rewrite <- Hid_cur.
                                                exact (in_map (fun '(bk, _, _, er) => (blk_id bk, er)) _ _ Hin_p1_cur). }
                                              destruct (blk_term bk_cur) as [[iid_tc tm_cur] md_tc] eqn:Etm_cur.
                                              cbn [fst snd] in Hni_cur.
                                              assert (Htm_vars :
                                                        forall x, In x (full_term_uses tm_cur) ->
                                                          Maps.lookup x (stack_vars sf1_cd) = Maps.lookup x (stack_vars sf2_cd)).
                                              { intros x Hx; apply Hvars_cd.
                                                - apply (Hblk_uses_av0 bk_cur x Hin_cur), m2r_term_entry_uses_in_block.
                                                  rewrite Etm_cur; cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx.
                                                - intros ->; apply Htm_np; try rewrite Etm_cur;
                                                    cbn [m2r_term_entry_uses]; apply in_app_iff; left; exact Hx. }
                                              eapply refine_prov_weaken.
                                              ----- apply (denote_non_invoke_term_exc_sim ctx1 ctx2 RExc_s1
                                                             iid_tc iid_tc tm_cur md_tc md_tc
                                                             U_cd σ1_cd σ2_cd sf1_cd sf2_cd fstk fstk g0
                                                             Hni_cur Htm_vars).
                                                    intros ex; refine (conj Logic.eq_refl (conj HincU_c _)).
                                                    exists P_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd;
                                                      split; [reflexivity | split; [reflexivity | right; exists gs_cd; split; assumption]].
                                              ----- intros U_t [s1_t res1_t] [s2_t res2_t].
                                                    destruct res1_t as [ex1 | bd1], res2_t as [ex2 | bd2]; cbn [exc_post];
                                                      try (intros H; exact H).
                                                    intros (-> & -> & -> & <- & Hsucc_cur).
                                                    destruct bd1 as [bid_t | dv_t];
                                                      [cbn in Hsucc_cur |- *; unfold m2r_block_succs; rewrite Etm_cur |];
                                                    exists P_cd, gs_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd;
                                                    exact (conj HincU_c (conj Logic.eq_refl (conj Logic.eq_refl
                                                             (conj Logic.eq_refl (conj Hdt_cd (conj Hlk_p_cd
                                                               (conj Hlk_end_cur (conj Hlk_er_cd (conj Hinv_cd
                                                                 (conj Htf_cd (conj Hgenv_cd (conj Hsafe_cd
                                                                   (conj Hvars_cd Hsucc_cur))))))))))))).
                               ---- intros U_bd s1_bd bd1 s2_bd bd2 _
                                      (P_cd & gs_cd & σ1_cd & σ2_cd & sf1_cd & sf2_cd &
                                       HincU_c & <- & -> & -> & Hdt_cd & Hlk_p_cd & Hlk_end_cur &
                                       Hlk_er_cd & Hinv_cd & Htf_cd & Hgenv_cd & Hsafe_cd & Hvars_cd & Hsucc_cur).
                                    destruct bd1 as [bid_tgt | dv_cur].
                                    ++++ apply refine_cfg_exc_ret.
                                         assert (Hsucc_bk_cur : In bid_tgt (m2r_block_succs bk_cur))
                                           by exact Hsucc_cur.
                                         assert (Hne_tgt : bid_tgt <> init c).
                                         { intros Heq_t; apply Hno_entry_pred; rewrite <- Heq_t.
                                           unfold m2r_all_succs; apply in_flat_map; exists bk_cur; split; assumption. }
                                         refine (conj Logic.eq_refl (conj Hne_tgt (conj HincU_c (conj _ _)))).
                                         { exists bk_cur; exact (conj Hin_cur (conj Hid_cur Hsucc_bk_cur)). }
                                         { exists P_cd, gs_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd; cbn [fst].
                                           rewrite Hlk_end_cur.
                                           exact (conj Hdt_cd (conj Hlk_p_cd (conj Hlk_er_cd
                                                    (conj Logic.eq_refl (conj Logic.eq_refl
                                                      (conj Hinv_cd (conj Htf_cd (conj Hgenv_cd
                                                        (conj Hsafe_cd Hvars_cd))))))))). }
                                    ++++ apply refine_cfg_exc_ret.
                                         refine (conj Logic.eq_refl (conj HincU_c _)).
                                         exists P_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd;
                                           split; [reflexivity | split; [reflexivity | right; exists gs_cd; split; assumption]].
                           *** rewrite (Hfb_none bs2 Efind_cur).
                               apply refine_cfg_exc_ret.
                               refine (conj Logic.eq_refl (conj HincU_l _)).
                               exists P_l, σ1_l, σ2_l, sf1_l, sf2_l;
                                 split; [reflexivity | split; [reflexivity | right; exists gs_l; split; assumption]].
                       +++ refine (conj Logic.eq_refl (conj Hne_s (conj HincU_s (conj _ _)))).
                           { exists b_init;
                               exact (conj Hin_init (conj (eq_trans Hid_init (eq_sym Hjid_s)) Hsucc_s)). }
                           { exists P_s, gs_s, σ1_s, σ2_s, sf1_s, sf2_s.
                             rewrite Hjid_s, Hlk_end_init.
                             exact (conj Hdt_s (conj Hlk_p_s (conj Hlk_er_s
                                      (conj Logic.eq_refl (conj Logic.eq_refl
                                        (conj Hinv_s (conj Htf_s (conj Hgenv_s
                                          (conj Hsafe_s Hvars_s))))))))). }
                   --- intros (P_s & gs_s & σ1_s & σ2_s & sf1_s & sf2_s &
                               HincU_s & Hreq & -> & -> & _ & _ & _ & Hinv_s & Htf_s & _).
                       inversion Hreq; subst r2; clear Hreq.
                       apply refine_prov_ret.
                       refine (conj Logic.eq_refl (conj HincU_s _)).
                       exists P_s, σ1_s, σ2_s, sf1_s, sf2_s;
                         split; [reflexivity | split; [reflexivity | right; exists gs_s; split; assumption]].
             ++ intros U_ocfg s1_ocfg r_ocfg1 s2_ocfg r_ocfg2 _ (<- & Hexit_ocfg).
                destruct r_ocfg1 as [bid_miss | uv_ret].
                ** apply refine_cfg_exc_raise_both.
                ** apply refine_cfg_exc_ret; exact (conj Logic.eq_refl Hexit_ocfg).
          -- intros U_rv s1_rv rv1 s2_rv rv2 _ Hrv_post.
             assert (Hrv_unif : rv1 = rv2 /\ ExitRel U_rv s1_rv s2_rv).
             { destruct rv1 as [ex1 | v1], rv2 as [ex2 | v2]; cbn [exc_post] in Hrv_post;
                 try contradiction;
                 (destruct Hrv_post as [<- Hex]; split; [reflexivity | exact Hex]). }
             clear Hrv_post; destruct Hrv_unif as [<- (HincU_rv & P_e & σ1_e & σ2_e & sf1_e & sf2_e & -> & -> & Hcase_e)].
             assert (Hpop :
                       refine_prov
                         (fun U' '(s1', r1) '(s2', r2) =>
                            exists σ1' σ2',
                              U' = U_rv /\ r1 = tt /\ r2 = tt /\
                              s1' = (σ1', ((sf_caller, fstk_caller), g0)) /\
                              s2' = (σ2', ((sf_caller, fstk_caller), g0)) /\
                              stage1_mem_inv U_rv P_e [] σ1' σ2' /\
                              Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
                         U_rv
                         (interp_cfg_model ctx1 pop_call_frame (σ1_e, ((sf1_e, sf_caller :: fstk_caller), g0)))
                         (interp_cfg_model ctx2 pop_call_frame (σ2_e, ((sf2_e, sf_caller :: fstk_caller), g0)))).
             { destruct Hcase_e as [[Hinv_e Htf_e] | (gs_e & Hinv_e & Htf_e)].
               - exact (pop_call_frame_stage1_unprom_sim ctx1 ctx2 fs0 U_rv P_e []
                          σ1_e σ2_e sf1_e sf_caller sf2_e sf_caller fstk_caller fstk_caller g0 Hinv_e Htf_e).
               - exact (pop_call_frame_stage1_prom_sim ctx1 ctx2 fs0 U_rv P_e gs_e []
                          σ1_e σ2_e sf1_e sf_caller sf2_e sf_caller fstk_caller fstk_caller g0 Hinv_e Htf_e). }
             eapply refine_cfg_model_bind; [exact Hpop |].
             intros U_pop s1_pop _ s2_pop _ _ (σ1_pop & σ2_pop & -> & _ & _ & -> & -> & Hinv_pop & _).
             pose proof (stage1_mem_nil_is_equal U_rv P_e σ1_pop σ2_pop Hinv_pop) as Heq_pop.
             eapply refine_prov_weaken.
             ++ exact (check_call_return_stage1_cfg_sim ctx1 ctx2
                         (dc_attrs (df_prototype df)) ret_attrs None fname args1 rv1
                         U_rv P_e [] σ1_pop σ2_pop
                         ((sf_caller, fstk_caller), g0) ((sf_caller, fstk_caller), g0) Hinv_pop).
             ++ intros U_f [s1_f rf1] [s2_f rf2] (-> & -> & -> & <-).
                exact (conj (fun x Hx => HincU_rv x (or_intror Hx))
                         (conj Heq_pop (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))).
  Qed.


  (** ** 3P. Whole-Module Lifter & Fixed-Guard CPS Combinators *)

  Lemma refine_mcfg_raiseLLVM_both {X1 X2}
    (RR : list N -> Res X1 -> Res X2 -> Prop) (U : list N)
    (ex : @exc (@ParamsV IP IPT)) (s1 s2 : FusedS) :
    refine_prov RR U
      (interp_mcfg_model (raiseLLVM ex) s1)
      (interp_mcfg_model (raiseLLVM ex) s2).
  Proof using.
    unfold raiseLLVM, trigger_cast.
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
    pstep; apply RP_Step; cbn; right; right; split; [reflexivity | intros [] [] _].
  Qed.

  Lemma library_functions_leaf_rel
    (P0 : list N) (g0 : @global_env (@ParamsV IP IPT))
    (decls : list (declaration dtyp)) :
    Forall (fun lib => leaf_ctx_fn_rel P0 g0 (snd lib) (snd lib))
      (@library_functions (@ParamsV IP IPT) decls).
  Proof using.
    apply Forall_forall; intros [fnm fden] Hin.
    unfold library_functions, _LIBRARIES in Hin.
    apply filter_In in Hin as [[Heq | [Heq | []]] _]; inversion Heq; subst fnm fden; cbn [snd].
    - left; split; [reflexivity | exact (@ev_ok_puts_denotation IP IPT)].
    - left; split; [reflexivity | exact (@ev_ok_putchar_denotation IP IPT)].
  Qed.

  Lemma library_functions_no_puts_only_putchar
    (decls : list (declaration dtyp)) :
    negb (in_raw_ids (Name "puts"%string) (List.map dc_name decls)) = true ->
    Forall (fun lib => snd lib = @putchar_denotation (@ParamsV IP IPT))
      (@library_functions (@ParamsV IP IPT) decls).
  Proof using.
    intros Hno; apply negb_true_iff, in_raw_ids_false in Hno.
    apply Forall_forall; intros [fnm fden] Hin.
    unfold library_functions, _LIBRARIES in Hin.
    apply filter_In in Hin as [Hin Hex].
    destruct Hin as [Heq | [Heq | []]]; inversion Heq; subst fnm fden; [| reflexivity].
    exfalso; apply existsb_exists in Hex as (s & Hs & Heq_s).
    destruct (RawIDOrd.eq_dec s (Name "puts"%string)) as [Heq_p | Hne];
      [rewrite Heq_p in Hs; exact (Hno Hs) | discriminate Heq_s].
  Qed.

  Lemma module_defs_refines_gen
    (Rfn : list N -> @global_env (@ParamsV IP IPT) ->
           @function_denotation (@ParamsV IP IPT) ->
           @function_denotation (@ParamsV IP IPT) -> Prop)
    (M1 M2 : CFG.mcfg dtyp)
    (Hbg : @build_global_environment (@ParamsV IP IPT) M2 =
           @build_global_environment (@ParamsV IP IPT) M1)
    (Hdecls : m_declarations M2 = m_declarations M1)
    (Hdefs : forall P0 g0,
               genv_safe P0 g0 ->
               Forall2
                 (fun d1 d2 =>
                    dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
                    Rfn P0 g0 (denote_function d1) (denote_function d2))
                 (m_definitions M1) (m_definitions M2))
    (Hlibs : forall P0 g0,
               genv_safe P0 g0 ->
               Forall (fun lib => Rfn P0 g0 (snd lib) (snd lib))
                 (@library_functions (@ParamsV IP IPT) (m_declarations M1)))
    (Hmrec : forall P0 g0 ctx1 ctx2 dt fv args U σ1 σ2 ls,
               (forall k, option_rel (Rfn P0 g0) (lookup k ctx1) (lookup k ctx2)) ->
               incl P0 U ->
               genv_safe P0 g0 ->
               mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2) ->
               refine_prov top_ans_post U
                 (interp_cfg_model ctx1 (mrec_ctx ctx1 _ (Call dt CC_Ccc fv args)) (σ1, (ls, g0)))
                 (interp_cfg_model ctx2 (mrec_ctx ctx2 _ (Call dt CC_Ccc fv args)) (σ2, (ls, g0)))) :
    prog_refines M1 M2.
  Proof using.
    intros ret_typ entry args U.
    unfold run_mcfg_model, denote_vellvm, init_fused_state.
    rewrite Hbg, Hdecls.
    set (ls0 := (Build_stack_frame Maps.empty None None, ([] : stack))).
    assert (Heq_init : mem_stack_equal (state_memory_stack initial_state)
                                       (state_memory_stack initial_state))
      by (unfold mem_stack_equal; repeat match goal with |- _ /\ _ => split end; reflexivity).
    eapply refine_mcfg_model_bind.
    - exact (build_global_environment_safe_sim M1 U [] initial_state initial_state
               ls0 Maps.empty (fun _ H => match H with end) (genv_safe_empty []) Heq_init).
    - intros U1 [σ1_g rest1_g] _ [σ2_g rest2_g] _ _
        (P1 & g0 & _ & Hp1u1 & Hs1_g & Hs2_g & Hg0 & Heq_g).
      cbn [fst snd] in Hs1_g, Hs2_g, Heq_g; subst rest1_g rest2_g.
      eapply refine_mcfg_model_bind.
      + exact (map_monad_address_one_function_pair_sim (Rfn P1 g0)
                 (m_definitions M1) (m_definitions M2) U1 σ1_g σ2_g ls0 g0 (Hdefs P1 g0 Hg0)).
      + intros U2 s1_f defns1 s2_f defns2 _ (-> & -> & -> & Hdefns).
        eapply refine_mcfg_model_bind.
        * exact (map_monad_address_one_library_pair_sim (Rfn P1 g0)
                   (library_functions (m_declarations M1)) U1 σ1_g σ2_g ls0 g0 (Hlibs P1 g0 Hg0)).
        * intros U3 s1_l libs1 s2_l libs2 _ (-> & -> & -> & Hlibs_rel).
          eapply refine_mcfg_model_bind; [unfold ls0; apply refine_mcfg_gread_same_g |].
          intros U4 s1_e addr1 s2_e addr2 _ (-> & -> & -> & -> & _).
          eapply refine_mcfg_model_bind with (RA := top_ans_post).
          -- rewrite !denote_mcfg_eq_interp_mrec.
             exact (Hmrec P1 g0
                      (IntMaps.IP.of_list (defns1 ++ libs1))
                      (IntMaps.IP.of_list (defns2 ++ libs2))
                      ret_typ addr2 args U1 σ1_g σ2_g ls0
                      (of_list_lookup_pair (Rfn P1 g0) _ _ (Forall2_app Hdefns Hlibs_rel))
                      Hp1u1 Hg0 Heq_g).
          -- intros U5 s1_end rv1 s2_end rv2 _ Hrv; cbn [top_ans_post] in Hrv; subst rv2.
             destruct rv1 as [ex | v].
             ++ apply refine_mcfg_raiseLLVM_both.
             ++ eapply refine_prov_obs_eq;
                  [symmetry; apply interp_mcfg_model_ret
                  | symmetry; apply interp_mcfg_model_ret |].
                apply refine_prov_ret; reflexivity.
  Qed.

  Lemma leaf_module_defs_refines (M1 M2 : CFG.mcfg dtyp)
    (Hbg : @build_global_environment (@ParamsV IP IPT) M2 =
           @build_global_environment (@ParamsV IP IPT) M1)
    (Hdecls : m_declarations M2 = m_declarations M1)
    (Hdefs : forall P0 g0,
               genv_safe P0 g0 ->
               Forall2
                 (fun d1 d2 =>
                    dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
                    leaf_ctx_fn_rel P0 g0 (denote_function d1) (denote_function d2))
                 (m_definitions M1) (m_definitions M2)) :
    prog_refines M1 M2.
  Proof using.
    eapply (module_defs_refines_gen leaf_ctx_fn_rel M1 M2 Hbg Hdecls Hdefs).
    - intros P0 g0 _; apply library_functions_leaf_rel.
    - intros P0 g0 ctx1 ctx2 dt fv args U σ1 σ2 ls Hctx Hpu _ Heq.
      eapply refine_prov_weaken;
        [exact (mrec_knot_leaf_call_sim P0 g0 ctx1 ctx2 Hctx
                  (Call dt CC_Ccc fv args) U σ1 σ2 ls Hpu Heq) |].
      intros U' [? r1] [? r2] (_ & _ & _ & _ & Hr); exact Hr.
  Qed.

  Definition s1_cps {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U : list N) (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2) : Prop :=
    forall (k1 : A1 -> itree ProvBotE Ans) (k2 : A2 -> itree ProvBotE Ans),
      (forall U' a1 a2, incl U U' -> RA U' a1 a2 -> m2r_paco r U' (k1 a1) (k2 a2)) ->
      m2r_paco r U (ITree.bind u1 k1) (ITree.bind u2 k2).

  Lemma refine_prov_to_s1_cps {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U : list N) (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2) :
    refine_prov RA U u1 u2 ->
    s1_cps r RA U u1 u2.
  Proof using.
    intros Href k1 k2 Hk.
    exact (refine_prov_to_cps r RA U u1 u2 Href r (fun _ _ _ H => H) k1 k2 Hk).
  Qed.

  Lemma s1_cps_obs_eq {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U : list N) (u1 u1' : itree ProvBotE A1) (u2 u2' : itree ProvBotE A2) :
    u1 ≅ u1' ->
    u2 ≅ u2' ->
    s1_cps r RA U u1 u2 ->
    s1_cps r RA U u1' u2'.
  Proof using.
    intros E1 E2 Hcps k1 k2 Hk.
    eapply m2r_paco_obs_eq;
      [eapply eq_itree_clo_bind with (UU := Logic.eq); [exact E1 | intros ? ? <-; reflexivity]
      | eapply eq_itree_clo_bind with (UU := Logic.eq); [exact E2 | intros ? ? <-; reflexivity]
      | exact (Hcps k1 k2 Hk)].
  Qed.

  Lemma s1_cps_ret {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (U : list N) (a1 : A1) (a2 : A2) :
    RA U a1 a2 ->
    s1_cps r RA U (Ret a1) (Ret a2).
  Proof using.
    intros Hra k1 k2 Hk.
    eapply m2r_paco_obs_eq;
      [symmetry; apply Eqit.bind_ret_l
      | symmetry; apply Eqit.bind_ret_l
      | exact (Hk U a1 a2 (incl_refl U) Hra)].
  Qed.

  Lemma s1_cps_bind {A1 A2 B1 B2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA : list N -> A1 -> A2 -> Prop)
    (RB : list N -> B1 -> B2 -> Prop)
    (U : list N)
    (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2)
    (f1 : A1 -> itree ProvBotE B1) (f2 : A2 -> itree ProvBotE B2) :
    s1_cps r RA U u1 u2 ->
    (forall U1 a1 a2, incl U U1 -> RA U1 a1 a2 -> s1_cps r RB U1 (f1 a1) (f2 a2)) ->
    s1_cps r RB U (ITree.bind u1 f1) (ITree.bind u2 f2).
  Proof using.
    intros Hu Hf k1 k2 Hk.
    eapply m2r_paco_obs_eq;
      [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
    apply Hu; intros U1 a1 a2 Hinc1 Ha.
    apply (Hf U1 a1 a2 Hinc1 Ha); intros U2 b1 b2 Hinc2 Hb.
    exact (Hk U2 b1 b2 (incl_tran Hinc1 Hinc2) Hb).
  Qed.

  Lemma s1_cps_weaken {A1 A2 : Type}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (RA RB : list N -> A1 -> A2 -> Prop)
    (U : list N) (u1 : itree ProvBotE A1) (u2 : itree ProvBotE A2) :
    s1_cps r RA U u1 u2 ->
    (forall U' a1 a2, incl U U' -> RA U' a1 a2 -> RB U' a1 a2) ->
    s1_cps r RB U u1 u2.
  Proof using.
    intros Hu Hw k1 k2 Hk.
    apply Hu; intros U' a1 a2 Hinc Ha.
    exact (Hk U' a1 a2 Hinc (Hw U' a1 a2 Hinc Ha)).
  Qed.

  Lemma s1_cps_to_paco
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (U : list N) (t1 t2 : itree ProvBotE Ans) :
    s1_cps r top_ans_post U t1 t2 ->
    m2r_paco r U t1 t2.
  Proof using.
    intros Hcps.
    eapply m2r_paco_obs_eq; [apply Eqit.bind_ret_r | apply Eqit.bind_ret_r |].
    eapply (Hcps (fun x => Ret x) (fun x => Ret x)).
    intros U' [s1 v1] [s2 v2] _ Heq.
    apply m2r_paco_fold, RP_Step; exact Heq.
  Qed.

  Lemma s1_cps_cfg_bind {A1 A2 B1 B2}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RA : list N -> Res A1 -> Res A2 -> Prop)
    (RB : list N -> Res B1 -> Res B2 -> Prop)
    (U : list N)
    (t1 : @CFGtop (@ParamsV IP IPT) A1) (t2 : @CFGtop (@ParamsV IP IPT) A2)
    (k1 : A1 -> @CFGtop (@ParamsV IP IPT) B1) (k2 : A2 -> @CFGtop (@ParamsV IP IPT) B2)
    (s1 s2 : FusedS) :
    s1_cps r RA U (interp_cfg_model ctx1 t1 s1) (interp_cfg_model ctx2 t2 s2) ->
    (forall U' s1' a1 s2' a2,
       incl U U' ->
       RA U' (s1', a1) (s2', a2) ->
       s1_cps r RB U'
         (interp_cfg_model ctx1 (k1 a1) s1')
         (interp_cfg_model ctx2 (k2 a2) s2')) ->
    s1_cps r RB U
      (interp_cfg_model ctx1 (ITree.bind t1 k1) s1)
      (interp_cfg_model ctx2 (ITree.bind t2 k2) s2).
  Proof using.
    intros Ht Hk.
    eapply s1_cps_obs_eq;
      [symmetry; apply interp_cfg_model_bind | symmetry; apply interp_cfg_model_bind |].
    eapply s1_cps_bind; [exact Ht |].
    intros U' [s1' a1] [s2' a2] Hinc Ha; exact (Hk U' s1' a1 s2' a2 Hinc Ha).
  Qed.

  Lemma s1_cps_cfg_exc_bind {A1 A2 B1 B2}
    (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
    (RA   : list N -> FusedS -> FusedS -> A1 -> A2 -> Prop)
    (RB   : list N -> FusedS -> FusedS -> B1 -> B2 -> Prop)
    (U : list N)
    (t1 : @CFGtop (@ParamsV IP IPT) A1) (t2 : @CFGtop (@ParamsV IP IPT) A2)
    (k1 : A1 -> @CFGtop (@ParamsV IP IPT) B1) (k2 : A2 -> @CFGtop (@ParamsV IP IPT) B2)
    (s1 s2 : FusedS) :
    s1_cps r (exc_post RExc RA) U
      (interp_cfg_exc ctx1 t1 s1) (interp_cfg_exc ctx2 t2 s2) ->
    (forall U' s1' a1 s2' a2,
       incl U U' ->
       RA U' s1' s2' a1 a2 ->
       s1_cps r (exc_post RExc RB) U'
         (interp_cfg_exc ctx1 (k1 a1) s1')
         (interp_cfg_exc ctx2 (k2 a2) s2')) ->
    s1_cps r (exc_post RExc RB) U
      (interp_cfg_exc ctx1 (ITree.bind t1 k1) s1)
      (interp_cfg_exc ctx2 (ITree.bind t2 k2) s2).
  Proof using.
    intros Ht Hk.
    eapply s1_cps_obs_eq;
      [symmetry; apply interp_cfg_exc_bind | symmetry; apply interp_cfg_exc_bind |].
    eapply s1_cps_bind; [exact Ht |].
    intros U' [s1' [x1 | a1]] [s2' [x2 | a2]] Hinc Hres; try contradiction.
    - apply s1_cps_ret; exact Hres.
    - exact (Hk U' s1' a1 s2' a2 Hinc Hres).
  Qed.


End MemoryAndSerialization.
