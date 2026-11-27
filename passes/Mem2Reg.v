(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Stack-Slot to SSA Register Promotion ([CertPasses.Mem2Reg])

    Purpose:
      Proves the Stage 1 interprocedural knot ([InterprocKnot], [s1_phi],
      [s1_lfp]) and top-level whole-program refinement theorems
      ([mem2reg_mcfg_refines], [mem2reg_mcfg_typ_refines]), and re-exports
      [Mem2RegSpec]..[Mem2RegStage1].

    Trust Contract & Fail-Closed Boundary:
      Soundness facade for extracted [Mem2RegSpec.mem2reg_mcfg{,_typ}];
      bounded-fuel Stage 1 promotion + Stage 2 dead-alloca elimination
      refines input IR under [prog_refines] and fails closed on unsafe IR.

    Assumptions:
      Parametric over [IP : IPtr] and [IPT : @IPtrTheory IP] (with
      [IPtrWellBehaved IP] for Stage 2 / top-level theorems); depends on
      [PassCommon] and [Mem2RegSpec]..[Mem2RegStage1]; zero custom axioms.

    Section Outline:
      - [MemoryAndSerialization]: 3Q. [InterprocKnot] ([s1_interproc_mrec_sim])
        and module-level spec lemmas.
      - Top-level refinement theorems ([promote_slot_iter_refines],
        [elim_dead_alloca_iter_refines], [mem2reg_mcfg{,_typ}_refines]). *)

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

From CertPasses Require Export Mem2RegSpec Mem2RegModel Mem2RegMemBase Mem2RegGhostInv Mem2RegExprLift Mem2RegCpsSSA Mem2RegLeafKnot Mem2RegStage2 Mem2RegStage1.

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

  (** ** 3Q. Stage 1 Interprocedural Knot ([s1_phi], [s1_lfp], and CPS Code Simulation) *)

  Lemma denote_operand_bundles_nil_eq (loc : string) (f : exp dtyp) :
    @denote_operand_bundles (@ParamsV IP IPT) loc f [] ≅ Ret tt.
  Proof using.
    unfold denote_operand_bundles; cbn [map_monad ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma safe_mem_code_to_check_other
    (safe_locals : list local_id) (p_dummy : local_id) (cd : code dtyp) :
    ~ In p_dummy (flat_map m2r_code_entry_uses cd) ->
    forallb (m2r_safe_mem_instr_any safe_locals) cd = true ->
    forallb (check_other_instr_for_slot true safe_locals p_dummy) cd = true.
  Proof using.
    induction cd as [| im rest IH]; cbn [flat_map forallb]; [intros _ _; reflexivity |].
    intros Hnin Hchk.
    rewrite andb_true_iff in Hchk; destruct Hchk as [Him Hrest].
    assert (Hnin_im : ~ In p_dummy (m2r_code_entry_uses im))
      by (intros H; apply Hnin, in_app_iff; left; exact H).
    assert (Hnin_rest : ~ In p_dummy (flat_map m2r_code_entry_uses rest))
      by (intros H; apply Hnin, in_app_iff; right; exact H).
    rewrite andb_true_iff; split; [| exact (IH Hnin_rest Hrest)].
    unfold check_other_instr_for_slot, m2r_safe_mem_instr_any in *.
    rewrite andb_true_iff, negb_true_iff; split.
    - destruct (in_raw_ids p_dummy (m2r_code_entry_uses im)) eqn:Ein; [| reflexivity].
      apply m2r_in_raw_ids_true in Ein; contradiction (Hnin_im Ein).
    - destruct im as [[iid ins] md]; destruct iid, ins; exact Him.
  Qed.

  Definition s1_fn_entry_rel
    (f1 f2 : @function_denotation (@ParamsV IP IPT)) : Prop :=
    (f1 = @putchar_denotation (@ParamsV IP IPT) /\
     f2 = @putchar_denotation (@ParamsV IP IPT)) \/
    (exists d,
       m2r_defn_mem_safe d = true /\
       f1 = denote_function d /\
       f2 = denote_function d) \/
    (exists df df',
       try_promote_slot_in_defn true df = Some df' /\
       f1 = denote_function df /\
       f2 = denote_function df').

  Record s1_prom_static : Type := {
    sps_fargs    : list local_id;
    sps_c        : CFG.cfg dtyp;
    sps_b_init   : block dtyp;
    sps_p        : local_id;
    sps_dt       : dtyp;
    sps_init_reg : local_id;
    sps_end_reg0 : local_id;
    sps_code0'   : code dtyp;
    sps_pass1    : list (block dtyp * local_id * code dtyp * local_id)
  }.

  Definition sps_avoid0 (sp : s1_prom_static) : list raw_id :=
    sps_fargs sp ++ cfg_all_ids (sps_c sp).

  Definition sps_safe_no_p (sp : s1_prom_static) : list local_id :=
    let all_defs := sps_fargs sp ++ flat_map full_block_defs (blks (sps_c sp)) in
    let safe_locals := m2r_collect_unique_allocas all_defs (blks (sps_c sp)) in
    List.filter (fun q => negb (raw_id_eqb q (sps_p sp))) safe_locals.

  Definition sps_end_map (sp : s1_prom_static) : list (block_id * local_id) :=
    List.map (fun '(bk, _, _, end_r) => (blk_id bk, end_r)) (sps_pass1 sp).

  Definition sps_blks' (sp : s1_prom_static) : ocfg dtyp :=
    build_promoted_blocks (init (sps_c sp)) (sps_dt sp) (sps_init_reg sp)
      (blks (sps_c sp)) (sps_pass1 sp).

  Definition s1_prom_static_wf (sp : s1_prom_static) : Prop :=
    let c := sps_c sp in
    let p := sps_p sp in
    let dt := sps_dt sp in
    NoDup (List.map blk_id (blks c)) /\
    ~ In (init c) (m2r_all_succs c) /\
    In (sps_b_init sp) (blks c) /\
    blk_id (sps_b_init sp) = init c /\
    is_scalar_dtyp dt = true /\
    (forall bk,
       In bk (blks c) ->
       blk_id bk <> init c ->
       check_block_non_entry_for_slot true (sps_safe_no_p sp) p dt bk = true /\
       ~ In p (full_block_defs bk)) /\
    List.map (fun '(bk, _, _, _) => bk) (sps_pass1 sp) = blks c /\
    (forall bk phi_r cd' end_r,
       In (bk, phi_r, cd', end_r) (sps_pass1 sp) ->
       ~ In phi_r (sps_avoid0 sp) /\
       ~ In end_r (sps_avoid0 sp) /\
       (if raw_id_eqb (blk_id bk) (init c) then
          cd' = sps_code0' sp /\ end_r = sps_end_reg0 sp
        else
          exists av_in av_out,
            incl (sps_avoid0 sp) av_in /\
            rewrite_code_for_slot p dt phi_r av_in (blk_code bk) = (cd', end_r, av_out))).

  Section InterprocKnot.
    Context (g0 : @global_env (@ParamsV IP IPT))
            (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
            (Hctx : forall k, option_rel s1_fn_entry_rel (lookup k ctx1) (lookup k ctx2)).

    Local Definition s1_call_post
      (U0 P0 : list N) (G : list ghost_slot)
      (fs0 : @Framestack (@ParamsV IP IPT))
      (ls1 ls2 : @stack_frame (@ParamsV IP IPT) * stack)
      : list N -> Res (@exc (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT)) ->
        Res (@exc (@ParamsV IP IPT) + @dvalue (@ParamsV IP IPT)) -> Prop :=
      fun U' '(s1', rv1) '(s2', rv2) =>
        exists P' σ1' σ2',
          incl U0 U' /\
          incl P0 P' /\
          rv1 = rv2 /\
          s1' = (σ1', (ls1, g0)) /\
          s2' = (σ2', (ls2, g0)) /\
          stage1_mem_inv U' P' G σ1' σ2' /\
          Memory_stack_frame_stack (state_memory_stack σ2') = fs0 /\
          genv_safe P' g0.

    Local Definition s1_unprom_exit_rel
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U_e : list N) (s1_e s2_e : FusedS) : Prop :=
      incl U0 U_e /\
      exists P_e σ1_e σ2_e sf1_e sf2_e,
        incl P0 P_e /\
        s1_e = (σ1_e, ((sf1_e, fstk1), g0)) /\
        s2_e = (σ2_e, ((sf2_e, fstk2), g0)) /\
        stage1_mem_inv U_e P_e G σ1_e σ2_e /\
        top_frame_unprom_from fs0 G (state_memory_stack σ2_e) /\
        genv_safe P_e g0.

    Local Definition s1_unprom_rexc
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U_e : list N) (s1_e s2_e : FusedS)
      (x1 x2 : @exc (@ParamsV IP IPT)) : Prop :=
      x1 = x2 /\ s1_unprom_exit_rel fs0 U0 P0 G fstk1 fstk2 U_e s1_e s2_e.

    Local Definition s1_unprom_rret
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U_e : list N) (s1_e s2_e : FusedS)
      (r1 r2 : (block_id * block_id) + @dvalue (@ParamsV IP IPT)) : Prop :=
      r1 = r2 /\ s1_unprom_exit_rel fs0 U0 P0 G fstk1 fstk2 U_e s1_e s2_e.

    Local Definition s1_unprom_loop_inv
      (d : definition dtyp (CFG.cfg dtyp))
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U : list N) (s1 s2 : FusedS) (_ : block_id * block_id) : Prop :=
      let c := df_instrs d in
      let safe_locals :=
        m2r_collect_unique_allocas (df_args d ++ flat_map full_block_defs (blks c)) (blks c) in
      incl U0 U /\
      exists P σ1 σ2 sf,
        incl P0 P /\
        s1 = (σ1, ((sf, fstk1), g0)) /\
        s2 = (σ2, ((sf, fstk2), g0)) /\
        stage1_mem_inv U P G σ1 σ2 /\
        top_frame_unprom_from fs0 G (state_memory_stack σ2) /\
        genv_safe P g0 /\
        safe_locals_env P safe_locals (stack_vars sf).

    Local Definition s1_prom_exit_rel
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U_e : list N) (s1_e s2_e : FusedS) : Prop :=
      incl U0 U_e /\
      exists P_e σ1_e σ2_e sf1_e sf2_e,
        incl P0 P_e /\
        s1_e = (σ1_e, ((sf1_e, fstk1), g0)) /\
        s2_e = (σ2_e, ((sf2_e, fstk2), g0)) /\
        genv_safe P_e g0 /\
        ((stage1_mem_inv U_e P_e G σ1_e σ2_e /\
          top_frame_unprom_from fs0 G (state_memory_stack σ2_e)) \/
         (exists gs_e,
            stage1_mem_inv U_e P_e (gs_e :: G) σ1_e σ2_e /\
            top_frame_prom_from fs0 gs_e G (state_memory_stack σ2_e))).

    Local Definition s1_prom_rexc
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U_e : list N) (s1_e s2_e : FusedS)
      (x1 x2 : @exc (@ParamsV IP IPT)) : Prop :=
      x1 = x2 /\ s1_prom_exit_rel fs0 U0 P0 G fstk1 fstk2 U_e s1_e s2_e.

    Local Definition s1_prom_rret
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U_e : list N) (s1_e s2_e : FusedS)
      (r1 r2 : (block_id * block_id) + @dvalue (@ParamsV IP IPT)) : Prop :=
      r1 = r2 /\ s1_prom_exit_rel fs0 U0 P0 G fstk1 fstk2 U_e s1_e s2_e.

    Local Definition s1_prom_loop_inv
      (sp : s1_prom_static)
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U : list N) (s1 s2 : FusedS) (j : block_id * block_id) : Prop :=
      let c := sps_c sp in
      snd j <> init c /\
      incl U0 U /\
      (exists b_pred,
         In b_pred (blks c) /\
         blk_id b_pred = fst j /\
         In (snd j) (m2r_block_succs b_pred)) /\
      (exists P gs σ1 σ2 sf1 sf2,
         incl P0 P /\
         gs_dt gs = sps_dt sp /\
         Maps.lookup (sps_p sp) (stack_vars sf1) = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs))) /\
         Maps.lookup (lookup_end_reg (sps_end_map sp) (fst j) (sps_init_reg sp)) (stack_vars sf2) =
           Some (DVALUE_Base (gs_db gs)) /\
         s1 = (σ1, ((sf1, fstk1), g0)) /\
         s2 = (σ2, ((sf2, fstk2), g0)) /\
         stage1_mem_inv U P (gs :: G) σ1 σ2 /\
         top_frame_prom_from fs0 gs G (state_memory_stack σ2) /\
         genv_safe P g0 /\
         safe_locals_env P (sps_safe_no_p sp) (stack_vars sf2) /\
         (forall x,
            In x (sps_avoid0 sp) -> x <> sps_p sp ->
            Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2))).

    Local Definition s1_phi
      (r : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
      (U : list N) (t1 t2 : itree ProvBotE Ans) : Prop :=
      (exists dt cc fv vs P G σ1 σ2 ls1 ls2 k1 k2,
         stage1_mem_inv U P G σ1 σ2 /\
         genv_safe P g0 /\
         (forall U' a1 a2,
            incl U U' ->
            s1_call_post U P G (Memory_stack_frame_stack (state_memory_stack σ2)) ls1 ls2 U' a1 a2 ->
            m2r_paco r U' (k1 a1) (k2 a2)) /\
         ITree.bind (interp_cfg_model ctx1 (mrec_ctx ctx1 _ (Call dt cc fv vs)) (σ1, (ls1, g0))) k1 ≅ t1 /\
         ITree.bind (interp_cfg_model ctx2 (mrec_ctx ctx2 _ (Call dt cc fv vs)) (σ2, (ls2, g0))) k2 ≅ t2)
      \/
      (exists d va fs0 U0 P0 G fstk1 fstk2 s1 s2 j k_out1 k_out2,
         m2r_defn_mem_safe d = true /\
         s1_unprom_loop_inv d fs0 U0 P0 G fstk1 fstk2 U s1 s2 j /\
         (forall U' a1 a2,
            incl U0 U' ->
            exc_post (s1_unprom_rexc fs0 U0 P0 G fstk1 fstk2)
                     (s1_unprom_rret fs0 U0 P0 G fstk1 fstk2) U' a1 a2 ->
            m2r_paco r U' (k_out1 a1) (k_out2 a2)) /\
         ITree.bind (interp_cfg_exc ctx1 (denote_ocfg_map (ocfg_map (blks (df_instrs d))) va j) s1) k_out1 ≅ t1 /\
         ITree.bind (interp_cfg_exc ctx2 (denote_ocfg_map (ocfg_map (blks (df_instrs d))) va j) s2) k_out2 ≅ t2)
      \/
      (exists sp va fs0 U0 P0 G fstk1 fstk2 s1 s2 j k_out1 k_out2,
         s1_prom_static_wf sp /\
         s1_prom_loop_inv sp fs0 U0 P0 G fstk1 fstk2 U s1 s2 j /\
         (forall U' a1 a2,
            incl U0 U' ->
            exc_post (s1_prom_rexc fs0 U0 P0 G fstk1 fstk2)
                     (s1_prom_rret fs0 U0 P0 G fstk1 fstk2) U' a1 a2 ->
            m2r_paco r U' (k_out1 a1) (k_out2 a2)) /\
         ITree.bind (interp_cfg_exc ctx1 (denote_ocfg_map (ocfg_map (blks (sps_c sp))) va j) s1) k_out1 ≅ t1 /\
         ITree.bind (interp_cfg_exc ctx2 (denote_ocfg_map (ocfg_map (sps_blks' sp)) va j) s2) k_out2 ≅ t2).

    Local Lemma s1_phi_mon
      (r1 r2 : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop)
      (Hle : forall U a1 a2, r1 U a1 a2 -> r2 U a1 a2) :
      forall U t1 t2, s1_phi r1 U t1 t2 -> s1_phi r2 U t1 t2.
    Proof using.
      intros U t1 t2 [Hcall | [Hunp | Hprom]].
      - left; destruct Hcall as (dt & cc & fv & vs & P & G & σ1 & σ2 & ls1 & ls2 & k1 & k2 &
                                 Hinv & Hg & Hk & E1 & E2).
        exists dt, cc, fv, vs, P, G, σ1, σ2, ls1, ls2, k1, k2.
        refine (conj Hinv (conj Hg (conj _ (conj E1 E2)))).
        intros U' a1 a2 Hinc Ha; exact (m2r_paco_mon r1 r2 Hle _ _ _ (Hk U' a1 a2 Hinc Ha)).
      - right; left; destruct Hunp as (d & va & fs0 & U0 & P0 & G & fstk1 & fstk2 & s1 & s2 & j &
                                       k1 & k2 & Hd & Hli & Hk & E1 & E2).
        exists d, va, fs0, U0, P0, G, fstk1, fstk2, s1, s2, j, k1, k2.
        refine (conj Hd (conj Hli (conj _ (conj E1 E2)))).
        intros U' a1 a2 Hinc Ha; exact (m2r_paco_mon r1 r2 Hle _ _ _ (Hk U' a1 a2 Hinc Ha)).
      - right; right; destruct Hprom as (sp & va & fs0 & U0 & P0 & G & fstk1 & fstk2 & s1 & s2 & j &
                                         k1 & k2 & Hwf & Hli & Hk & E1 & E2).
        exists sp, va, fs0, U0, P0, G, fstk1, fstk2, s1, s2, j, k1, k2.
        refine (conj Hwf (conj Hli (conj _ (conj E1 E2)))).
        intros U' a1 a2 Hinc Ha; exact (m2r_paco_mon r1 r2 Hle _ _ _ (Hk U' a1 a2 Hinc Ha)).
    Qed.

    Local Definition s1_lfp (U : list N) (t1 t2 : itree ProvBotE Ans) : Prop :=
      forall R : list N -> itree ProvBotE Ans -> itree ProvBotE Ans -> Prop,
        (forall U' a1 a2, s1_phi R U' a1 a2 -> R U' a1 a2) ->
        R U t1 t2.

    Local Lemma s1_lfp_fold (U : list N) (t1 t2 : itree ProvBotE Ans) :
      s1_phi s1_lfp U t1 t2 ->
      s1_lfp U t1 t2.
    Proof using.
      intros Hphi R Hclosed.
      apply Hclosed.
      exact (s1_phi_mon s1_lfp R (fun U' a1 a2 Hl => Hl R Hclosed) U t1 t2 Hphi).
    Qed.

    Local Lemma s1_lfp_unfold (U : list N) (t1 t2 : itree ProvBotE Ans) :
      s1_lfp U t1 t2 ->
      s1_phi s1_lfp U t1 t2.
    Proof using.
      intros Hl; apply (Hl (s1_phi s1_lfp)).
      intros U' a1 a2 H; exact (s1_phi_mon (s1_phi s1_lfp) s1_lfp (@s1_lfp_fold) U' a1 a2 H).
    Qed.

    Local Lemma s1_iter_one_step
      (RI   : list N -> FusedS -> FusedS -> block_id * block_id -> Prop)
      (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
      (RRet : list N -> FusedS -> FusedS ->
              (block_id * block_id) + @dvalue (@ParamsV IP IPT) ->
              (block_id * block_id) + @dvalue (@ParamsV IP IPT) -> Prop)
      (b1 b2 : block_id * block_id ->
               @CFGtop (@ParamsV IP IPT)
                 ((block_id * block_id) + ((block_id * block_id) + @dvalue (@ParamsV IP IPT))))
      (U : list N) (s1 s2 : FusedS) (j : block_id * block_id)
      (k_out1 k_out2 : Res (@exc (@ParamsV IP IPT) + ((block_id * block_id) + @dvalue (@ParamsV IP IPT))) ->
                       itree ProvBotE Ans)
      (Hbody :
         s1_cps s1_lfp
           (exc_post RExc
              (fun U' s1' s2' lr1 lr2 =>
                 match lr1, lr2 with
                 | inl j1, inl j2 => j1 = j2 /\ RI U' s1' s2' j1
                 | inr v1, inr v2 => RRet U' s1' s2' v1 v2
                 | _, _ => False
                 end))
           U
           (interp_cfg_exc ctx1 (b1 j) s1)
           (interp_cfg_exc ctx2 (b2 j) s2))
      (Hloop :
         forall U' s1' s2' j',
           incl U U' ->
           RI U' s1' s2' j' ->
           s1_lfp U'
             (ITree.bind (interp_cfg_exc ctx1 (ITree.iter b1 j') s1') k_out1)
             (ITree.bind (interp_cfg_exc ctx2 (ITree.iter b2 j') s2') k_out2))
      (Hk_out :
         forall U' a1 a2,
           incl U U' ->
           exc_post RExc RRet U' a1 a2 ->
           m2r_paco s1_lfp U' (k_out1 a1) (k_out2 a2)) :
      m2r_paco s1_lfp U
        (ITree.bind (interp_cfg_exc ctx1 (ITree.iter b1 j) s1) k_out1)
        (ITree.bind (interp_cfg_exc ctx2 (ITree.iter b2 j) s2) k_out2).
    Proof using.
      set (step_k := fun ctx (b : block_id * block_id ->
                                  @CFGtop (@ParamsV IP IPT)
                                    ((block_id * block_id) + ((block_id * block_id) + @dvalue (@ParamsV IP IPT))))
                         '(s', res) =>
                       match res with
                       | inl x => Ret (s', inl x)
                       | inr (inl j') => Tau (interp_cfg_exc ctx (ITree.iter b j') s')
                       | inr (inr v) => Ret (s', inr v)
                       end : itree ProvBotE (Res (@exc (@ParamsV IP IPT) +
                                                 ((block_id * block_id) + @dvalue (@ParamsV IP IPT))))).
      assert (Hunf : forall ctx b s i,
                interp_cfg_exc ctx (ITree.iter b i) s ≅
                ITree.bind (interp_cfg_exc ctx (b i) s) (step_k ctx b)).
      { intros ctx b s i.
        rewrite (interp_cfg_exc_obs_eq ctx _ _ s (unfold_iter b i)), interp_cfg_exc_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros [s' [x | [j' | v]]] _ <-; cbn [step_k];
          [reflexivity | apply interp_cfg_exc_tau | apply interp_cfg_exc_ret]. }
      assert (Eb1 : ITree.bind (interp_cfg_exc ctx1 (b1 j) s1)
                      (fun x => ITree.bind (step_k ctx1 b1 x) k_out1) ≅
                    ITree.bind (interp_cfg_exc ctx1 (ITree.iter b1 j) s1) k_out1).
      { symmetry; rewrite <- Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [apply Hunf | intros ? ? <-; reflexivity]. }
      assert (Eb2 : ITree.bind (interp_cfg_exc ctx2 (b2 j) s2)
                      (fun x => ITree.bind (step_k ctx2 b2 x) k_out2) ≅
                    ITree.bind (interp_cfg_exc ctx2 (ITree.iter b2 j) s2) k_out2).
      { symmetry; rewrite <- Eqit.bind_bind.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [apply Hunf | intros ? ? <-; reflexivity]. }
      eapply m2r_paco_obs_eq; [exact Eb1 | exact Eb2 |].
      apply Hbody.
      intros U' [s1' res1] [s2' res2] Hinc Hpost.
      destruct res1 as [x1 | [j1 | v1]], res2 as [x2 | [j2 | v2]]; cbn in Hpost; try contradiction.
      - eapply m2r_paco_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        exact (Hk_out U' (s1', inl x1) (s2', inl x2) Hinc Hpost).
      - destruct Hpost as [<- Hri].
        eapply m2r_paco_tau_both_r;
          [symmetry; apply Eqit.bind_tau | symmetry; apply Eqit.bind_tau |].
        exact (Hloop U' s1' s2' j1 Hinc Hri).
      - eapply m2r_paco_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        exact (Hk_out U' (s1', inr v1) (s2', inr v2) Hinc Hpost).
    Qed.

    Local Lemma s1_other_instr_exc_cps
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
      (Hnd_bks : NoDup (List.map blk_id bks))
      (Hbk : In bk bks)
      (Hsplit : blk_code bk = pre_c ++ im :: post_c)
      (Hsub : forall q,
                In q safe_sub ->
                In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
      (Hchk : check_other_instr_for_slot true safe_sub p im = true)
      (HTF_eq : forall s_a s_b,
                  Memory_stack_frame_stack (state_memory_stack s_b) =
                    Memory_stack_frame_stack (state_memory_stack s_a) ->
                  TF s_a -> TF s_b)
      (HTF_add : forall s_a s_b ptrs,
                   (forall z, In z (List.map ptr_to_int ptrs) -> forall gs0, In gs0 G -> ~ gs_in_range gs0 z) ->
                   Memory_stack_frame_stack (state_memory_stack s_b) =
                     Memory_stack_frame_stack (add_all_to_frame ptrs (state_memory_stack s_a)) ->
                   TF s_a -> TF s_b)
      (HRExc : forall U_x P_x σ1_x σ2_x ex,
                 incl U U_x ->
                 incl P_unprom P_x ->
                 stage1_mem_inv U_x P_x G σ1_x σ2_x ->
                 TF σ2_x ->
                 genv_safe P_x g0 ->
                 RExc U_x (σ1_x, ((sf1, fstk1), g0)) (σ2_x, ((sf2, fstk2), g0)) ex ex)
      (Hinv : stage1_mem_inv U P_unprom G σ1 σ2)
      (HTF : TF σ2)
      (Hgenv : genv_safe P_unprom g0)
      (Hsafe_loc : safe_locals_env P_unprom safe_sub (stack_vars sf2))
      (Huse_vars : forall x,
                     In x (m2r_code_entry_uses im) ->
                     Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
      s1_cps s1_lfp
        (exc_post RExc
           (fun U' s1' s2' r1 r2 =>
              exists P_unprom' σ1' σ2' sf1' sf2',
                incl U U' /\
                incl P_unprom P_unprom' /\
                r1 = tt /\ r2 = tt /\
                s1' = (σ1', ((sf1', fstk1), g0)) /\
                s2' = (σ2', ((sf2', fstk2), g0)) /\
                stage1_mem_inv U' P_unprom' G σ1' σ2' /\
                TF σ2' /\
                genv_safe P_unprom' g0 /\
                safe_locals_env P_unprom' safe_sub (stack_vars sf2') /\
                ((sf1' = sf1 /\ sf2' = sf2) \/
                 (exists id0 v,
                    fst (fst im) = IId id0 /\
                    sf1' = upd_local_sf sf1 (Maps.add id0 v (stack_vars sf1)) /\
                    sf2' = upd_local_sf sf2 (Maps.add id0 v (stack_vars sf2))))))
        U
        (interp_cfg_exc ctx1 (denote_instr im va1) (σ1, ((sf1, fstk1), g0)))
        (interp_cfg_exc ctx2 (denote_instr im va2) (σ2, ((sf2, fstk2), g0))).
    Proof using.
      destruct im as [[iid ins] md].
      destruct ins as [| op | [dt_c fn_e] args_c anns_c obs_c | | | | | | | |];
        try (apply refine_prov_to_s1_cps;
             exact (stage1_no_call_instr_exc_sim ctx1 ctx2 RExc TF fargs bks bk pre_c post_c
                      safe_sub p (iid, _, md) va1 va2 U P_unprom G σ1 σ2 sf1 sf2 fstk1 fstk2 g0
                      Hnd_bks Hbk Hsplit Hsub Hchk HTF_eq HTF_add Hinv HTF Hgenv Hsafe_loc Huse_vars)).
      assert (Hcall_chk : obs_c = [] /\ intrinsic_exp fn_e = None).
      { unfold check_other_instr_for_slot in Hchk.
        destruct iid; rewrite !andb_true_iff in Hchk;
          destruct Hchk as [_ [[_ Hobs] Hintr]];
          apply m2r_is_empty_spec in Hobs;
          destruct (intrinsic_exp fn_e); try discriminate Hintr;
          exact (conj Hobs Logic.eq_refl). }
      destruct Hcall_chk as [-> Hintr_none].
      destruct iid as [id_call_orig | vid_call_orig];
        cbn [denote_instr]; rewrite Hintr_none;
        [..].
      all: eapply s1_cps_cfg_exc_bind;
        [apply refine_prov_to_s1_cps;
         eapply denote_call_args_stage1_exc_sim; [exact Hinv |];
         intros x Hx; apply Huse_vars;
         cbn [m2r_code_entry_uses full_instr_uses];
         apply in_app_iff; left; apply in_app_iff; right; apply in_app_iff; left; exact Hx
        | intros U1 s1_a vs1 s2_a vs2 _ (-> & -> & -> & <-);
          eapply s1_cps_cfg_exc_bind with
            (RA := fun U' s1' s2' (_ _ : unit) =>
                     U' = U /\
                     s1' = (σ1, ((sf1, fstk1), g0)) /\
                     s2' = (σ2, ((sf2, fstk2), g0)));
          [eapply s1_cps_obs_eq;
             [symmetry; apply interp_cfg_exc_obs_eq, denote_operand_bundles_nil_eq
             | symmetry; apply interp_cfg_exc_obs_eq, denote_operand_bundles_nil_eq |];
           apply refine_prov_to_s1_cps, refine_cfg_exc_ret;
           exact (conj (Logic.eq_refl U) (conj Logic.eq_refl Logic.eq_refl))
          | intros U2 s1_ob _ s2_ob _ _ (-> & -> & ->);
            eapply s1_cps_cfg_exc_bind with
              (RA := fun U_c s1_c s2_c rv1 rv2 =>
                       exists P_c σ1_c σ2_c,
                         incl U U_c /\
                         incl P_unprom P_c /\
                         rv1 = rv2 /\
                         s1_c = (σ1_c, ((sf1, fstk1), g0)) /\
                         s2_c = (σ2_c, ((sf2, fstk2), g0)) /\
                         stage1_mem_inv U_c P_c G σ1_c σ2_c /\
                         Memory_stack_frame_stack (state_memory_stack σ2_c) =
                           Memory_stack_frame_stack (state_memory_stack σ2) /\
                         genv_safe P_c g0);
            [eapply s1_cps_cfg_exc_bind;
               [apply refine_prov_to_s1_cps, denote_exp_cfg_exc_sim;
                intros x Hx; apply Huse_vars;
                cbn [m2r_code_entry_uses full_instr_uses full_texp_uses snd];
                apply in_app_iff; left; apply in_app_iff; left; exact Hx
               | intros U3 s1_fn fv1 s2_fn fv2 _ (-> & -> & -> & <- & _);
                 intros k_c1 k_c2 Hk_c;
                 apply (m2r_cps_call_exc s1_lfp); apply s1_lfp_fold; left;
                 exists dt_c, (anns_cconv anns_c), fv1, vs1, P_unprom, G,
                        σ1, σ2, (sf1, fstk1), (sf2, fstk2),
                        (fun '(s1', y1) => Tau (k_c1 (s1', inr y1))),
                        (fun '(s2', y2) => Tau (k_c2 (s2', inr y2)));
                 refine (conj Hinv (conj Hgenv (conj _ (conj _ _))));
                 [intros U_c [s1_c rv1] [s2_c rv2] Hinc_c Hpost_c;
                  apply m2r_paco_fold; eapply RP_TauL; [reflexivity |]; eapply RP_TauR; [reflexivity |];
                  apply m2r_paco_unfold;
                  exact (Hk_c U_c (s1_c, inr rv1) (s2_c, inr rv2) Hinc_c Hpost_c)
                 | reflexivity | reflexivity]]
            | intros U_c s1_c rv1 s2_c rv2 _
                (P_c & σ1_c & σ2_c & HincU_c & HincP_c & <- & -> & -> & Hinv_c & Hfs_c & Hgenv_c);
              pose proof (HTF_eq σ2 σ2_c Hfs_c HTF) as HTF_c;
              pose proof (safe_locals_env_incl P_unprom P_c safe_sub (stack_vars sf2) HincP_c Hsafe_loc)
                as Hsafe_c;
              eapply s1_cps_cfg_exc_bind;
                [apply refine_prov_to_s1_cps;
                 exact (check_call_return_stage1_exc_sim ctx1 ctx2 RExc
                          (ann_fun_attributes anns_c) (ann_ret_attributes anns_c)
                          (metadata_range md) _ vs1 rv1
                          U_c P_c G σ1_c σ2_c ((sf1, fstk1), g0) ((sf2, fstk2), g0) Hinv_c)
                | intros U_cr s1_cr res1 s2_cr res2 _ (-> & -> & -> & <-);
                  eapply s1_cps_cfg_exc_bind with
                    (RA := fun U' s1' s2' r1 r2 =>
                             U' = U_c /\
                             s1' = (σ1_c, ((sf1, fstk1), g0)) /\
                             s2' = (σ2_c, ((sf2, fstk2), g0)) /\
                             r1 = r2);
                    [destruct res1 as [ex | dv];
                     [apply refine_prov_to_s1_cps, refine_cfg_exc_raiseLLVM_both;
                      exact (HRExc U_c P_c σ1_c σ2_c ex HincU_c HincP_c Hinv_c HTF_c Hgenv_c)
                     | apply refine_prov_to_s1_cps, refine_cfg_exc_ret;
                       exact (conj (Logic.eq_refl U_c)
                                (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)))]
                    | intros U_ret s1_ret dv1 s2_ret dv2 _ (-> & -> & -> & <-);
                      lazymatch goal with
                      | |- s1_cps _ _ _ (interp_cfg_exc _ (lwrite ?id0 _) _) _ =>
                          assert (Hid_nsafe : ~ In id0 safe_sub) by
                            (intros Hin_s;
                             destruct (unique_alloca_code_def_is_alloca fargs bks id0 Hnd_bks (Hsub id0 Hin_s)
                                         bk pre_c (INSTR_Call (dt_c, fn_e) args_c anns_c []) md post_c
                                         Hbk Hsplit) as (? & ? & Hbad);
                             discriminate Hbad);
                          apply refine_prov_to_s1_cps;
                          eapply refine_prov_tau_star_l; [apply tau_star_cfg_exc_lwrite |];
                          eapply refine_prov_tau_star_r; [apply tau_star_cfg_exc_lwrite |];
                          apply refine_prov_ret;
                          exists P_c, σ1_c, σ2_c,
                                 (upd_local_sf sf1 (Maps.add id0 dv1 (stack_vars sf1))),
                                 (upd_local_sf sf2 (Maps.add id0 dv1 (stack_vars sf2)));
                          refine (conj HincU_c (conj HincP_c
                                    (conj Logic.eq_refl (conj Logic.eq_refl
                                      (conj Logic.eq_refl (conj Logic.eq_refl
                                        (conj Hinv_c (conj HTF_c (conj Hgenv_c
                                          (conj (safe_locals_env_add_other P_c safe_sub id0 dv1 _ Hid_nsafe Hsafe_c)
                                                _))))))))));
                          right; exists id0, dv1; repeat split; reflexivity
                      | |- _ =>
                          apply refine_prov_to_s1_cps, refine_cfg_exc_ret;
                          exists P_c, σ1_c, σ2_c, sf1, sf2;
                          refine (conj HincU_c (conj HincP_c
                                    (conj Logic.eq_refl (conj Logic.eq_refl
                                      (conj Logic.eq_refl (conj Logic.eq_refl
                                        (conj Hinv_c (conj HTF_c (conj Hgenv_c
                                          (conj Hsafe_c (or_introl (conj Logic.eq_refl Logic.eq_refl))))))))))))
                      end]]]]].
    Qed.

    Local Lemma s1_other_code_exc_cps
      (RExc : list N -> FusedS -> FusedS -> @exc (@ParamsV IP IPT) -> @exc (@ParamsV IP IPT) -> Prop)
      (TF : state -> Prop)
      (fargs : list local_id) (bks : ocfg dtyp) (bk : block dtyp)
      (pre_c cd post_c : code dtyp)
      (safe_sub : list local_id) (p : local_id)
      (va1 va2 : option (@ptr ProvenanceV (@PointerV IP)))
      (U P_unprom : list N) (G : list ghost_slot)
      (σ1 σ2 : state)
      (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) (fstk1 fstk2 : stack)
      (Hnd_bks : NoDup (List.map blk_id bks))
      (Hbk : In bk bks)
      (Hsplit : blk_code bk = pre_c ++ cd ++ post_c)
      (Hsub : forall q,
                In q safe_sub ->
                In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs bks) bks))
      (Hchk : forallb (check_other_instr_for_slot true safe_sub p) cd = true)
      (HTF_eq : forall s_a s_b,
                  Memory_stack_frame_stack (state_memory_stack s_b) =
                    Memory_stack_frame_stack (state_memory_stack s_a) ->
                  TF s_a -> TF s_b)
      (HTF_add : forall s_a s_b ptrs,
                   (forall z, In z (List.map ptr_to_int ptrs) -> forall gs0, In gs0 G -> ~ gs_in_range gs0 z) ->
                   Memory_stack_frame_stack (state_memory_stack s_b) =
                     Memory_stack_frame_stack (add_all_to_frame ptrs (state_memory_stack s_a)) ->
                   TF s_a -> TF s_b)
      (HRExc : forall U_x P_x σ1_x σ2_x sf1_x sf2_x ex,
                 incl U U_x ->
                 incl P_unprom P_x ->
                 stage1_mem_inv U_x P_x G σ1_x σ2_x ->
                 TF σ2_x ->
                 genv_safe P_x g0 ->
                 RExc U_x (σ1_x, ((sf1_x, fstk1), g0)) (σ2_x, ((sf2_x, fstk2), g0)) ex ex)
      (Hinv : stage1_mem_inv U P_unprom G σ1 σ2)
      (HTF : TF σ2)
      (Hgenv : genv_safe P_unprom g0)
      (Hsafe_loc : safe_locals_env P_unprom safe_sub (stack_vars sf2))
      (Hvars : forall x,
                 x <> p ->
                 Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
      s1_cps s1_lfp
        (exc_post RExc
           (fun U' s1' s2' r1 r2 =>
              exists P_unprom' σ1' σ2' sf1' sf2',
                incl U U' /\
                incl P_unprom P_unprom' /\
                r1 = tt /\ r2 = tt /\
                s1' = (σ1', ((sf1', fstk1), g0)) /\
                s2' = (σ2', ((sf2', fstk2), g0)) /\
                stage1_mem_inv U' P_unprom' G σ1' σ2' /\
                TF σ2' /\
                genv_safe P_unprom' g0 /\
                safe_locals_env P_unprom' safe_sub (stack_vars sf2') /\
                (forall x, x <> p -> Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf2')) /\
                (sf1 = sf2 -> sf1' = sf2')))
        U
        (interp_cfg_exc ctx1 (denote_code cd va1) (σ1, ((sf1, fstk1), g0)))
        (interp_cfg_exc ctx2 (denote_code cd va2) (σ2, ((sf2, fstk2), g0))).
    Proof using.
      revert pre_c U P_unprom σ1 σ2 sf1 sf2 Hsplit Hchk HRExc Hinv HTF Hgenv Hsafe_loc Hvars.
      induction cd as [| im rest IH];
        intros pre_c U P_unprom σ1 σ2 sf1 sf2 Hsplit Hchk HRExc Hinv HTF Hgenv Hsafe_loc Hvars;
        unfold denote_code; cbn [forallb] in Hchk; cbn [loop_monad].
      - apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
        exists P_unprom, σ1, σ2, sf1, sf2.
        refine (conj (incl_refl U) (conj (incl_refl P_unprom)
                  (conj Logic.eq_refl (conj Logic.eq_refl
                    (conj Logic.eq_refl (conj Logic.eq_refl
                      (conj Hinv (conj HTF (conj Hgenv
                        (conj Hsafe_loc (conj Hvars (fun Heq => Heq)))))))))))).
      - rewrite andb_true_iff in Hchk; destruct Hchk as [Hchk_im Hchk_rest].
        assert (Huse_im : forall x,
                  In x (m2r_code_entry_uses im) ->
                  Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)).
        { intros x Hx; apply Hvars; intros ->.
          unfold check_other_instr_for_slot in Hchk_im.
          rewrite andb_true_iff, negb_true_iff in Hchk_im.
          exact (proj1 (in_raw_ids_false _ _) (proj1 Hchk_im) Hx). }
        eapply s1_cps_cfg_exc_bind.
        + exact (s1_other_instr_exc_cps RExc TF fargs bks bk pre_c (rest ++ post_c)
                   safe_sub p im va1 va2 U P_unprom G σ1 σ2 sf1 sf2 fstk1 fstk2
                   Hnd_bks Hbk Hsplit Hsub Hchk_im HTF_eq HTF_add
                   (fun U_x P_x σ1_x σ2_x ex H1 H2 H3 H4 H5 =>
                      HRExc U_x P_x σ1_x σ2_x sf1 sf2 ex H1 H2 H3 H4 H5)
                   Hinv HTF Hgenv Hsafe_loc Huse_im).
        + intros U1 s1_m _ s2_m _ _
            (P1 & σ1_m & σ2_m & sf1_m & sf2_m &
             HincU1 & HincP1 & _ & _ & -> & -> & Hinv1 & HTF1 & Hgenv1 & Hsafe1 & Hsf_step).
          assert (Hvars1 : forall x, x <> p -> Maps.lookup x (stack_vars sf1_m) = Maps.lookup x (stack_vars sf2_m)).
          { intros x Hne; destruct Hsf_step as [[-> ->] | (id0 & v & _ & -> & ->)];
              [exact (Hvars x Hne) |].
            cbn [stack_vars upd_local_sf Maps.lookup Maps.add Map_rmap]; destruct (raw_id_eqb x id0) eqn:Ex_id; [apply raw_id_eqb_spec in Ex_id; subst x | apply raw_id_eqb_neq in Ex_id; rename Ex_id into Hx_id];
              [rewrite !RMF.F.add_eq_o by reflexivity; reflexivity
              | rewrite !RMF.F.add_neq_o by (intros Heq'; exact (Hx_id (Logic.eq_sym Heq'))); exact (Hvars x Hne)]. }
          assert (Hsplit_rest : blk_code bk = (pre_c ++ [im]) ++ rest ++ post_c)
            by (rewrite <- app_assoc; exact Hsplit).
          eapply s1_cps_weaken.
          * exact (IH (pre_c ++ [im]) U1 P1 σ1_m σ2_m sf1_m sf2_m Hsplit_rest Hchk_rest
                     (fun U_x P_x σ1_x σ2_x sf1_x sf2_x ex H1 H2 =>
                        HRExc U_x P_x σ1_x σ2_x sf1_x sf2_x ex (incl_tran HincU1 H1) (incl_tran HincP1 H2))
                     Hinv1 HTF1 Hgenv1 Hsafe1 Hvars1).
          * intros U2 [s1_f res1] [s2_f res2] _.
            destruct res1 as [ex1 | u1], res2 as [ex2 | u2]; cbn [exc_post];
              try (intros H; exact H).
            intros (P2 & σ1_f & σ2_f & sf1_f & sf2_f &
                    HincU2 & HincP2 & -> & -> & -> & -> & Hinv2 & HTF2 & Hgenv2 & Hsafe2 & Hvars2 & Heq2).
            exists P2, σ1_f, σ2_f, sf1_f, sf2_f.
            refine (conj (incl_tran HincU1 HincU2) (conj (incl_tran HincP1 HincP2)
                      (conj Logic.eq_refl (conj Logic.eq_refl
                        (conj Logic.eq_refl (conj Logic.eq_refl
                          (conj Hinv2 (conj HTF2 (conj Hgenv2 (conj Hsafe2 (conj Hvars2 _))))))))))).
            intros Heq_sf; apply Heq2.
            destruct Hsf_step as [[-> ->] | (id0 & v & _ & -> & ->)]; [exact Heq_sf | subst sf2; reflexivity].
    Qed.

    Local Lemma s1_rewrite_code_exc_cps
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
      (Hchk : forallb (check_code_entry_for_slot true safe_no_p p dt) cd = true)
      (Hrw : rewrite_code_for_slot p dt cur_reg avoid cd = (cd', end_reg, avoid'))
      (Hinc_av : incl avoid0 avoid)
      (Hcur_nin0 : ~ In cur_reg avoid0)
      (Hsc : is_scalar_dtyp dt = true)
      (HRExc : forall U_x P_x gs_x σ1_x σ2_x sf1_x sf2_x ex,
                 incl U U_x ->
                 incl P_unprom P_x ->
                 stage1_mem_inv U_x P_x (gs_x :: G) σ1_x σ2_x ->
                 top_frame_prom_from fs0 gs_x G (state_memory_stack σ2_x) ->
                 genv_safe P_x g0 ->
                 RExc U_x (σ1_x, ((sf1_x, fstk1), g0)) (σ2_x, ((sf2_x, fstk2), g0)) ex ex)
      (Hdt : gs_dt gs = dt)
      (Hlk_p : Maps.lookup p (stack_vars sf1) = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs))))
      (Hlk_cur : Maps.lookup cur_reg (stack_vars sf2) = Some (DVALUE_Base (gs_db gs)))
      (Hinv : stage1_mem_inv U P_unprom (gs :: G) σ1 σ2)
      (Htf : top_frame_prom_from fs0 gs G (state_memory_stack σ2))
      (Hgenv : genv_safe P_unprom g0)
      (Hsafe_loc : safe_locals_env P_unprom safe_no_p (stack_vars sf2))
      (Hvars : forall x,
                 In x avoid0 -> x <> p ->
                 Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)) :
      s1_cps s1_lfp
        (exc_post RExc
           (fun U' s1' s2' r1 r2 =>
              exists P_unprom' gs' σ1' σ2' sf1' sf2',
                incl U U' /\
                incl P_unprom P_unprom' /\
                r1 = tt /\ r2 = tt /\
                gs_dt gs' = dt /\
                Maps.lookup p (stack_vars sf1') = Some (DVALUE_Base (DVALUE_Pointer (gs_pt gs'))) /\
                Maps.lookup end_reg (stack_vars sf2') = Some (DVALUE_Base (gs_db gs')) /\
                s1' = (σ1', ((sf1', fstk1), g0)) /\
                s2' = (σ2', ((sf2', fstk2), g0)) /\
                stage1_mem_inv U' P_unprom' (gs' :: G) σ1' σ2' /\
                top_frame_prom_from fs0 gs' G (state_memory_stack σ2') /\
                genv_safe P_unprom' g0 /\
                safe_locals_env P_unprom' safe_no_p (stack_vars sf2') /\
                (forall x,
                   In x avoid0 -> x <> p ->
                   Maps.lookup x (stack_vars sf1') = Maps.lookup x (stack_vars sf2'))))
        U
        (interp_cfg_exc ctx1 (denote_code cd va1) (σ1, ((sf1, fstk1), g0)))
        (interp_cfg_exc ctx2 (denote_code cd' va2) (σ2, ((sf2, fstk2), g0))).
    Proof using.
      revert pre_c cur_reg avoid cd' end_reg avoid' U P_unprom gs σ1 σ2 sf1 sf2
        Hsplit Huses_av0 Hdefs_av0 Hp_nd_cd Hchk Hrw Hinc_av Hcur_nin0
        HRExc Hdt Hlk_p Hlk_cur Hinv Htf Hgenv Hsafe_loc Hvars.
      induction cd as [| im rest IH];
        intros pre_c cur_reg avoid cd' end_reg avoid' U P_unprom gs σ1 σ2 sf1 sf2
          Hsplit Huses_av0 Hdefs_av0 Hp_nd_cd Hchk Hrw Hinc_av Hcur_nin0
          HRExc Hdt Hlk_p Hlk_cur Hinv Htf Hgenv Hsafe_loc Hvars;
        cbn [rewrite_code_for_slot forallb flat_map] in *.
      - inversion Hrw; subst cd' end_reg avoid'; clear Hrw.
        unfold denote_code; cbn [loop_monad].
        apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
        exists P_unprom, gs, σ1, σ2, sf1, sf2;
          repeat match goal with |- _ /\ _ => split end; try apply incl_refl; try reflexivity; assumption.
      - rewrite andb_true_iff in Hchk; destruct Hchk as [Hchk_im Hchk_rest].
        assert (Hp_nd_im : ~ In p (instr_id_defs (fst (fst im))))
          by (destruct im as [[iid_i ?] ?]; intros Hp; apply Hp_nd_cd, in_app_iff; left; exact Hp).
        assert (Hp_nd_rest : ~ In p (flat_map (fun '(iid, _, _) => instr_id_defs iid) rest))
          by (intros Hp; apply Hp_nd_cd, in_app_iff; right; exact Hp).
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
          eapply s1_cps_obs_eq;
            [reflexivity
            | apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
          eapply s1_cps_cfg_exc_bind.
          * apply refine_prov_to_s1_cps.
            exact (denote_mk_load_pair_exc_sim ctx1 ctx2 RExc dst p lv_reg cur_reg dt anns_ld md_ld
                     va1 va2 U P_unprom gs G σ1 σ2 sf1 sf2 fstk1 fstk2 g0
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
                     Hinc_av1 Hcur_nin0 HRExc Hdt Hlk_p1 Hlk_cur1 Hinv Htf Hgenv Hsafe1 Hvars1).
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
            eapply s1_cps_obs_eq;
              [reflexivity
              | apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
            eapply s1_cps_cfg_exc_bind.
            -- apply refine_prov_to_s1_cps.
               exact (denote_mk_store_pair_exc_sim ctx1 ctx2 RExc vid p sv_reg st_reg dt val_exp
                        anns_st md_st va1 va2 fs0 U P_unprom gs G σ1 σ2 sf1 sf2 fstk1 fstk2 g0
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
                        Hinc_av1 Hst_nin0 HRExc Hdt Hlk_p Hlk_st Hinv1 Htf1 Hgenv Hsafe1 Hvars1).
          * destruct (rewrite_code_for_slot p dt cur_reg avoid rest) as [[rest' er] av'] eqn:Erest.
            inversion Hrw; subst cd' end_reg avoid'; clear Hrw.
            assert (Huse_im : forall x,
                      In x (m2r_code_entry_uses im) ->
                      Maps.lookup x (stack_vars sf1) = Maps.lookup x (stack_vars sf2)).
            { intros x Hx; apply Hvars.
              - exact (Huses_av0 im x (or_introl Logic.eq_refl) Hx).
              - intros ->; unfold check_other_instr_for_slot in Hchk_im;
                  rewrite andb_true_iff, negb_true_iff in Hchk_im;
                  exact (proj1 (in_raw_ids_false _ _) (proj1 Hchk_im) Hx). }
            unfold denote_code; cbn [loop_monad].
            eapply s1_cps_cfg_exc_bind.
            -- exact (s1_other_instr_exc_cps RExc
                        (fun s => top_frame_prom_from fs0 gs G (state_memory_stack s))
                        fargs bks bk pre_c (rest ++ post_c)
                        safe_no_p p im va1 va2 U P_unprom (gs :: G) σ1 σ2 sf1 sf2 fstk1 fstk2
                        Hnd_bks Hbk Hsplit Hsub Hchk_im
                        (fun s_a s_b Heq_fs HT => top_frame_prom_frame_eq fs0 gs G _ _ (eq_sym Heq_fs) HT)
                        (fun s_a s_b ptrs Hdisj Heq_fs HT =>
                           top_frame_prom_frame_eq fs0 gs G _ _ (eq_sym Heq_fs)
                             (top_frame_prom_add_ptrs fs0 gs G ptrs _ HT Hdisj))
                        (fun U_x P_x σ1_x σ2_x ex H1 H2 H3 H4 H5 =>
                           HRExc U_x P_x gs σ1_x σ2_x sf1 sf2 ex H1 H2 H3 H4 H5)
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
                 assert (Hid_av0 : In id0 avoid0)
                   by (apply (Hdefs_av0 im id0 (or_introl Logic.eq_refl)); rewrite Heq_iid; left; reflexivity).
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
               eapply s1_cps_weaken.
               ++ exact (IH (pre_c ++ [im]) cur_reg avoid rest' er av' U1 P1 gs σ1_m σ2_m sf1_m sf2_m
                           Hsplit_rest Huses_rest Hdefs_rest Hp_nd_rest Hchk_rest Erest
                           Hinc_av Hcur_nin0
                           (fun U_x P_x gs_x σ1_x σ2_x sf1_x sf2_x ex H1 H2 =>
                              HRExc U_x P_x gs_x σ1_x σ2_x sf1_x sf2_x ex
                                (incl_tran HincU1 H1) (incl_tran HincP1 H2))
                           Hdt Hlk_p1 Hlk_cur1 Hinv1 Htf1 Hgenv1 Hsafe1 Hvars1).
               ++ intros U2 [s1_f res1] [s2_f res2] _.
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

    Local Lemma s1_external_call_cfg_sim
      (dt : dtyp) (fv : @dvalue (@ParamsV IP IPT)) (vs : list (@dvalue (@ParamsV IP IPT)))
      (U P : list N) (G : list ghost_slot)
      (σ1 σ2 : state) (ls1 ls2 : @stack_frame (@ParamsV IP IPT) * stack)
      (Hinv : stage1_mem_inv U P G σ1 σ2)
      (Hg : genv_safe P g0) :
      refine_prov
        (s1_call_post U P G (Memory_stack_frame_stack (state_memory_stack σ2)) ls1 ls2)
        U
        (interp_cfg_model ctx1 (inr <$> external_call dt fv vs) (σ1, (ls1, g0)))
        (interp_cfg_model ctx2 (inr <$> external_call dt fv vs) (σ2, (ls2, g0))).
    Proof using.
      unfold Functor.fmap, Functor_itree, ITree.map.
      eapply refine_cfg_model_bind with
        (RA := fun U' '(s1', r1) '(s2', r2) =>
                 incl U U' /\
                 s1' = (σ1, (ls1, g0)) /\
                 s2' = (σ2, (ls2, g0)) /\
                 r1 = r2).
      - unfold external_call, Subevent.trigger; try unfold trigger_cast.
        eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_non_intr; reflexivity
          | symmetry; apply interp_cfg_model_non_intr; reflexivity |].
        cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
        unfold fused_trigger_prov.
        eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_bind | symmetry; apply Eqit.bind_bind |].
        eapply PassCommonModel.refine_prov_bind; [apply refine_prov_refl_incl |].
        intros U' r1 r2 _ [Hinc <-].
        eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        apply refine_prov_tau_both, refine_prov_tau_both, refine_prov_tau_both, refine_prov_ret.
        exact (conj Hinc (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl))).
      - intros U' s1' r1 s2' r2 _ (Hinc & -> & -> & <-).
        eapply refine_prov_obs_eq;
          [symmetry; apply interp_cfg_model_ret | symmetry; apply interp_cfg_model_ret |].
        apply refine_prov_ret.
        exists P, σ1, σ2.
        exact (conj Hinc
                 (conj (incl_refl P)
                    (conj Logic.eq_refl
                       (conj Logic.eq_refl
                          (conj Logic.eq_refl
                             (conj (stage1_mem_inv_incl_U U U' P G σ1 σ2 Hinc Hinv)
                                   (conj Logic.eq_refl Hg))))))).
    Qed.

    Local Definition ocfg_step_body
      (bmap : rmap (block dtyp))
      (va : option (@ptr ProvenanceV (@PointerV IP)))
      : (block_id * block_id) ->
        @CFGtop (@ParamsV IP IPT)
          ((block_id * block_id) + ((block_id * block_id) + @dvalue (@ParamsV IP IPT))) :=
      fun '((bid_from, bid_src) : block_id * block_id) =>
        match RM.find bid_src bmap with
        | None => ExtLib.Structures.Monad.ret (inr (inl (bid_from, bid_src)))
        | Some block_src =>
            ExtLib.Structures.Monad.bind (denote_block block_src bid_from va)
              (fun bd =>
                 match bd with
                 | inr dv => ExtLib.Structures.Monad.ret (inr (inr dv))
                 | inl bid_target => ExtLib.Structures.Monad.ret (inl (bid_src, bid_target))
                 end)
        end.

    Local Lemma denote_ocfg_map_eq_iter
      (bmap : rmap (block dtyp))
      (va : option (@ptr ProvenanceV (@PointerV IP)))
      (j : block_id * block_id) :
      denote_ocfg_map bmap va j = ITree.iter (ocfg_step_body bmap va) j.
    Proof using.
      unfold denote_ocfg_map, ocfg_step_body; reflexivity.
    Qed.

    Local Lemma s1_unprom_block_body_cps
      (d : definition dtyp (CFG.cfg dtyp))
      (va : option (@ptr ProvenanceV (@PointerV IP)))
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U : list N) (s1 s2 : FusedS) (j : block_id * block_id)
      (Hd : m2r_defn_mem_safe d = true)
      (Hli : s1_unprom_loop_inv d fs0 U0 P0 G fstk1 fstk2 U s1 s2 j) :
      let bmap := ocfg_map (blks (df_instrs d)) in
      s1_cps s1_lfp
        (exc_post (s1_unprom_rexc fs0 U0 P0 G fstk1 fstk2)
           (fun U' s1' s2' lr1 lr2 =>
              match lr1, lr2 with
              | inl j1, inl j2 =>
                  j1 = j2 /\ s1_unprom_loop_inv d fs0 U0 P0 G fstk1 fstk2 U' s1' s2' j1
              | inr v1, inr v2 =>
                  s1_unprom_rret fs0 U0 P0 G fstk1 fstk2 U' s1' s2' v1 v2
              | _, _ => False
              end))
        U
        (interp_cfg_exc ctx1 (ocfg_step_body bmap va j) s1)
        (interp_cfg_exc ctx2 (ocfg_step_body bmap va j) s2).
    Proof using.
      cbv zeta.
      unfold m2r_defn_mem_safe in Hd; cbn zeta in Hd.
      set (c := df_instrs d) in *.
      set (fargs := df_args d) in *.
      set (safe_locals :=
             m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs (blks c)) (blks c)) in *.
      rewrite andb_true_iff in Hd; destruct Hd as [Hnd_bks Hbks_chk].
      apply m2r_nodup_ids_spec in Hnd_bks.
      unfold s1_unprom_loop_inv in Hli; cbn zeta in Hli; fold c fargs safe_locals in Hli.
      destruct Hli as (HincU0 & P & σ1 & σ2 & sf & HincP0 & -> & -> & Hinv & Htf & Hgenv & Hsafe_loc).
      destruct j as [bf bs]; unfold ocfg_step_body; cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite ScopeTheory.ocfg_map_find_block.
      destruct (find_block (blks c) bs) as [bk |] eqn:Efb.
      - destruct (m2r_find_block_some_inv (blks c) bs bk Efb) as [Hin_bk _].
        rewrite forallb_forall in Hbks_chk; specialize (Hbks_chk bk Hin_bk).
        rewrite andb_true_iff in Hbks_chk; destruct Hbks_chk as [Hcd_safe Hni_tm].
        unfold denote_block.
        eapply s1_cps_cfg_exc_bind with
          (RA := fun U_bd s1_bd s2_bd bd1 bd2 =>
                   exists P_cd σ1_cd σ2_cd sf2_cd,
                     incl U0 U_bd /\
                     incl P0 P_cd /\
                     bd1 = bd2 /\
                     s1_bd = (σ1_cd, ((sf2_cd, fstk1), g0)) /\
                     s2_bd = (σ2_cd, ((sf2_cd, fstk2), g0)) /\
                     stage1_mem_inv U_bd P_cd G σ1_cd σ2_cd /\
                     top_frame_unprom_from fs0 G (state_memory_stack σ2_cd) /\
                     genv_safe P_cd g0 /\
                     safe_locals_env P_cd safe_locals (stack_vars sf2_cd)).
        + eapply s1_cps_cfg_exc_bind.
          * apply refine_prov_to_s1_cps.
            exact (denote_phis_same_exc_sim ctx1 ctx2
                     (s1_unprom_rexc fs0 U0 P0 G fstk1 fstk2)
                     bf (blk_phis bk) U σ1 σ2 sf sf fstk1 fstk2 g0
                     (fun _ _ => Logic.eq_refl)).
          * intros U_ph s1_ph _ s2_ph _ _ (dvs & -> & _ & _ & Hfst_dvs & -> & ->).
            set (sf_ph := upd_local_sf sf (write_phi_dvs dvs (stack_vars sf))).
            assert (Hsafe_ph : safe_locals_env P safe_locals (stack_vars sf_ph)).
            { apply write_phi_dvs_safe_locals; [| exact Hsafe_loc].
              intros q Hq Hin_dvs; rewrite Hfst_dvs in Hin_dvs.
              apply in_map_iff in Hin_dvs as ([[x_ph ph_q] md_q] & <- & Hpe_in).
              exact (unique_alloca_not_phi_def fargs (blks c) x_ph Hnd_bks Hq
                       bk x_ph ph_q md_q Hin_bk Hpe_in Logic.eq_refl). }
            set (p_dummy := fresh_name "m2r_unused" (flat_map m2r_code_entry_uses (blk_code bk))).
            assert (Hchk_cd : forallb (check_other_instr_for_slot true safe_locals p_dummy) (blk_code bk) = true)
              by (apply safe_mem_code_to_check_other; [apply fresh_name_not_in | exact Hcd_safe]).
            assert (Hsplit_cd : blk_code bk = [] ++ blk_code bk ++ [])
              by (rewrite app_nil_r; reflexivity).
            eapply s1_cps_cfg_exc_bind.
            -- exact (s1_other_code_exc_cps
                        (s1_unprom_rexc fs0 U0 P0 G fstk1 fstk2)
                        (fun s => top_frame_unprom_from fs0 G (state_memory_stack s))
                        fargs (blks c) bk [] (blk_code bk) []
                        safe_locals p_dummy va va U P G σ1 σ2 sf_ph sf_ph fstk1 fstk2
                        Hnd_bks Hin_bk Hsplit_cd (fun q Hq => Hq) Hchk_cd
                        (fun s_a s_b Heq_fs HT => top_frame_unprom_frame_eq fs0 G _ _ (eq_sym Heq_fs) HT)
                        (fun s_a s_b ptrs Hdisj Heq_fs HT =>
                           top_frame_unprom_frame_eq fs0 G _ _ (eq_sym Heq_fs)
                             (top_frame_unprom_add_ptrs fs0 G ptrs _ HT Hdisj))
                        (fun U_x P_x σ1_x σ2_x sf1_x sf2_x ex H1 H2 H3 H4 H5 =>
                           conj Logic.eq_refl
                             (conj (incl_tran HincU0 H1)
                                (ex_intro _ P_x (ex_intro _ σ1_x (ex_intro _ σ2_x
                                   (ex_intro _ sf1_x (ex_intro _ sf2_x
                                      (conj (incl_tran HincP0 H2)
                                         (conj Logic.eq_refl
                                            (conj Logic.eq_refl (conj H3 (conj H4 H5))))))))))))
                        Hinv Htf Hgenv Hsafe_ph (fun _ _ => Logic.eq_refl)).
            -- intros U_cd s1_cd _ s2_cd _ _
                 (P_cd & σ1_cd & σ2_cd & sf1_cd & sf2_cd &
                  HincU_cd & HincP_cd & _ & _ & -> & -> &
                  Hinv_cd & Htf_cd & Hgenv_cd & Hsafe_cd & _ & Heq_sf_cd).
               pose proof (Heq_sf_cd Logic.eq_refl) as ->.
               destruct (blk_term bk) as [[iid_t tm] md_t]; cbn [fst snd] in Hni_tm.
               apply refine_prov_to_s1_cps.
               eapply refine_prov_weaken.
               ++ apply (denote_non_invoke_term_exc_sim ctx1 ctx2
                           (s1_unprom_rexc fs0 U0 P0 G fstk1 fstk2)
                           iid_t iid_t tm md_t md_t
                           U_cd σ1_cd σ2_cd sf2_cd sf2_cd fstk1 fstk2 g0
                           Hni_tm (fun _ _ => Logic.eq_refl)).
                  intros ex; refine (conj Logic.eq_refl (conj (incl_tran HincU0 HincU_cd) _)).
                  exists P_cd, σ1_cd, σ2_cd, sf2_cd, sf2_cd.
                  exact (conj (incl_tran HincP0 HincP_cd)
                           (conj Logic.eq_refl (conj Logic.eq_refl (conj Hinv_cd (conj Htf_cd Hgenv_cd))))).
               ++ intros U_t [s1_t res1] [s2_t res2].
                  destruct res1 as [ex1 | bd1], res2 as [ex2 | bd2]; cbn [exc_post];
                    try (intros H; exact H).
                  intros (-> & -> & -> & <- & _).
                  exists P_cd, σ1_cd, σ2_cd, sf2_cd.
                  exact (conj (incl_tran HincU0 HincU_cd)
                           (conj (incl_tran HincP0 HincP_cd)
                              (conj Logic.eq_refl
                                 (conj Logic.eq_refl
                                    (conj Logic.eq_refl
                                       (conj Hinv_cd (conj Htf_cd (conj Hgenv_cd Hsafe_cd)))))))).
        + intros U_bd s1_bd bd1 s2_bd bd2 _
            (P_cd & σ1_cd & σ2_cd & sf2_cd &
             HincU_c & HincP_c & <- & -> & -> & Hinv_cd & Htf_cd & Hgenv_cd & Hsafe_cd).
          destruct bd1 as [bid_tgt | dv_cur].
          * apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
            refine (conj Logic.eq_refl (conj HincU_c _)).
            exists P_cd, σ1_cd, σ2_cd, sf2_cd.
            exact (conj HincP_c (conj Logic.eq_refl (conj Logic.eq_refl
                     (conj Hinv_cd (conj Htf_cd (conj Hgenv_cd Hsafe_cd)))))).
          * apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
            refine (conj Logic.eq_refl (conj HincU_c _)).
            exists P_cd, σ1_cd, σ2_cd, sf2_cd, sf2_cd.
            exact (conj HincP_c (conj Logic.eq_refl (conj Logic.eq_refl
                     (conj Hinv_cd (conj Htf_cd Hgenv_cd))))).
      - apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
        refine (conj Logic.eq_refl (conj HincU0 _)).
        exists P, σ1, σ2, sf, sf.
        exact (conj HincP0 (conj Logic.eq_refl (conj Logic.eq_refl
                 (conj Hinv (conj Htf Hgenv))))).
    Qed.

    Local Lemma s1_unprom_denote_function_cps
      (d : definition dtyp (CFG.cfg dtyp))
      (cc : cconv) (args : list (@dvalue (@ParamsV IP IPT)))
      (U0 P0 : list N) (G : list ghost_slot)
      (σ1_in σ2_in : state)
      (ls1 ls2 : @stack_frame (@ParamsV IP IPT) * stack)
      (Hd : m2r_defn_mem_safe d = true)
      (Hinv0 : stage1_mem_inv U0 P0 G σ1_in σ2_in)
      (Hgenv0 : genv_safe P0 g0) :
      s1_cps s1_lfp
        (s1_call_post U0 P0 G (Memory_stack_frame_stack (state_memory_stack σ2_in)) ls1 ls2)
        U0
        (interp_cfg_model ctx1 (denote_function d cc args) (σ1_in, (ls1, g0)))
        (interp_cfg_model ctx2 (denote_function d cc args) (σ2_in, (ls2, g0))).
    Proof using.
      destruct ls1 as [sf_c1 fstk_c1], ls2 as [sf_c2 fstk_c2].
      unfold denote_function.
      destruct (dc_param_attrs (df_prototype d)) as [ret_attrs args_attrs].
      set (fname := show_raw_id (dc_name (df_prototype d))).
      set (fs0 := Memory_stack_frame_stack (state_memory_stack σ2_in)).
      eapply s1_cps_cfg_bind with
        (RA := fun U' '(s1', _) '(s2', _) =>
                 U' = U0 /\
                 s1' = (σ1_in, ((sf_c1, fstk_c1), g0)) /\
                 s2' = (σ2_in, ((sf_c2, fstk_c2), g0))).
      - apply refine_prov_to_s1_cps.
        eapply refine_cfg_EOU; [apply refine_EOU_refl |].
        intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
      - intros U_cc s1_cc _ s2_cc _ _ (-> & -> & ->).
        eapply s1_cps_cfg_bind.
        + apply refine_prov_to_s1_cps.
          exact (apply_args_attrs_stage1_cfg_sim ctx1 ctx2 args_attrs
                   ("Argument of " ++ fname ++ " violates noundef.")%string
                   args U0 P0 G σ1_in σ2_in
                   ((sf_c1, fstk_c1), g0) ((sf_c2, fstk_c2), g0) Hinv0).
        + intros U_aa s1_aa args1 s2_aa args2 _ (-> & -> & -> & <-).
          eapply s1_cps_cfg_bind.
          * apply refine_prov_to_s1_cps.
            exact (push_call_frame_stage1_sim ctx1 ctx2 d d args1 U0 P0 G
                     σ1_in σ2_in sf_c1 sf_c2 fstk_c1 fstk_c2 g0 Logic.eq_refl Hinv0).
          * intros U_pf s1_pf varg1 s2_pf varg2 _
              (pr_va & bs & vs & σ1_pf & σ2_pf & Hnin_va & -> & <- & Ecomb & -> & -> & Hinv_pf & Htf_pf).
            fold fs0 in Htf_pf.
            set (sf0 := {| stack_vars := init_local_env bs;
                           stack_exc  := None;
                           stack_loc  := Some ""%string |}).
            set (fstk1 := sf_c1 :: fstk_c1).
            set (fstk2 := sf_c2 :: fstk_c2).
            assert (Hgenv_pf : genv_safe (pr_va :: P0) g0)
              by (apply (genv_safe_incl P0 (pr_va :: P0) g0 (fun x Hx => or_intror Hx) Hgenv0)).
            assert (Hsafe_sf0 :
                      safe_locals_env (pr_va :: P0)
                        (m2r_collect_unique_allocas
                           (df_args d ++ flat_map full_block_defs (blks (df_instrs d)))
                           (blks (df_instrs d)))
                        (stack_vars sf0))
              by (exact (proj2 (safe_locals_env_init_args (pr_va :: P0) (df_args d) (blks (df_instrs d))
                                  _ args1 bs vs Ecomb (fun _ H => H)))).
            eapply s1_cps_cfg_bind with
              (RA := exc_post
                       (s1_unprom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                       (fun U_e s1_e s2_e v1 v2 =>
                          v1 = v2 /\
                          s1_unprom_exit_rel fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2 U_e s1_e s2_e)).
            -- change (interp_cfg_model ctx1
                         (run_exc (denote_cfg_map (ocfg_map (blks (df_instrs d))) (df_instrs d) (Some varg1)))
                         (σ1_pf, ((sf0, fstk1), g0)))
                 with (interp_cfg_exc ctx1
                         (denote_cfg_map (ocfg_map (blks (df_instrs d))) (df_instrs d) (Some varg1))
                         (σ1_pf, ((sf0, fstk1), g0))).
               change (interp_cfg_model ctx2
                         (run_exc (denote_cfg_map (ocfg_map (blks (df_instrs d))) (df_instrs d) (Some varg1)))
                         (σ2_pf, ((sf0, fstk2), g0)))
                 with (interp_cfg_exc ctx2
                         (denote_cfg_map (ocfg_map (blks (df_instrs d))) (df_instrs d) (Some varg1))
                         (σ2_pf, ((sf0, fstk2), g0))).
               unfold denote_cfg_map.
               eapply s1_cps_cfg_exc_bind with
                 (RA := s1_unprom_rret fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2).
               ++ rewrite !denote_ocfg_map_eq_iter.
                  intros k_o1 k_o2 Hk_o.
                  assert (Hli0 :
                            s1_unprom_loop_inv d fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2
                              (pr_va :: U0) (σ1_pf, ((sf0, fstk1), g0)) (σ2_pf, ((sf0, fstk2), g0))
                              (init (df_instrs d), init (df_instrs d))).
                  { split; [apply incl_refl |].
                    exists (pr_va :: P0), σ1_pf, σ2_pf, sf0.
                    exact (conj (incl_refl _)
                             (conj Logic.eq_refl (conj Logic.eq_refl
                                (conj Hinv_pf (conj Htf_pf (conj Hgenv_pf Hsafe_sf0)))))). }
                  eapply (s1_iter_one_step
                            (s1_unprom_loop_inv d fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                            (s1_unprom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                            (s1_unprom_rret fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                            (ocfg_step_body (ocfg_map (blks (df_instrs d))) (Some varg1))
                            (ocfg_step_body (ocfg_map (blks (df_instrs d))) (Some varg1))
                            (pr_va :: U0) _ _ (init (df_instrs d), init (df_instrs d)) k_o1 k_o2).
                  ** exact (s1_unprom_block_body_cps d (Some varg1) fs0
                              (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2
                              (pr_va :: U0) _ _ _ Hd Hli0).
                  ** intros U' s1' s2' j' _ Hli'; apply s1_lfp_fold; right; left.
                     exists d, (Some varg1), fs0, (pr_va :: U0), (pr_va :: P0), G,
                            fstk1, fstk2, s1', s2', j', k_o1, k_o2.
                     rewrite !denote_ocfg_map_eq_iter.
                     refine (conj Hd (conj Hli' (conj Hk_o (conj _ _)))); reflexivity.
                  ** exact Hk_o.
               ++ intros U_ocfg s1_ocfg r_ocfg1 s2_ocfg r_ocfg2 _ [<- Hexit_ocfg].
                  destruct r_ocfg1 as [bid_miss | uv_ret].
                  ** apply refine_prov_to_s1_cps, refine_cfg_exc_raise_both.
                  ** apply refine_prov_to_s1_cps, refine_cfg_exc_ret;
                       exact (conj Logic.eq_refl Hexit_ocfg).
            -- intros U_rv s1_rv rv1 s2_rv rv2 _ Hrv_post.
               assert (Hrv_unif :
                         rv1 = rv2 /\
                         s1_unprom_exit_rel fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2 U_rv s1_rv s2_rv).
               { destruct rv1 as [ex1 | v1], rv2 as [ex2 | v2]; cbn [exc_post] in Hrv_post;
                   try contradiction;
                   destruct Hrv_post as [<- Hpost_r]; exact (conj Logic.eq_refl Hpost_r). }
               clear Hrv_post.
               destruct Hrv_unif as [<- (HincU_rv & P_e & σ1_e & σ2_e & sf1_e & sf2_e &
                                         HincP_e & -> & -> & Hinv_e & Htf_e & Hgenv_e)].
               eapply s1_cps_cfg_bind.
               ++ apply refine_prov_to_s1_cps.
                  exact (pop_call_frame_stage1_unprom_sim ctx1 ctx2 fs0 U_rv P_e G
                           σ1_e σ2_e sf1_e sf_c1 sf2_e sf_c2 fstk_c1 fstk_c2 g0 Hinv_e Htf_e).
               ++ intros U_pop s1_pop _ s2_pop _ _
                    (σ1_pop & σ2_pop & -> & _ & _ & -> & -> & Hinv_pop & Hfs_pop).
                  apply refine_prov_to_s1_cps; eapply refine_prov_weaken.
                  ** exact (check_call_return_stage1_cfg_sim ctx1 ctx2
                              (dc_attrs (df_prototype d)) ret_attrs None fname args1 rv1
                              U_rv P_e G σ1_pop σ2_pop
                              ((sf_c1, fstk_c1), g0) ((sf_c2, fstk_c2), g0) Hinv_pop).
                  ** intros U_f [s1_f rf1] [s2_f rf2] (-> & -> & -> & <-).
                     exists P_e, σ1_pop, σ2_pop.
                     exact (conj (fun x Hx => HincU_rv x (or_intror Hx))
                              (conj (fun x Hx => HincP_e x (or_intror Hx))
                                 (conj Logic.eq_refl
                                    (conj Logic.eq_refl
                                       (conj Logic.eq_refl
                                          (conj Hinv_pop (conj Hfs_pop Hgenv_e))))))).
    Qed.

    Local Lemma s1_prom_block_body_cps
      (sp : s1_prom_static)
      (va : option (@ptr ProvenanceV (@PointerV IP)))
      (fs0 : @Framestack (@ParamsV IP IPT))
      (U0 P0 : list N) (G : list ghost_slot)
      (fstk1 fstk2 : stack)
      (U : list N) (s1 s2 : FusedS) (j : block_id * block_id)
      (Hwf : s1_prom_static_wf sp)
      (Hli : s1_prom_loop_inv sp fs0 U0 P0 G fstk1 fstk2 U s1 s2 j) :
      s1_cps s1_lfp
        (exc_post (s1_prom_rexc fs0 U0 P0 G fstk1 fstk2)
           (fun U' s1' s2' lr1 lr2 =>
              match lr1, lr2 with
              | inl j1, inl j2 =>
                  j1 = j2 /\ s1_prom_loop_inv sp fs0 U0 P0 G fstk1 fstk2 U' s1' s2' j1
              | inr v1, inr v2 =>
                  s1_prom_rret fs0 U0 P0 G fstk1 fstk2 U' s1' s2' v1 v2
              | _, _ => False
              end))
        U
        (interp_cfg_exc ctx1 (ocfg_step_body (ocfg_map (blks (sps_c sp))) va j) s1)
        (interp_cfg_exc ctx2 (ocfg_step_body (ocfg_map (sps_blks' sp)) va j) s2).
    Proof using.
      set (c := sps_c sp) in *.
      set (fargs := sps_fargs sp) in *.
      set (p := sps_p sp) in *.
      set (dt := sps_dt sp) in *.
      set (init_reg := sps_init_reg sp) in *.
      set (avoid0 := sps_avoid0 sp) in *.
      set (safe_no_p := sps_safe_no_p sp) in *.
      set (end_map := sps_end_map sp) in *.
      unfold s1_prom_static_wf in Hwf; fold c p dt safe_no_p avoid0 in Hwf.
      destruct Hwf as (Hnd_bks & Hno_entry_pred & _ & _ & Hsc & Hbks_other & Hbks_p1 & Hall_p1).
      unfold s1_prom_loop_inv in Hli; fold c p dt init_reg avoid0 safe_no_p end_map in Hli.
      destruct Hli as (Hne_bs & HincU_l & (b_pred & Hin_pred & Hid_pred & Hsucc_pred) &
                       P_l & gs_l & σ1_l & σ2_l & sf1_l & sf2_l &
                       HincP_l & Hdt_l & Hlk_p_l & Hlk_end_l & -> & -> &
                       Hinv_l & Htf_l & Hgenv_l & Hsafe_l & Hvars_l).
      assert (Hsub_safe : forall q,
                In q safe_no_p ->
                In q (m2r_collect_unique_allocas (fargs ++ flat_map full_block_defs (blks c)) (blks c))).
      { intros q Hq; unfold safe_no_p, sps_safe_no_p in Hq; cbn zeta in Hq; fold fargs c p in Hq.
        apply filter_In in Hq as [Hq _]; exact Hq. }
      assert (Hsafe_av0 : incl safe_no_p avoid0)
        by (intros q Hq; unfold avoid0, sps_avoid0; fold fargs c; apply safe_locals_in_avoid0, Hsub_safe, Hq).
      assert (Hblk_uses_av0 : forall bk x, In bk (blks c) -> In x (full_block_uses bk) -> In x avoid0)
        by (intros bk x Hbk Hx; unfold avoid0, sps_avoid0; fold fargs c;
            apply in_app_iff; right; exact (in_uses_in_cfg_all_ids c bk x Hbk Hx)).
      assert (Hblk_defs_av0 : forall bk x, In bk (blks c) -> In x (full_block_defs bk) -> In x avoid0)
        by (intros bk x Hbk Hx; unfold avoid0, sps_avoid0; fold fargs c;
            apply in_app_iff; right; exact (in_defs_in_cfg_all_ids c bk x Hbk Hx)).
      assert (Hnd_end_map : NoDup (List.map fst end_map))
        by (unfold end_map, sps_end_map; rewrite pass1_end_map_fst, Hbks_p1; exact Hnd_bks).
      pose proof (pass1_find_block_spec (init c) dt init_reg (blks c) (sps_pass1 sp) Hbks_p1)
        as [Hfb_none Hfb_some]; cbv zeta in Hfb_none, Hfb_some; fold end_map in Hfb_some.
      destruct j as [bf2 bs2]; cbn [fst snd] in *.
      unfold ocfg_step_body, sps_blks'; fold c dt init_reg.
      cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      rewrite !ScopeTheory.ocfg_map_find_block.
      destruct (find_block (blks c) bs2) as [bk_cur |] eqn:Efind_cur.
      - destruct (m2r_find_block_some_inv (blks c) bs2 bk_cur Efind_cur) as [Hin_cur Hid_cur].
        destruct (Hfb_some bs2 bk_cur Efind_cur)
          as (phi_r & cd_cur' & end_r & Hin_p1_cur & Efind_cur').
        rewrite Efind_cur'.
        pose proof (Hall_p1 bk_cur phi_r cd_cur' end_r Hin_p1_cur)
          as (Hphi_nin0 & Hend_nin0 & Hcur_p1_spec).
        destruct (raw_id_eqb (blk_id bk_cur) (init c)) eqn:Ecur_id; [apply raw_id_eqb_spec in Ecur_id; rename Ecur_id into Hbad | apply raw_id_eqb_neq in Ecur_id; rename Ecur_id into Hne_cur_id];
          [exfalso; congruence |].
        destruct Hcur_p1_spec as (av_in & av_out & Hinc_avin & Erw_cur).
        destruct (Hbks_other bk_cur Hin_cur Hne_cur_id) as [Hbk_cur_chk Hp_nd_bk_cur].
        unfold check_block_non_entry_for_slot in Hbk_cur_chk.
        rewrite !andb_true_iff, !negb_true_iff in Hbk_cur_chk.
        destruct Hbk_cur_chk as (((Hphi_np & Hcd_cur) & Htm_np) & Hni_cur).
        apply in_raw_ids_false in Hphi_np; apply in_raw_ids_false in Htm_np.
        set (preds_cur := List.filter (fun b_p => in_raw_ids (blk_id bk_cur) (m2r_block_succs b_p)) (blks c)).
        set (inc_cur := List.map (fun b_p => (blk_id b_p, @EXP_Ident dtyp (ID_Local (lookup_end_reg end_map (blk_id b_p) init_reg)))) preds_cur).
        assert (Hassoc_cur :
                  assoc bf2 inc_cur =
                  Some (EXP_Ident (ID_Local (lookup_end_reg end_map bf2 init_reg)))).
        { apply m2r_assoc_nodup.
          - unfold inc_cur; rewrite map_map; cbn [fst].
            exact (m2r_nodup_map_filter blk_id _ (blks c) Hnd_bks).
          - unfold inc_cur; rewrite <- Hid_pred at 1 2.
            apply (in_map (fun b_p => (blk_id b_p, @EXP_Ident dtyp (ID_Local (lookup_end_reg end_map (blk_id b_p) init_reg))))).
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
        eapply s1_cps_cfg_exc_bind with
          (RA := fun U_bd s1_bd s2_bd bd1 bd2 =>
                   exists (P_cd : list N) gs_cd σ1_cd σ2_cd
                          (sf1_cd sf2_cd : @stack_frame (@ParamsV IP IPT)),
                     incl U0 U_bd /\
                     incl P0 P_cd /\
                     bd1 = bd2 /\
                     s1_bd = (σ1_cd, ((sf1_cd, fstk1), g0)) /\
                     s2_bd = (σ2_cd, ((sf2_cd, fstk2), g0)) /\
                     gs_dt gs_cd = dt /\
                     Maps.lookup p (stack_vars sf1_cd) =
                       Some (@DVALUE_Base (@ParamsV IP IPT) (@DVALUE_Pointer (@ParamsV IP IPT) (gs_pt gs_cd))) /\
                     lookup_end_reg end_map bs2 init_reg = end_r /\
                     Maps.lookup end_r (stack_vars sf2_cd) =
                       Some (@DVALUE_Base (@ParamsV IP IPT) (gs_db gs_cd)) /\
                     stage1_mem_inv U_bd P_cd (gs_cd :: G) σ1_cd σ2_cd /\
                     top_frame_prom_from fs0 gs_cd G (state_memory_stack σ2_cd) /\
                     genv_safe P_cd g0 /\
                     safe_locals_env P_cd safe_no_p (stack_vars sf2_cd) /\
                     (forall x, In x avoid0 -> x <> p ->
                        Maps.lookup x (stack_vars sf1_cd) = Maps.lookup x (stack_vars sf2_cd)) /\
                     match bd1 with
                     | inl bid_target => In bid_target (m2r_block_succs bk_cur)
                     | inr _ => True
                     end).
        + eapply s1_cps_cfg_exc_bind.
          * apply refine_prov_to_s1_cps.
            exact (denote_phis_stage1_prom_sim ctx1 ctx2
                     (s1_prom_rexc fs0 U0 P0 G fstk1 fstk2)
                     bf2 phi_r (lookup_end_reg end_map bf2 init_reg)
                     dt inc_cur (blk_phis bk_cur) (DVALUE_Base (gs_db gs_l))
                     U σ1_l σ2_l sf1_l sf2_l fstk1 fstk2 g0
                     Hassoc_cur Hlk_end_l Hphi_vars).
          * intros U_ph s1_ph _ s2_ph _ _ (dvs & -> & _ & _ & Hfst_dvs & -> & ->).
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
            eapply s1_cps_cfg_exc_bind.
            -- exact (s1_rewrite_code_exc_cps
                        (s1_prom_rexc fs0 U0 P0 G fstk1 fstk2)
                        avoid0 fargs (blks c) bk_cur [] (blk_code bk_cur) []
                        safe_no_p p dt phi_r av_in cd_cur' end_r av_out
                        va va fs0 U P_l gs_l G σ1_l σ2_l
                        (upd_local_sf sf1_l (write_phi_dvs dvs (stack_vars sf1_l)))
                        (upd_local_sf sf2_l (write_phi_dvs ((phi_r, DVALUE_Base (gs_db gs_l)) :: dvs) (stack_vars sf2_l)))
                        fstk1 fstk2
                        Hnd_bks Hin_cur Hsplit_cur Hsub_safe Hsafe_av0
                        Huses_cur Hdefs_cur Hp_nd_cd_cur Hcd_cur Erw_cur
                        Hinc_avin Hphi_nin0 Hsc
                        (fun U_x P_x gs_x σ1_x σ2_x sf1_x sf2_x ex H1 H2 H3 H4 H5 =>
                           conj Logic.eq_refl
                             (conj (incl_tran HincU_l H1)
                                (ex_intro _ P_x (ex_intro _ σ1_x (ex_intro _ σ2_x
                                   (ex_intro _ sf1_x (ex_intro _ sf2_x
                                      (conj (incl_tran HincP_l H2)
                                         (conj Logic.eq_refl (conj Logic.eq_refl
                                            (conj H5 (or_intror (ex_intro _ gs_x (conj H3 H4))))))))))))))
                        Hdt_l Hlk_p_ph Hlk_phi_ph Hinv_l Htf_l Hgenv_l Hsafe_ph Hvars_ph).
            -- intros U_cd s1_cd _ s2_cd _ _
                 (P_cd & gs_cd & σ1_cd & σ2_cd & sf1_cd & sf2_cd &
                  HincU_cd & HincP_cd & _ & _ & Hdt_cd & Hlk_p_cd & Hlk_er_cd &
                  -> & -> & Hinv_cd & Htf_cd & Hgenv_cd & Hsafe_cd & Hvars_cd).
               assert (HincU_c : incl U0 U_cd) by (exact (incl_tran HincU_l HincU_cd)).
               assert (HincP_c : incl P0 P_cd) by (exact (incl_tran HincP_l HincP_cd)).
               assert (Hlk_end_cur : lookup_end_reg end_map bs2 init_reg = end_r).
               { apply lookup_end_reg_in_nodup; [exact Hnd_end_map |].
                 unfold end_map, sps_end_map; rewrite <- Hid_cur.
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
               apply refine_prov_to_s1_cps; eapply refine_prov_weaken.
               ++ apply (denote_non_invoke_term_exc_sim ctx1 ctx2
                           (s1_prom_rexc fs0 U0 P0 G fstk1 fstk2)
                           iid_tc iid_tc tm_cur md_tc md_tc
                           U_cd σ1_cd σ2_cd sf1_cd sf2_cd fstk1 fstk2 g0
                           Hni_cur Htm_vars).
                  intros ex; refine (conj Logic.eq_refl (conj HincU_c _)).
                  exists P_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd.
                  exact (conj HincP_c (conj Logic.eq_refl (conj Logic.eq_refl
                           (conj Hgenv_cd (or_intror (ex_intro _ gs_cd (conj Hinv_cd Htf_cd))))))).
               ++ intros U_t [s1_t res1_t] [s2_t res2_t].
                  destruct res1_t as [ex1 | bd1], res2_t as [ex2 | bd2]; cbn [exc_post];
                    try (intros H; exact H).
                  intros (-> & -> & -> & <- & Hsucc_cur).
                  destruct bd1 as [bid_t | dv_t];
                    [cbn in Hsucc_cur |- *; unfold m2r_block_succs; rewrite Etm_cur |];
                  exists P_cd, gs_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd;
                  exact (conj HincU_c (conj HincP_c (conj Logic.eq_refl (conj Logic.eq_refl
                           (conj Logic.eq_refl (conj Hdt_cd (conj Hlk_p_cd
                             (conj Hlk_end_cur (conj Hlk_er_cd (conj Hinv_cd
                               (conj Htf_cd (conj Hgenv_cd (conj Hsafe_cd
                                 (conj Hvars_cd Hsucc_cur)))))))))))))).
        + intros U_bd s1_bd bd1 s2_bd bd2 _
            (P_cd & gs_cd & σ1_cd & σ2_cd & sf1_cd & sf2_cd &
             HincU_c & HincP_c & <- & -> & -> & Hdt_cd & Hlk_p_cd & Hlk_end_cur &
             Hlk_er_cd & Hinv_cd & Htf_cd & Hgenv_cd & Hsafe_cd & Hvars_cd & Hsucc_cur).
          destruct bd1 as [bid_tgt | dv_cur].
          * apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
            assert (Hsucc_bk_cur : In bid_tgt (m2r_block_succs bk_cur))
              by exact Hsucc_cur.
            assert (Hne_tgt : bid_tgt <> init c).
            { intros Heq_t; apply Hno_entry_pred; rewrite <- Heq_t.
              unfold m2r_all_succs; apply in_flat_map; exists bk_cur; split; assumption. }
            refine (conj Logic.eq_refl (conj Hne_tgt (conj HincU_c (conj _ _)))).
            -- exists bk_cur; exact (conj Hin_cur (conj Hid_cur Hsucc_bk_cur)).
            -- exists P_cd, gs_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd; cbn [fst]; fold end_map init_reg.
               rewrite Hlk_end_cur.
               exact (conj HincP_c (conj Hdt_cd (conj Hlk_p_cd (conj Hlk_er_cd
                        (conj Logic.eq_refl (conj Logic.eq_refl
                          (conj Hinv_cd (conj Htf_cd (conj Hgenv_cd (conj Hsafe_cd Hvars_cd)))))))))).
          * apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
            refine (conj Logic.eq_refl (conj HincU_c _)).
            exists P_cd, σ1_cd, σ2_cd, sf1_cd, sf2_cd.
            exact (conj HincP_c (conj Logic.eq_refl (conj Logic.eq_refl
                     (conj Hgenv_cd (or_intror (ex_intro _ gs_cd (conj Hinv_cd Htf_cd))))))).
      - rewrite (Hfb_none bs2 Efind_cur).
        apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
        refine (conj Logic.eq_refl (conj HincU_l _)).
        exists P_l, σ1_l, σ2_l, sf1_l, sf2_l.
        exact (conj HincP_l (conj Logic.eq_refl (conj Logic.eq_refl
                 (conj Hgenv_l (or_intror (ex_intro _ gs_l (conj Hinv_l Htf_l))))))).
    Qed.

    Local Lemma s1_prom_denote_function_cps
      (df df' : definition dtyp (CFG.cfg dtyp))
      (cc : cconv) (args : list (@dvalue (@ParamsV IP IPT)))
      (U0 P0 : list N) (G : list ghost_slot)
      (σ1_in σ2_in : state)
      (ls1 ls2 : @stack_frame (@ParamsV IP IPT) * stack)
      (Htry : try_promote_slot_in_defn true df = Some df')
      (Hinv0 : stage1_mem_inv U0 P0 G σ1_in σ2_in)
      (Hgenv0 : genv_safe P0 g0) :
      s1_cps s1_lfp
        (s1_call_post U0 P0 G (Memory_stack_frame_stack (state_memory_stack σ2_in)) ls1 ls2)
        U0
        (interp_cfg_model ctx1 (denote_function df cc args) (σ1_in, (ls1, g0)))
        (interp_cfg_model ctx2 (denote_function df' cc args) (σ2_in, (ls2, g0))).
    Proof using.
      destruct ls1 as [sf_c1 fstk_c1], ls2 as [sf_c2 fstk_c2].
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
      destruct (find_promotable_in_init_code true all_defs all_uses safe_locals
                  (init c) (blks c) b_init [] (blk_code b_init))
        as [[[[[pre_al al_ins] post_al] p] dt] |] eqn:Efind_al;
        [| discriminate Htry].
      pose proof (find_promotable_in_init_code_inv true all_defs all_uses safe_locals
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
                args := CFG.args c |}).
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
      set (sp := {| sps_fargs    := fargs;
                    sps_c        := c;
                    sps_b_init   := b_init;
                    sps_p        := p;
                    sps_dt       := dt;
                    sps_init_reg := init_reg;
                    sps_end_reg0 := init_end_reg;
                    sps_code0'   := init_code';
                    sps_pass1    := pass1_out |}).
      assert (Hwf : s1_prom_static_wf sp).
      { unfold s1_prom_static_wf; cbn [sps_c sps_b_init sps_p sps_dt sps_pass1 sps_code0' sps_end_reg0].
        unfold sps_safe_no_p, sps_avoid0; cbn [sps_fargs sps_c sps_p]; fold all_defs safe_locals safe_no_p avoid0.
        refine (conj Hnd_bks (conj Hno_entry_pred (conj Hin_init (conj Hid_init (conj Hsc (conj _ (conj Hbks_p1 Hall_p1))))))).
        intros bk Hbk Hne; split.
        - pose proof Ebks_chk as Hb; rewrite forallb_forall in Hb; specialize (Hb bk Hbk).
          destruct (raw_id_eqb (blk_id bk) (init c)) eqn:Ebad; [apply raw_id_eqb_spec in Ebad; rename Ebad into Hbad | clear Ebad]; [exfalso; exact (Hne Hbad) | exact Hb].
        - exact (Hp_nd_other bk Hbk (fun Heq => Hne (eq_trans Heq Hid_init))). }
      set (end_map := sps_end_map sp).
      assert (Hnd_end_map : NoDup (List.map fst end_map))
        by (unfold end_map, sps_end_map, sp; cbn [sps_pass1]; rewrite pass1_end_map_fst, Hbks_p1; exact Hnd_bks).
      pose proof (pass1_find_block_spec (init c) dt init_reg (blks c) pass1_out Hbks_p1)
        as [_ Hfb_some]; cbv zeta in Hfb_some; fold end_map in Hfb_some.
      unfold denote_function; cbn [df_prototype df_args df_instrs]; fold fargs c c'.
      destruct (dc_param_attrs (df_prototype df)) as [ret_attrs args_attrs].
      set (fname := show_raw_id (dc_name (df_prototype df))).
      set (fs0 := Memory_stack_frame_stack (state_memory_stack σ2_in)).
      eapply s1_cps_cfg_bind with
        (RA := fun U' '(s1', _) '(s2', _) =>
                 U' = U0 /\
                 s1' = (σ1_in, ((sf_c1, fstk_c1), g0)) /\
                 s2' = (σ2_in, ((sf_c2, fstk_c2), g0))).
      - apply refine_prov_to_s1_cps.
        eapply refine_cfg_EOU; [apply refine_EOU_refl |].
        intros [] [] _; exact (conj Logic.eq_refl (conj Logic.eq_refl Logic.eq_refl)).
      - intros U_cc s1_cc _ s2_cc _ _ (-> & -> & ->).
        eapply s1_cps_cfg_bind.
        + apply refine_prov_to_s1_cps.
          exact (apply_args_attrs_stage1_cfg_sim ctx1 ctx2 args_attrs
                   ("Argument of " ++ fname ++ " violates noundef.")%string
                   args U0 P0 G σ1_in σ2_in
                   ((sf_c1, fstk_c1), g0) ((sf_c2, fstk_c2), g0) Hinv0).
        + intros U_aa s1_aa args1 s2_aa args2 _ (-> & -> & -> & <-).
          eapply s1_cps_cfg_bind.
          * apply refine_prov_to_s1_cps.
            exact (push_call_frame_stage1_sim ctx1 ctx2 df
                     {| df_prototype := df_prototype df; df_args := fargs; df_instrs := c' |}
                     args1 U0 P0 G σ1_in σ2_in sf_c1 sf_c2 fstk_c1 fstk_c2 g0
                     Logic.eq_refl Hinv0).
          * intros U_pf s1_pf varg1 s2_pf varg2 _
              (pr_va & bs & vs & σ1_pf & σ2_pf & Hnin_va & -> & <- & Ecomb & -> & -> & Hinv_pf & Htf_pf).
            fold fs0 in Htf_pf.
            set (sf0 := {| stack_vars := init_local_env bs;
                           stack_exc  := None;
                           stack_loc  := Some ""%string |}).
            set (fstk1 := sf_c1 :: fstk_c1).
            set (fstk2 := sf_c2 :: fstk_c2).
            assert (Hgenv_pf : genv_safe (pr_va :: P0) g0)
              by (apply (genv_safe_incl P0 (pr_va :: P0) g0 (fun x Hx => or_intror Hx) Hgenv0)).
            assert (Hsafe_sf0 : safe_locals_env (pr_va :: P0) safe_no_p (stack_vars sf0))
              by (exact (proj2 (safe_locals_env_init_args (pr_va :: P0) fargs (blks c) safe_no_p
                                  args1 bs vs Ecomb Hsub_safe))).
            eapply s1_cps_cfg_bind with
              (RA := exc_post
                       (s1_prom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                       (fun U_e s1_e s2_e v1 v2 =>
                          v1 = v2 /\
                          s1_prom_exit_rel fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2 U_e s1_e s2_e)).
            -- change (interp_cfg_model ctx1
                         (run_exc (denote_cfg_map (ocfg_map (blks c)) c (Some varg1)))
                         (σ1_pf, ((sf0, fstk1), g0)))
                 with (interp_cfg_exc ctx1
                         (denote_cfg_map (ocfg_map (blks c)) c (Some varg1))
                         (σ1_pf, ((sf0, fstk1), g0))).
               change (interp_cfg_model ctx2
                         (run_exc (denote_cfg_map (ocfg_map (blks c')) c' (Some varg1)))
                         (σ2_pf, ((sf0, fstk2), g0)))
                 with (interp_cfg_exc ctx2
                         (denote_cfg_map (ocfg_map (blks c')) c' (Some varg1))
                         (σ2_pf, ((sf0, fstk2), g0))).
               unfold denote_cfg_map; rewrite Hc'_eq; cbn [init blks].
               change (build_promoted_blocks (init c) dt init_reg (blks c) pass1_out)
                 with (sps_blks' sp).
               eapply s1_cps_cfg_exc_bind with
                 (RA := s1_prom_rret fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2).
               ++ rewrite !denote_ocfg_map_eq_iter.
                  intros k_o1 k_o2 Hk_o.
                  eapply (s1_iter_one_step
                            (s1_prom_loop_inv sp fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                            (s1_prom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                            (s1_prom_rret fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                            (ocfg_step_body (ocfg_map (blks c)) (Some varg1))
                            (ocfg_step_body (ocfg_map (sps_blks' sp)) (Some varg1))
                            (pr_va :: U0)
                            (σ1_pf, ((sf0, fstk1), g0))
                            (σ2_pf, ((sf0, fstk2), g0))
                            (init c, init c) k_o1 k_o2).
                  ** destruct (Hfb_some (init c) b_init Efind_init)
                       as (phi_init & cd_init & end_init & Hin_p1_init & Efind_init').
                     pose proof (Hall_p1 b_init phi_init cd_init end_init Hin_p1_init)
                       as (_ & _ & Hinit_p1_spec).
                     rewrite Hid_init, raw_id_eqb_refl in Hinit_p1_spec, Efind_init'.
                     destruct Hinit_p1_spec as [-> ->].
                     assert (Hlk_end_init : lookup_end_reg end_map (init c) init_reg = init_end_reg).
                     { apply lookup_end_reg_in_nodup; [exact Hnd_end_map |].
                       unfold end_map, sps_end_map; cbn [sps_pass1]; rewrite <- Hid_init.
                       exact (in_map (fun '(bk, _, _, er) => (blk_id bk, er)) _ _ Hin_p1_init). }
                     unfold ocfg_step_body, sps_blks', sp; cbn [sps_c sps_dt sps_init_reg sps_pass1 ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
                     rewrite ScopeTheory.ocfg_map_find_block, Efind_init.
                     rewrite ScopeTheory.ocfg_map_find_block, Efind_init'.
                     unfold denote_block; cbn [blk_phis blk_code blk_term]; rewrite Ephis_init.
                     eapply s1_cps_obs_eq;
                       [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                                           (eq_itree_bind_congr_l
                                              (eq_itree_bind_congr_l (denote_phis_nil_eq (init c)))))
                       | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _
                                            (eq_itree_bind_congr_l
                                               (eq_itree_bind_congr_l (denote_phis_nil_eq (init c))))) |].
                     eapply s1_cps_obs_eq;
                       [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_bind _ _ _))
                       | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
                     eapply s1_cps_obs_eq;
                       [symmetry; apply interp_cfg_exc_obs_eq, Eqit.bind_ret_l
                       | symmetry; apply interp_cfg_exc_obs_eq, Eqit.bind_ret_l |].
                     rewrite Hsplit_init; unfold init_code'.
                     eapply s1_cps_cfg_exc_bind with
                       (RA := fun U_b1 s1_b1 s2_b1 bd1 bd2 =>
                                exists (P_b1 : list N) gs_b1 σ1_b1 σ2_b1
                                       (sf1_b1 sf2_b1 : @stack_frame (@ParamsV IP IPT)),
                                  incl (pr_va :: U0) U_b1 /\
                                  incl (pr_va :: P0) P_b1 /\
                                  bd1 = bd2 /\
                                  s1_b1 = (σ1_b1, ((sf1_b1, fstk1), g0)) /\
                                  s2_b1 = (σ2_b1, ((sf2_b1, fstk2), g0)) /\
                                  gs_dt gs_b1 = dt /\
                                  Maps.lookup p (stack_vars sf1_b1) =
                                    Some (@DVALUE_Base (@ParamsV IP IPT) (@DVALUE_Pointer (@ParamsV IP IPT) (gs_pt gs_b1))) /\
                                  Maps.lookup init_end_reg (stack_vars sf2_b1) =
                                    Some (@DVALUE_Base (@ParamsV IP IPT) (gs_db gs_b1)) /\
                                  stage1_mem_inv U_b1 P_b1 (gs_b1 :: G) σ1_b1 σ2_b1 /\
                                  top_frame_prom_from fs0 gs_b1 G (state_memory_stack σ2_b1) /\
                                  genv_safe P_b1 g0 /\
                                  safe_locals_env P_b1 safe_no_p (stack_vars sf2_b1) /\
                                  (forall x, In x avoid0 -> x <> p ->
                                     Maps.lookup x (stack_vars sf1_b1) = Maps.lookup x (stack_vars sf2_b1)) /\
                                  match bd1 with
                                  | inl bid_target => In bid_target (m2r_block_succs b_init)
                                  | inr _ => True
                                  end).
                     --- eapply s1_cps_obs_eq;
                           [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _
                                               (eq_itree_bind_congr_l (denote_code_app_eq pre_al _ (Some varg1))))
                           | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _
                                                (eq_itree_bind_congr_l (denote_code_app_eq pre_al _ (Some varg1)))) |].
                         eapply s1_cps_obs_eq;
                           [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_bind _ _ _))
                           | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
                         eapply s1_cps_cfg_exc_bind.
                         +++ assert (Hsplit_pre :
                                       blk_code b_init = [] ++ pre_al ++ (IId p, INSTR_Alloca dt anns_al, md_al) :: post_al)
                               by exact Hsplit_init.
                             exact (s1_other_code_exc_cps
                                      (s1_prom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                                      (fun s => top_frame_unprom_from fs0 G (state_memory_stack s))
                                      fargs (blks c) b_init [] pre_al
                                      ((IId p, INSTR_Alloca dt anns_al, md_al) :: post_al)
                                      safe_no_p p (Some varg1) (Some varg1)
                                      (pr_va :: U0) (pr_va :: P0) G σ1_pf σ2_pf sf0 sf0 fstk1 fstk2
                                      Hnd_bks Hin_init Hsplit_pre Hsub_safe Hpre_chk
                                      (fun s_a s_b Heq_fs HT => top_frame_unprom_frame_eq fs0 G _ _ (eq_sym Heq_fs) HT)
                                      (fun s_a s_b ptrs Hdisj Heq_fs HT =>
                                         top_frame_unprom_frame_eq fs0 G _ _ (eq_sym Heq_fs)
                                           (top_frame_unprom_add_ptrs fs0 G ptrs _ HT Hdisj))
                                      (fun U_x P_x σ1_x σ2_x sf1_x sf2_x ex H1 H2 H3 H4 H5 =>
                                         conj Logic.eq_refl
                                           (conj H1
                                              (ex_intro _ P_x (ex_intro _ σ1_x (ex_intro _ σ2_x
                                                 (ex_intro _ sf1_x (ex_intro _ sf2_x
                                                    (conj H2
                                                       (conj Logic.eq_refl (conj Logic.eq_refl
                                                          (conj H5 (or_introl (conj H3 H4)))))))))))))
                                      Hinv_pf Htf_pf Hgenv_pf Hsafe_sf0 (fun _ _ => Logic.eq_refl)).
                         +++ intros U_pre s1_pre _ s2_pre _ _
                               (P_pre & σ1_pre & σ2_pre & sf1_pre & sf2_pre &
                                HincU_pre & HincP_pre & _ & _ & -> & -> &
                                Hinv_pre & Htf_pre & Hgenv_pre & Hsafe_pre & _ & Heq_sf_pre).
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
                             eapply s1_cps_obs_eq;
                               [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (eq_itree_bind_congr_l Econs_l))
                               | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (eq_itree_bind_congr_l Econs_r)) |].
                             eapply s1_cps_obs_eq;
                               [symmetry; apply (interp_cfg_exc_obs_eq ctx1 _ _ _ (Eqit.bind_bind _ _ _))
                               | symmetry; apply (interp_cfg_exc_obs_eq ctx2 _ _ _ (Eqit.bind_bind _ _ _)) |].
                             eapply s1_cps_cfg_exc_bind.
                             *** apply refine_prov_to_s1_cps.
                                 exact (stage1_prom_alloca_init_exc_sim ctx1 ctx2
                                          (s1_prom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                                          p init_reg dt anns_al md_al (Some varg1) (Some varg1)
                                          fs0 U_pre P_pre G σ1_pre σ2_pre sf2_pre sf2_pre fstk1 fstk2 g0
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
                                           Some (DVALUE_Base (gs_db gs0)))
                                   by (rewrite Hdb0; cbn [Maps.lookup Maps.add Map_rmap]; apply RMF.F.add_eq_o; reflexivity).
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
                                                              (Maps.add p (DVALUE_Base (DVALUE_Pointer (gs_pt gs0))) (stack_vars sf2_pre))))
                                   by (intros x Hx _; cbn [Maps.lookup Maps.add Map_rmap]; symmetry;
                                       rewrite RMF.F.add_neq_o by (intros ->; exact (Hinit_nin0 Hx)); reflexivity).
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
                                 eapply s1_cps_cfg_exc_bind.
                                 ---- exact (s1_rewrite_code_exc_cps
                                               (s1_prom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                                               avoid0 fargs (blks c) b_init
                                               (pre_al ++ [(IId p, INSTR_Alloca dt anns_al, md_al)]) post_al []
                                               safe_no_p p dt init_reg avoid2 post_al' init_end_reg avoid3
                                               (Some varg1) (Some varg1) fs0 (gs_pr gs0 :: U_pre) P_pre gs0 G
                                               σ1_al σ2_al
                                               (upd_local_sf sf2_pre
                                                  (Maps.add p (@DVALUE_Base (@ParamsV IP IPT) (@DVALUE_Pointer (@ParamsV IP IPT) (gs_pt gs0))) (stack_vars sf2_pre)))
                                               (upd_local_sf sf2_pre
                                                  (Maps.add init_reg (@DVALUE_Base (@ParamsV IP IPT) DVALUE_Poison)
                                                     (Maps.add p (@DVALUE_Base (@ParamsV IP IPT) (@DVALUE_Pointer (@ParamsV IP IPT) (gs_pt gs0))) (stack_vars sf2_pre))))
                                               fstk1 fstk2
                                               Hnd_bks Hin_init Hsplit_post Hsub_safe Hsafe_av0
                                               Huses_post Hdefs_post Hp_nd_post Hpost_chk Erw_post
                                               Hinc_av2 Hinit_nin0 Hsc
                                               (fun U_x P_x gs_x σ1_x σ2_x sf1_x sf2_x ex H1 H2 H3 H4 H5 =>
                                                  conj Logic.eq_refl
                                                    (conj (incl_tran HincU_al H1)
                                                       (ex_intro _ P_x (ex_intro _ σ1_x (ex_intro _ σ2_x
                                                          (ex_intro _ sf1_x (ex_intro _ sf2_x
                                                             (conj (incl_tran HincP_pre H2)
                                                                (conj Logic.eq_refl (conj Logic.eq_refl
                                                                   (conj H5 (or_intror (ex_intro _ gs_x (conj H3 H4))))))))))))))
                                               Hdt0 Hlk_p_al Hlk_init_al
                                               Hinv_al Htf_al Hgenv_pre Hsafe_al Hvars_al).
                                 ---- intros U_post s1_post _ s2_post _ _
                                        (P_post & gs_post & σ1_post & σ2_post & sf1_post & sf2_post &
                                         HincU_post & HincP_post & _ & _ & Hdt_post & Hlk_p_post & Hlk_er_post &
                                         -> & -> & Hinv_post & Htf_post & Hgenv_post & Hsafe_post & Hvars_post).
                                      assert (HincU_p : incl (pr_va :: U0) U_post)
                                        by (exact (incl_tran HincU_al HincU_post)).
                                      assert (HincP_p : incl (pr_va :: P0) P_post)
                                        by (exact (incl_tran HincP_pre HincP_post)).
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
                                      apply refine_prov_to_s1_cps; eapply refine_prov_weaken.
                                      ++++ apply (denote_non_invoke_term_exc_sim ctx1 ctx2
                                                    (s1_prom_rexc fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2)
                                                    iid_tm iid_tm tm_init md_tm md_tm
                                                    U_post σ1_post σ2_post sf1_post sf2_post fstk1 fstk2 g0
                                                    Hni_init Htm_vars).
                                           intros ex; refine (conj Logic.eq_refl (conj HincU_p _)).
                                           exists P_post, σ1_post, σ2_post, sf1_post, sf2_post.
                                           exact (conj HincP_p (conj Logic.eq_refl (conj Logic.eq_refl
                                                    (conj Hgenv_post (or_intror (ex_intro _ gs_post (conj Hinv_post Htf_post))))))).
                                      ++++ intros U_t [s1_t res1_t] [s2_t res2_t].
                                           destruct res1_t as [ex1 | bd1], res2_t as [ex2 | bd2]; cbn [exc_post];
                                             try (intros H; exact H).
                                           intros (-> & -> & -> & <- & Hsucc).
                                           destruct bd1 as [bid_t | dv_t];
                                             [cbn in Hsucc |- *; unfold m2r_block_succs; rewrite Etm_init |];
                                           exists P_post, gs_post, σ1_post, σ2_post, sf1_post, sf2_post;
                                           exact (conj HincU_p (conj HincP_p (conj Logic.eq_refl (conj Logic.eq_refl
                                                    (conj Logic.eq_refl (conj Hdt_post (conj Hlk_p_post
                                                      (conj Hlk_er_post (conj Hinv_post (conj Htf_post
                                                        (conj Hgenv_post (conj Hsafe_post (conj Hvars_post Hsucc))))))))))))).
                     --- intros U_b1 s1_b1 bd1 s2_b1 bd2 _
                           (P_b1 & gs_b1 & σ1_b1 & σ2_b1 & sf1_b1 & sf2_b1 &
                            HincU_b1 & HincP_b1 & <- & -> & -> & Hdt_b1 & Hlk_p_b1 & Hlk_er_b1 &
                            Hinv_b1 & Htf_b1 & Hgenv_b1 & Hsafe_b1 & Hvars_b1 & Hsucc_b1).
                         destruct bd1 as [bid_next | dv_ret].
                         +++ apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
                             assert (Hsucc_init : In bid_next (m2r_block_succs b_init))
                               by exact Hsucc_b1.
                             assert (Hne_init : bid_next <> init c).
                             { intros Heq_n; apply Hno_entry_pred; rewrite <- Heq_n.
                               unfold m2r_all_succs; apply in_flat_map; exists b_init; split; assumption. }
                             refine (conj Logic.eq_refl _).
                             unfold s1_prom_loop_inv; cbn [sps_c sps_dt sps_p sps_init_reg fst snd].
                             unfold sps_safe_no_p, sps_avoid0; cbn [sps_fargs sps_c sps_p]; fold all_defs safe_locals safe_no_p avoid0.
                             refine (conj Hne_init (conj HincU_b1 (conj _ _))).
                             *** exists b_init; exact (conj Hin_init (conj Hid_init Hsucc_init)).
                             *** assert (Hlk_end_init' :
                                           lookup_end_reg
                                             (sps_end_map
                                                {| sps_fargs := fargs; sps_c := c; sps_b_init := b_init;
                                                   sps_p := p; sps_dt := dt; sps_init_reg := init_reg;
                                                   sps_end_reg0 := init_end_reg;
                                                   sps_code0' := pre_al ++ (IId p, INSTR_Alloca dt anns_al, md_al) :: init_op :: post_al';
                                                   sps_pass1 := pass1_out |})
                                             (init c) init_reg = init_end_reg)
                                   by exact Hlk_end_init.
                                 exists P_b1, gs_b1, σ1_b1, σ2_b1, sf1_b1, sf2_b1.
                                 rewrite Hlk_end_init'.
                                 exact (conj HincP_b1 (conj Hdt_b1 (conj Hlk_p_b1 (conj Hlk_er_b1
                                          (conj Logic.eq_refl (conj Logic.eq_refl
                                            (conj Hinv_b1 (conj Htf_b1 (conj Hgenv_b1
                                              (conj Hsafe_b1 Hvars_b1)))))))))).
                         +++ apply refine_prov_to_s1_cps, refine_cfg_exc_ret.
                             refine (conj Logic.eq_refl (conj HincU_b1 _)).
                             exists P_b1, σ1_b1, σ2_b1, sf1_b1, sf2_b1.
                             exact (conj HincP_b1 (conj Logic.eq_refl (conj Logic.eq_refl
                                      (conj Hgenv_b1 (or_intror (ex_intro _ gs_b1 (conj Hinv_b1 Htf_b1))))))).
                  ** intros U' s1' s2' j' _ Hli'; apply s1_lfp_fold; right; right.
                     exists sp, (Some varg1), fs0, (pr_va :: U0), (pr_va :: P0), G,
                            fstk1, fstk2, s1', s2', j', k_o1, k_o2.
                     rewrite !denote_ocfg_map_eq_iter.
                     refine (conj Hwf (conj Hli' (conj Hk_o (conj _ _)))); reflexivity.
                  ** exact Hk_o.
               ++ intros U_ocfg s1_ocfg r_ocfg1 s2_ocfg r_ocfg2 _ [<- Hexit_ocfg].
                  destruct r_ocfg1 as [bid_miss | uv_ret].
                  ** apply refine_prov_to_s1_cps, refine_cfg_exc_raise_both.
                  ** apply refine_prov_to_s1_cps, refine_cfg_exc_ret;
                       exact (conj Logic.eq_refl Hexit_ocfg).
            -- intros U_rv s1_rv rv1 s2_rv rv2 _ Hrv_post.
               assert (Hrv_unif :
                         rv1 = rv2 /\
                         s1_prom_exit_rel fs0 (pr_va :: U0) (pr_va :: P0) G fstk1 fstk2 U_rv s1_rv s2_rv).
               { destruct rv1 as [ex1 | v1], rv2 as [ex2 | v2]; cbn [exc_post] in Hrv_post;
                   try contradiction;
                   destruct Hrv_post as [<- Hpost_r]; exact (conj Logic.eq_refl Hpost_r). }
               clear Hrv_post.
               destruct Hrv_unif as [<- (HincU_rv & P_e & σ1_e & σ2_e & sf1_e & sf2_e &
                                         HincP_e & -> & -> & Hgenv_e & Hcase_e)].
               assert (Hpop :
                         refine_prov
                           (fun U' '(s1', r1) '(s2', r2) =>
                              exists σ1' σ2',
                                U' = U_rv /\ r1 = tt /\ r2 = tt /\
                                s1' = (σ1', ((sf_c1, fstk_c1), g0)) /\
                                s2' = (σ2', ((sf_c2, fstk_c2), g0)) /\
                                stage1_mem_inv U_rv P_e G σ1' σ2' /\
                                Memory_stack_frame_stack (state_memory_stack σ2') = fs0)
                           U_rv
                           (interp_cfg_model ctx1 pop_call_frame (σ1_e, ((sf1_e, sf_c1 :: fstk_c1), g0)))
                           (interp_cfg_model ctx2 pop_call_frame (σ2_e, ((sf2_e, sf_c2 :: fstk_c2), g0)))).
               { destruct Hcase_e as [[Hinv_e Htf_e] | (gs_e & Hinv_e & Htf_e)].
                 - exact (pop_call_frame_stage1_unprom_sim ctx1 ctx2 fs0 U_rv P_e G
                            σ1_e σ2_e sf1_e sf_c1 sf2_e sf_c2 fstk_c1 fstk_c2 g0 Hinv_e Htf_e).
                 - exact (pop_call_frame_stage1_prom_sim ctx1 ctx2 fs0 U_rv P_e gs_e G
                            σ1_e σ2_e sf1_e sf_c1 sf2_e sf_c2 fstk_c1 fstk_c2 g0 Hinv_e Htf_e). }
               eapply s1_cps_cfg_bind; [apply refine_prov_to_s1_cps, Hpop |].
               intros U_pop s1_pop _ s2_pop _ _
                 (σ1_pop & σ2_pop & -> & _ & _ & -> & -> & Hinv_pop & Hfs_pop).
               apply refine_prov_to_s1_cps; eapply refine_prov_weaken.
               ++ exact (check_call_return_stage1_cfg_sim ctx1 ctx2
                           (dc_attrs (df_prototype df)) ret_attrs None fname args1 rv1
                           U_rv P_e G σ1_pop σ2_pop
                           ((sf_c1, fstk_c1), g0) ((sf_c2, fstk_c2), g0) Hinv_pop).
               ++ intros U_f [s1_f rf1] [s2_f rf2] (-> & -> & -> & <-).
                  exists P_e, σ1_pop, σ2_pop.
                  exact (conj (fun x Hx => HincU_rv x (or_intror Hx))
                           (conj (fun x Hx => HincP_e x (or_intror Hx))
                              (conj Logic.eq_refl
                                 (conj Logic.eq_refl
                                    (conj Logic.eq_refl
                                       (conj Hinv_pop (conj Hfs_pop Hgenv_e))))))).
    Qed.

    Local Lemma s1_phi_step (U : list N) (t1 t2 : itree ProvBotE Ans) :
      s1_phi s1_lfp U t1 t2 ->
      m2r_paco s1_lfp U t1 t2.
    Proof using Hctx.
      intros [Hcall | [Hunp | Hprom]].
      - destruct Hcall as (dt & cc & fv & vs & P & G & σ1 & σ2 & ls1 & ls2 & k1 & k2 &
                           Hinv & Hg & Hk & E1 & E2).
        eapply m2r_paco_obs_eq; [exact E1 | exact E2 |]; clear t1 t2 E1 E2.
        revert k1 k2 Hk;
          change (s1_cps s1_lfp
                    (s1_call_post U P G (Memory_stack_frame_stack (state_memory_stack σ2)) ls1 ls2)
                    U
                    (interp_cfg_model ctx1 (mrec_ctx ctx1 _ (Call dt cc fv vs)) (σ1, (ls1, g0)))
                    (interp_cfg_model ctx2 (mrec_ctx ctx2 _ (Call dt cc fv vs)) (σ2, (ls2, g0)))).
        unfold mrec_ctx; cbn [ExtLib.Structures.Monad.bind Monad_itree].
        destruct fv as [db | |];
          [| eapply s1_cps_cfg_bind with (RA := fun _ _ _ => False);
               [apply refine_prov_to_s1_cps, refine_cfg_raise_both | intros _ _ _ _ _ _ []]
          | eapply s1_cps_cfg_bind with (RA := fun _ _ _ => False);
               [apply refine_prov_to_s1_cps, refine_cfg_raise_both | intros _ _ _ _ _ _ []]].
        destruct db as [addr | ? ? | ? | ? | ? | | | ? ?]; cbn [check_callee EOU_to_itree];
          lazymatch goal with
          | |- context [ITree.bind (raise _) _] =>
              eapply s1_cps_cfg_bind with (RA := fun _ _ _ => False);
              [apply refine_prov_to_s1_cps, refine_cfg_raise_both | intros _ _ _ _ _ _ []]
          | _ => idtac
          end.
        + cbn [check_callee].
          destruct ((ptr_to_int addr =? ptr_to_int null)%Z).
          * cbn [EOU_to_itree].
            eapply s1_cps_cfg_bind with (RA := fun _ _ _ => False);
              [apply refine_prov_to_s1_cps, refine_cfg_raiseUB_l | intros _ _ _ _ _ _ []].
          * cbn [EOU_to_itree lookup_defn].
            eapply s1_cps_obs_eq;
              [symmetry; apply interp_cfg_model_obs_eq, Eqit.bind_ret_l
              | symmetry; apply interp_cfg_model_obs_eq, Eqit.bind_ret_l |].
            pose proof (Hctx (ptr_to_int addr)) as Hlk.
            destruct (lookup (ptr_to_int addr) ctx1) as [f1 |],
                     (lookup (ptr_to_int addr) ctx2) as [f2 |];
              inversion Hlk; subst; clear Hlk.
            -- match goal with H : s1_fn_entry_rel _ _ |- _ =>
                 destruct H as [[-> ->] | [(d & Hd & -> & ->) | (df & df' & Htry & -> & ->)]]
               end.
               ++ apply refine_prov_to_s1_cps; eapply refine_prov_weaken;
                    [apply putchar_denotation_stage1_cfg_sim |].
                  intros U' [s1' r1] [s2' r2] (-> & -> & -> & <-).
                  exists P, σ1, σ2.
                  exact (conj (incl_refl U) (conj (incl_refl P)
                           (conj Logic.eq_refl (conj Logic.eq_refl (conj Logic.eq_refl
                             (conj Hinv (conj Logic.eq_refl Hg))))))).
               ++ exact (s1_unprom_denote_function_cps d cc vs U P G σ1 σ2 ls1 ls2 Hd Hinv Hg).
               ++ exact (s1_prom_denote_function_cps df df' cc vs U P G σ1 σ2 ls1 ls2 Htry Hinv Hg).
            -- apply refine_prov_to_s1_cps.
               exact (s1_external_call_cfg_sim dt (DVALUE_Base (DVALUE_Pointer addr)) vs
                        U P G σ1 σ2 ls1 ls2 Hinv Hg).
        + cbn [check_callee EOU_to_itree].
          eapply s1_cps_cfg_bind with (RA := fun _ _ _ => False);
            [apply refine_prov_to_s1_cps, refine_cfg_raiseUB_l | intros _ _ _ _ _ _ []].
      - destruct Hunp as (d & va & fs0 & U0 & P0 & G & fstk1 & fstk2 & s1 & s2 & j &
                          k_out1 & k_out2 & Hd & Hli & Hk_out & E1 & E2).
        eapply m2r_paco_obs_eq; [exact E1 | exact E2 |]; clear t1 t2 E1 E2.
        pose proof (proj1 Hli) as Hinc0.
        rewrite !denote_ocfg_map_eq_iter.
        eapply (s1_iter_one_step
                  (s1_unprom_loop_inv d fs0 U0 P0 G fstk1 fstk2)
                  (s1_unprom_rexc fs0 U0 P0 G fstk1 fstk2)
                  (s1_unprom_rret fs0 U0 P0 G fstk1 fstk2)
                  (ocfg_step_body (ocfg_map (blks (df_instrs d))) va)
                  (ocfg_step_body (ocfg_map (blks (df_instrs d))) va)
                  U s1 s2 j k_out1 k_out2).
        + exact (s1_unprom_block_body_cps d va fs0 U0 P0 G fstk1 fstk2 U s1 s2 j Hd Hli).
        + intros U' s1' s2' j' _ Hli'; apply s1_lfp_fold; right; left.
          exists d, va, fs0, U0, P0, G, fstk1, fstk2, s1', s2', j', k_out1, k_out2.
          rewrite !denote_ocfg_map_eq_iter.
          refine (conj Hd (conj Hli' (conj Hk_out (conj _ _)))); reflexivity.
        + intros U' a1 a2 Hinc Ha; exact (Hk_out U' a1 a2 (incl_tran Hinc0 Hinc) Ha).
      - destruct Hprom as (sp & va & fs0 & U0 & P0 & G & fstk1 & fstk2 & s1 & s2 & j &
                           k_out1 & k_out2 & Hwf & Hli & Hk_out & E1 & E2).
        eapply m2r_paco_obs_eq; [exact E1 | exact E2 |]; clear t1 t2 E1 E2.
        pose proof (proj1 (proj2 Hli)) as Hinc0.
        rewrite !denote_ocfg_map_eq_iter.
        eapply (s1_iter_one_step
                  (s1_prom_loop_inv sp fs0 U0 P0 G fstk1 fstk2)
                  (s1_prom_rexc fs0 U0 P0 G fstk1 fstk2)
                  (s1_prom_rret fs0 U0 P0 G fstk1 fstk2)
                  (ocfg_step_body (ocfg_map (blks (sps_c sp))) va)
                  (ocfg_step_body (ocfg_map (sps_blks' sp)) va)
                  U s1 s2 j k_out1 k_out2).
        + exact (s1_prom_block_body_cps sp va fs0 U0 P0 G fstk1 fstk2 U s1 s2 j Hwf Hli).
        + intros U' s1' s2' j' _ Hli'; apply s1_lfp_fold; right; right.
          exists sp, va, fs0, U0, P0, G, fstk1, fstk2, s1', s2', j', k_out1, k_out2.
          rewrite !denote_ocfg_map_eq_iter.
          refine (conj Hwf (conj Hli' (conj Hk_out (conj _ _)))); reflexivity.
        + intros U' a1 a2 Hinc Ha; exact (Hk_out U' a1 a2 (incl_tran Hinc0 Hinc) Ha).
    Qed.

    Lemma s1_interproc_mrec_sim
      (P0 : list N) (dt : dtyp) (fv : @dvalue (@ParamsV IP IPT))
      (args : list (@dvalue (@ParamsV IP IPT)))
      (U : list N) (σ1 σ2 : state)
      (ls : @stack_frame (@ParamsV IP IPT) * stack)
      (Hpu : incl P0 U)
      (Hg : genv_safe P0 g0)
      (Heq : mem_stack_equal (state_memory_stack σ1) (state_memory_stack σ2)) :
      refine_prov top_ans_post U
        (interp_cfg_model ctx1 (mrec_ctx ctx1 _ (Call dt CC_Ccc fv args)) (σ1, (ls, g0)))
        (interp_cfg_model ctx2 (mrec_ctx ctx2 _ (Call dt CC_Ccc fv args)) (σ2, (ls, g0))).
    Proof using Hctx.
      apply m2r_paco_to_refine_prov.
      eapply (m2r_paco_acc (fun _ _ _ => False) s1_lfp).
      - intros r _ Hlr U' a1 a2 Hl.
        exact (m2r_paco_mon s1_lfp r Hlr U' a1 a2
                 (s1_phi_step U' a1 a2 (s1_lfp_unfold U' a1 a2 Hl))).
      - apply s1_lfp_fold; left.
        exists dt, CC_Ccc, fv, args, P0, ([] : list ghost_slot), σ1, σ2, ls, ls,
               (fun x : Ans => Ret x), (fun x : Ans => Ret x).
        refine (conj (stage1_equal_to_mem_inv U P0 σ1 σ2 Hpu Heq)
                 (conj Hg (conj _ (conj (Eqit.bind_ret_r _) (Eqit.bind_ret_r _))))).
        intros U' [s1' rv1] [s2' rv2] _ (P' & σ1' & σ2' & _ & _ & Heq_rv & _).
        apply m2r_paco_fold, RP_Step; exact Heq_rv.
    Qed.

  End InterprocKnot.

  Lemma interproc_module_defs_refines (M1 M2 : CFG.mcfg dtyp)
    (Hbg : @build_global_environment (@ParamsV IP IPT) M2 =
           @build_global_environment (@ParamsV IP IPT) M1)
    (Hdecls : m_declarations M2 = m_declarations M1)
    (Hnoputs : negb (in_raw_ids (Name "puts"%string) (List.map dc_name (m_declarations M1))) = true)
    (Hdefs : Forall2
               (fun d1 d2 =>
                  dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
                  s1_fn_entry_rel (denote_function d1) (denote_function d2))
               (m_definitions M1) (m_definitions M2)) :
    prog_refines M1 M2.
  Proof using.
    eapply (module_defs_refines_gen (fun _ _ => s1_fn_entry_rel) M1 M2 Hbg Hdecls).
    - intros _ _ _; exact Hdefs.
    - intros _ _ _.
      pose proof (library_functions_no_puts_only_putchar (m_declarations M1) Hnoputs) as Hlf.
      induction Hlf as [| lib libs Hhd _ IH]; constructor;
        [left; exact (conj Hhd Hhd) | exact IH].
    - intros P0 g0 ctx1 ctx2 dt fv args U σ1 σ2 ls Hctx Hpu Hg Heq.
      exact (s1_interproc_mrec_sim g0 ctx1 ctx2 Hctx P0 dt fv args U σ1 σ2 ls Hpu Hg Heq).
  Qed.

  Lemma build_global_environment_defs_eq
    (M : CFG.mcfg dtyp) (defs' : list (definition dtyp (CFG.cfg dtyp)))
    (Hproto : List.map df_prototype defs' = List.map df_prototype (m_definitions M))
    (Hba : flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) defs' =
           flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) (m_definitions M)) :
    let M' := {| m_name         := m_name M;
                 m_target       := m_target M;
                 m_datalayout   := m_datalayout M;
                 m_type_defs    := m_type_defs M;
                 m_globals      := m_globals M;
                 m_declarations := m_declarations M;
                 m_definitions  := defs' |} in
    @build_global_environment (@ParamsV IP IPT) M' =
    @build_global_environment (@ParamsV IP IPT) M.
  Proof using.
    intros M'.
    assert (Hmba : mcfg_block_addresses M' = mcfg_block_addresses M)
      by (unfold mcfg_block_addresses, M'; cbn [m_globals m_definitions]; rewrite Hba; reflexivity).
    unfold build_global_environment; rewrite Hmba; unfold M';
      cbn [m_declarations m_globals m_definitions]; rewrite Hproto; reflexivity.
  Qed.

  Lemma leaf_ctx_fn_rel_refl_list
    (P0 : list N) (g0 : @global_env (@ParamsV IP IPT))
    (defs : list (definition dtyp (CFG.cfg dtyp))) :
    Forall2
      (fun d1 d2 =>
         dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
         leaf_ctx_fn_rel P0 g0 (denote_function d1) (denote_function d2))
      defs defs.
  Proof using.
    induction defs as [| d rest IH]; constructor; [| exact IH].
    split; [reflexivity | left; exact (conj Logic.eq_refl (@ev_ok_denote_function IP IPT d))].
  Qed.

  Lemma s1_fn_entry_rel_refl_safe_list
    (defs : list (definition dtyp (CFG.cfg dtyp))) :
    forallb m2r_defn_mem_safe defs = true ->
    Forall2
      (fun d1 d2 =>
         dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
         s1_fn_entry_rel (denote_function d1) (denote_function d2))
      defs defs.
  Proof using.
    induction defs as [| d rest IH]; cbn [forallb]; [intros _; constructor |].
    intros Hsafe; rewrite andb_true_iff in Hsafe; destruct Hsafe as [Hd Hrest].
    constructor; [| exact (IH Hrest)].
    split; [reflexivity | right; left; exists d; exact (conj Hd (conj Logic.eq_refl Logic.eq_refl))].
  Qed.

  Lemma promote_first_in_defs_leaf_spec
    (defs defs' : list (definition dtyp (CFG.cfg dtyp))) :
    promote_first_in_defs false defs = Some defs' ->
    List.map df_prototype defs' = List.map df_prototype defs /\
    flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) defs' =
      flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) defs /\
    (forall P0 g0,
       genv_safe P0 g0 ->
       Forall2
         (fun d1 d2 =>
            dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
            leaf_ctx_fn_rel P0 g0 (denote_function d1) (denote_function d2))
         defs defs').
  Proof using.
    revert defs'; induction defs as [| df rest IH]; intros defs' Hprom;
      cbn [promote_first_in_defs] in Hprom; [discriminate Hprom |].
    destruct (try_promote_slot_in_defn false df) as [df' |] eqn:Etry.
    - inversion Hprom; subst defs'; clear Hprom.
      destruct (promote_slot_in_defn_block_addresses false df df' Etry) as [Hpr Hba].
      cbn [List.map flat_map]; rewrite Hpr, Hba; refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
      intros P0 g0 Hg0; constructor; [| apply leaf_ctx_fn_rel_refl_list].
      split; [rewrite Hpr; reflexivity | exact (try_promote_slot_leaf_denote_function_sim P0 g0 df df' Hg0 Etry)].
    - destruct (promote_first_in_defs false rest) as [rest' |] eqn:Erest;
        [| discriminate Hprom].
      inversion Hprom; subst defs'; clear Hprom; cbn [option_map List.map flat_map].
      destruct (IH rest' Logic.eq_refl) as (Hpr & Hba & Hrel).
      rewrite Hpr, Hba; refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
      intros P0 g0 Hg0; constructor; [| exact (Hrel P0 g0 Hg0)].
      split; [reflexivity | left; exact (conj Logic.eq_refl (@ev_ok_denote_function IP IPT df))].
  Qed.

  Lemma promote_first_in_defs_interproc_spec
    (defs defs' : list (definition dtyp (CFG.cfg dtyp))) :
    forallb m2r_defn_mem_safe defs = true ->
    promote_first_in_defs true defs = Some defs' ->
    List.map df_prototype defs' = List.map df_prototype defs /\
    flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) defs' =
      flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) defs /\
    Forall2
      (fun d1 d2 =>
         dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
         s1_fn_entry_rel (denote_function d1) (denote_function d2))
      defs defs'.
  Proof using.
    revert defs'; induction defs as [| df rest IH]; intros defs' Hsafe Hprom;
      cbn [forallb] in Hsafe; cbn [promote_first_in_defs] in Hprom; [discriminate Hprom |].
    rewrite andb_true_iff in Hsafe; destruct Hsafe as [Hdf_safe Hrest_safe].
    destruct (try_promote_slot_in_defn true df) as [df' |] eqn:Etry.
    - inversion Hprom; subst defs'; clear Hprom.
      destruct (promote_slot_in_defn_block_addresses true df df' Etry) as [Hpr Hba].
      cbn [List.map flat_map]; rewrite Hpr, Hba; refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
      constructor; [| exact (s1_fn_entry_rel_refl_safe_list rest Hrest_safe)].
      split; [rewrite Hpr; reflexivity
             | right; right; exists df, df'; exact (conj Etry (conj Logic.eq_refl Logic.eq_refl))].
    - destruct (promote_first_in_defs true rest) as [rest' |] eqn:Erest;
        [| discriminate Hprom].
      inversion Hprom; subst defs'; clear Hprom; cbn [option_map List.map flat_map].
      destruct (IH rest' Hrest_safe Logic.eq_refl) as (Hpr & Hba & Hrel).
      rewrite Hpr, Hba; refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
      constructor; [| exact Hrel].
      split; [reflexivity
             | right; left; exists df; exact (conj Hdf_safe (conj Logic.eq_refl Logic.eq_refl))].
  Qed.

  Lemma elim_first_dead_alloca_in_defs_spec {IPWB : IPtrWellBehaved IP}
    (defs defs' : list (definition dtyp (CFG.cfg dtyp))) :
    elim_first_dead_alloca_in_defs defs = Some defs' ->
    List.map df_prototype defs' = List.map df_prototype defs /\
    flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) defs' =
      flat_map (fun d => flat_map block_block_addresses (blks (df_instrs d))) defs /\
    (forall P0 g0,
       genv_safe P0 g0 ->
       Forall2
         (fun d1 d2 =>
            dc_name (df_prototype d1) = dc_name (df_prototype d2) /\
            leaf_ctx_fn_rel P0 g0 (denote_function d1) (denote_function d2))
         defs defs').
  Proof using.
    revert defs'; induction defs as [| df rest IH]; intros defs' Helim;
      cbn [elim_first_dead_alloca_in_defs] in Helim; [discriminate Helim |].
    destruct (try_elim_dead_alloca_in_defn df) as [df' |] eqn:Etry.
    - inversion Helim; subst defs'; clear Helim.
      destruct (elim_dead_alloca_in_defn_block_addresses df df' Etry) as [Hpr Hba].
      cbn [List.map flat_map]; rewrite Hpr, Hba; refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
      intros P0 g0 Hg0; constructor; [| apply leaf_ctx_fn_rel_refl_list].
      split; [rewrite Hpr; reflexivity
             | exact (try_elim_dead_alloca_denote_function_sim P0 g0 df df' Hg0 Etry)].
    - destruct (elim_first_dead_alloca_in_defs rest) as [rest' |] eqn:Erest;
        [| discriminate Helim].
      inversion Helim; subst defs'; clear Helim; cbn [option_map List.map flat_map].
      destruct (IH rest' Logic.eq_refl) as (Hpr & Hba & Hrel).
      rewrite Hpr, Hba; refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
      intros P0 g0 Hg0; constructor; [| exact (Hrel P0 g0 Hg0)].
      split; [reflexivity | left; exact (conj Logic.eq_refl (@ev_ok_denote_function IP IPT df))].
  Qed.

End MemoryAndSerialization.


(** * 4. Top-Level Whole-Module Refinement Theorems *)

Theorem promote_slot_step_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (promote_slot_step_mcfg M).
Proof.
  intros IP IPT M.
  unfold promote_slot_step_mcfg.
  destruct (mcfg_no_inttoptr M) eqn:Eno_itp; [| apply prog_refines_refl].
  destruct (m2r_module_interproc_safe M) eqn:Eis.
  - unfold m2r_module_interproc_safe in Eis.
    rewrite !andb_true_iff in Eis; destruct Eis as [[[_ _] Hnoputs] Hsafe].
    destruct (promote_first_in_defs true (m_definitions M)) as [defs' |] eqn:Eprom;
      [| apply prog_refines_refl].
    destruct (promote_first_in_defs_interproc_spec (m_definitions M) defs' Hsafe Eprom)
      as (Hproto & Hba & Hrel).
    exact (interproc_module_defs_refines M _
             (build_global_environment_defs_eq M defs' Hproto Hba)
             Logic.eq_refl Hnoputs Hrel).
  - destruct (promote_first_in_defs false (m_definitions M)) as [defs' |] eqn:Eprom;
      [| apply prog_refines_refl].
    destruct (@promote_first_in_defs_leaf_spec IP IPT (m_definitions M) defs' Eprom)
      as (Hproto & Hba & Hrel).
    exact (leaf_module_defs_refines M _
             (build_global_environment_defs_eq M defs' Hproto Hba)
             Logic.eq_refl Hrel).
Qed.

Theorem promote_slot_iter_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} (fuel : nat) (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (promote_slot_iter fuel M).
Proof.
  intros IP IPT fuel.
  induction fuel as [| fuel' IH]; intros M; cbn [promote_slot_iter].
  - apply prog_refines_refl.
  - eapply prog_refines_trans; [apply promote_slot_step_refines | apply IH].
Qed.

Theorem elim_dead_alloca_step_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} {IPWB : IPtrWellBehaved IP}
         (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (elim_dead_alloca_step_mcfg M).
Proof.
  intros IP IPT IPWB M.
  unfold elim_dead_alloca_step_mcfg.
  destruct (mcfg_no_inttoptr M); [| apply prog_refines_refl].
  destruct (elim_first_dead_alloca_in_defs (m_definitions M)) as [defs' |] eqn:Eelim;
    [| apply prog_refines_refl].
  destruct (@elim_first_dead_alloca_in_defs_spec IP IPT IPWB (m_definitions M) defs' Eelim)
    as (Hproto & Hba & Hrel).
  exact (leaf_module_defs_refines M _
           (build_global_environment_defs_eq M defs' Hproto Hba)
           Logic.eq_refl Hrel).
Qed.

Theorem elim_dead_alloca_iter_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} {IPWB : IPtrWellBehaved IP}
         (fuel : nat) (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (elim_dead_alloca_iter fuel M).
Proof.
  intros IP IPT IPWB fuel.
  induction fuel as [| fuel' IH]; intros M; cbn [elim_dead_alloca_iter].
  - apply prog_refines_refl.
  - eapply prog_refines_trans; [apply elim_dead_alloca_step_refines | apply IH].
Qed.

Theorem mem2reg_mcfg_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} {IPWB : IPtrWellBehaved IP}
         (M : CFG.mcfg dtyp),
    @prog_refines IP IPT M (mem2reg_mcfg M).
Proof.
  intros IP IPT IPWB M.
  unfold mem2reg_mcfg.
  eapply prog_refines_trans;
    [apply promote_slot_iter_refines | apply elim_dead_alloca_iter_refines].
Qed.

Theorem mem2reg_mcfg_typ_refines :
  forall {IP : IPtr} {IPT : @IPtrTheory IP} {IPWB : IPtrWellBehaved IP}
         (M : CFG.mcfg typ),
    @prog_refines IP IPT (convert_types M) (mem2reg_mcfg_typ M).
Proof.
  intros IP IPT IPWB M.
  unfold mem2reg_mcfg_typ.
  apply mem2reg_mcfg_refines.
Qed.
