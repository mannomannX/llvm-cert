(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Module-Merge VDraw Lifting & Flex-Merge Soundness ([CertPasses.ModuleMergeVDrawLift])

    Purpose:
      Lifts [cfg_local_vdraw_sim] across [run_exc], [denote_function], [mrec],
      [interp_intrinsics], and [interp_state] ([mcfg_vdraw_sim_to_model]),
      defines flexible parameter-renaming validation ([check_flex_module_merge]),
      and proves [check_flex_module_merge_value_refines].

    Trust Contract & Fail-Closed Boundary:
      Proof/checker module re-exported by [CertPasses.ModuleMerge].
      [check_flex_module_merge] enforces identical [m_globals], non-intrinsic
      [m_declarations], [NoDup] symbols, [blockaddress] preservation, and
      matching prototypes/slices, returning [false] on any violation.

    Assumptions:
      Depends on Stdlib, Paco, ITree, ExtLib, Vellvm,
      [CertPasses.ModuleMerge{Eqb,Link,VDrawCore}], and [CertPasses.{PassCommon,
      SimplifyCFG,DCE,SCCP,Mem2Reg,Inline,Pipeline,McfgExport}]; zero axioms.

    Section Outline:
      (8.4) Lifting [cfg_local_vdraw_sim_b] through [mrec], [interp_intrinsics],
      & [mcfg_vdraw_sim_to_model]; (8.5) [check_flex_module_merge] &
      [check_flex_module_merge_value_refines]. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Number
  Decimal
  Hexadecimal
  Strings.Ascii
  Strings.String
  List
  Bool
  Lia
  Classes.RelationClasses.
Import ListNotations.

From Paco Require Import
  paco.

From ITree Require Import
  ITree
  ITreeFacts
  Eq.Eqit
  Events.State
  Events.StateFacts
  Basics.HeterogeneousRelations.

From ExtLib Require Import
  Structures.Maps
  Structures.Monads.

From Vellvm Require Import
  Semantics.VellvmIntegers
  Utils
  Syntax
  Syntax.LLVMAst
  Syntax.AstLib
  Syntax.CFG
  Syntax.DynamicTypes
  Semantics
  ScopeTheory
  Utils.rutt_cutoff
  Semantics.Interfaces.IPtr
  Semantics.Interfaces.Params
  Semantics.Interfaces.Memory
  Semantics.Implementations.IPtrInfinite
  Semantics.Implementations.IPtrFinite
  Semantics.Implementations.ParamsV
  Semantics.Implementations.Memory
  Semantics.Handlers
  Semantics.InterpretationStack
  Semantics.Denotation
  Semantics.TopLevel
  Semantics.Libraries
  Semantics.LLVMEvents
  Theory.I2F.Refinement
  Theory.I2F.I2F_interp
  Theory.I2F.I2F_toplevel.

From CertPasses Require Import
  PassCommon
  SimplifyCFG
  DCE
  SCCP
  Mem2Reg
  Inline
  Pipeline
  McfgExport.
Import Logic.

Set Default Goal Selector "!".
Unset Implicit Arguments.
#[local] Open Scope list_scope.
#[local] Existing Instance MemoryModelStateV.
#[local] Existing Instance MemoryModelPrimitivesV.

From CertPasses Require Import ModuleMergeEqb ModuleMergeLink ModuleMergeVDrawCore.

Section ValueDrawRefinement.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.
  #[local] Hint Resolve refine_prov__mon cfg_local_sim__mon gen_stack_sim__mon
    refine_prov_draw__mon vds_sim__mon : paco.
  #[local] Hint Extern 1 (monotone5 (vds_sim_ _ _ _ _ _ _ _ _)) => apply vds_sim__mon : paco.
  #[local] Notation PaV := (@ParamsV IP IPT).
  Arguments interp_vellvm_rel_draw_h {_ _} [T] _ _.

  (** ** 8.4 Lifting [cfg_local_vdraw_sim] Across [run_exc],
      [check_call_return], [denote_function], [mrec], & [interp_state] *)

  (** Boolean gate [allow_call]:
      - [allow_call = true] ([cfg_vdraw_sim] / [cfg_local_vdraw_sim]) permits
        arbitrary internal/recursive/indirect [CallE] events and composes across
        arbitrary multi-function call graphs whenever internal callees return
        matching values (either via body return equality or via a [noundef]
        return attribute upgrading [DVALUE_Poison] to [raiseUB]).
      - [allow_call = false] ([cfg_vdraw_leaf_sim] / [cfg_local_vdraw_leaf_sim])
        rules out internal [CallE] synchronization and lifts [Poison -> Concrete]
        return refinement ([mm_ret_dvalue_refines], e.g. [xor %x, %x -> 0] and
        [freeze] folding) to whole-module [prog_value_draw_refines] WITHOUT
        requiring [noundef] on the function prototype. *)
  Definition sync_cfg_b (allow_call : bool) {X} (e : @CFGEtop PaV X) : bool :=
    match e with
    | inl1 _ => allow_call
    | inr1 m => @sync_non_local_mcfg IP IPT X m
    end.

  Definition cfg_vdraw_sim_b (allow_call : bool) {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    : env_stack -> @local_env PaV -> @local_env PaV -> @CFGtop PaV R1 -> @CFGtop PaV R2 -> Prop :=
    vds_sim (@is_ub_cfg IP IPT) (@sync_cfg_b allow_call) EqE_CFG EqA_CFG
      (@cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT) RR.

  Definition cfg_local_vdraw_sim_b (allow_call : bool) {R1 R2}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV)
    (t1 : @CFGtop PaV R1) (t2 : @CFGtop PaV R2) : Prop :=
    vds_sim (@is_ub_cfg IP IPT) (@sync_cfg_b allow_call) EqE_CFG EqA_CFG
      (@cfg_event_post IP IPT) (@as_local_cfg IP IPT) (fun _ _ => None)
      (fun _ => RR) [] env1 env2 t1 t2.

  Definition cfg_local_vdraw_sim {R1 R2} := @cfg_local_vdraw_sim_b true R1 R2.
  Definition cfg_local_vdraw_leaf_sim {R1 R2} := @cfg_local_vdraw_sim_b false R1 R2.

  Lemma sync_non_local_cfg_to_sync_cfg_true {X} (e : @CFGEtop PaV X) :
    @sync_non_local_cfg IP IPT X e = true -> sync_cfg_b true e = true.
  Proof using.
    destruct e as [c | m]; [intros _; reflexivity | exact (fun H => H)].
  Qed.

  Lemma cfg_vdraw_sim_to_b_true {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    stk env1 env2 (t1 : @CFGtop PaV R1) (t2 : @CFGtop PaV R2) :
    cfg_vdraw_sim RR stk env1 env2 t1 t2 ->
    cfg_vdraw_sim_b true RR stk env1 env2 t1 t2.
  Proof using.
    revert stk env1 env2 t1 t2; pcofix CIH; intros stk env1 env2 t1 t2 Hs; pstep; punfold Hs.
    induction Hs as [stk env1 env2 t1 t2 Hstep
                     | stk env1 env2 t1 m1 t2 Ht1 _ IH
                     | stk env1 env2 t1 t2 m2 Ht2 _ IH
                     | stk env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                     | stk env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                     | stk env1 env2 t1 x v k1 t2 Ht1 _ IH
                     | stk env1 env2 t1 t2 x v k2 Ht2 _ IH
                     | stk env1 env2 t1 dt v k1 t2 Ht1 Hv _ IH
                     | stk env1 env2 t1 t2 dt k2 Ht2 _ IH].
    - apply VDS_Step; unfold vds_step_body in *.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1].
      + exact Hstep.
      + destruct (observe t2);
          [exact Hstep | destruct Hstep as [Hs | Hb]; [right; apply CIH, Hs | inversion Hb] | exact Hstep].
      + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct (observe t2) as [r2 | m2 | X2 e2 k2]; try contradiction.
        destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
        * left; split; [apply sync_non_local_cfg_to_sync_cfg_true, Hsync | split; [exact HE |]].
          intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp);
            destruct HA as [HA | Hb]; [right; apply CIH, HA | inversion Hb].
        * right; left.
          destruct (as_local_cfg e1) as [le1 |], (as_local_cfg e2) as [le2 |]; try contradiction.
          destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
          -- destruct Hloc as (Hx & Hv & [Hr | Hb]); [| inversion Hb].
             split; [exact Hx | split; [exact Hv | right; apply CIH, Hr]].
          -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
             intros v Hv; specialize (Hrd v Hv);
               destruct Hrd as [Hrd | Hb]; [right; apply CIH, Hrd | inversion Hb].
        * right; right.
          destruct (as_stack_cfg e1) as [se1 |], (as_stack_cfg e2) as [se2 |]; try contradiction.
          destruct se1, se2; try contradiction.
          -- destruct Hstk as [Hr | Hb]; [right; apply CIH, Hr | inversion Hb].
          -- destruct stk as [| [p1 p2] rest]; [exact I |].
             destruct Hstk as [Hr | Hb]; [right; apply CIH, Hr | inversion Hb].
    - eapply VDS_TauL; [exact Ht1 | exact IH].
    - eapply VDS_TauR; [exact Ht2 | exact IH].
    - eapply VDS_ReadL; [exact Ht1 | exact Hlk | exact IH].
    - eapply VDS_ReadR; [exact Ht2 | exact Hlk | exact IH].
    - eapply VDS_WriteL; [exact Ht1 | exact IH].
    - eapply VDS_WriteR; [exact Ht2 | exact IH].
    - eapply VDS_DrawL; [exact Ht1 | exact Hv | exact IH].
    - eapply VDS_DrawR; [exact Ht2 | intros v Hv; exact (IH v Hv)].
  Qed.

  Lemma cfg_local_sim_to_local_vdraw_sim {R1 R2}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env PaV)
    (t1 : @CFGtop PaV R1) (t2 : @CFGtop PaV R2) :
    cfg_local_sim RR env1 env2 t1 t2 ->
    cfg_local_vdraw_sim RR env1 env2 t1 t2.
  Proof using.
    unfold cfg_local_vdraw_sim, cfg_local_vdraw_sim_b.
    revert env1 env2 t1 t2; pcofix CIH; intros env1 env2 t1 t2 Hls; pstep; punfold Hls.
    induction Hls as [env1 env2 t1 t2 Hstep
                      | env1 env2 t1 m1 t2 Ht1 _ IH
                      | env1 env2 t1 t2 m2 Ht2 _ IH
                      | env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                      | env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                      | env1 env2 t1 x v k1 t2 Ht1 _ IH
                      | env1 env2 t1 t2 x v k2 Ht2 _ IH].
    - apply VDS_Step; unfold vds_step_body, cls_step_body in *.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1].
      + exact Hstep.
      + destruct (observe t2); [exact Hstep | pclearbot; right; apply CIH, Hstep | exact Hstep].
      + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct (observe t2) as [r2 | m2 | X2 e2 k2]; try contradiction.
        destruct Hvis as [(Hsync & HE & HA) | Hrd].
        * left; split; [apply sync_non_local_cfg_to_sync_cfg_true, Hsync | split; [exact HE |]].
          intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); pclearbot; right; apply CIH, HA.
        * right; left.
          destruct_sum1 e1; try contradiction;
            destruct e1 as [| x1]; try contradiction;
            destruct_sum1 e2; try contradiction;
            destruct e2 as [| x2]; try contradiction.
          destruct Hrd as (Hx & Hlk & Hrd'); split; [exact Hx | split; [exact Hlk |]].
          intros v Hv; specialize (Hrd' v Hv); pclearbot; right; apply CIH, Hrd'.
    - eapply VDS_TauL; [exact Ht1 | exact IH].
    - eapply VDS_TauR; [exact Ht2 | exact IH].
    - eapply VDS_ReadL; [exact Ht1 | exact Hlk | exact IH].
    - eapply VDS_ReadR; [exact Ht2 | exact Hlk | exact IH].
    - eapply VDS_WriteL; [exact Ht1 | exact IH].
    - eapply VDS_WriteR; [exact Ht2 | exact IH].
  Qed.

  Lemma cfg_local_vdraw_to_stack_sim_b (allow_call : bool) {R1 R2}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    stk env1 env2 (t1 : @CFGtop PaV R1) (t2 : @CFGtop PaV R2) :
    cfg_local_vdraw_sim_b allow_call RR env1 env2 t1 t2 ->
    cfg_vdraw_sim_b allow_call (fun stk' e1' e2' r1 r2 => stk' = stk /\ RR e1' e2' r1 r2)
      stk env1 env2 t1 t2.
  Proof using.
    unfold cfg_local_vdraw_sim_b, cfg_vdraw_sim_b.
    remember (@nil (@local_env PaV * @local_env PaV)) as stk_nil eqn:Estk.
    clear Estk.
    revert stk_nil env1 env2 t1 t2; pcofix CIH;
      intros stk_nil env1 env2 t1 t2 Hlv; pstep; punfold Hlv.
    induction Hlv as [s0 env1 env2 t1 t2 Hstep
                      | s0 env1 env2 t1 m1 t2 Ht1 _ IH
                      | s0 env1 env2 t1 t2 m2 Ht2 _ IH
                      | s0 env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                      | s0 env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                      | s0 env1 env2 t1 x v k1 t2 Ht1 _ IH
                      | s0 env1 env2 t1 t2 x v k2 Ht2 _ IH
                      | s0 env1 env2 t1 dt v k1 t2 Ht1 Hv _ IH
                      | s0 env1 env2 t1 t2 dt k2 Ht2 _ IH].
    - apply VDS_Step; unfold vds_step_body in *.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1].
      + destruct (observe t2); [split; [reflexivity | exact Hstep] | exact Hstep | exact Hstep].
      + destruct (observe t2);
          [exact Hstep | destruct Hstep as [Hs | Hb]; [right; eapply CIH, Hs | inversion Hb] | exact Hstep].
      + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct (observe t2) as [r2 | m2 | X2 e2 k2]; try contradiction.
        destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk_f]]; [| | contradiction].
        * left; split; [exact Hsync | split; [exact HE |]].
          intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp);
            destruct HA as [HA | Hb]; [right; eapply CIH, HA | inversion Hb].
        * right; left.
          destruct (as_local_cfg e1) as [le1 |], (as_local_cfg e2) as [le2 |]; try contradiction.
          destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
          -- destruct Hloc as (Hx & Hv & [Hr | Hb]); [| inversion Hb].
             split; [exact Hx | split; [exact Hv | right; eapply CIH, Hr]].
          -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
             intros v Hv; specialize (Hrd v Hv);
               destruct Hrd as [Hrd | Hb]; [right; eapply CIH, Hrd | inversion Hb].
    - eapply VDS_TauL; [exact Ht1 | exact IH].
    - eapply VDS_TauR; [exact Ht2 | exact IH].
    - eapply VDS_ReadL; [exact Ht1 | exact Hlk | exact IH].
    - eapply VDS_ReadR; [exact Ht2 | exact Hlk | exact IH].
    - eapply VDS_WriteL; [exact Ht1 | exact IH].
    - eapply VDS_WriteR; [exact Ht2 | exact IH].
    - eapply VDS_DrawL; [exact Ht1 | exact Hv | exact IH].
    - eapply VDS_DrawR; [exact Ht2 | intros v Hv; exact (IH v Hv)].
  Qed.

  #[local] Instance mm_Proper_run_exc {A : Type} :
    Morphisms.Proper
      (Morphisms.respectful (eq_itree Logic.eq) (eq_itree Logic.eq))
      (@run_exc PaV A).
  Proof using.
    ginit; gcofix CIH; intros t1 t2 Heq.
    rewrite (unfold_run_exc_obs t1), (unfold_run_exc_obs t2).
    punfold Heq; red in Heq.
    destruct Heq as [r1 r2 <- | m1 m2 Hm | X e k1 k2 Hk | ? ? Hchk _ | ? ? Hchk _];
      try inversion Hchk; pclearbot.
    - gstep; constructor; reflexivity.
    - gstep; constructor; gfinal; left; exact (CIH m1 m2 Hm).
    - destruct (exc_of_event e) as [x |].
      + gstep; constructor; reflexivity.
      + gstep; constructor; intros y;
          gstep; constructor; gfinal; left;
          exact (CIH (k1 y) (k2 y) (Hk y)).
  Qed.

  #[local] Lemma mm_run_exc_vis_eq {A X}
    (e : @CFGEtop PaV X) (k : X -> @CFGtop PaV A) :
    exc_of_event e = None ->
    run_exc (Vis e k) ≅ Vis e (fun y => Tau (run_exc (k y))).
  Proof using.
    intros Hnone; rewrite unfold_run_exc_obs; cbn - [exc_of_event run_exc];
      rewrite Hnone; reflexivity.
  Qed.

  Lemma cfg_local_vdraw_sim_run_exc_aux (allow_call : bool) {R1 R2}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop) :
    forall s0 env1 env2
      (u1 : @CFGtop PaV R1) (u2 : @CFGtop PaV R2)
      (t1 : @CFGtop PaV (@exc PaV + R1)) (t2 : @CFGtop PaV (@exc PaV + R2)),
      run_exc u1 ≅ t1 ->
      run_exc u2 ≅ t2 ->
      vds_sim (@is_ub_cfg IP IPT) (@sync_cfg_b allow_call) EqE_CFG EqA_CFG
        (@cfg_event_post IP IPT) (@as_local_cfg IP IPT) (fun _ _ => None)
        (fun _ => RR) s0 env1 env2 u1 u2 ->
      vds_sim (@is_ub_cfg IP IPT) (@sync_cfg_b allow_call) EqE_CFG EqA_CFG
        (@cfg_event_post IP IPT) (@as_local_cfg IP IPT) (fun _ _ => None)
        (fun _ e1 e2 (x1 : @exc PaV + R1) (x2 : @exc PaV + R2) =>
           match x1, x2 with
           | inl a1, inl a2 => a1 = a2
           | inr r1, inr r2 => RR e1 e2 r1 r2
           | _, _ => False
           end) s0 env1 env2 t1 t2.
  Proof using.
    pcofix CIH.
    intros s0 env1 env2 u1 u2 t1 t2 Et1 Et2 Hsim; pstep.
    set (r_rel := fun s1 e1 e2 a1 a2 =>
                    exists v1 v2,
                      run_exc v1 ≅ a1 /\
                      run_exc v2 ≅ a2 /\
                      vds_sim (@is_ub_cfg IP IPT) (@sync_cfg_b allow_call) EqE_CFG EqA_CFG
                        (@cfg_event_post IP IPT) (@as_local_cfg IP IPT) (fun _ _ => None)
                        (fun _ => RR) s1 e1 e2 v1 v2).
    assert (Hr_eq : forall s1 e1 e2 a1 a1' a2 a2',
              a1 ≅ a1' -> a2 ≅ a2' -> r_rel s1 e1 e2 a1 a2 -> r_rel s1 e1 e2 a1' a2').
    { intros s1 e1 e2 a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv).
      exists v1, v2; split;
        [etransitivity; [exact Ev1 | exact Ea1]
        | split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv]]. }
    eapply vds_sim__mon with (r := r_rel);
      [| intros s1 e1 e2 a1 a2 (v1 & v2 & Ev1 & Ev2 & Hv);
         right; eapply CIH; [exact Ev1 | exact Ev2 | exact Hv]].
    eapply vds_sim__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
    punfold Hsim; clear t1 t2 Et1 Et2 CIH r.
    induction Hsim as [s0 env1 env2 u1 u2 Hstep
                       | s0 env1 env2 u1 mu1 u2 Hu1 _ IH
                       | s0 env1 env2 u1 u2 mu2 Hu2 _ IH
                       | s0 env1 env2 u1 x v k1 u2 Hu1 Hlk _ IH
                       | s0 env1 env2 u1 u2 x v k2 Hu2 Hlk _ IH
                       | s0 env1 env2 u1 x v k1 u2 Hu1 _ IH
                       | s0 env1 env2 u1 u2 x v k2 Hu2 _ IH
                       | s0 env1 env2 u1 dt v k1 u2 Hu1 Hv _ IH
                       | s0 env1 env2 u1 u2 dt k2 Hu2 _ IH].
    - eapply vds_sim__obs_eq;
        [exact Hr_eq | symmetry; apply unfold_run_exc_obs | symmetry; apply unfold_run_exc_obs |].
      unfold CFGtop, CFGEtop, MCFGtop, MCFGEtop in *.
      unfold vds_step_body in Hstep.
      destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        apply VDS_Step; cbn; exact Hstep.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        destruct Hstep as [Hstep | Hb]; [| inversion Hb].
        apply VDS_Step; cbn; exists m1, m2;
          split; [reflexivity | split; [reflexivity | exact Hstep]].
      + destruct Hstep as [Hub | Hvis].
        * rewrite (is_ub_cfg_exc_none ev1 Hub).
          apply VDS_Step; cbn; left; exact Hub.
        * destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk_f]]; [| | contradiction].
          -- rewrite (EqE_CFG_exc_of_event ev1 ev2 HE).
             destruct (exc_of_event ev2) as [ex |].
             ++ apply VDS_Step; cbn; reflexivity.
             ++ apply VDS_Step; cbn; right; left.
                split; [exact Hsync | split; [exact HE |]].
                intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp);
                  destruct HA as [HA | Hb]; [| inversion Hb].
                exists (Tau (k1 a1)), (Tau (k2 a2)).
                split; [rewrite unfold_run_exc_obs; reflexivity |].
                split; [rewrite unfold_run_exc_obs; reflexivity |].
                pstep; eapply VDS_TauL; [reflexivity |]; eapply VDS_TauR; [reflexivity |].
                punfold HA; exact HA.
          -- destruct ev1 as [| me1], ev2 as [| me2]; cbn in Hloc;
               try (destruct (as_local_mcfg me1); contradiction); try contradiction.
             destruct (as_local_mcfg me1) as [le1 |] eqn:Ele1,
                      (as_local_mcfg me2) as [le2 |] eqn:Ele2; try contradiction.
             destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction;
               destruct_sum1 me1; try discriminate Ele1;
               destruct_sum1 me2; try discriminate Ele2;
               inversion Ele1; subst; inversion Ele2; subst; cbn [exc_of_event].
             ++ destruct Hloc as (Hx & Hv & [Hr | Hb]); [| inversion Hb]; subst x2 v2.
                apply VDS_Step; cbn; right; right; left.
                split; [reflexivity | split; [reflexivity |]].
                exists (Tau (k1 tt)), (Tau (k2 tt)).
                split; [rewrite unfold_run_exc_obs; reflexivity |].
                split; [rewrite unfold_run_exc_obs; reflexivity |].
                pstep; eapply VDS_TauL; [reflexivity |]; eapply VDS_TauR; [reflexivity |].
                punfold Hr; exact Hr.
             ++ destruct Hloc as (Hx & Hlk & Hrd); subst x2.
                apply VDS_Step; cbn; right; right; left.
                split; [reflexivity | split; [exact Hlk |]].
                intros v Hv; specialize (Hrd v Hv); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
                exists (Tau (k1 v)), (Tau (k2 v)).
                split; [rewrite unfold_run_exc_obs; reflexivity |].
                split; [rewrite unfold_run_exc_obs; reflexivity |].
                pstep; eapply VDS_TauL; [reflexivity |]; eapply VDS_TauR; [reflexivity |].
                punfold Hrd; exact Hrd.
    - eapply vds_sim__obs_eq with (t1 := Tau (run_exc mu1)) (t2 := run_exc u2);
        [exact Hr_eq | symmetry; rewrite (unfold_run_exc_obs u1), Hu1; reflexivity | reflexivity |].
      eapply VDS_TauL; [reflexivity | exact IH].
    - eapply vds_sim__obs_eq with (t1 := run_exc u1) (t2 := Tau (run_exc mu2));
        [exact Hr_eq | reflexivity | symmetry; rewrite (unfold_run_exc_obs u2), Hu2; reflexivity |].
      eapply VDS_TauR; [reflexivity | exact IH].
    - eapply VDS_ReadL with (x := x) (k1 := fun y => Tau (run_exc (k1 y))).
      + rewrite Hu1, !bind_trigger, mm_run_exc_vis_eq; [reflexivity | reflexivity].
      + exact Hlk.
      + eapply VDS_TauL; [reflexivity | exact IH].
    - eapply VDS_ReadR with (x := x) (k2 := fun y => Tau (run_exc (k2 y))).
      + rewrite Hu2, !bind_trigger, mm_run_exc_vis_eq; [reflexivity | reflexivity].
      + exact Hlk.
      + eapply VDS_TauR; [reflexivity | exact IH].
    - eapply VDS_WriteL with (x := x) (v := v) (k1 := fun y => Tau (run_exc (k1 y))).
      + rewrite Hu1, !bind_trigger, mm_run_exc_vis_eq; [reflexivity | reflexivity].
      + eapply VDS_TauL; [reflexivity | exact IH].
    - eapply VDS_WriteR with (x := x) (v := v) (k2 := fun y => Tau (run_exc (k2 y))).
      + rewrite Hu2, !bind_trigger, mm_run_exc_vis_eq; [reflexivity | reflexivity].
      + eapply VDS_TauR; [reflexivity | exact IH].
    - eapply VDS_DrawL with (dt := dt) (v := v) (k1 := fun y => Tau (run_exc (k1 y))).
      + rewrite Hu1, !bind_trigger, mm_run_exc_vis_eq; [reflexivity | reflexivity].
      + exact Hv.
      + eapply VDS_TauL; [reflexivity | exact IH].
    - eapply VDS_DrawR with (dt := dt) (k2 := fun y => Tau (run_exc (k2 y))).
      + rewrite Hu2, !bind_trigger, mm_run_exc_vis_eq; [reflexivity | reflexivity].
      + intros v Hv; eapply VDS_TauR; [reflexivity | exact (IH v Hv)].
  Qed.

  Lemma cfg_local_vdraw_sim_run_exc (allow_call : bool) {R1 R2}
    (RR : @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    env1 env2 (u1 : @CFGtop PaV R1) (u2 : @CFGtop PaV R2) :
    cfg_local_vdraw_sim_b allow_call RR env1 env2 u1 u2 ->
    cfg_local_vdraw_sim_b allow_call
      (fun e1 e2 (x1 : @exc PaV + R1) (x2 : @exc PaV + R2) =>
         match x1, x2 with
         | inl a1, inl a2 => a1 = a2
         | inr r1, inr r2 => RR e1 e2 r1 r2
         | _, _ => False
         end) env1 env2 (run_exc u1) (run_exc u2).
  Proof using.
    intros H; eapply cfg_local_vdraw_sim_run_exc_aux; [reflexivity | reflexivity | exact H].
  Qed.

  Definition mm_exc_ret_refines (rv1 rv2 : @exc PaV + @dvalue PaV) : Prop :=
    match rv1, rv2 with
    | inl x1, inl x2 => x1 = x2
    | inr v1, inr v2 => mm_ret_dvalue_refines v1 v2
    | _, _ => False
    end.

  Lemma vds_cfg_trigger_mcfg_sync (allow_call : bool) {X}
    (me : @MCFGEtop PaV X)
    (Hsync : @sync_non_local_mcfg IP IPT X me = true)
    stk env1 env2 :
    cfg_vdraw_sim_b allow_call
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2 (ITree.trigger (inr1 me)) (ITree.trigger (inr1 me)).
  Proof using.
    pstep; apply VDS_Step; unfold vds_step_body, ITree.trigger; cbn [observe sync_cfg_b].
    right; left; split; [exact Hsync | split; [apply EqE_CFG_refl |]].
    intros a1 a2 Ha _; apply EqA_CFG_eq in Ha; subst a2.
    left; apply vds_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma vds_cfg_trigger_cast_sync (allow_call : bool) {F : Type -> Type} `{F -< @CFGEtop PaV}
    (e : F void)
    (Hsync : sync_cfg_b allow_call (subevent _ e) = true)
    (Hrefl : EqE_CFG void void (subevent _ e) (subevent _ e))
    {R1 R2} (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    stk env1 env2 :
    cfg_vdraw_sim_b allow_call RR stk env1 env2 (trigger_cast e) (trigger_cast e).
  Proof using.
    unfold trigger_cast, ITree.trigger; pstep; apply VDS_Step;
      unfold vds_step_body; rewrite !observe_bind; cbn.
    right; left; split; [exact Hsync | split; [exact Hrefl | intros []]].
  Qed.

  Lemma vds_cfg_EOU (allow_call : bool) {A} (m : EOU A) stk env1 env2 :
    cfg_vdraw_sim_b allow_call
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2 (EOU_to_itree m) (EOU_to_itree m).
  Proof using.
    destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - unfold raise; apply vds_cfg_trigger_cast_sync; [reflexivity | apply EqE_CFG_refl].
    - unfold raiseOOM; apply vds_cfg_trigger_cast_sync; [reflexivity | apply EqE_CFG_refl].
    - unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply VDS_Step;
        unfold vds_step_body; rewrite !observe_bind; cbn; left; reflexivity.
    - apply vds_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma vds_cfg_apply_attrs (allow_call : bool)
    (attrs : list param_attr) (msg : string) (v : @dvalue PaV)
    stk env1 env2 :
    cfg_vdraw_sim_b allow_call
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2 (apply_attrs attrs msg v) (apply_attrs attrs msg v).
  Proof using.
    unfold apply_attrs.
    eapply vds_sim_bind; [apply vds_cfg_EOU | intros ? ? ? v' _ (-> & -> & -> & <-)].
    eapply vds_sim_bind with
      (RR := fun stk' e1' e2' (r1 r2 : unit) => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2).
    - unfold assert_attrs_dereferenceable.
      destruct (find_option attr_dereferenceable attrs) as [[on n] |];
        [| apply vds_sim_ret; repeat split; reflexivity].
      destruct v' as [[p | | | | | | |] | |];
        try (apply vds_sim_ret; repeat split; reflexivity).
      unfold assert_dereferenceable.
      destruct (_ || _).
      + apply vds_sim_ret; repeat split; reflexivity.
      + eapply vds_sim_bind.
        * unfold load, trigger_cast; apply vds_cfg_trigger_mcfg_sync; reflexivity.
        * intros ? ? ? _ _ (-> & -> & -> & _); apply vds_sim_ret; repeat split; reflexivity.
    - intros ? ? ? _ _ (-> & -> & -> & _); apply vds_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma vds_cfg_apply_args_attrs (allow_call : bool) attrss msg args :
    forall stk env1 env2,
      cfg_vdraw_sim_b allow_call
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2 (apply_args_attrs attrss msg args) (apply_args_attrs attrss msg args).
  Proof using.
    revert attrss; induction args as [| v vs IH]; intros attrss stk env1 env2; cbn [apply_args_attrs].
    - apply vds_sim_ret; repeat split; reflexivity.
    - destruct attrss as [| a r];
        (eapply vds_sim_bind; [apply vds_cfg_apply_attrs |];
         intros ? ? ? v' _ (-> & -> & -> & <-);
         eapply vds_sim_bind; [apply IH |];
         intros ? ? ? vs' _ (-> & -> & -> & <-);
         apply vds_sim_ret; repeat split; reflexivity).
  Qed.

  Lemma vds_cfg_check_call_return_eq (allow_call : bool)
    fattrs ret_attrs ranges loc args rv stk env1 env2 :
    cfg_vdraw_sim_b allow_call
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2
      (check_call_return fattrs ret_attrs ranges loc args rv)
      (check_call_return fattrs ret_attrs ranges loc args rv).
  Proof using.
    unfold check_call_return.
    eapply vds_sim_bind; [apply vds_cfg_EOU | intros ? ? ? [] _ (-> & -> & -> & <-)].
    destruct rv as [ex | v].
    - apply vds_sim_ret; repeat split; reflexivity.
    - eapply vds_sim_bind; [apply vds_cfg_apply_attrs |].
      intros ? ? ? v' _ (-> & -> & -> & <-); apply vds_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_vdraw_sim_check_call_return_ret (allow_call : bool)
    (fattrs : list fn_attr) (ret_attrs : list param_attr)
    (loc : string) (args : list (@dvalue PaV))
    (rv1 rv2 : @exc PaV + @dvalue PaV)
    stk env1 env2
    (Hrv : mm_exc_ret_refines rv1 rv2) :
    cfg_vdraw_sim_b allow_call
      (fun stk' e1' e2' r1 r2 =>
         stk' = stk /\ e1' = env1 /\ e2' = env2 /\
         mm_exc_ret_refines r1 r2 /\
         (rv1 = rv2 -> r1 = r2) /\
         (existsb attr_is_noundef ret_attrs = true -> r1 = r2))
      stk env1 env2
      (check_call_return fattrs ret_attrs None loc args rv1)
      (check_call_return fattrs ret_attrs None loc args rv2).
  Proof using.
    destruct rv1 as [x1 | v1], rv2 as [x2 | v2]; cbn in Hrv; try contradiction.
    - subst x2.
      eapply vds_sim_weaken; [| apply vds_cfg_check_call_return_eq].
      intros ? ? ? r1 r2 (-> & -> & -> & <-).
      split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
      split; [destruct r1; [reflexivity | apply mm_ret_dvalue_refines_refl] |].
      split; intros _; reflexivity.
    - destruct Hrv as [<- | [-> Hv2]].
      + eapply vds_sim_weaken; [| apply vds_cfg_check_call_return_eq].
        intros ? ? ? r1 r2 (-> & -> & -> & <-).
        split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
        split; [destruct r1; [reflexivity | apply mm_ret_dvalue_refines_refl] |].
        split; intros _; reflexivity.
      + unfold check_call_return, check_call_result.
        destruct (existsb fn_attr_is_noreturn fattrs).
        * cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree EOU_to_itree].
          unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply VDS_Step;
            unfold vds_step_body; rewrite !observe_bind; cbn; left; reflexivity.
        * cbn [dvalue_well_defined negb].
          destruct (existsb fn_attr_is_nocreateundeforpoison fattrs && forallb dvalue_well_defined args);
            cbn [andb ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree EOU_to_itree].
          -- unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply VDS_Step;
               unfold vds_step_body; rewrite !observe_bind; cbn; left; reflexivity.
          -- eapply vds_sim_obs_eq;
               [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
             cbn [value_metadata_range]; unfold apply_attrs, apply_value_attrs; cbv zeta.
             rewrite value_attrs_poison_poison.
             pose proof (value_attrs_poison_scalar_nonptr ret_attrs v2 Hv2) as Hv2'.
             cbn [dvalue_well_defined negb].
             destruct (existsb attr_is_noundef ret_attrs) eqn:Enu;
               cbn [andb ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree EOU_monad EOU_to_itree].
             ++ unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply VDS_Step;
                  unfold vds_step_body; rewrite !observe_bind; cbn; left; reflexivity.
             ++ eapply vds_sim_obs_eq with
                  (t1 := Ret (inr (DVALUE_Base DVALUE_Poison)))
                  (t2 := Ret (inr (value_attrs_poison ret_attrs v2))).
                ** symmetry; rewrite Eqit.bind_bind, Eqit.bind_ret_l; unfold assert_attrs_dereferenceable.
                   destruct (find_option attr_dereferenceable ret_attrs) as [[on n] |];
                     cbn [ExtLib.Structures.Monad.ret Monad_itree];
                     rewrite Eqit.bind_bind, !Eqit.bind_ret_l; reflexivity.
                ** symmetry; rewrite Eqit.bind_bind, Eqit.bind_ret_l; unfold assert_attrs_dereferenceable.
                   destruct (find_option attr_dereferenceable ret_attrs) as [[on n] |];
                     [destruct (value_attrs_poison ret_attrs v2) as [[| | | | | | |] | |];
                        try contradiction |];
                     cbn [ExtLib.Structures.Monad.ret Monad_itree];
                     rewrite Eqit.bind_bind, !Eqit.bind_ret_l; reflexivity.
                ** apply vds_sim_ret.
                   split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
                   split; [right; split; [reflexivity | exact Hv2'] |].
                   split; [intros Heq; injection Heq as Heqv; rewrite <- Heqv, value_attrs_poison_poison; reflexivity
                          | intros H; discriminate H].
  Qed.

  Lemma cfg_vdraw_sim_denote_function_gen (allow_call : bool)
    (df1 df2 : definition dtyp (CFG.cfg dtyp))
    (RR_body : @dvalue PaV -> @dvalue PaV -> Prop)
    (HR_sub : forall v1 v2, RR_body v1 v2 -> mm_ret_dvalue_refines v1 v2)
    (Hproto : df_prototype df1 = df_prototype df2)
    (Hlen   : List.length (df_args df1) = List.length (df_args df2))
    (Hbody  : forall fvs va,
                List.length fvs = List.length (df_args df1) ->
                cfg_local_vdraw_sim_b allow_call (fun _ _ r1 r2 => RR_body r1 r2)
                  (init_local_env (List.combine (df_args df1) fvs))
                  (init_local_env (List.combine (df_args df2) fvs))
                  (denote_cfg (df_instrs df1) va)
                  (denote_cfg (df_instrs df2) va)) :
    forall stk env1 env2 cc args,
      cfg_vdraw_sim_b allow_call
        (fun stk' e1' e2' r1 r2 =>
           stk' = stk /\ e1' = env1 /\ e2' = env2 /\
           mm_exc_ret_refines r1 r2 /\
           ((forall a b, RR_body a b -> a = b) \/
            existsb attr_is_noundef (fst (dc_param_attrs (df_prototype df1))) = true ->
            r1 = r2))
        stk env1 env2 (denote_function df1 cc args) (denote_function df2 cc args).
  Proof using.
    intros stk env1 env2 cc args.
    unfold denote_function; cbv zeta; rewrite Hproto.
    destruct (dc_param_attrs (df_prototype df2)) as [ret_attrs args_attrs] eqn:Epa.
    cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    eapply vds_sim_bind;
      [apply vds_cfg_EOU | intros ? ? ? [] _ (-> & -> & -> & <-)].
    eapply vds_sim_bind;
      [apply vds_cfg_apply_args_attrs
      | intros ? ? ? args' _ (-> & -> & -> & <-)].
    eapply vds_sim_bind with
      (RR := fun stk' e1' e2' varg1 varg2 =>
               stk' = (env1, env2) :: stk /\
               (exists fvs vs,
                  List.length fvs = List.length (df_args df1) /\
                  e1' = init_local_env (List.combine (df_args df1) fvs) /\
                  e2' = init_local_env (List.combine (df_args df2) fvs)) /\
               varg1 = varg2).
    { unfold push_call_frame;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      destruct (combine_lists_varargs_same_len (df_args df1) (df_args df2) args' Hlen)
        as [[msg [Ec1 Ec2]] | (fvs & vs & Hlf & Ec1 & Ec2)].
      - rewrite Ec1, Ec2; cbn [EOU_to_itree].
        eapply vds_sim_bind with (RR := fun _ _ _ _ _ => False); [| intros ? ? ? ? ? []].
        unfold raise; apply vds_cfg_trigger_cast_sync; [reflexivity | apply EqE_CFG_refl].
      - rewrite Ec1, Ec2; cbn [EOU_to_itree ExtLib.Structures.Monad.ret Monad_itree].
        eapply vds_sim_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |];
          cbv beta iota zeta.
        eapply vds_sim_bind;
          [apply vds_cfg_EOU | intros ? ? ? dts _ (-> & -> & -> & <-)]; cbv zeta.
        eapply vds_sim_bind.
        { unfold mem_push, trigger_cast; apply vds_cfg_trigger_mcfg_sync; reflexivity. }
        intros ? ? ? [] _ (-> & -> & -> & <-).
        eapply vds_sim_bind with
          (RR := fun stk' e1' e2' (r1 r2 : unit) =>
                   stk' = (env1, env2) :: stk /\
                   e1' = init_local_env (List.combine (df_args df1) fvs) /\
                   e2' = init_local_env (List.combine (df_args df2) fvs) /\
                   r1 = r2).
        { unfold stack_push, trigger_cast; pstep; apply VDS_Step;
            unfold vds_step_body, ITree.trigger; cbn.
          right; right; right; left;
            apply vds_sim_ret; repeat split; reflexivity. }
        intros ? ? ? [] _ (-> & -> & -> & <-).
        eapply vds_sim_bind.
        { unfold alloca, trigger_cast; apply vds_cfg_trigger_mcfg_sync; reflexivity. }
        intros ? ? ? varargs _ (-> & -> & -> & <-).
        eapply vds_sim_bind.
        { unfold store, trigger_cast; apply vds_cfg_trigger_mcfg_sync; reflexivity. }
        intros ? ? ? [] _ (-> & -> & -> & <-).
        destruct varargs as [[p | | | | | | |] | |];
          try (unfold raise; apply vds_cfg_trigger_cast_sync;
               [reflexivity | apply EqE_CFG_refl]).
        apply vds_sim_ret;
          split; [reflexivity | split; [exists fvs, vs; repeat split; assumption | reflexivity]]. }
    intros ? ? ? varg _ (-> & (fvs & vs & Hlf & -> & ->) & <-).
    eapply vds_sim_bind.
    - change (denote_cfg_map (ocfg_map (blks (df_instrs df1))) (df_instrs df1) (Some varg))
        with (denote_cfg (df_instrs df1) (Some varg)).
      change (denote_cfg_map (ocfg_map (blks (df_instrs df2))) (df_instrs df2) (Some varg))
        with (denote_cfg (df_instrs df2) (Some varg)).
      apply cfg_local_vdraw_to_stack_sim_b.
      apply cfg_local_vdraw_sim_run_exc.
      exact (Hbody fvs (Some varg) Hlf).
    - intros ? final_e1 final_e2 rv1 rv2 (-> & Hrv).
      eapply vds_sim_bind with
        (RR := fun stk' e1' e2' (r1 r2 : unit) =>
                 stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2).
      { unfold pop_call_frame; cbn [ExtLib.Structures.Monad.bind Monad_itree].
        eapply vds_sim_bind with
          (RR := fun stk' e1' e2' (r1 r2 : unit) =>
                   stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2).
        - unfold stack_pop, trigger_cast; pstep; apply VDS_Step;
            unfold vds_step_body, ITree.trigger; cbn.
          right; right; right; left;
            apply vds_sim_ret; repeat split; reflexivity.
        - intros ? ? ? [] _ (-> & -> & -> & <-).
          unfold mem_pop, trigger_cast; apply vds_cfg_trigger_mcfg_sync; reflexivity. }
      intros ? ? ? [] _ (-> & -> & -> & <-).
      destruct rv1 as [x1 | v1], rv2 as [x2 | v2]; try contradiction.
          -- subst x2.
             eapply vds_sim_weaken; [| apply vds_cfg_check_call_return_eq].
             intros ? ? ? r1 r2 (-> & -> & -> & <-).
             split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
             split; [destruct r1; [reflexivity | apply mm_ret_dvalue_refines_refl] | intros _; reflexivity].
          -- pose proof (HR_sub v1 v2 Hrv) as Hret.
             eapply vds_sim_weaken;
               [| exact (cfg_vdraw_sim_check_call_return_ret allow_call
                           (dc_attrs (df_prototype df2)) ret_attrs
                           (show_raw_id (dc_name (df_prototype df2)))
                           args' (inr v1) (inr v2) stk env1 env2 Hret)].
             intros ? ? ? r1 r2 (-> & -> & -> & Hmr & Heq_rv & Hnu).
             cbn [fst].
             split; [reflexivity | split; [reflexivity | split; [reflexivity |]]].
             split; [exact Hmr |].
             intros [Heq_all | Hnu_true].
             ++ apply Heq_rv; f_equal; exact (Heq_all v1 v2 Hrv).
             ++ exact (Hnu Hnu_true).
  Qed.

  (** Lift [cfg_vdraw_sim_b] across [mm_mrec_ctx] and [interp_mrec]. *)
  Lemma cfg_vdraw_sim_mrec_ctx_eq
    (ctx1 ctx2 : IntMap (@function_denotation PaV))
    (Hctx : forall k,
              option_rel
                (fun f1 f2 =>
                   forall stk env1 env2 cc args,
                     cfg_vdraw_sim_b true
                       (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
                       stk env1 env2 (f1 cc args) (f2 cc args))
                (lookup k ctx1) (lookup k ctx2)) :
    forall stk env1 env2 dt cc fv fas,
      cfg_vdraw_sim_b true
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2
        (mm_mrec_ctx ctx1 _ (Call dt cc fv fas))
        (mm_mrec_ctx ctx2 _ (Call dt cc fv fas)).
  Proof using.
    intros stk env1 env2 dt cc fv fas.
    unfold mm_mrec_ctx; cbn [ExtLib.Structures.Monad.bind Monad_itree].
    eapply vds_sim_bind;
      [apply vds_cfg_EOU | intros ? ? ? [] _ (-> & -> & -> & <-)].
    assert (Hext :
      cfg_vdraw_sim_b true
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2
        (Functor.fmap (@inr (@exc PaV) _) (external_call dt fv fas))
        (Functor.fmap (@inr (@exc PaV) _) (external_call dt fv fas))).
    { cbn [Functor.fmap Functor_itree ITree.map]; unfold external_call, trigger_cast.
      eapply vds_sim_bind.
      - apply vds_cfg_trigger_mcfg_sync; reflexivity.
      - intros ? ? ? dv _ (-> & -> & -> & <-); apply vds_sim_ret; repeat split; reflexivity. }
    unfold lookup_defn.
    destruct fv as [[p | | | | | | |] | |]; try exact Hext.
    pose proof (Hctx (ptr_to_int p)) as Hlk.
    destruct Hlk as [| f1 f2 Hf12]; [exact Hext | apply Hf12].
  Qed.

  Lemma cfg_vdraw_sim_mrec_ctx_ret (allow_call : bool)
    (ctx1 ctx2 : IntMap (@function_denotation PaV))
    (Hctx : forall k,
              option_rel
                (fun f1 f2 =>
                   forall stk env1 env2 cc args,
                     cfg_vdraw_sim_b allow_call
                       (fun stk' e1' e2' r1 r2 =>
                          stk' = stk /\ e1' = env1 /\ e2' = env2 /\ mm_exc_ret_refines r1 r2)
                       stk env1 env2 (f1 cc args) (f2 cc args))
                (lookup k ctx1) (lookup k ctx2)) :
    forall stk env1 env2 dt cc fv fas,
      cfg_vdraw_sim_b allow_call
        (fun stk' e1' e2' r1 r2 =>
           stk' = stk /\ e1' = env1 /\ e2' = env2 /\ mm_exc_ret_refines r1 r2)
        stk env1 env2
        (mm_mrec_ctx ctx1 _ (Call dt cc fv fas))
        (mm_mrec_ctx ctx2 _ (Call dt cc fv fas)).
  Proof using.
    intros stk env1 env2 dt cc fv fas.
    unfold mm_mrec_ctx; cbn [ExtLib.Structures.Monad.bind Monad_itree].
    eapply vds_sim_bind;
      [apply vds_cfg_EOU | intros ? ? ? [] _ (-> & -> & -> & <-)].
    assert (Hext :
      cfg_vdraw_sim_b allow_call
        (fun stk' e1' e2' r1 r2 =>
           stk' = stk /\ e1' = env1 /\ e2' = env2 /\ mm_exc_ret_refines r1 r2)
        stk env1 env2
        (Functor.fmap (@inr (@exc PaV) _) (external_call dt fv fas))
        (Functor.fmap (@inr (@exc PaV) _) (external_call dt fv fas))).
    { cbn [Functor.fmap Functor_itree ITree.map]; unfold external_call, trigger_cast.
      eapply vds_sim_bind.
      - apply vds_cfg_trigger_mcfg_sync; reflexivity.
      - intros ? ? ? dv _ (-> & -> & -> & <-); apply vds_sim_ret.
        split; [reflexivity | split; [reflexivity | split; [reflexivity | apply mm_ret_dvalue_refines_refl]]]. }
    unfold lookup_defn.
    destruct fv as [[p | | | | | | |] | |]; try exact Hext.
    pose proof (Hctx (ptr_to_int p)) as Hlk.
    destruct Hlk as [| f1 f2 Hf12]; [exact Hext | apply Hf12].
  Qed.

  Lemma cfg_to_mcfg_vdraw_sim_mrec (allow_call : bool)
    (ctx1 ctx2 : IntMap (@function_denotation PaV))
    (Hctx : allow_call = true ->
            forall k,
              option_rel
                (fun f1 f2 =>
                   forall stk env1 env2 cc args,
                     cfg_vdraw_sim_b true
                       (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
                       stk env1 env2 (f1 cc args) (f2 cc args))
                (lookup k ctx1) (lookup k ctx2)) :
    forall {R1 R2}
      (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
      stk env1 env2
      (u1 : @CFGtop PaV R1) (u2 : @CFGtop PaV R2)
      (t1 : @MCFGtop PaV R1) (t2 : @MCFGtop PaV R2),
      interp_mrec (mm_mrec_ctx ctx1) u1 ≅ t1 ->
      interp_mrec (mm_mrec_ctx ctx2) u2 ≅ t2 ->
      cfg_vdraw_sim_b allow_call RR stk env1 env2 u1 u2 ->
      mcfg_vdraw_sim RR stk env1 env2 t1 t2.
  Proof using.
    intros R1 R2 RR.
    pcofix CIH.
    intros stk env1 env2 u1 u2 t1 t2 Et1 Et2 Hsim.
    pstep.
    set (r_rel := fun s0 e1 e2 a1 a2 =>
                    exists v1 v2,
                      interp_mrec (mm_mrec_ctx ctx1) v1 ≅ a1 /\
                      interp_mrec (mm_mrec_ctx ctx2) v2 ≅ a2 /\
                      cfg_vdraw_sim_b allow_call RR s0 e1 e2 v1 v2).
    assert (Hr_eq : forall s0 e1 e2 a1 a1' a2 a2',
              a1 ≅ a1' -> a2 ≅ a2' -> r_rel s0 e1 e2 a1 a2 -> r_rel s0 e1 e2 a1' a2').
    { intros s0 e1 e2 a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv).
      exists v1, v2; split;
        [etransitivity; [exact Ev1 | exact Ea1]
        | split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv]]. }
    eapply vds_sim__mon with (r := r_rel);
      [| intros s0 e1 e2 a1 a2 (v1 & v2 & Ev1 & Ev2 & Hv);
         right; eapply CIH; [exact Ev1 | exact Ev2 | exact Hv]].
    eapply vds_sim__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
    punfold Hsim; clear t1 t2 Et1 Et2 CIH r.
    induction Hsim as [stk env1 env2 u1 u2 Hstep
                       | stk env1 env2 u1 mu1 u2 Hu1 _ IH
                       | stk env1 env2 u1 u2 mu2 Hu2 _ IH
                       | stk env1 env2 u1 x v k1 u2 Hu1 Hlk _ IH
                       | stk env1 env2 u1 u2 x v k2 Hu2 Hlk _ IH
                       | stk env1 env2 u1 x v k1 u2 Hu1 _ IH
                       | stk env1 env2 u1 u2 x v k2 Hu2 _ IH
                       | stk env1 env2 u1 dt v k1 u2 Hu1 Hv _ IH
                       | stk env1 env2 u1 u2 dt k2 Hu2 _ IH].
    - eapply vds_sim__obs_eq;
        [exact Hr_eq | symmetry; apply unfold_interp_mrec | symmetry; apply unfold_interp_mrec |].
      unfold CFGtop, CFGEtop, MCFGtop, MCFGEtop in *.
      unfold vds_step_body in Hstep.
      destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        apply VDS_Step; cbn; exact Hstep.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        destruct Hstep as [Hstep | Hb]; [| inversion Hb].
        apply VDS_Step; cbn.
        exists m1, m2; split; [reflexivity | split; [reflexivity | exact Hstep]].
      + destruct Hstep as [Hub | Hvis].
        * destruct ev1 as [ce1 | me1]; [discriminate Hub |].
          apply VDS_Step; cbn; left; exact Hub.
        * destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          -- destruct ev1 as [ce1 | me1], ev2 as [ce2 | me2]; cbn in HE; try contradiction.
             ++ destruct allow_call; [| discriminate Hsync].
                destruct ce1 as [dt1 cc1 fv1 fas1], ce2 as [dt2 cc2 fv2 fas2].
                destruct HE as (<- & <- & <- & <-).
                apply VDS_Step; cbn.
                exists (ITree.bind (mm_mrec_ctx ctx1 _ (Call dt1 cc1 fv1 fas1)) k1),
                       (ITree.bind (mm_mrec_ctx ctx2 _ (Call dt1 cc1 fv1 fas1)) k2).
                split; [reflexivity | split; [reflexivity |]].
                eapply vds_sim_bind.
                ** apply (cfg_vdraw_sim_mrec_ctx_eq ctx1 ctx2 (Hctx Logic.eq_refl)).
                ** intros ? ? ? rv1 rv2 (-> & -> & -> & <-).
                   specialize (HA rv1 rv1 Logic.eq_refl I);
                     destruct HA as [HA | Hb]; [exact HA | inversion Hb].
             ++ apply VDS_Step; cbn; right; left.
                split; [exact Hsync | split; [exact HE |]].
                intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp);
                  destruct HA as [HA | Hb]; [| inversion Hb].
                exists (Tau (k1 a1)), (Tau (k2 a2)).
                split; [rewrite unfold_interp_mrec; reflexivity |].
                split; [rewrite unfold_interp_mrec; reflexivity |].
                pstep; eapply VDS_TauL; [reflexivity |]; eapply VDS_TauR; [reflexivity |].
                punfold HA; exact HA.
          -- destruct ev1 as [| me1], ev2 as [| me2]; cbn in Hloc;
               try (destruct (as_local_mcfg me1); contradiction); try contradiction.
             destruct (as_local_mcfg me1) as [le1 |] eqn:Ele1,
                      (as_local_mcfg me2) as [le2 |] eqn:Ele2; try contradiction.
             destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
             ++ destruct Hloc as (Hx & Hv & [Hr | Hb]); [| inversion Hb].
                apply VDS_Step; cbn; right; right; left.
                rewrite Ele1, Ele2; split; [exact Hx | split; [exact Hv |]].
                exists (Tau (k1 tt)), (Tau (k2 tt)).
                split; [rewrite unfold_interp_mrec; reflexivity |].
                split; [rewrite unfold_interp_mrec; reflexivity |].
                pstep; eapply VDS_TauL; [reflexivity |]; eapply VDS_TauR; [reflexivity |].
                punfold Hr; exact Hr.
             ++ destruct Hloc as (Hx & Hlk & Hrd).
                apply VDS_Step; cbn; right; right; left.
                rewrite Ele1, Ele2; split; [exact Hx | split; [exact Hlk |]].
                intros v Hv; specialize (Hrd v Hv);
                  destruct Hrd as [Hrd | Hb]; [| inversion Hb].
                exists (Tau (k1 v)), (Tau (k2 v)).
                split; [rewrite unfold_interp_mrec; reflexivity |].
                split; [rewrite unfold_interp_mrec; reflexivity |].
                pstep; eapply VDS_TauL; [reflexivity |]; eapply VDS_TauR; [reflexivity |].
                punfold Hrd; exact Hrd.
          -- destruct ev1 as [| me1], ev2 as [| me2]; cbn in Hstk;
               try (destruct (as_stack_mcfg me1); contradiction); try contradiction.
             destruct (as_stack_mcfg me1) as [se1 |] eqn:Ese1,
                      (as_stack_mcfg me2) as [se2 |] eqn:Ese2; try contradiction.
             destruct se1, se2; try contradiction.
             ++ destruct Hstk as [Hr | Hb]; [| inversion Hb].
                apply VDS_Step; cbn; right;
                  right; right; rewrite Ese1, Ese2.
                exists (Tau (k1 tt)), (Tau (k2 tt)).
                split; [rewrite unfold_interp_mrec; reflexivity |].
                split; [rewrite unfold_interp_mrec; reflexivity |].
                pstep; eapply VDS_TauL; [reflexivity |]; eapply VDS_TauR; [reflexivity |].
                punfold Hr; exact Hr.
             ++ apply VDS_Step; cbn; right;
                  right; right; rewrite Ese1, Ese2.
                destruct stk as [| [p1 p2] rest]; [exact I |].
                destruct Hstk as [Hr | Hb]; [| inversion Hb].
                exists (Tau (k1 tt)), (Tau (k2 tt)).
                split; [rewrite unfold_interp_mrec; reflexivity |].
                split; [rewrite unfold_interp_mrec; reflexivity |].
                pstep; eapply VDS_TauL; [reflexivity |]; eapply VDS_TauR; [reflexivity |].
                punfold Hr; exact Hr.
    - eapply vds_sim__obs_eq with (t1 := Tau (interp_mrec (mm_mrec_ctx ctx1) mu1))
                                  (t2 := interp_mrec (mm_mrec_ctx ctx2) u2);
        [exact Hr_eq
        | unfold CFGtop, CFGEtop in Hu1;
          symmetry; rewrite unfold_interp_mrec, Hu1; reflexivity
        | reflexivity |].
      eapply VDS_TauL; [reflexivity | exact IH].
    - eapply vds_sim__obs_eq with (t1 := interp_mrec (mm_mrec_ctx ctx1) u1)
                                  (t2 := Tau (interp_mrec (mm_mrec_ctx ctx2) mu2));
        [exact Hr_eq
        | reflexivity
        | unfold CFGtop, CFGEtop in Hu2;
          symmetry; rewrite unfold_interp_mrec, Hu2; reflexivity |].
      eapply VDS_TauR; [reflexivity | exact IH].
    - eapply VDS_ReadL with (x := x) (k1 := fun y => Tau (interp_mrec (mm_mrec_ctx ctx1) (k1 y))).
      + unfold CFGtop, CFGEtop in *; rewrite Hu1, !bind_trigger, unfold_interp_mrec;
          cbn [observe _interp_mrec subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr
               cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1];
          reflexivity.
      + exact Hlk.
      + eapply VDS_TauL; [reflexivity | exact IH].
    - eapply VDS_ReadR with (x := x) (k2 := fun y => Tau (interp_mrec (mm_mrec_ctx ctx2) (k2 y))).
      + unfold CFGtop, CFGEtop in *; rewrite Hu2, !bind_trigger, unfold_interp_mrec;
          cbn [observe _interp_mrec subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr
               cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1];
          reflexivity.
      + exact Hlk.
      + eapply VDS_TauR; [reflexivity | exact IH].
    - eapply VDS_WriteL with (x := x) (v := v) (k1 := fun y => Tau (interp_mrec (mm_mrec_ctx ctx1) (k1 y))).
      + unfold CFGtop, CFGEtop in *; rewrite Hu1, !bind_trigger, unfold_interp_mrec;
          cbn [observe _interp_mrec subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr
               cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1];
          reflexivity.
      + eapply VDS_TauL; [reflexivity | exact IH].
    - eapply VDS_WriteR with (x := x) (v := v) (k2 := fun y => Tau (interp_mrec (mm_mrec_ctx ctx2) (k2 y))).
      + unfold CFGtop, CFGEtop in *; rewrite Hu2, !bind_trigger, unfold_interp_mrec;
          cbn [observe _interp_mrec subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr
               cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1];
          reflexivity.
      + eapply VDS_TauR; [reflexivity | exact IH].
    - eapply VDS_DrawL with (dt := dt) (v := v) (k1 := fun y => Tau (interp_mrec (mm_mrec_ctx ctx1) (k1 y))).
      + unfold CFGtop, CFGEtop in *; rewrite Hu1, !bind_trigger, unfold_interp_mrec;
          cbn [observe _interp_mrec subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr
               cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1];
          reflexivity.
      + exact Hv.
      + eapply VDS_TauL; [reflexivity | exact IH].
    - eapply VDS_DrawR with (dt := dt) (k2 := fun y => Tau (interp_mrec (mm_mrec_ctx ctx2) (k2 y))).
      + unfold CFGtop, CFGEtop in *; rewrite Hu2, !bind_trigger, unfold_interp_mrec;
          cbn [observe _interp_mrec subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr
               cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun case_ Case_sum1 case_sum1];
          reflexivity.
      + intros v Hv; eapply VDS_TauR; [reflexivity | exact (IH v Hv)].
  Qed.

  Local Definition intr_step_rel {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (s0 : env_stack) (e1 e2 : @local_env PaV)
    (x1 : R1 + @MCFGtop PaV R1) (x2 : R2 + @MCFGtop PaV R2) : Prop :=
    match x1, x2 with
    | inl r1, inl r2 => RR s0 e1 e2 r1 r2
    | inr v1, inr v2 => mcfg_vdraw_sim RR s0 e1 e2 v1 v2
    | _, _ => False
    end.

  Local Lemma mcfg_vdraw_sim_intrinsics_step {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop) :
    forall stk env1 env2
      (u1 : @MCFGtop PaV R1) (u2 : @MCFGtop PaV R2),
      vds_step_body (@is_ub_mcfg IP IPT) (@sync_non_local_mcfg IP IPT) EqE_MCFG EqA_MCFG
        (@mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
        RR (upaco5 (vds_sim_ (@is_ub_mcfg IP IPT) (@sync_non_local_mcfg IP IPT) EqE_MCFG EqA_MCFG
                      (@mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT) RR) bot5)
        stk env1 env2 (observe u1) (observe u2) ->
      mcfg_vdraw_sim (intr_step_rel RR) stk env1 env2 (decomp_intr u1) (decomp_intr u2).
  Proof using.
    intros stk env1 env2 u1 u2 Hstep.
    unfold vds_step_body, decomp_intr in *.
    destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
    - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
      apply vds_sim_ret; exact Hstep.
    - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
      destruct Hstep as [Hstep | Hb]; [| inversion Hb].
      apply vds_sim_ret; exact Hstep.
    - destruct Hstep as [Hub | Hvis].
      + destruct_sum1 ev1; try discriminate Hub; destruct ev1 as [u].
        pstep; apply VDS_Step; unfold vds_step_body;
          rewrite observe_bind; cbn; left; reflexivity.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
        * destruct ev1 as [ec1 | [ie1 | re1]], ev2 as [ec2 | [ie2 | re2]]; cbn in HE; try contradiction.
          -- cbn [interp_intrinsics_h case_ Case_sum1 case_sum1
                  Case_sum1_Handler Handler.case_ E_trigger]; unfold ITree.trigger.
             pstep; apply VDS_Step; unfold vds_step_body; rewrite !observe_bind; cbn.
             right; left; split; [reflexivity | split; [exact HE |]].
             intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
             left; eapply vds_sim_obs_eq;
               [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
             apply vds_sim_ret; exact HA.
          -- destruct ie1 as [dt1 fn1 args1 va1], ie2 as [dt2 fn2 args2 va2].
             destruct HE as (<- & <- & <- & <-);
               cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
             eapply vds_sim_bind; [apply mcfg_stack_to_vdraw_sim, handle_intrinsics_sync |].
             intros ? ? ? a1 _ (-> & -> & -> & <-).
             specialize (HA a1 a1 Logic.eq_refl I); destruct HA as [HA | Hb]; [| inversion Hb].
             apply vds_sim_ret; exact HA.
          -- cbn [interp_intrinsics_h case_ Case_sum1 case_sum1
                  Case_sum1_Handler Handler.case_ F_trigger]; unfold ITree.trigger.
             pstep; apply VDS_Step; unfold vds_step_body; rewrite !observe_bind; cbn.
             right; left; split; [exact Hsync | split; [exact HE |]].
             intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
             left; eapply vds_sim_obs_eq;
               [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
             apply vds_sim_ret; exact HA.
        * destruct (as_local_mcfg ev1) as [le1 |] eqn:Ele1,
                   (as_local_mcfg ev2) as [le2 |] eqn:Ele2; try contradiction.
          destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction;
            destruct_sum1 ev1; try discriminate Ele1;
            destruct_sum1 ev2; try discriminate Ele2;
            inversion Ele1; subst; inversion Ele2; subst;
            cbn [interp_intrinsics_h case_ Case_sum1 case_sum1
                 Case_sum1_Handler Handler.case_ F_trigger];
            unfold ITree.trigger.
          -- destruct Hloc as (<- & <- & [Hr | Hb]); [| inversion Hb].
             pstep; apply VDS_Step; unfold vds_step_body; rewrite !observe_bind; cbn.
             right; right; left; split;
               [reflexivity | split; [reflexivity |]].
             left; eapply vds_sim_obs_eq;
               [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
             apply vds_sim_ret; exact Hr.
          -- destruct Hloc as (<- & Hlk & Hrd).
             pstep; apply VDS_Step; unfold vds_step_body; rewrite !observe_bind; cbn.
             right; right; left; split;
               [reflexivity | split; [exact Hlk |]].
             intros v Hv; specialize (Hrd v Hv); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
             left; eapply vds_sim_obs_eq;
               [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
             apply vds_sim_ret; exact Hrd.
        * destruct (as_stack_mcfg ev1) as [se1 |] eqn:Ese1,
                   (as_stack_mcfg ev2) as [se2 |] eqn:Ese2; try contradiction.
          destruct se1, se2; try contradiction;
            destruct_sum1 ev1; try discriminate Ese1;
            destruct_sum1 ev2; try discriminate Ese2;
            inversion Ese1; subst; inversion Ese2; subst;
            cbn [interp_intrinsics_h case_ Case_sum1 case_sum1
                 Case_sum1_Handler Handler.case_ F_trigger];
            unfold ITree.trigger.
          -- destruct Hstk as [Hr | Hb]; [| inversion Hb].
             pstep; apply VDS_Step; unfold vds_step_body; rewrite !observe_bind; cbn.
             right; right; right.
             left; eapply vds_sim_obs_eq;
               [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
             apply vds_sim_ret; exact Hr.
          -- pstep; apply VDS_Step; unfold vds_step_body; rewrite !observe_bind; cbn.
             right; right; right.
             destruct stk as [| [p1 p2] rest]; [exact I |].
             destruct Hstk as [Hr | Hb]; [| inversion Hb].
             left; eapply vds_sim_obs_eq;
               [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
             apply vds_sim_ret; exact Hr.
  Qed.

  Local Definition intr_r_both {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (s0 : env_stack) (e1 e2 : @local_env PaV)
    (a1 : @MCFGtop PaV R1) (a2 : @MCFGtop PaV R2) : Prop :=
    (exists v1 v2,
       interp_intrinsics v1 ≅ a1 /\
       interp_intrinsics v2 ≅ a2 /\
       mcfg_vdraw_sim RR s0 e1 e2 v1 v2) \/
    (exists w1 w2,
       ITree.bind w1 intr_cont ≅ a1 /\
       ITree.bind w2 intr_cont ≅ a2 /\
       mcfg_vdraw_sim (intr_step_rel RR) s0 e1 e2 w1 w2).

  Local Lemma intr_r_both_obs_eq {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop) :
    forall s0 e1 e2 a1 a1' a2 a2',
      a1 ≅ a1' -> a2 ≅ a2' -> intr_r_both RR s0 e1 e2 a1 a2 -> intr_r_both RR s0 e1 e2 a1' a2'.
  Proof using.
    intros s0 e1 e2 a1 a1' a2 a2' Ea1 Ea2 Hrb; unfold intr_r_both in Hrb |- *.
    destruct Hrb as [(v1 & v2 & Ev1 & Ev2 & Hv) | (w1 & w2 & Ew1 & Ew2 & Hw)].
    - left; exists v1, v2; split;
        [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hv]].
    - right; exists w1, w2; split;
        [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hw]].
  Qed.

  Local Lemma mcfg_vdraw_sim_intrinsics_branch_b {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop) :
    forall stk env1 env2 w1 w2 t1 t2,
      ITree.bind w1 intr_cont ≅ t1 ->
      ITree.bind w2 intr_cont ≅ t2 ->
      mcfg_vdraw_sim (intr_step_rel RR) stk env1 env2 w1 w2 ->
      vds_sim_ (@is_ub_mcfg IP IPT) (@sync_non_local_mcfg IP IPT) EqE_MCFG EqA_MCFG
        (@mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT) RR (intr_r_both RR)
        stk env1 env2 t1 t2.
  Proof using.
    intros stk env1 env2 w1 w2 t1 t2 Et1 Et2 Hw.
    eapply vds_sim__obs_eq; [exact (intr_r_both_obs_eq RR) | exact Et1 | exact Et2 |].
    punfold Hw; clear t1 t2 Et1 Et2.
    induction Hw as [stk env1 env2 w1 w2 Hstep
                     | stk env1 env2 w1 mw1 w2 Hw1 _ IH
                     | stk env1 env2 w1 w2 mw2 Hw2 _ IH
                     | stk env1 env2 w1 x v kw1 w2 Hw1 Hlk _ IH
                     | stk env1 env2 w1 w2 x v kw2 Hw2 Hlk _ IH
                     | stk env1 env2 w1 x v kw1 w2 Hw1 _ IH
                     | stk env1 env2 w1 w2 x v kw2 Hw2 _ IH
                     | stk env1 env2 w1 dt v kw1 w2 Hw1 Hv _ IH
                     | stk env1 env2 w1 w2 dt kw2 Hw2 _ IH].
    - unfold vds_step_body in Hstep.
      destruct (observe w1) as [x1 | mw1 | X1 ev1 kw1] eqn:How1.
      + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
        destruct x1 as [r1 | v1], x2 as [r2 | v2]; cbn in Hstep; try contradiction.
        * apply VDS_Step; unfold vds_step_body;
            rewrite !observe_bind, How1, How2; cbn; exact Hstep.
        * apply VDS_Step; unfold vds_step_body; rewrite !observe_bind, How1, How2; cbn.
          unfold intr_r_both; left; exists v1, v2;
            split; [reflexivity | split; [reflexivity | exact Hstep]].
      + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
        destruct Hstep as [Hstep | Hb]; [| inversion Hb].
        apply VDS_Step; unfold vds_step_body; rewrite !observe_bind, How1, How2.
        unfold intr_r_both; right; exists mw1, mw2;
          split; [reflexivity | split; [reflexivity | exact Hstep]].
      + apply VDS_Step; unfold vds_step_body; rewrite (observe_bind w1 intr_cont), How1.
        destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
        rewrite (observe_bind w2 intr_cont), How2.
        destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
        * left; split; [exact Hsync | split; [exact HE |]].
          intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
          unfold intr_r_both; right; exists (kw1 a1), (kw2 a2);
            split; [reflexivity | split; [reflexivity | exact HA]].
        * right; left.
          destruct (as_local_mcfg ev1) as [le1 |], (as_local_mcfg ev2) as [le2 |]; try contradiction.
          destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
          -- destruct Hloc as (Hx & Hv & [Hr | Hb]); [| inversion Hb].
             split;
               [exact Hx
               | split;
                   [exact Hv
                   | unfold intr_r_both; right; exists (kw1 tt), (kw2 tt);
                     split; [reflexivity | split; [reflexivity | exact Hr]]]].
          -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
             intros v Hv; specialize (Hrd v Hv); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
             unfold intr_r_both; right; exists (kw1 v), (kw2 v);
               split; [reflexivity | split; [reflexivity | exact Hrd]].
        * right; right.
          destruct (as_stack_mcfg ev1) as [se1 |], (as_stack_mcfg ev2) as [se2 |]; try contradiction.
          destruct se1, se2; try contradiction.
          -- destruct Hstk as [Hr | Hb]; [| inversion Hb].
             unfold intr_r_both; right; exists (kw1 tt), (kw2 tt);
               split; [reflexivity | split; [reflexivity | exact Hr]].
          -- destruct stk as [| [p1 p2] rest]; [exact I |].
             destruct Hstk as [Hr | Hb]; [| inversion Hb].
             unfold intr_r_both; right; exists (kw1 tt), (kw2 tt);
               split; [reflexivity | split; [reflexivity | exact Hr]].
    - eapply VDS_TauL; [rewrite (observe_bind w1 intr_cont), Hw1; reflexivity | exact IH].
    - eapply VDS_TauR; [rewrite (observe_bind w2 intr_cont), Hw2; reflexivity | exact IH].
    - eapply VDS_ReadL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
    - eapply VDS_ReadR; [rewrite Hw2, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
    - eapply VDS_WriteL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
    - eapply VDS_WriteR; [rewrite Hw2, Eqit.bind_bind; reflexivity | exact IH].
    - eapply VDS_DrawL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact Hv | exact IH].
    - eapply VDS_DrawR; [rewrite Hw2, Eqit.bind_bind; reflexivity | intros v Hv; exact (IH v Hv)].
  Qed.

  Local Lemma mcfg_vdraw_sim_intrinsics_branch_a {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop) :
    forall stk env1 env2 u1 u2 t1 t2,
      interp_intrinsics u1 ≅ t1 ->
      interp_intrinsics u2 ≅ t2 ->
      mcfg_vdraw_sim RR stk env1 env2 u1 u2 ->
      vds_sim_ (@is_ub_mcfg IP IPT) (@sync_non_local_mcfg IP IPT) EqE_MCFG EqA_MCFG
        (@mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT) RR (intr_r_both RR)
        stk env1 env2 t1 t2.
  Proof using.
    intros stk env1 env2 u1 u2 t1 t2 Et1 Et2 Hu.
    eapply vds_sim__obs_eq; [exact (intr_r_both_obs_eq RR) | exact Et1 | exact Et2 |].
    punfold Hu; clear t1 t2 Et1 Et2.
    induction Hu as [stk env1 env2 u1 u2 Hstep
                     | stk env1 env2 u1 mu1 u2 Hu1 _ IH
                     | stk env1 env2 u1 u2 mu2 Hu2 _ IH
                     | stk env1 env2 u1 x v k1 u2 Hu1 Hlk _ IH
                     | stk env1 env2 u1 u2 x v k2 Hu2 Hlk _ IH
                     | stk env1 env2 u1 x v k1 u2 Hu1 _ IH
                     | stk env1 env2 u1 u2 x v k2 Hu2 _ IH
                     | stk env1 env2 u1 dt v k1 u2 Hu1 Hv _ IH
                     | stk env1 env2 u1 u2 dt k2 Hu2 _ IH].
    - eapply mcfg_vdraw_sim_intrinsics_branch_b;
        [apply decomp_intr_spec
        | apply decomp_intr_spec
        | apply mcfg_vdraw_sim_intrinsics_step, Hstep].
    - eapply vds_sim__obs_eq with (t1 := Tau (interp_intrinsics mu1))
                                  (t2 := interp_intrinsics u2);
        [exact (intr_r_both_obs_eq RR)
        | symmetry; rewrite (itree_eta u1), Hu1, interp_intrinsics_Tau; reflexivity
        | reflexivity |].
      eapply VDS_TauL; [reflexivity | exact IH].
    - eapply vds_sim__obs_eq with (t1 := interp_intrinsics u1)
                                  (t2 := Tau (interp_intrinsics mu2));
        [exact (intr_r_both_obs_eq RR)
        | reflexivity
        | symmetry; rewrite (itree_eta u2), Hu2, interp_intrinsics_Tau; reflexivity |].
      eapply VDS_TauR; [reflexivity | exact IH].
    - eapply VDS_ReadL with (x := x) (k1 := fun y => Tau (interp_intrinsics (k1 y))).
      + rewrite Hu1, !bind_trigger, interp_intrinsics_vis_eqit;
          cbn - [interp_intrinsics ITree.trigger ITree.bind]; unfold F_trigger;
          cbn - [interp_intrinsics ITree.trigger ITree.bind]; rewrite bind_trigger; reflexivity.
      + exact Hlk.
      + eapply VDS_TauL; [reflexivity | exact IH].
    - eapply VDS_ReadR with (x := x) (k2 := fun y => Tau (interp_intrinsics (k2 y))).
      + rewrite Hu2, !bind_trigger, interp_intrinsics_vis_eqit;
          cbn - [interp_intrinsics ITree.trigger ITree.bind]; unfold F_trigger;
          cbn - [interp_intrinsics ITree.trigger ITree.bind]; rewrite bind_trigger; reflexivity.
      + exact Hlk.
      + eapply VDS_TauR; [reflexivity | exact IH].
    - eapply VDS_WriteL with (x := x) (v := v) (k1 := fun y => Tau (interp_intrinsics (k1 y))).
      + rewrite Hu1, !bind_trigger, interp_intrinsics_vis_eqit;
          cbn - [interp_intrinsics ITree.trigger ITree.bind]; unfold F_trigger;
          cbn - [interp_intrinsics ITree.trigger ITree.bind]; rewrite bind_trigger; reflexivity.
      + eapply VDS_TauL; [reflexivity | exact IH].
    - eapply VDS_WriteR with (x := x) (v := v) (k2 := fun y => Tau (interp_intrinsics (k2 y))).
      + rewrite Hu2, !bind_trigger, interp_intrinsics_vis_eqit;
          cbn - [interp_intrinsics ITree.trigger ITree.bind]; unfold F_trigger;
          cbn - [interp_intrinsics ITree.trigger ITree.bind]; rewrite bind_trigger; reflexivity.
      + eapply VDS_TauR; [reflexivity | exact IH].
    - eapply VDS_DrawL with (dt := dt) (v := v) (k1 := fun y => Tau (interp_intrinsics (k1 y))).
      + rewrite Hu1, !bind_trigger, interp_intrinsics_vis_eqit;
          cbn - [interp_intrinsics ITree.trigger ITree.bind]; unfold F_trigger;
          cbn - [interp_intrinsics ITree.trigger ITree.bind]; rewrite bind_trigger; reflexivity.
      + exact Hv.
      + eapply VDS_TauL; [reflexivity | exact IH].
    - eapply VDS_DrawR with (dt := dt) (k2 := fun y => Tau (interp_intrinsics (k2 y))).
      + rewrite Hu2, !bind_trigger, interp_intrinsics_vis_eqit;
          cbn - [interp_intrinsics ITree.trigger ITree.bind]; unfold F_trigger;
          cbn - [interp_intrinsics ITree.trigger ITree.bind]; rewrite bind_trigger; reflexivity.
      + intros v Hv; eapply VDS_TauR; [reflexivity | exact (IH v Hv)].
  Qed.

  (** Lift [mcfg_vdraw_sim] across [interp_intrinsics]. *)
  Lemma mcfg_vdraw_sim_interp_intrinsics {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop) :
    forall stk env1 env2
      (u1 : @MCFGtop PaV R1) (u2 : @MCFGtop PaV R2),
      mcfg_vdraw_sim RR stk env1 env2 u1 u2 ->
      mcfg_vdraw_sim RR stk env1 env2 (interp_intrinsics u1) (interp_intrinsics u2).
  Proof using.
    assert (Hmain :
      forall stk env1 env2 t1 t2,
        intr_r_both RR stk env1 env2 t1 t2 ->
        mcfg_vdraw_sim RR stk env1 env2 t1 t2).
    { pcofix CIH.
      intros stk env1 env2 t1 t2 Hrb; pstep.
      eapply vds_sim__mon with (r := intr_r_both RR);
        [| intros s0 e1 e2 a1 a2 Hr; right; apply CIH, Hr].
      unfold intr_r_both in Hrb.
      destruct Hrb as [(v1 & v2 & Ev1 & Ev2 & Hv) | (w1 & w2 & Ew1 & Ew2 & Hw)].
      - eapply mcfg_vdraw_sim_intrinsics_branch_a; eassumption.
      - eapply mcfg_vdraw_sim_intrinsics_branch_b; eassumption. }
    intros stk env1 env2 u1 u2 Hsim.
    apply Hmain; unfold intr_r_both; left; exists u1, u2;
      split; [reflexivity | split; [reflexivity | exact Hsim]].
  Qed.

  (** Lower [mcfg_vdraw_sim] to [interp_state interp_vellvm_rel_draw_h]. *)
  Definition as_draw_mcfg {X} (e : @MCFGEtop PaV X) : option (@DrawE PaV X) :=
    match e with
    | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 de))))) => Some de
    | _ => None
    end.

  Lemma interp_vellvm_rel_draw_h_non_draw {X} (e : @MCFGEtop PaV X) (s : FusedS)
    (Hnd : as_draw_mcfg e = None) :
    interp_vellvm_rel_draw_h e s = lift_prov_to_draw (interp_vellvm_prov_h X e s).
  Proof using.
    destruct_sum1 e; try discriminate Hnd; reflexivity.
  Qed.

  Lemma lift_prov_to_draw_eq {T} (t1 t2 : itree ProvBotE T) :
    t1 ≅ t2 -> lift_prov_to_draw t1 ≅ lift_prov_to_draw t2.
  Proof using.
    revert t1 t2; pcofix CIH; intros t1 t2 Heq; pstep; red.
    unfold lift_prov_to_draw; rewrite !observe_translate.
    punfold Heq; red in Heq.
    destruct Heq as [r1 r2 <- | m1 m2 Hm | X e k1 k2 Hk | ? ? Hchk _ | ? ? Hchk _];
      try inversion Hchk; cbn; constructor.
    - reflexivity.
    - pclearbot; right; apply CIH, Hm.
    - intros x; specialize (Hk x); pclearbot; right; apply CIH, Hk.
  Qed.

  Lemma lift_prov_to_draw_vis {T X} (e : ProvBotE X) (k : X -> itree ProvBotE T) :
    lift_prov_to_draw (Vis e k) ≅ Vis (inr1 e) (fun x => lift_prov_to_draw (k x)).
  Proof using.
    unfold lift_prov_to_draw; rewrite unfold_translate; reflexivity.
  Qed.

  Lemma interp_vellvm_rel_draw_h_stack_sync {X1 X2}
    (e1 : @MCFGEtop PaV X1) (e2 : @MCFGEtop PaV X2)
    (Hsync : sync_non_local_mcfg e1 = true)
    (HE : EqE_MCFG X1 X2 e1 e2)
    stk env1 env2 (s1 s2 : FusedS)
    (Hmatch : fused_state_match stk env1 env2 s1 s2)
    (U : list N) :
    refine_prov_draw
      (fun _ '(s1', a1) '(s2', a2) =>
         fused_state_match stk env1 env2 s1' s2' /\
         EqA_MCFG X1 X2 e1 a1 e2 a2 /\
         mcfg_event_post e1 a1)
      U (interp_vellvm_rel_draw_h e1 s1) (interp_vellvm_rel_draw_h e2 s2).
  Proof using.
    destruct (as_draw_mcfg e1) as [d1 |] eqn:Ed1.
    - destruct_sum1 e1; try discriminate Ed1;
        destruct_sum1 e2; cbn in HE; try contradiction.
      destruct e1 as [dt1], e2 as [dt2]; cbn in HE; subst dt2.
      unfold interp_vellvm_rel_draw_h;
        cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_]; unfold ITree.trigger.
      pstep; apply RPD_Step; unfold rpd_step_body; rewrite !observe_bind; cbn.
      right; right; split; [reflexivity | intros v Hv].
      left; eapply refine_prov_draw_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      pstep; apply RPD_Step; cbn [rpd_step_body observe EqA_MCFG mcfg_event_post].
      split; [exact Hmatch | split; [reflexivity | intros Hsc; exact (proj1 (Hv Hsc))]].
    - assert (Ed2 : as_draw_mcfg e2 = None).
      { destruct_sum2 e1 e2 HE; try discriminate Ed1; reflexivity. }
      rewrite (interp_vellvm_rel_draw_h_non_draw e1 s1 Ed1),
              (interp_vellvm_rel_draw_h_non_draw e2 s2 Ed2).
      apply refine_prov_to_rel_draw.
      eapply interp_vellvm_prov_h_stack_sync; eassumption.
  Qed.

  Definition rel_draw_model_step_state (R : Type) : Type :=
    (FusedS * R) + (FusedS * @MCFGtop PaV R).

  Definition rel_draw_model_cont (R : Type) (x : rel_draw_model_step_state R)
    : itree ProvDrawBotE (FusedS * R) :=
    match x with
    | inl sr => Ret sr
    | inr (s, u) => Tau (interp_state interp_vellvm_rel_draw_h u s)
    end.

  Definition decomp_rel_draw_model {R : Type} (u : @MCFGtop PaV R) (s : FusedS)
    : itree ProvDrawBotE (rel_draw_model_step_state R) :=
    match observe u with
    | RetF r => Ret (inl (s, r))
    | TauF m => Ret (inr (s, m))
    | VisF _ e k => ITree.bind (interp_vellvm_rel_draw_h e s) (fun '(s', x) => Ret (inr (s', k x)))
    end.

  Lemma decomp_rel_draw_model_spec {R : Type} (u : @MCFGtop PaV R) (s : FusedS) :
    ITree.bind (decomp_rel_draw_model u s) (rel_draw_model_cont R) ≅
    interp_state interp_vellvm_rel_draw_h u s.
  Proof using.
    unfold decomp_rel_draw_model; rewrite (unfold_interp_state interp_vellvm_rel_draw_h u s).
    destruct (observe u) as [r | m | X e k]; cbn -[interp_vellvm_rel_draw_h].
    - rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_bind; apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' x] ? <-; rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Definition rel_draw_model_stack_step_rel {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    : list N -> rel_draw_model_step_state R1 -> rel_draw_model_step_state R2 -> Prop :=
    fun _ x1 x2 =>
      match x1, x2 with
      | inl (s1, r1), inl (s2, r2) =>
          exists stk e1 e2, fused_state_match stk e1 e2 s1 s2 /\ RR stk e1 e2 r1 r2
      | inr (s1, u1), inr (s2, u2) =>
          exists stk e1 e2, fused_state_match stk e1 e2 s1 s2 /\ mcfg_vdraw_sim RR stk e1 e2 u1 u2
      | _, _ => False
      end.

  Local Lemma mcfg_vdraw_sim_to_model_step {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop) :
    forall U stk env1 env2 (s1 s2 : FusedS)
      (u1 : @MCFGtop PaV R1) (u2 : @MCFGtop PaV R2),
      fused_state_match stk env1 env2 s1 s2 ->
      vds_step_body (@is_ub_mcfg IP IPT) (@sync_non_local_mcfg IP IPT) EqE_MCFG EqA_MCFG
        (@mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
        RR (upaco5 (vds_sim_ (@is_ub_mcfg IP IPT) (@sync_non_local_mcfg IP IPT) EqE_MCFG EqA_MCFG
                      (@mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT) RR) bot5)
        stk env1 env2 (observe u1) (observe u2) ->
      refine_prov_draw (rel_draw_model_stack_step_rel RR) U
        (decomp_rel_draw_model u1 s1) (decomp_rel_draw_model u2 s2).
  Proof using.
    intros U stk env1 env2 s1 s2 u1 u2 Hmatch Hstep.
    unfold vds_step_body, decomp_rel_draw_model in *.
    destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
    - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
      pstep; apply RPD_Step; cbn;
        exists stk, env1, env2; split; assumption.
    - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
      destruct Hstep as [Hstep | Hb]; [| inversion Hb].
      pstep; apply RPD_Step; cbn;
        exists stk, env1, env2; split; assumption.
    - destruct Hstep as [Hub | Hvis].
      + destruct_sum1 ev1; try discriminate Hub; destruct ev1 as [u].
        pstep; apply RPD_Step; unfold rpd_step_body, interp_vellvm_rel_draw_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_trigger_prov, ITree.trigger, lift_prov_to_draw;
          repeat (rewrite observe_bind || rewrite observe_translate); cbn; left; reflexivity.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
        * eapply refine_prov_draw_bind;
            [eapply interp_vellvm_rel_draw_h_stack_sync; eassumption |].
          intros U' [s1' a1] [s2' a2] _ (Hm' & Ha & Hp).
          specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
          pstep; apply RPD_Step; cbn;
            exists stk, env1, env2; split; [exact Hm' | exact HA].
        * destruct (as_local_mcfg ev1) as [le1 |] eqn:Ele1,
                   (as_local_mcfg ev2) as [le2 |] eqn:Ele2; try contradiction.
          destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction;
            destruct_sum1 ev1; try discriminate Ele1;
            destruct_sum1 ev2; try discriminate Ele2;
            inversion Ele1; subst; inversion Ele2; subst;
            unfold interp_vellvm_rel_draw_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
            destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
          -- destruct Hloc as (<- & <- & [Hr | Hb]); [| inversion Hb].
             destruct Hmatch as (<- & <- & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
             eapply refine_prov_draw_obs_eq;
               [symmetry; rewrite (lift_prov_to_draw_eq _ _ (fused_local_prov_write _ _ _ _ _ _)),
                          lift_prov_to_draw_ret, Eqit.bind_ret_l; reflexivity
               | symmetry; rewrite (lift_prov_to_draw_eq _ _ (fused_local_prov_write _ _ _ _ _ _)),
                          lift_prov_to_draw_ret, Eqit.bind_ret_l; reflexivity |].
             pstep; apply RPD_Step; cbn.
             exists stk, (Maps.add x1 v1 env1), (Maps.add x1 v1 env2); split; [| exact Hr].
             rewrite Hvars1, Hvars2;
               repeat split; try exact Hexc; try exact Hloc; try exact Hsfm; reflexivity.
          -- destruct Hloc as (<- & Hlk_eq & Hrd).
             pose proof Hmatch as (Hmm & Hgg & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
             destruct (Maps.lookup x1 env1) as [v |] eqn:Elkv.
             ++ assert (Elkv2 : Maps.lookup x1 env2 = Some v) by congruence.
                eapply refine_prov_draw_obs_eq.
                ** symmetry;
                     rewrite (lift_prov_to_draw_eq _ _
                                (fused_local_prov_read_some x1 v (mm1, ((sf1, fstk1), gg1))
                                   (ltac:(cbn; rewrite Hvars1; exact Elkv)))),
                             lift_prov_to_draw_ret, Eqit.bind_ret_l; reflexivity.
                ** symmetry;
                     rewrite (lift_prov_to_draw_eq _ _
                                (fused_local_prov_read_some x1 v (mm2, ((sf2, fstk2), gg2))
                                   (ltac:(cbn; rewrite Hvars2; exact Elkv2)))),
                             lift_prov_to_draw_ret, Eqit.bind_ret_l; reflexivity.
                ** specialize (Hrd v Logic.eq_refl); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
                   pstep; apply RPD_Step; cbn;
                     exists stk, env1, env2; split; [exact Hmatch | exact Hrd].
             ++ assert (Elkv2 : Maps.lookup x1 env2 = None) by congruence.
                destruct (fused_local_prov_read_none x1 (mm1, ((sf1, fstk1), gg1))
                            (ltac:(cbn; rewrite Hvars1; exact Elkv))) as (msg1 & kf1 & Ef1).
                destruct (fused_local_prov_read_none x1 (mm2, ((sf2, fstk2), gg2))
                            (ltac:(cbn; rewrite Hvars2; exact Elkv2))) as (msg2 & kf2 & Ef2).
                eapply refine_prov_draw_obs_eq;
                  [symmetry; rewrite (lift_prov_to_draw_eq _ _ Ef1),
                             lift_prov_to_draw_vis, Eqit.bind_vis; reflexivity
                  | symmetry; rewrite (lift_prov_to_draw_eq _ _ Ef2),
                             lift_prov_to_draw_vis, Eqit.bind_vis; reflexivity |].
                pstep; apply RPD_Step; cbn;
                  right; right; split; [exact I | intros [] [] _].
        * destruct (as_stack_mcfg ev1) as [se1 |] eqn:Ese1,
                   (as_stack_mcfg ev2) as [se2 |] eqn:Ese2; try contradiction.
          destruct se1 as [bs1 | | |], se2 as [bs2 | | |]; try contradiction;
            destruct_sum1 ev1; try discriminate Ese1;
            destruct_sum1 ev2; try discriminate Ese2;
            inversion Ese1; subst; inversion Ese2; subst;
            unfold interp_vellvm_rel_draw_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
            destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]];
            destruct Hmatch as (<- & <- & Hsf & Hsfm).
          -- destruct Hstk as [Hr | Hb]; [| inversion Hb].
             assert (Hps1 :
               fused_stack_prov _ (StackPush bs1) (mm1, ((sf1, fstk1), gg1)) ≅
               Ret ((mm1, (({| stack_vars := init_local_env bs1; stack_exc := None;
                               stack_loc := Some (printer_object.(printer_get_loc) tt) |},
                            sf1 :: fstk1), gg1)), tt)).
             { unfold fused_stack_prov, on_ls_prov, handle_stack;
                 cbn - [Maps.lookup Maps.add lift_bot_prov init_local_env printer_get_loc].
               rewrite lift_bot_prov_bind_ret, lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity. }
             assert (Hps2 :
               fused_stack_prov _ (StackPush bs2) (mm1, ((sf2, fstk2), gg1)) ≅
               Ret ((mm1, (({| stack_vars := init_local_env bs2; stack_exc := None;
                               stack_loc := Some (printer_object.(printer_get_loc) tt) |},
                            sf2 :: fstk2), gg1)), tt)).
             { unfold fused_stack_prov, on_ls_prov, handle_stack;
                 cbn - [Maps.lookup Maps.add lift_bot_prov init_local_env printer_get_loc].
               rewrite lift_bot_prov_bind_ret, lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity. }
             eapply refine_prov_draw_obs_eq;
               [symmetry; rewrite (lift_prov_to_draw_eq _ _ Hps1),
                          lift_prov_to_draw_ret, Eqit.bind_ret_l; reflexivity
               | symmetry; rewrite (lift_prov_to_draw_eq _ _ Hps2),
                          lift_prov_to_draw_ret, Eqit.bind_ret_l; reflexivity |].
             pstep; apply RPD_Step; cbn.
             exists ((env1, env2) :: stk), (init_local_env bs1), (init_local_env bs2).
             split; [| exact Hr].
             repeat split; try reflexivity.
             apply SFM_cons; [exact Hsf | exact Hsfm].
          -- destruct stk as [| [p1 p2] rest].
             ++ inversion Hsfm; subst.
                unfold fused_stack_prov, on_ls_prov, handle_stack, raise, trigger_cast,
                       ITree.trigger, lift_bot_prov, lift_prov_to_draw;
                  cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret
                       ExtLib.Data.Monads.StateMonad.Monad_stateT Monad_itree].
                pstep; apply RPD_Step; unfold rpd_step_body;
                  repeat (rewrite observe_bind || rewrite observe_translate); cbn.
                right; right; split; [exact I | intros [] [] _].
             ++ destruct Hstk as [Hr | Hb]; [| inversion Hb].
                inversion Hsfm as [| ? ? sf1' sf2' ? fstk1' fstk2' Hsf' Hsfm']; subst.
                assert (Hpp1 :
                  fused_stack_prov _ StackPop (mm1, ((sf1, sf1' :: fstk1'), gg1)) ≅
                  Ret ((mm1, ((sf1', fstk1'), gg1)), tt)).
                { unfold fused_stack_prov, on_ls_prov, handle_stack;
                    cbn - [Maps.lookup Maps.add lift_bot_prov init_local_env printer_get_loc].
                  rewrite lift_bot_prov_bind_ret, lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity. }
                assert (Hpp2 :
                  fused_stack_prov _ StackPop (mm1, ((sf2, sf2' :: fstk2'), gg1)) ≅
                  Ret ((mm1, ((sf2', fstk2'), gg1)), tt)).
                { unfold fused_stack_prov, on_ls_prov, handle_stack;
                    cbn - [Maps.lookup Maps.add lift_bot_prov init_local_env printer_get_loc].
                  rewrite lift_bot_prov_bind_ret, lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity. }
                eapply refine_prov_draw_obs_eq;
                  [symmetry; rewrite (lift_prov_to_draw_eq _ _ Hpp1),
                             lift_prov_to_draw_ret, Eqit.bind_ret_l; reflexivity
                  | symmetry; rewrite (lift_prov_to_draw_eq _ _ Hpp2),
                             lift_prov_to_draw_ret, Eqit.bind_ret_l; reflexivity |].
                pstep; apply RPD_Step; cbn.
                exists rest, p1, p2; split; [| exact Hr].
                repeat (first [exact Hsf' | exact Hsfm' | reflexivity | split]).
  Qed.

  Local Definition rdm_r_both {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop)
    (U0 : list N)
    (a1 : itree ProvDrawBotE (FusedS * R1))
    (a2 : itree ProvDrawBotE (FusedS * R2)) : Prop :=
    (exists stk e1 e2 s1 s2 v1 v2,
       interp_state interp_vellvm_rel_draw_h v1 s1 ≅ a1 /\
       interp_state interp_vellvm_rel_draw_h v2 s2 ≅ a2 /\
       fused_state_match stk e1 e2 s1 s2 /\
       mcfg_vdraw_sim RR stk e1 e2 v1 v2) \/
    (exists w1 w2,
       ITree.bind w1 (rel_draw_model_cont R1) ≅ a1 /\
       ITree.bind w2 (rel_draw_model_cont R2) ≅ a2 /\
       refine_prov_draw (rel_draw_model_stack_step_rel RR) U0 w1 w2).

  Local Lemma rdm_r_both_obs_eq {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop) :
    forall U0 a1 a1' a2 a2',
      a1 ≅ a1' -> a2 ≅ a2' -> rdm_r_both RR U0 a1 a2 -> rdm_r_both RR U0 a1' a2'.
  Proof using.
    intros U0 a1 a1' a2 a2' Ea1 Ea2 Hrb; unfold rdm_r_both in Hrb |- *.
    destruct Hrb as [(stk & e1 & e2 & s1 & s2 & v1 & v2 & Ev1 & Ev2 & Hm & Hv) |
                     (w1 & w2 & Ew1 & Ew2 & Hw)].
    - left; exists stk, e1, e2, s1, s2, v1, v2.
      split; [etransitivity; eassumption |];
        split; [etransitivity; eassumption | split; assumption].
    - right; exists w1, w2.
      split; [etransitivity; eassumption |];
        split; [etransitivity; eassumption | exact Hw].
  Qed.

  Local Lemma mcfg_vdraw_sim_to_model_branch_b {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop) :
    forall U0 w1 w2 t1 t2,
      ITree.bind w1 (rel_draw_model_cont R1) ≅ t1 ->
      ITree.bind w2 (rel_draw_model_cont R2) ≅ t2 ->
      refine_prov_draw (rel_draw_model_stack_step_rel RR) U0 w1 w2 ->
      refine_prov_draw_
        (fun (_ : list N) '(s1', r1) '(s2', r2) =>
           exists stk' e1' e2',
             fused_state_match stk' e1' e2' s1' s2' /\ RR stk' e1' e2' r1 r2)
        (rdm_r_both RR) U0 t1 t2.
  Proof using.
    intros U0 w1 w2 t1 t2 Et1 Et2 Hw.
    eapply refine_prov_draw__obs_eq;
      [exact (rdm_r_both_obs_eq RR) | exact Et1 | exact Et2 |].
    punfold Hw; clear t1 t2 Et1 Et2.
    induction Hw as [U0 w1 w2 Hstep
                     | U0 w1 mw1 w2 Hw1 _ IH
                     | U0 w1 w2 mw2 Hw2 _ IH
                     | U0 w1 dt v kw1 w2 Hw1 Hv _ IH
                     | U0 w1 w2 dt kw2 Hw2 _ IH].
    - unfold rpd_step_body in Hstep.
      destruct (observe w1) as [x1 | mw1 | X1 ev1 kw1] eqn:How1.
      + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
        destruct x1 as [[s1 r1] | [s1 v1]], x2 as [[s2 r2] | [s2 v2]]; cbn in Hstep; try contradiction.
        * apply RPD_Step; unfold rpd_step_body;
            rewrite !observe_bind, How1, How2; cbn; exact Hstep.
        * destruct Hstep as (stk & e1 & e2 & Hm & Hv).
          apply RPD_Step; unfold rpd_step_body; rewrite !observe_bind, How1, How2; cbn.
          unfold rdm_r_both; left; exists stk, e1, e2, s1, s2, v1, v2;
            split; [reflexivity | split; [reflexivity | split; assumption]].
      + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction; pclearbot.
        apply RPD_Step; unfold rpd_step_body; rewrite !observe_bind, How1, How2.
        unfold rdm_r_both; right; exists mw1, mw2;
          split; [reflexivity | split; [reflexivity | exact Hstep]].
      + apply RPD_Step; unfold rpd_step_body;
          rewrite (observe_bind w1 (rel_draw_model_cont R1)), How1.
        destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left; destruct ev1 as [d1 | [p1 | b1]]; try contradiction; destruct p1.
          intros p Hp; specialize (Hleft p Hp); pclearbot.
          unfold rdm_r_both; right; exists (kw1 p), w2;
            split; [reflexivity | split; [reflexivity | exact Hleft]].
        * right; right.
          destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          rewrite (observe_bind w2 (rel_draw_model_cont R2)), How2.
          clear How1 How2;
            destruct ev1 as [d1 | [p1 | b1]], ev2 as [d2 | [p2 | b2]]; cbn in *; try contradiction.
          -- revert kw1 kw2 Hboth; destruct d1 as [dt1], d2 as [dt2];
               intros kw1 kw2 [Hdt Hd]; split; [exact Hdt |].
             intros v Hv; specialize (Hd v Hv); pclearbot.
             unfold rdm_r_both; right; exists (kw1 v), (kw2 v);
               split; [reflexivity | split; [reflexivity | exact Hd]].
          -- revert kw1 kw2 Hboth; destruct p1, p2;
               intros kw1 kw2 Hboth p Hp; specialize (Hboth p Hp); pclearbot.
             unfold rdm_r_both; right; exists (kw1 p), (kw2 p);
               split; [reflexivity | split; [reflexivity | exact Hboth]].
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
             unfold rdm_r_both; right; exists (kw1 a1), (kw2 a2);
               split; [reflexivity | split; [reflexivity | exact HA]].
    - eapply RPD_TauL; [rewrite (observe_bind w1 (rel_draw_model_cont R1)), Hw1; reflexivity | exact IH].
    - eapply RPD_TauR; [rewrite (observe_bind w2 (rel_draw_model_cont R2)), Hw2; reflexivity | exact IH].
    - eapply RPD_DrawL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact Hv | exact IH].
    - eapply RPD_DrawR; [rewrite Hw2, Eqit.bind_bind; reflexivity | intros v Hv; exact (IH v Hv)].
  Qed.

  Local Lemma mcfg_vdraw_sim_to_model_branch_a {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop) :
    forall U0 stk env1 env2 s1 s2 u1 u2 t1 t2,
      interp_state interp_vellvm_rel_draw_h u1 s1 ≅ t1 ->
      interp_state interp_vellvm_rel_draw_h u2 s2 ≅ t2 ->
      fused_state_match stk env1 env2 s1 s2 ->
      mcfg_vdraw_sim RR stk env1 env2 u1 u2 ->
      refine_prov_draw_
        (fun (_ : list N) '(s1', r1) '(s2', r2) =>
           exists stk' e1' e2',
             fused_state_match stk' e1' e2' s1' s2' /\ RR stk' e1' e2' r1 r2)
        (rdm_r_both RR) U0 t1 t2.
  Proof using.
    intros U0 stk env1 env2 s1 s2 u1 u2 t1 t2 Et1 Et2 Hmatch Hu.
    eapply refine_prov_draw__obs_eq;
      [exact (rdm_r_both_obs_eq RR) | exact Et1 | exact Et2 |].
    punfold Hu; clear t1 t2 Et1 Et2.
    revert s1 s2 Hmatch;
      induction Hu as [stk env1 env2 u1 u2 Hstep
                       | stk env1 env2 u1 mu1 u2 Hu1 _ IH
                       | stk env1 env2 u1 u2 mu2 Hu2 _ IH
                       | stk env1 env2 u1 x v k1 u2 Hu1 Hlk _ IH
                       | stk env1 env2 u1 u2 x v k2 Hu2 Hlk _ IH
                       | stk env1 env2 u1 x v k1 u2 Hu1 _ IH
                       | stk env1 env2 u1 u2 x v k2 Hu2 _ IH
                       | stk env1 env2 u1 dt v k1 u2 Hu1 Hv _ IH
                       | stk env1 env2 u1 u2 dt k2 Hu2 _ IH];
      intros s1 s2 Hmatch.
    - eapply mcfg_vdraw_sim_to_model_branch_b;
        [apply decomp_rel_draw_model_spec
        | apply decomp_rel_draw_model_spec
        | eapply mcfg_vdraw_sim_to_model_step; eassumption].
    - eapply refine_prov_draw__obs_eq with
        (t1 := Tau (interp_state interp_vellvm_rel_draw_h mu1 s1))
        (t2 := interp_state interp_vellvm_rel_draw_h u2 s2);
        [exact (rdm_r_both_obs_eq RR)
        | symmetry; rewrite (unfold_interp_state interp_vellvm_rel_draw_h u1 s1), Hu1; reflexivity
        | reflexivity |].
      eapply RPD_TauL; [reflexivity | apply IH, Hmatch].
    - eapply refine_prov_draw__obs_eq with
        (t1 := interp_state interp_vellvm_rel_draw_h u1 s1)
        (t2 := Tau (interp_state interp_vellvm_rel_draw_h mu2 s2));
        [exact (rdm_r_both_obs_eq RR)
        | reflexivity
        | symmetry; rewrite (unfold_interp_state interp_vellvm_rel_draw_h u2 s2), Hu2; reflexivity |].
      eapply RPD_TauR; [reflexivity | apply IH, Hmatch].
    - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
      pose proof Hmatch as (_ & _ & (Hvars1 & _) & _).
      eapply refine_prov_draw__obs_eq with
        (t1 := Tau (interp_state interp_vellvm_rel_draw_h (k1 v) (mm1, ((sf1, fstk1), gg1))))
        (t2 := interp_state interp_vellvm_rel_draw_h u2 (mm2, ((sf2, fstk2), gg2))).
      + exact (rdm_r_both_obs_eq RR).
      + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
          cbn [interp_vellvm_rel_draw_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_
               subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun
               inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
        rewrite (lift_prov_to_draw_eq _ _
                   (fused_local_prov_read_some x v (mm1, ((sf1, fstk1), gg1))
                      (ltac:(cbn; rewrite Hvars1; exact Hlk)))),
                lift_prov_to_draw_ret, Eqit.bind_ret_l; reflexivity.
      + reflexivity.
      + eapply RPD_TauL; [reflexivity | apply IH, Hmatch].
    - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
      pose proof Hmatch as (_ & _ & (_ & Hvars2 & _) & _).
      eapply refine_prov_draw__obs_eq with
        (t1 := interp_state interp_vellvm_rel_draw_h u1 (mm1, ((sf1, fstk1), gg1)))
        (t2 := Tau (interp_state interp_vellvm_rel_draw_h (k2 v) (mm2, ((sf2, fstk2), gg2)))).
      + exact (rdm_r_both_obs_eq RR).
      + reflexivity.
      + symmetry; rewrite Hu2, bind_trigger, interp_state_vis;
          cbn [interp_vellvm_rel_draw_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_
               subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun
               inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
        rewrite (lift_prov_to_draw_eq _ _
                   (fused_local_prov_read_some x v (mm2, ((sf2, fstk2), gg2))
                      (ltac:(cbn; rewrite Hvars2; exact Hlk)))),
                lift_prov_to_draw_ret, Eqit.bind_ret_l; reflexivity.
      + eapply RPD_TauR; [reflexivity | apply IH, Hmatch].
    - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
      destruct Hmatch as (<- & <- & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
      eapply refine_prov_draw__obs_eq with
        (t1 := Tau (interp_state interp_vellvm_rel_draw_h (k1 tt)
                      (mm1, ((upd_local_sf sf1 (Maps.add x v sf1.(stack_vars)), fstk1), gg1))))
        (t2 := interp_state interp_vellvm_rel_draw_h u2 (mm1, ((sf2, fstk2), gg1))).
      + exact (rdm_r_both_obs_eq RR).
      + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
          cbn [interp_vellvm_rel_draw_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_
               subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun
               inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
        try change (resum IFun unit (LocalWrite x v)) with (LocalWrite x v);
        rewrite (lift_prov_to_draw_eq _ _ (fused_local_prov_write _ _ _ _ _ _)),
                lift_prov_to_draw_ret, Eqit.bind_ret_l; reflexivity.
      + reflexivity.
      + eapply RPD_TauL; [reflexivity | apply IH].
        rewrite Hvars1;
          repeat split; try exact Hvars2;
          try exact Hexc; try exact Hloc; try exact Hsfm; reflexivity.
    - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
      destruct Hmatch as (<- & <- & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
      eapply refine_prov_draw__obs_eq with
        (t1 := interp_state interp_vellvm_rel_draw_h u1 (mm1, ((sf1, fstk1), gg1)))
        (t2 := Tau (interp_state interp_vellvm_rel_draw_h (k2 tt)
                      (mm1, ((upd_local_sf sf2 (Maps.add x v sf2.(stack_vars)), fstk2), gg1)))).
      + exact (rdm_r_both_obs_eq RR).
      + reflexivity.
      + symmetry; rewrite Hu2, bind_trigger, interp_state_vis;
          cbn [interp_vellvm_rel_draw_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_
               subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun
               inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
        try change (resum IFun unit (LocalWrite x v)) with (LocalWrite x v);
        rewrite (lift_prov_to_draw_eq _ _ (fused_local_prov_write _ _ _ _ _ _)),
                lift_prov_to_draw_ret, Eqit.bind_ret_l; reflexivity.
      + eapply RPD_TauR; [reflexivity | apply IH].
        rewrite Hvars2;
          repeat split; try exact Hvars1;
          try exact Hexc; try exact Hloc; try exact Hsfm; reflexivity.
    - eapply RPD_DrawL with (dt := dt)
        (k1 := fun v => Tau (interp_state interp_vellvm_rel_draw_h (k1 v) s1)).
      + rewrite Hu1, bind_trigger, interp_state_vis;
          cbn [interp_vellvm_rel_draw_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_
               subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun
               inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun];
          rewrite Eqit.bind_bind.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros v' ? <-].
        rewrite Eqit.bind_ret_l; reflexivity.
      + exact Hv.
      + eapply RPD_TauL; [reflexivity | apply IH, Hmatch].
    - eapply RPD_DrawR with (dt := dt)
        (k2 := fun v => Tau (interp_state interp_vellvm_rel_draw_h (k2 v) s2)).
      + rewrite Hu2, bind_trigger, interp_state_vis;
          cbn [interp_vellvm_rel_draw_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_
               subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun
               inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun];
          rewrite Eqit.bind_bind.
        apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros v' ? <-].
        rewrite Eqit.bind_ret_l; reflexivity.
      + intros v Hv; eapply RPD_TauR; [reflexivity | apply (IH v Hv), Hmatch].
  Qed.

  Lemma mcfg_vdraw_sim_to_model {R1 R2}
    (RR : env_stack -> @local_env PaV -> @local_env PaV -> R1 -> R2 -> Prop) :
    forall U stk env1 env2 (s1 s2 : FusedS)
      (u1 : @MCFGtop PaV R1) (u2 : @MCFGtop PaV R2),
      fused_state_match stk env1 env2 s1 s2 ->
      mcfg_vdraw_sim RR stk env1 env2 u1 u2 ->
      refine_prov_draw
        (fun _ '(s1', r1) '(s2', r2) =>
           exists stk' e1' e2', fused_state_match stk' e1' e2' s1' s2' /\ RR stk' e1' e2' r1 r2)
        U
        (interp_state interp_vellvm_rel_draw_h u1 s1)
        (interp_state interp_vellvm_rel_draw_h u2 s2).
  Proof using.
    assert (Hmain :
      forall U0 t1 t2,
        rdm_r_both RR U0 t1 t2 ->
        refine_prov_draw
          (fun _ '(s1', r1) '(s2', r2) =>
             exists stk' e1' e2', fused_state_match stk' e1' e2' s1' s2' /\ RR stk' e1' e2' r1 r2)
          U0 t1 t2).
    { pcofix CIH.
      intros U0 t1 t2 Hrb; pstep.
      eapply refine_prov_draw__mon with (r := rdm_r_both RR);
        [| intros U1 a1 a2 Hr; right; apply CIH, Hr].
      unfold rdm_r_both in Hrb.
      destruct Hrb as [(stk & e1 & e2 & s1 & s2 & v1 & v2 & Ev1 & Ev2 & Hm & Hv) |
                       (w1 & w2 & Ew1 & Ew2 & Hw)].
      - eapply mcfg_vdraw_sim_to_model_branch_a; eassumption.
      - eapply mcfg_vdraw_sim_to_model_branch_b; eassumption. }
    intros U stk env1 env2 s1 s2 u1 u2 Hmatch Hsim.
    apply Hmain; unfold rdm_r_both; left;
      exists stk, env1, env2, s1, s2, u1, u2;
      split; [reflexivity | split; [reflexivity | split; assumption]].
  Qed.

  (** ** 8.5 Whole-Module Value-Refinement & Relational-[DrawE] Composition ([F-59]) *)

  Lemma of_list_fn_ctx_vdraw_sim {P : @function_denotation PaV -> @function_denotation PaV -> Prop}
    (l1 l2 : list (Z * @function_denotation PaV))
    (Hl : Forall2 (fun '(k1, f1) '(k2, f2) => k1 = k2 /\ P f1 f2) l1 l2) :
    forall k, option_rel P (lookup k (IntMaps.IP.of_list l1)) (lookup k (IntMaps.IP.of_list l2)).
  Proof using.
    induction Hl as [| [k1 f1] [k2 f2] l1' l2' [<- Hf] _ IH]; intros k.
    - cbn; constructor.
    - cbn [IntMaps.IP.of_list fold_right]; unfold IntMaps.IP.uncurry, lookup; cbn [fst snd].
      destruct (Z.eq_dec k1 k) as [<- | Hne].
      + rewrite !IntMaps.IP.F.add_eq_o by reflexivity; constructor; exact Hf.
      + rewrite !IntMaps.IP.F.add_neq_o by exact Hne; apply IH.
  Qed.

  Local Lemma i8_str_index_vdraw_sim (allow_call : bool) strptr index e1 e2 :
    cfg_local_vdraw_sim_b allow_call
      (fun e1' e2' r1 r2 => e1' = e1 /\ e2' = e2 /\ r1 = r2)
      e1 e2 (i8_str_index strptr index) (i8_str_index strptr index).
  Proof using.
    assert (Heou : forall A (m : EOU A) s0 a1 a2,
              vds_sim (@is_ub_cfg IP IPT) (@sync_cfg_b allow_call) EqE_CFG EqA_CFG
                (@cfg_event_post IP IPT) (@as_local_cfg IP IPT) (fun _ _ => None)
                (fun _ e1' e2' r1 r2 => e1' = a1 /\ e2' = a2 /\ r1 = r2)
                s0 a1 a2 (EOU_to_itree m) (EOU_to_itree m)).
    { intros A [s | s | s | x] s0 a1 a2; cbn [EOU_to_itree].
      - unfold raise, trigger_cast, ITree.trigger; pstep; apply VDS_Step;
          unfold vds_step_body; rewrite !observe_bind; cbn;
          right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros []]].
      - unfold raiseOOM, trigger_cast, ITree.trigger; pstep; apply VDS_Step;
          unfold vds_step_body; rewrite !observe_bind; cbn;
          right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros []]].
      - unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply VDS_Step;
          unfold vds_step_body; rewrite !observe_bind; cbn; left; reflexivity.
      - apply vds_sim_ret; repeat split; reflexivity. }
    assert (Herr : forall msg A s0 a1 a2,
              vds_sim (@is_ub_cfg IP IPT) (@sync_cfg_b allow_call) EqE_CFG EqA_CFG
                (@cfg_event_post IP IPT) (@as_local_cfg IP IPT) (fun _ _ => None)
                (fun _ e1' e2' (r1 r2 : A) => e1' = a1 /\ e2' = a2 /\ r1 = r2)
                s0 a1 a2 (raise msg) (raise msg)).
    { intros msg A s0 a1 a2; unfold raise, trigger_cast, ITree.trigger; pstep; apply VDS_Step;
        unfold vds_step_body; rewrite !observe_bind; cbn;
        right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros []]]. }
    unfold i8_str_index, cfg_local_vdraw_sim_b.
    eapply vds_sim_bind; [apply Heou | intros ? ? ? iptr _ (-> & -> & <-)].
    eapply vds_sim_bind; [apply Heou | intros ? ? ? addr _ (-> & -> & <-)].
    eapply vds_sim_bind with (RR := fun _ e1' e2' r1 r2 => e1' = e1 /\ e2' = e2 /\ r1 = r2).
    { unfold load, trigger_cast, ITree.trigger; pstep; apply VDS_Step; cbn;
        right; left; split; [reflexivity | split; [apply EqE_CFG_refl |]].
      intros a1 a2 Ha _; apply EqA_CFG_eq in Ha; subst a2;
        left; apply vds_sim_ret; repeat split; reflexivity. }
    intros ? ? ? d_byte _ (-> & -> & <-).
    destruct d_byte as [[| sz b | | | | | |] | |]; try apply Herr.
    destruct sz as [p | p |]; try apply Herr;
      destruct p as [p | p |]; try apply Herr;
      destruct p as [p | p |]; try apply Herr;
      destruct p as [p | p |]; try apply Herr.
    apply vds_sim_ret; repeat split; reflexivity.
  Qed.

  Local Lemma putchar_vdraw_sim (allow_call : bool) :
    forall stk env1 env2 cc args,
      cfg_vdraw_sim_b allow_call
        (fun stk' e1' e2' r1 r2 =>
           stk' = stk /\ e1' = env1 /\ e2' = env2 /\
           mm_exc_ret_refines r1 r2 /\ r1 = r2)
        stk env1 env2 (putchar_denotation cc args) (putchar_denotation cc args).
  Proof using.
    intros stk env1 env2 cc args; unfold putchar_denotation.
    destruct args as [| ch [| ? ?]];
      try (unfold raise; apply vds_cfg_trigger_cast_sync;
           [reflexivity | apply EqE_CFG_refl]).
    cbn [Functor.fmap Functor_itree]; unfold ITree.map.
    eapply vds_sim_bind with (RR := fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2);
      [| intros ? ? ? dv _ (-> & -> & -> & <-); apply vds_sim_ret;
         split; [reflexivity | split; [reflexivity | split; [reflexivity |]]];
         split; [apply mm_ret_dvalue_refines_refl | reflexivity]].
    destruct ch as [[| sz x32 | | | | | |] | |];
      try (unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply VDS_Step;
           unfold vds_step_body; rewrite !observe_bind; cbn; left; reflexivity).
    destruct (Pos.eq_dec 32 sz) as [<- | _];
      [| unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply VDS_Step;
         unfold vds_step_body; rewrite !observe_bind; cbn; left; reflexivity].
    eapply vds_sim_bind.
    - unfold io_stdout, trigger_cast; apply vds_cfg_trigger_mcfg_sync; reflexivity.
    - intros ? ? ? _ _ (-> & -> & -> & <-); apply vds_sim_ret; repeat split; reflexivity.
  Qed.

  Local Lemma puts_vdraw_sim (allow_call : bool) :
    forall stk env1 env2 cc args,
      cfg_vdraw_sim_b allow_call
        (fun stk' e1' e2' r1 r2 =>
           stk' = stk /\ e1' = env1 /\ e2' = env2 /\
           mm_exc_ret_refines r1 r2 /\ r1 = r2)
        stk env1 env2 (puts_denotation cc args) (puts_denotation cc args).
  Proof using.
    intros stk env1 env2 cc args; unfold puts_denotation.
    destruct args as [| u_strptr [| ? ?]];
      try (unfold raise; apply vds_cfg_trigger_cast_sync;
           [reflexivity | apply EqE_CFG_refl]).
    cbn [Functor.fmap Functor_itree]; unfold ITree.map.
    eapply vds_sim_bind with (RR := fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2);
      [| intros ? ? ? dv _ (-> & -> & -> & <-); apply vds_sim_ret;
         split; [reflexivity | split; [reflexivity | split; [reflexivity |]]];
         split; [apply mm_ret_dvalue_refines_refl | reflexivity]].
    destruct u_strptr as [[strptr | | | | | | |] | |];
      try (unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply VDS_Step;
           unfold vds_step_body; rewrite !observe_bind; cbn; left; reflexivity).
    eapply vds_sim_bind; [apply cfg_local_vdraw_to_stack_sim_b, i8_str_index_vdraw_sim |].
    intros ? ? ? ch _ (-> & -> & -> & <-).
    eapply vds_sim_bind.
    - apply cfg_local_vdraw_to_stack_sim_b.
      assert (Hvds_any_stk :
        forall {A1 A2} (Rloc : @local_env PaV -> @local_env PaV -> A1 -> A2 -> Prop)
          s0 e1 e2 (t1 : @CFGtop PaV A1) (t2 : @CFGtop PaV A2),
          cfg_local_vdraw_sim_b allow_call Rloc e1 e2 t1 t2 ->
          vds_sim (@is_ub_cfg IP IPT) (@sync_cfg_b allow_call) EqE_CFG EqA_CFG
            (@cfg_event_post IP IPT) (@as_local_cfg IP IPT) (fun _ _ => None)
            (fun _ => Rloc) s0 e1 e2 t1 t2).
      { intros A1 A2 Rloc s0.
        unfold cfg_local_vdraw_sim_b.
        remember (@nil (@local_env PaV * @local_env PaV)) as s_nil eqn:Es; clear Es.
        pcofix CIH; intros e1_l e2_l t1_l t2_l Hl; pstep; punfold Hl.
        induction Hl as [s1 e1 e2 t1 t2 Hstep
                         | s1 e1 e2 t1 m1 t2 Ht1 _ IH
                         | s1 e1 e2 t1 t2 m2 Ht2 _ IH
                         | s1 e1 e2 t1 x v k1 t2 Ht1 Hlk _ IH
                         | s1 e1 e2 t1 t2 x v k2 Ht2 Hlk _ IH
                         | s1 e1 e2 t1 x v k1 t2 Ht1 _ IH
                         | s1 e1 e2 t1 t2 x v k2 Ht2 _ IH
                         | s1 e1 e2 t1 dt v k1 t2 Ht1 Hv _ IH
                         | s1 e1 e2 t1 t2 dt k2 Ht2 _ IH].
        - apply VDS_Step; unfold vds_step_body in *.
          destruct (observe t1) as [r1 | m1 | X1 ev1 k1].
          + exact Hstep.
          + destruct (observe t2);
              [exact Hstep | destruct Hstep as [Hs | Hb]; [right; eapply CIH, Hs | inversion Hb] | exact Hstep].
          + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
            destruct (observe t2) as [r2 | m2 | X2 ev2 k2]; try contradiction.
            destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hf]]; [| | contradiction].
            * left; split; [exact Hsync | split; [exact HE |]].
              intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp);
                destruct HA as [HA | Hb]; [right; eapply CIH, HA | inversion Hb].
            * right; left.
              destruct (as_local_cfg ev1) as [le1 |], (as_local_cfg ev2) as [le2 |]; try contradiction.
              destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
              -- destruct Hloc as (Hx & Hv & [Hr | Hb]); [| inversion Hb].
                 split; [exact Hx | split; [exact Hv | right; eapply CIH, Hr]].
              -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                 intros v Hv; specialize (Hrd v Hv);
                   destruct Hrd as [Hrd | Hb]; [right; eapply CIH, Hrd | inversion Hb].
        - eapply VDS_TauL; [exact Ht1 | exact (IH CIH)].
        - eapply VDS_TauR; [exact Ht2 | exact (IH CIH)].
        - eapply VDS_ReadL; [exact Ht1 | exact Hlk | exact (IH CIH)].
        - eapply VDS_ReadR; [exact Ht2 | exact Hlk | exact (IH CIH)].
        - eapply VDS_WriteL; [exact Ht1 | exact (IH CIH)].
        - eapply VDS_WriteR; [exact Ht2 | exact (IH CIH)].
        - eapply VDS_DrawL; [exact Ht1 | exact Hv | exact (IH CIH)].
        - eapply VDS_DrawR; [exact Ht2 | intros v Hv; exact (IH v Hv CIH)]. }
      set (pbody := fun '((c, bytes), offset) =>
                      if @Integers.eq 8 c (@Integers.zero 8)
                      then Ret (inr ((@Integers.repr 8 10) :: bytes))
                      else ITree.bind (i8_str_index strptr offset)
                             (fun next_char => Ret (inl (next_char, c :: bytes, (offset + 1)%Z)))).
      set (ic := fun lr : (@Integers.bit_int 8 * list (@Integers.bit_int 8) * Z) + list (@Integers.bit_int 8) =>
                   match lr with
                   | inl j => Tau (ITree.iter pbody j)
                   | inr r => Ret r
                   end).
      set (istep := fun e1' e2'
                      (x1 x2 : (@Integers.bit_int 8 * list (@Integers.bit_int 8) * Z) + list (@Integers.bit_int 8)) =>
                      match x1, x2 with
                      | inl j1, inl j2 => e1' = env1 /\ e2' = env2 /\ j1 = j2
                      | inr r1, inr r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2
                      | _, _ => False
                      end).
      assert (Hpbody : forall j,
                cfg_local_vdraw_sim_b allow_call istep env1 env2 (pbody j) (pbody j)).
      { intros [[c bytes] offset]; unfold pbody.
        destruct (@Integers.eq 8 c (@Integers.zero 8)).
        - apply vds_sim_ret; cbn; repeat split; reflexivity.
        - eapply vds_sim_bind; [apply i8_str_index_vdraw_sim |].
          intros ? ? ? next_char _ (-> & -> & <-).
          apply vds_sim_ret; cbn; repeat split; reflexivity. }
      assert (Hiter_aux :
        forall s0 e1 e2 w1 w2 t1 t2,
          ITree.bind w1 ic ≅ t1 ->
          ITree.bind w2 ic ≅ t2 ->
          vds_sim (@is_ub_cfg IP IPT) (@sync_cfg_b allow_call) EqE_CFG EqA_CFG
            (@cfg_event_post IP IPT) (@as_local_cfg IP IPT) (fun _ _ => None)
            (fun _ => istep) s0 e1 e2 w1 w2 ->
          vds_sim (@is_ub_cfg IP IPT) (@sync_cfg_b allow_call) EqE_CFG EqA_CFG
            (@cfg_event_post IP IPT) (@as_local_cfg IP IPT) (fun _ _ => None)
            (fun _ e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2) s0 e1 e2 t1 t2).
      { pcofix CIH.
        intros s0 e1 e2 w1 w2 t1 t2 Et1 Et2 Hw; pstep.
        set (r_rel := fun s1 e1' e2' a1 a2 =>
                        exists v1 v2,
                          ITree.bind v1 ic ≅ a1 /\
                          ITree.bind v2 ic ≅ a2 /\
                          vds_sim (@is_ub_cfg IP IPT) (@sync_cfg_b allow_call) EqE_CFG EqA_CFG
                            (@cfg_event_post IP IPT) (@as_local_cfg IP IPT) (fun _ _ => None)
                            (fun _ => istep) s1 e1' e2' v1 v2).
        assert (Hr_eq : forall s1 e1' e2' a1 a1' a2 a2',
                  a1 ≅ a1' -> a2 ≅ a2' -> r_rel s1 e1' e2' a1 a2 -> r_rel s1 e1' e2' a1' a2').
        { intros s1 e1' e2' a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv).
          exists v1, v2; split;
            [etransitivity; [exact Ev1 | exact Ea1]
            | split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv]]. }
        eapply vds_sim__mon with (r := r_rel);
          [| intros s1 e1' e2' a1 a2 (v1 & v2 & Ev1 & Ev2 & Hv);
             right; eapply CIH; [exact Ev1 | exact Ev2 | exact Hv]].
        eapply vds_sim__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
        punfold Hw; clear t1 t2 Et1 Et2 CIH r.
        induction Hw as [s0 e1 e2 w1 w2 Hstep
                         | s0 e1 e2 w1 mw1 w2 Hw1 _ IH
                         | s0 e1 e2 w1 w2 mw2 Hw2 _ IH
                         | s0 e1 e2 w1 x v kw1 w2 Hw1 Hlk _ IH
                         | s0 e1 e2 w1 w2 x v kw2 Hw2 Hlk _ IH
                         | s0 e1 e2 w1 x v kw1 w2 Hw1 _ IH
                         | s0 e1 e2 w1 w2 x v kw2 Hw2 _ IH
                         | s0 e1 e2 w1 dt v kw1 w2 Hw1 Hv _ IH
                         | s0 e1 e2 w1 w2 dt kw2 Hw2 _ IH].
        - unfold vds_step_body in Hstep.
          destruct (observe w1) as [x1 | mw1 | X1 ev1 kw1] eqn:How1.
          + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
            destruct x1 as [j1 | r1], x2 as [j2 | r2]; cbn in Hstep; try contradiction.
            * destruct Hstep as (-> & -> & <-).
              apply VDS_Step; unfold vds_step_body; rewrite !observe_bind, How1, How2; cbn.
              exists (pbody j1), (pbody j1).
              split; [symmetry; apply unfold_iter |].
              split; [symmetry; apply unfold_iter |].
              apply Hvds_any_stk, Hpbody.
            * apply VDS_Step; unfold vds_step_body; rewrite !observe_bind, How1, How2; cbn; exact Hstep.
          + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
            destruct Hstep as [Hstep | Hb]; [| inversion Hb].
            apply VDS_Step; unfold vds_step_body; rewrite !observe_bind, How1, How2.
            exists mw1, mw2; split; [reflexivity | split; [reflexivity | exact Hstep]].
          + apply VDS_Step; unfold vds_step_body; rewrite (observe_bind w1 ic), How1.
            destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
            destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
            rewrite (observe_bind w2 ic), How2.
            destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hf]]; [| | contradiction].
            * left; split; [exact Hsync | split; [exact HE |]].
              intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
              exists (kw1 a1), (kw2 a2); split; [reflexivity | split; [reflexivity | exact HA]].
            * right; left.
              destruct (as_local_cfg ev1) as [le1 |], (as_local_cfg ev2) as [le2 |]; try contradiction.
              destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
              -- destruct Hloc as (Hx & Hv & [Hr | Hb]); [| inversion Hb].
                 split;
                   [exact Hx
                   | split;
                       [exact Hv
                       | exists (kw1 tt), (kw2 tt);
                         split; [reflexivity | split; [reflexivity | exact Hr]]]].
              -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                 intros v Hv; specialize (Hrd v Hv); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
                 exists (kw1 v), (kw2 v); split; [reflexivity | split; [reflexivity | exact Hrd]].
        - eapply VDS_TauL; [rewrite (observe_bind w1 ic), Hw1; reflexivity | exact IH].
        - eapply VDS_TauR; [rewrite (observe_bind w2 ic), Hw2; reflexivity | exact IH].
        - eapply VDS_ReadL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
        - eapply VDS_ReadR; [rewrite Hw2, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
        - eapply VDS_WriteL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
        - eapply VDS_WriteR; [rewrite Hw2, Eqit.bind_bind; reflexivity | exact IH].
        - eapply VDS_DrawL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact Hv | exact IH].
        - eapply VDS_DrawR; [rewrite Hw2, Eqit.bind_bind; reflexivity | intros v Hv; exact (IH v Hv)]. }
      eapply Hiter_aux with (w1 := pbody (ch, [], 1%Z)) (w2 := pbody (ch, [], 1%Z));
        [symmetry; apply unfold_iter | symmetry; apply unfold_iter | apply Hvds_any_stk, Hpbody].
    - intros ? ? ? bytes _ (-> & -> & -> & <-).
      eapply vds_sim_bind.
      + unfold io_stdout, trigger_cast; apply vds_cfg_trigger_mcfg_sync; reflexivity.
      + intros ? ? ? _ _ (-> & -> & -> & <-); apply vds_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma library_functions_vdraw_sync (allow_call : bool) (decls : list (declaration dtyp)) :
    Forall
      (fun '(_, den) =>
         forall stk env1 env2 cc args,
           cfg_vdraw_sim_b allow_call
             (fun stk' e1' e2' r1 r2 =>
                stk' = stk /\ e1' = env1 /\ e2' = env2 /\
                mm_exc_ret_refines r1 r2 /\ r1 = r2)
             stk env1 env2 (den cc args) (den cc args))
      (library_functions decls).
  Proof using.
    unfold library_functions, _LIBRARIES.
    apply Forall_forall; intros [nm den] Hin.
    apply filter_In in Hin as [Hin _]; cbn [In] in Hin.
    destruct Hin as [Heq | [Heq | []]]; injection Heq as _ <-;
      [exact (puts_vdraw_sim allow_call) | exact (putchar_vdraw_sim allow_call)].
  Qed.

  (** Per-definition value- & [DrawE]-refinement contract parameterized by
      [allow_call]:
      - When [allow_call = true], either the CFG body preserves exact return
        values ([RR_body = eq], still allowing full relational-[DrawE] [freeze]
        folding and SSA parameter renaming without [noundef]) OR the prototype
        carries [noundef] on its return (upgrading [Poison -> Concrete] to exact
        return equality via [check_call_return] across arbitrary internal calls).
      - When [allow_call = false], call-free leaf functions refine
        [Poison -> Concrete] ([mm_ret_dvalue_refines], e.g. [xor %x, %x -> 0])
        and fold [freeze] ([DrawE]) at the whole-module boundary WITHOUT
        requiring [noundef] on the function prototype. *)
  Definition defn_pair_vdraw_spec (allow_call : bool)
    (d1 d2 : definition dtyp (CFG.cfg dtyp)) : Prop :=
    df_prototype d2 = df_prototype d1 /\
    List.length (df_args d2) = List.length (df_args d1) /\
    exists (RR_body : @dvalue PaV -> @dvalue PaV -> Prop),
      (forall v1 v2, RR_body v1 v2 -> mm_ret_dvalue_refines v1 v2) /\
      (allow_call = true ->
       (forall a b, RR_body a b -> a = b) \/
       existsb attr_is_noundef (fst (dc_param_attrs (df_prototype d1))) = true) /\
      (forall fvs va,
         List.length fvs = List.length (df_args d1) ->
         cfg_local_vdraw_sim_b allow_call (fun _ _ r1 r2 => RR_body r1 r2)
           (init_local_env (List.combine (df_args d1) fvs))
           (init_local_env (List.combine (df_args d2) fvs))
           (denote_cfg (df_instrs d1) va)
           (denote_cfg (df_instrs d2) va)).

  Lemma map_monad_address_defs_vdraw_sim (allow_call : bool)
    (defs1 defs2 : list (definition dtyp (CFG.cfg dtyp)))
    (Hdefs : Forall2 (defn_pair_vdraw_spec allow_call) defs1 defs2) :
    forall stk env1 env2,
      mcfg_vdraw_sim
        (fun stk' e1' e2' l1 l2 =>
           stk' = stk /\ e1' = env1 /\ e2' = env2 /\
           Forall2
             (fun '(k1, fn1) '(k2, fn2) =>
                k1 = k2 /\
                forall s0 a1 a2 cc args,
                  cfg_vdraw_sim_b allow_call
                    (fun s0' a1' a2' r1 r2 =>
                       s0' = s0 /\ a1' = a1 /\ a2' = a2 /\
                       mm_exc_ret_refines r1 r2 /\
                       (allow_call = true -> r1 = r2))
                    s0 a1 a2 (fn1 cc args) (fn2 cc args))
             l1 l2)
        stk env1 env2
        (map_monad address_one_function defs1)
        (map_monad address_one_function defs2).
  Proof using.
    induction Hdefs as [| d1 d2 r1 r2 (Hpr & Hlen & RR_b & Hsub & Hup & Hbd) _ IH];
      intros stk env1 env2; cbn [map_monad].
    - apply vds_sim_ret; repeat split; constructor.
    - eapply vds_sim_bind with
        (RR := fun stk' e1' e2'
                 (p1 p2 : Z * @function_denotation PaV) =>
                 stk' = stk /\ e1' = env1 /\ e2' = env2 /\
                 fst p1 = fst p2 /\
                 forall s0 a1 a2 cc args,
                   cfg_vdraw_sim_b allow_call
                     (fun s0' a1' a2' r1 r2 =>
                        s0' = s0 /\ a1' = a1 /\ a2' = a2 /\
                        mm_exc_ret_refines r1 r2 /\
                        (allow_call = true -> r1 = r2))
                     s0 a1 a2 (snd p1 cc args) (snd p2 cc args)).
      + unfold address_one_function; rewrite Hpr.
        eapply vds_sim_bind.
        * apply mcfg_stack_to_vdraw_sim; unfold gread, trigger_cast;
            apply gen_stack_sim_trigger_sync; [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
        * intros ? ? ? fv _ (-> & -> & -> & <-).
          destruct fv as [[p | | | | | | |] | |];
            try (apply mcfg_stack_to_vdraw_sim; unfold raise;
                 apply gen_stack_sim_trigger_cast_sync; [reflexivity | apply EqE_MCFG_refl]).
          apply vds_sim_ret; cbn [fst snd].
          split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity |]]]].
          intros s0 a1 a2 cc args.
          eapply vds_sim_weaken;
            [| exact (cfg_vdraw_sim_denote_function_gen allow_call d1 d2 RR_b Hsub
                        ( eq_sym Hpr ) ( eq_sym Hlen ) Hbd s0 a1 a2 cc args)].
          intros ? ? ? rv1 rv2 (-> & -> & -> & Hmr & Hreq).
          split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [exact Hmr |]]]].
          intros Hac; exact (Hreq (Hup Hac)).
      + intros ? ? ? [k1 fn1] [k2 fn2] (-> & -> & -> & Hk & Hhd); cbn [fst snd] in Hk, Hhd.
        eapply vds_sim_bind; [apply IH |].
        intros ? ? ? tl1 tl2 (-> & -> & -> & Htl).
        apply vds_sim_ret; repeat split; constructor; [split; assumption | assumption].
  Qed.

  Lemma map_monad_address_library_vdraw_sim (allow_call : bool)
    (libs : list (function_id * @function_denotation PaV))
    (Hlibs : Forall
               (fun '(_, den) =>
                  forall stk env1 env2 cc args,
                    cfg_vdraw_sim_b allow_call
                      (fun stk' e1' e2' r1 r2 =>
                         stk' = stk /\ e1' = env1 /\ e2' = env2 /\
                         mm_exc_ret_refines r1 r2 /\ r1 = r2)
                      stk env1 env2 (den cc args) (den cc args))
               libs) :
    forall stk env1 env2,
      mcfg_vdraw_sim
        (fun stk' e1' e2' l1 l2 =>
           stk' = stk /\ e1' = env1 /\ e2' = env2 /\
           Forall2
             (fun '(k1, fn1) '(k2, fn2) =>
                k1 = k2 /\
                forall s0 a1 a2 cc args,
                  cfg_vdraw_sim_b allow_call
                    (fun s0' a1' a2' r1 r2 =>
                       s0' = s0 /\ a1' = a1 /\ a2' = a2 /\
                       mm_exc_ret_refines r1 r2 /\
                       (allow_call = true -> r1 = r2))
                    s0 a1 a2 (fn1 cc args) (fn2 cc args))
             l1 l2)
        stk env1 env2
        (map_monad address_one_library_function libs)
        (map_monad address_one_library_function libs).
  Proof using.
    induction Hlibs as [| [fid den] rest Hden _ IH]; intros stk env1 env2; cbn [map_monad].
    - apply vds_sim_ret; repeat split; constructor.
    - eapply vds_sim_bind with
        (RR := fun stk' e1' e2'
                 (p1 p2 : Z * @function_denotation PaV) =>
                 stk' = stk /\ e1' = env1 /\ e2' = env2 /\
                 fst p1 = fst p2 /\
                 forall s0 a1 a2 cc args,
                   cfg_vdraw_sim_b allow_call
                     (fun s0' a1' a2' r1 r2 =>
                        s0' = s0 /\ a1' = a1 /\ a2' = a2 /\
                        mm_exc_ret_refines r1 r2 /\
                        (allow_call = true -> r1 = r2))
                     s0 a1 a2 (snd p1 cc args) (snd p2 cc args)).
      + unfold address_one_library_function.
        eapply vds_sim_bind.
        * apply mcfg_stack_to_vdraw_sim; unfold gread, trigger_cast;
            apply gen_stack_sim_trigger_sync; [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
        * intros ? ? ? fv _ (-> & -> & -> & <-).
          destruct fv as [[p | | | | | | |] | |];
            try (apply mcfg_stack_to_vdraw_sim; unfold raise;
                 apply gen_stack_sim_trigger_cast_sync; [reflexivity | apply EqE_MCFG_refl]).
          apply vds_sim_ret; cbn [fst snd].
          split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity |]]]].
          intros s0 a1 a2 cc args.
          eapply vds_sim_weaken; [| exact (Hden s0 a1 a2 cc args)].
          intros ? ? ? rv1 rv2 (-> & -> & -> & Hmr & Heq).
          split;
            [reflexivity
            | split;
                [reflexivity
                | split; [reflexivity | split; [exact Hmr | intros _; exact Heq]]]].
      + intros ? ? ? [k1 fn1] [k2 fn2] (-> & -> & -> & Hk & Hhd); cbn [fst snd] in Hk, Hhd.
        eapply vds_sim_bind; [apply IH |].
        intros ? ? ? tl1 tl2 (-> & -> & -> & Htl).
        apply vds_sim_ret; repeat split; constructor; [split; assumption | assumption].
  Qed.

  (** General Whole-Module Lifter for Value-Refinement & Relational-[DrawE] ([F-59]). *)
  Theorem module_defs_vdraw_refines (allow_call : bool)
    (M1 M2 : CFG.mcfg dtyp)
    (Hbg : @build_global_environment PaV M1 ≅ @build_global_environment PaV M2)
    (Hdecls : non_intrinsic_decls (m_declarations M2) =
              non_intrinsic_decls (m_declarations M1))
    (Hdefs : Forall2 (defn_pair_vdraw_spec allow_call) (m_definitions M1) (m_definitions M2)) :
    prog_value_draw_refines M1 M2.
  Proof using.
    intros ret_typ entry args U.
    unfold run_mcfg_rel_draw_model, interp_mcfg_rel_draw_model.
    eapply refine_prov_draw_antitone with (U := U);
      [| apply incl_refl
       | eapply mcfg_vdraw_sim_to_model with
           (RR := fun _ _ _ r1 r2 => mm_ret_dvalue_refines r1 r2)
           (stk := []) (env1 := Maps.empty) (env2 := Maps.empty)];
      [intros _ _ [s1 r1] [s2 r2] _ (_ & _ & _ & _ & Hmr); exact Hmr | ..].
    { unfold init_fused_state, fused_state_match; repeat split; try reflexivity; constructor. }
    apply mcfg_vdraw_sim_interp_intrinsics.
    unfold denote_vellvm.
    assert (Hlibs_eq :
      library_functions (m_declarations M2) = library_functions (m_declarations M1)).
    { rewrite (library_functions_non_intrinsic_eq (m_declarations M2)),
              (library_functions_non_intrinsic_eq (m_declarations M1)), Hdecls;
        reflexivity. }
    rewrite Hlibs_eq.
    eapply vds_sim_bind.
    { eapply vds_sim_obs_eq;
        [symmetry; exact Hbg | reflexivity
         | apply mcfg_stack_to_vdraw_sim, mcfg_stack_sim_refl_diag; constructor]. }
    intros stk1 e1 e2 [] _ (_ & <- & _).
    eapply vds_sim_bind;
      [exact (map_monad_address_defs_vdraw_sim allow_call _ _ Hdefs stk1 e1 e1) |].
    intros ? ? ? defns1 defns2 (-> & -> & -> & Hdefns).
    eapply vds_sim_bind;
      [exact (map_monad_address_library_vdraw_sim allow_call _
                (library_functions_vdraw_sync allow_call (m_declarations M1)) stk1 e1 e1) |].
    intros ? ? ? libs1 libs2 (-> & -> & -> & Hlibs).
    eapply vds_sim_bind.
    { apply mcfg_stack_to_vdraw_sim; unfold gread, trigger_cast;
        apply gen_stack_sim_trigger_sync; [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq]. }
    intros ? ? ? addr _ (-> & -> & -> & <-).
    eapply vds_sim_bind.
    - assert (Hmrec_eq : forall fundefs,
                denote_mcfg fundefs ret_typ addr args =
                interp_mrec (mm_mrec_ctx fundefs)
                  (mm_mrec_ctx fundefs _ (Call ret_typ CC_Ccc addr args)))
        by (intros fundefs; unfold denote_mcfg, mrec; reflexivity).
      rewrite !Hmrec_eq.
      pose proof (Forall2_app Hdefns Hlibs) as Hall.
      assert (Hctx_ret :
        forall k,
          option_rel
            (fun f1 f2 =>
               forall stk env1 env2 cc fargs,
                 cfg_vdraw_sim_b allow_call
                   (fun stk' e1' e2' r1 r2 =>
                      stk' = stk /\ e1' = env1 /\ e2' = env2 /\ mm_exc_ret_refines r1 r2)
                   stk env1 env2 (f1 cc fargs) (f2 cc fargs))
            (lookup k (IntMaps.IP.of_list (defns1 ++ libs1)))
            (lookup k (IntMaps.IP.of_list (defns2 ++ libs2)))).
      { apply of_list_fn_ctx_vdraw_sim.
        eapply Forall2_impl; [| exact Hall].
        intros [k1 fn1] [k2 fn2] [Hk Hfn].
        split; [exact Hk | intros stk env1 env2 cc fargs].
        eapply vds_sim_weaken; [| exact (Hfn stk env1 env2 cc fargs)].
        intros ? ? ? rv1 rv2 (-> & -> & -> & Hmr & _); repeat split; exact Hmr. }
      assert (Hctx_eq :
        allow_call = true ->
        forall k,
          option_rel
            (fun f1 f2 =>
               forall stk env1 env2 cc fargs,
                 cfg_vdraw_sim_b true
                   (fun stk' e1' e2' r1 r2 =>
                      stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
                   stk env1 env2 (f1 cc fargs) (f2 cc fargs))
            (lookup k (IntMaps.IP.of_list (defns1 ++ libs1)))
            (lookup k (IntMaps.IP.of_list (defns2 ++ libs2)))).
      { intros Hac; subst allow_call; apply of_list_fn_ctx_vdraw_sim.
        eapply Forall2_impl; [| exact Hall].
        intros [k1 fn1] [k2 fn2] [Hk Hfn].
        split; [exact Hk | intros stk env1 env2 cc fargs].
        eapply vds_sim_weaken; [| exact (Hfn stk env1 env2 cc fargs)].
        intros ? ? ? rv1 rv2 (-> & -> & -> & _ & Heq); repeat split; exact (Heq Logic.eq_refl). }
      eapply cfg_to_mcfg_vdraw_sim_mrec with
        (allow_call := allow_call)
        (ctx1 := IntMaps.IP.of_list (defns1 ++ libs1))
        (ctx2 := IntMaps.IP.of_list (defns2 ++ libs2));
        [exact Hctx_eq | reflexivity | reflexivity |].
      exact (cfg_vdraw_sim_mrec_ctx_ret allow_call _ _ Hctx_ret stk1 e1 e1 ret_typ CC_Ccc addr args).
    - intros ? ? ? rv1 rv2 (-> & -> & -> & Hrv).
      destruct rv1 as [ex1 | v1], rv2 as [ex2 | v2]; cbn in Hrv; try contradiction.
      + subst ex2.
        unfold raiseLLVM, trigger_cast, ITree.trigger; pstep; apply VDS_Step;
          unfold vds_step_body; rewrite !observe_bind; cbn.
        right; left; split; [reflexivity | split; [reflexivity | intros [] [] _ _]].
      + apply vds_sim_ret; exact Hrv.
  Qed.

  (** Flexible module-merge checker permitting SSA parameter renaming
      ([List.length (df_args df_merged) = List.length (df_args df_orig)], as
      produced by [ir-bridge merge] + [to-vellvm] when an unmerged parameter [%0]
      is renamed to [%_llv_a0] in an optimized slice) while enforcing exact
      prototype/attribute/global/declaration/blockaddress preservation. *)
  Definition check_flex_defn_pair
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (df_orig df_merged : definition dtyp (CFG.cfg dtyp)) : bool :=
    mm_declaration_eqb (df_prototype df_merged) (df_prototype df_orig) &&
    Nat.eqb (List.length (df_args df_merged)) (List.length (df_args df_orig)) &&
    (mm_definition_eqb df_merged df_orig ||
     existsb (check_slice_matches_defn df_orig df_merged) verified_slices).

  Fixpoint check_flex_defs_merge
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (defs_orig defs_merged : list (definition dtyp (CFG.cfg dtyp))) : bool :=
    match defs_orig, defs_merged with
    | [], [] => true
    | d1 :: r1, d2 :: r2 =>
        check_flex_defn_pair verified_slices d1 d2 &&
        check_flex_defs_merge verified_slices r1 r2
    | _, _ => false
    end.

  Definition check_flex_module_merge
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) : bool :=
    mm_list_eqb mm_global_eqb (m_globals m_merged) (m_globals m_orig) &&
    forallb global_no_extern_weak (m_globals m_orig) &&
    mm_list_eqb mm_declaration_eqb
      (non_intrinsic_decls (m_declarations m_merged))
      (non_intrinsic_decls (m_declarations m_orig)) &&
    forallb decl_no_extern_weak (m_declarations m_orig) &&
    forallb decl_no_extern_weak (m_declarations m_merged) &&
    forallb (fun d => decl_no_extern_weak (df_prototype d)) (m_definitions m_orig) &&
    mm_nodup_raw_ids
      (List.map dc_name
         (m_declarations m_orig ++ List.map df_prototype (m_definitions m_orig))) &&
    mm_nodup_raw_ids
      (List.map dc_name
         (m_declarations m_merged ++ List.map df_prototype (m_definitions m_merged))) &&
    mm_list_eqb mm_block_addr_eqb
      (nodup block_address_eq_dec (mcfg_block_addresses m_merged))
      (nodup block_address_eq_dec (mcfg_block_addresses m_orig)) &&
    check_flex_defs_merge verified_slices (m_definitions m_orig) (m_definitions m_merged).

  Lemma check_module_merge_implies_flex
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
    check_module_merge m_orig m_merged verified_slices = true ->
    check_flex_module_merge m_orig m_merged verified_slices = true.
  Proof using.
    unfold check_module_merge, check_flex_module_merge.
    rewrite !Bool.andb_true_iff.
    intros [[[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9] H10].
    repeat split; try assumption.
    clear H1 H2 H3 H4 H5 H6 H7 H8 H9; revert H10; generalize (m_definitions m_merged) as defs2;
      induction (m_definitions m_orig) as [| d1 r1 IH]; intros [| d2 r2] H10;
      cbn in *; try exact H10.
    apply Bool.andb_true_iff in H10 as [Hhd Htl].
    apply Bool.andb_true_iff; split; [| exact (IH r2 Htl)].
    unfold check_defn_pair, check_flex_defn_pair in *.
    rewrite !Bool.andb_true_iff in *; destruct Hhd as [[Hp Ha] Hd].
    apply (mm_list_eqb_eq _ raw_id_eqb_spec) in Ha.
    repeat split; [exact Hp | apply Nat.eqb_eq; rewrite Ha; reflexivity | exact Hd].
  Qed.

  Lemma check_flex_defs_merge_Forall2
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp)) :
    forall defs_orig defs_merged,
      check_flex_defs_merge verified_slices defs_orig defs_merged = true ->
      Forall2
        (fun df_orig df_merged =>
           df_prototype df_merged = df_prototype df_orig /\
           List.length (df_args df_merged) = List.length (df_args df_orig) /\
           (df_merged = df_orig \/
            exists fid m_src m_tgt df_src df_tgt,
              In (fid, m_src, m_tgt) verified_slices /\
              slice_witness_prop df_orig df_merged fid m_src m_tgt df_src df_tgt))
        defs_orig defs_merged.
  Proof using.
    induction defs_orig as [| d1 r1 IH]; intros [| d2 r2] H;
      cbn [check_flex_defs_merge] in H; try discriminate H; [constructor |].
    apply Bool.andb_true_iff in H as [Hhd Htl].
    constructor; [| exact (IH r2 Htl)].
    unfold check_flex_defn_pair in Hhd.
    rewrite !Bool.andb_true_iff, Bool.orb_true_iff in Hhd.
    destruct Hhd as [[Hproto Hlen] Hdisj].
    apply mm_declaration_eqb_eq in Hproto.
    apply Nat.eqb_eq in Hlen.
    refine (conj Hproto (conj Hlen _)).
    destruct Hdisj as [Heq | Hex].
    - left; apply mm_definition_eqb_eq, Heq.
    - right; apply existsb_exists in Hex as [[[fid m_src] m_tgt] [Hin Hmatch]].
      destruct (check_slice_matches_defn_spec d1 d2 fid m_src m_tgt Hmatch)
        as [df_src [df_tgt Hsw]].
      exists fid, m_src, m_tgt, df_src, df_tgt; exact (conj Hin Hsw).
  Qed.

  Lemma check_flex_module_merge_build_global_environment_eq
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hchk : check_flex_module_merge m_orig m_merged verified_slices = true) :
    @build_global_environment PaV m_orig ≅ @build_global_environment PaV m_merged.
  Proof using.
    unfold check_flex_module_merge in Hchk; rewrite !Bool.andb_true_iff in Hchk.
    destruct Hchk as [[[[[[[[[Hg _] Hdecl] _] _] _] _] _] Hba] Hdefs].
    apply (mm_list_eqb_eq _ mm_global_eqb_eq) in Hg.
    apply (mm_list_eqb_eq _ mm_declaration_eqb_eq) in Hdecl.
    apply (mm_list_eqb_eq _ mm_block_addr_eqb_eq) in Hba.
    pose proof (check_flex_defs_merge_Forall2 verified_slices _ _ Hdefs) as HF.
    clear Hdefs; assert (Hpr : List.map df_prototype (m_definitions m_merged) =
                               List.map df_prototype (m_definitions m_orig)).
    { induction HF as [| d1 d2 r1 r2 [Hp _] _ IH]; cbn [List.map];
        [reflexivity | rewrite Hp, IH; reflexivity]. }
    apply build_global_environment_non_intrinsic_eqit; symmetry; assumption.
  Qed.

  (** Open-world per-slice value-refinement & relational-[DrawE] contract
      ([F-59]): permits SSA parameter renaming, asymmetric demonic/angelic
      [DrawE] ([freeze] folding), and [DVALUE_Poison -> Concrete] scalar return
      refinement (upgraded via [noundef] across internal calls, or preserving
      exact return equality without [noundef]). *)
  Definition slice_value_refines
    (entry : function_id * CFG.mcfg dtyp * CFG.mcfg dtyp) : Prop :=
    let '(_, m_slice_src, m_slice_tgt) := entry in
    forall df_src df_tgt,
      m_definitions m_slice_src = [df_src] ->
      m_definitions m_slice_tgt = [df_tgt] ->
      exists (RR_body : @dvalue PaV -> @dvalue PaV -> Prop),
        (forall v1 v2, RR_body v1 v2 -> mm_ret_dvalue_refines v1 v2) /\
        ((forall a b, RR_body a b -> a = b) \/
         existsb attr_is_noundef (fst (dc_param_attrs (df_prototype df_src))) = true) /\
        forall fvs va,
          List.length fvs = List.length (df_args df_src) ->
          cfg_local_vdraw_sim (fun _ _ r1 r2 => RR_body r1 r2)
            (init_local_env (List.combine (df_args df_src) fvs))
            (init_local_env (List.combine (df_args df_tgt) fvs))
            (denote_cfg (df_instrs df_src) va)
            (denote_cfg (df_instrs df_tgt) va).

  (** Strictly generalizes [slice_body_refines]: every [slice_body_refines]
      slice with matching parameter list lengths satisfies [slice_value_refines]. *)
  Lemma slice_body_to_value_refines
    (entry : function_id * CFG.mcfg dtyp * CFG.mcfg dtyp) :
    slice_body_refines entry ->
    (let '(_, m_src, m_tgt) := entry in
     forall df_src df_tgt,
       m_definitions m_src = [df_src] ->
       m_definitions m_tgt = [df_tgt] ->
       df_args df_tgt = df_args df_src) ->
    slice_value_refines entry.
  Proof using.
    destruct entry as [[fid m_src] m_tgt]; intros Hsb Hargs df_src df_tgt Hs Ht.
    exists (@Logic.eq (@dvalue PaV)).
    split; [intros v1 v2 <-; apply mm_ret_dvalue_refines_refl |].
    split; [left; intros a b H; exact H |].
    intros fvs va Hlen.
    rewrite (Hargs df_src df_tgt Hs Ht).
    apply cfg_local_sim_to_local_vdraw_sim.
    apply (Hsb df_src df_tgt Hs Ht).
    intros x Hx; apply init_local_env_in.
    rewrite (map_fst_combine_eq (df_args df_src) fvs Hlen); exact Hx.
  Qed.

  (** Call-free leaf slice contract ([F-59]): lifts [DVALUE_Poison -> Concrete]
      (e.g. [xor %x, %x -> 0]) and [freeze] folding ([DrawE]) to whole-module
      [prog_value_draw_refines] WITHOUT requiring [noundef] on the prototype! *)
  Definition slice_leaf_value_refines
    (entry : function_id * CFG.mcfg dtyp * CFG.mcfg dtyp) : Prop :=
    let '(_, m_slice_src, m_slice_tgt) := entry in
    forall df_src df_tgt,
      m_definitions m_slice_src = [df_src] ->
      m_definitions m_slice_tgt = [df_tgt] ->
      forall fvs va,
        List.length fvs = List.length (df_args df_src) ->
        cfg_local_vdraw_leaf_sim (fun _ _ r1 r2 => mm_ret_dvalue_refines r1 r2)
          (init_local_env (List.combine (df_args df_src) fvs))
          (init_local_env (List.combine (df_args df_tgt) fvs))
          (denote_cfg (df_instrs df_src) va)
          (denote_cfg (df_instrs df_tgt) va).

  (** Master Compositional Module-Merge Value- & [DrawE]-Refinement Theorem ([F-59]). *)
  Theorem check_flex_module_merge_value_refines
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hchk : check_flex_module_merge m_orig m_merged verified_slices = true)
    (Hslices : Forall slice_value_refines verified_slices) :
    prog_value_draw_refines m_orig m_merged.
  Proof using.
    apply (module_defs_vdraw_refines true m_orig m_merged).
    - exact (check_flex_module_merge_build_global_environment_eq m_orig m_merged verified_slices Hchk).
    - unfold check_flex_module_merge in Hchk; rewrite !Bool.andb_true_iff in Hchk.
      destruct Hchk as [[[[[[[[_ Hdecl] _] _] _] _] _] _] _].
      exact (proj1 (mm_list_eqb_eq _ mm_declaration_eqb_eq _ _) Hdecl).
    - unfold check_flex_module_merge in Hchk; rewrite !Bool.andb_true_iff in Hchk.
      destruct Hchk as [_ Hdefs].
      pose proof (check_flex_defs_merge_Forall2 verified_slices _ _ Hdefs) as Hprov.
      clear Hdefs;
      induction Hprov as [| df_orig df_merged r1 r2 (Hpr & Hlen & Hdisj) _ IH];
        [constructor | constructor; [| exact IH]].
      destruct Hdisj as [-> | (fid & m_src & m_tgt & df_src & df_tgt & Hin & Hsw)].
      + refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
        exists (@Logic.eq (@dvalue PaV)).
        split; [intros v1 v2 <-; apply mm_ret_dvalue_refines_refl |].
        split; [intros _; left; intros a b H; exact H |].
        intros fvs va _; apply cfg_local_sim_to_local_vdraw_sim, SCCP.denote_cfg_refl_sim.
      + refine (conj Hpr (conj Hlen _)).
        rewrite Forall_forall in Hslices.
        destruct (Hslices (fid, m_src, m_tgt) Hin df_src df_tgt
                    (sw_src_defs _ _ _ _ _ _ _ Hsw)
                    (sw_tgt_defs _ _ _ _ _ _ _ Hsw))
          as (RR_b & Hsub & Hup & Hbd).
        exists RR_b; split; [exact Hsub |].
        split.
        * intros _; rewrite <- (sw_src_param_attrs _ _ _ _ _ _ _ Hsw); exact Hup.
        * intros fvs va Hlf.
          rewrite <- (sw_src_args _ _ _ _ _ _ _ Hsw) in Hlf |- *.
          rewrite <- (sw_src_instrs _ _ _ _ _ _ _ Hsw),
                  <- (sw_tgt_args _ _ _ _ _ _ _ Hsw),
                  <- (sw_tgt_instrs _ _ _ _ _ _ _ Hsw).
          exact (Hbd fvs va Hlf).
  Qed.

  Corollary check_module_merge_value_refines
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hchk : check_module_merge m_orig m_merged verified_slices = true)
    (Hslices : Forall slice_value_refines verified_slices) :
    prog_value_draw_refines m_orig m_merged.
  Proof using.
    exact (check_flex_module_merge_value_refines m_orig m_merged verified_slices
             (check_module_merge_implies_flex m_orig m_merged verified_slices Hchk) Hslices).
  Qed.

  (** Whole-module value- & [DrawE]-refinement theorem for call-free leaf modules
      and per-function slices WITHOUT [noundef] (closing [xor %x, %x -> 0] +
      [freeze] folding even when the prototype carries no [noundef] attribute). *)
  Theorem check_flex_module_merge_leaf_value_refines
    (m_orig m_merged : CFG.mcfg dtyp)
    (verified_slices : list (function_id * CFG.mcfg dtyp * CFG.mcfg dtyp))
    (Hchk : check_flex_module_merge m_orig m_merged verified_slices = true)
    (Hunchanged_leaf :
      forall df,
        In df (m_definitions m_orig) ->
        forall fvs va,
          List.length fvs = List.length (df_args df) ->
          cfg_local_vdraw_leaf_sim (fun _ _ r1 r2 => mm_ret_dvalue_refines r1 r2)
            (init_local_env (List.combine (df_args df) fvs))
            (init_local_env (List.combine (df_args df) fvs))
            (denote_cfg (df_instrs df) va)
            (denote_cfg (df_instrs df) va))
    (Hslices : Forall slice_leaf_value_refines verified_slices) :
    prog_value_draw_refines m_orig m_merged.
  Proof using.
    apply (module_defs_vdraw_refines false m_orig m_merged).
    - exact (check_flex_module_merge_build_global_environment_eq m_orig m_merged verified_slices Hchk).
    - unfold check_flex_module_merge in Hchk; rewrite !Bool.andb_true_iff in Hchk.
      destruct Hchk as [[[[[[[[_ Hdecl] _] _] _] _] _] _] _].
      exact (proj1 (mm_list_eqb_eq _ mm_declaration_eqb_eq _ _) Hdecl).
    - unfold check_flex_module_merge in Hchk; rewrite !Bool.andb_true_iff in Hchk.
      destruct Hchk as [_ Hdefs].
      pose proof (check_flex_defs_merge_Forall2 verified_slices _ _ Hdefs) as Hprov.
      clear Hdefs; revert Hunchanged_leaf;
        induction Hprov as [| df_orig df_merged r1 r2 (Hpr & Hlen & Hdisj) _ IH];
        intros Hunchanged_sub; [constructor |].
      constructor.
      + destruct Hdisj as [-> | (fid & m_src & m_tgt & df_src & df_tgt & Hin & Hsw)].
        * refine (conj Logic.eq_refl (conj Logic.eq_refl _)).
          exists mm_ret_dvalue_refines.
          split; [intros v1 v2 H; exact H |].
          split; [intros H; discriminate H |].
          apply Hunchanged_sub; left; reflexivity.
        * refine (conj Hpr (conj Hlen _)).
          rewrite Forall_forall in Hslices.
          exists mm_ret_dvalue_refines.
          split; [intros v1 v2 H; exact H |].
          split; [intros H; discriminate H |].
          intros fvs va Hlf.
          rewrite <- (sw_src_args _ _ _ _ _ _ _ Hsw) in Hlf |- *.
          rewrite <- (sw_src_instrs _ _ _ _ _ _ _ Hsw),
                  <- (sw_tgt_args _ _ _ _ _ _ _ Hsw),
                  <- (sw_tgt_instrs _ _ _ _ _ _ _ Hsw).
          exact (Hslices (fid, m_src, m_tgt) Hin df_src df_tgt
                   (sw_src_defs _ _ _ _ _ _ _ Hsw)
                   (sw_tgt_defs _ _ _ _ _ _ _ Hsw) fvs va Hlf).
      + apply IH; intros df Hdf; apply Hunchanged_sub; right; exact Hdf.
  Qed.

End ValueDrawRefinement.


