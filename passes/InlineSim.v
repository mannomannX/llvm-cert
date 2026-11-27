(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Elastic Coinductive Inlining Simulation ([CertPasses.InlineSim])

    Purpose:
      Defines finite [Tau] prefixes ([itree_tau_star]), inlining contexts
      ([inline_ctx]), the generic coinductive simulation [gen_inline_sim],
      concrete [cfg_inline_sim]/[mcfg_inline_sim] instances, and lifting across
      [mrec], [interp_intrinsics], and [interp_state] ([mcfg_inline_sim_to_model]).

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml.

    Assumptions:
      Depends on Stdlib, Paco, ITree, ExtLib, Vellvm, [CertPasses.PassCommon],
      [CertPasses.common.ItreeTactics], and [CertPasses.InlineFrameGenv]; zero
      custom axioms (arbitrary [IPtr] / [IPtrTheory]).

    Section Outline:
      (8A) [itree_tau_star] & [inline_ctx]; (8B) [GenInlineSim] combinators;
      (8C) Concrete [CFGtop]/[MCFGtop] instances; (8D) Lifting across [mrec],
      [interp_intrinsics], & [mcfg_inline_sim_to_model]. *)

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

From CertPasses Require Import InlineFrameGenv.

Section InliningSemantics.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Notation PaV := (@ParamsV IP IPT).
  #[local] Existing Instance MemoryModelStateV.
  #[local] Existing Instance MemoryModelPrimitivesV.
  #[local] Hint Resolve refine_prov__mon : paco.

  (** ** 8A. Finite [Tau]/Bisimulation Prefix ([itree_tau_star]) and Inlining Contexts *)

  Inductive itree_tau_star {E : Type -> Type} {R : Type}
    : itree E R -> itree E R -> Prop :=
  | ITS_Refl (t : itree E R) :
      itree_tau_star t t
  | ITS_Eq (t1 t2 t3 : itree E R) :
      t1 ≅ t2 ->
      itree_tau_star t2 t3 ->
      itree_tau_star t1 t3
  | ITS_Tau (m t' : itree E R) :
      itree_tau_star m t' ->
      itree_tau_star (Tau m) t'.

  Lemma itree_tau_star_trans {E : Type -> Type} {R : Type}
    (t1 t2 t3 : itree E R) :
    itree_tau_star t1 t2 ->
    itree_tau_star t2 t3 ->
    itree_tau_star t1 t3.
  Proof using.
    intros H12 H23; induction H12 as [t | a b c Hab _ IH | m b _ IH].
    - exact H23.
    - eapply ITS_Eq; [exact Hab | apply IH, H23].
    - apply ITS_Tau, IH, H23.
  Qed.

  Lemma itree_tau_star_bind {E : Type -> Type} {A B : Type}
    (t t' : itree E A) (k : A -> itree E B) :
    itree_tau_star t t' ->
    itree_tau_star (ITree.bind t k) (ITree.bind t' k).
  Proof using.
    intros Ht; induction Ht as [a | a b c Hab _ IH | m b _ IH].
    - apply ITS_Refl.
    - eapply ITS_Eq; [rewrite Hab; reflexivity | exact IH].
    - eapply ITS_Eq; [apply Eqit.bind_tau | apply ITS_Tau, IH].
  Qed.

  Inductive inline_ctx : Type :=
  | IC_Synced (stk : env_stack) (e1 e2 : @local_env PaV)
  | IC_MemPushed (stk : env_stack) (e1 e2 : @local_env PaV)
  | IC_Inlined (stk : env_stack) (caller_e1 e1 e2 : @local_env PaV).

  Definition ic_env1 (ic : inline_ctx) : option (@local_env PaV) :=
    match ic with
    | IC_Synced _ e1 _ => Some e1
    | IC_MemPushed _ _ _ => None
    | IC_Inlined _ _ e1 _ => Some e1
    end.

  Definition ic_env2 (ic : inline_ctx) : option (@local_env PaV) :=
    match ic with
    | IC_Synced _ _ e2 => Some e2
    | IC_MemPushed _ _ _ => None
    | IC_Inlined _ _ _ e2 => Some e2
    end.

  Definition ic_write1 (x : local_id) (v : @dvalue PaV) (ic : inline_ctx) : option inline_ctx :=
    match ic with
    | IC_Synced stk e1 e2 => Some (IC_Synced stk (Maps.add x v e1) e2)
    | IC_MemPushed _ _ _ => None
    | IC_Inlined stk ce1 e1 e2 => Some (IC_Inlined stk ce1 (Maps.add x v e1) e2)
    end.

  Definition ic_write2 (x : local_id) (v : @dvalue PaV) (ic : inline_ctx) : option inline_ctx :=
    match ic with
    | IC_Synced stk e1 e2 => Some (IC_Synced stk e1 (Maps.add x v e2))
    | IC_MemPushed _ _ _ => None
    | IC_Inlined stk ce1 e1 e2 => Some (IC_Inlined stk ce1 e1 (Maps.add x v e2))
    end.

  Definition is_ic_inlined (ic : inline_ctx) : bool :=
    match ic with
    | IC_Inlined _ _ _ _ => true
    | _ => false
    end.

  Definition is_ic_synced (ic : inline_ctx) : bool :=
    match ic with
    | IC_Synced _ _ _ => true
    | _ => false
    end.

  Definition inline_fused_match (g0 : global_env) (ic : inline_ctx) (s1 s2 : FusedS) : Prop :=
    let '(m1, ((sf1, fstk1), g1)) := s1 in
    let '(m2, ((sf2, fstk2), g2)) := s2 in
    g1 = g0 /\
    g2 = g0 /\
    match ic with
    | IC_Synced stk e1 e2 =>
        m1 = m2 /\
        sf_match e1 e2 sf1 sf2 /\
        stk_frames_match stk fstk1 fstk2
    | IC_MemPushed stk e1 e2 =>
        m1 = push_empty_frame m2 /\
        sf_match e1 e2 sf1 sf2 /\
        stk_frames_match stk fstk1 fstk2
    | IC_Inlined stk caller_e1 e1 e2 =>
        m1 = push_empty_frame m2 /\
        sf1.(stack_vars) = e1 /\
        exists caller_sf1 fstk1',
          fstk1 = caller_sf1 :: fstk1' /\
          sf_match caller_e1 e2 caller_sf1 sf2 /\
          stk_frames_match stk fstk1' fstk2
    end.

  Definition inl_is_ub_mcfg {X : Type} (e : @MCFGEtop PaV X) : bool :=
    match e with
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 (ThrowOOM _))))))) => true
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 (ThrowUB _))))))))) => true
    | _ => false
    end.

  Definition inl_is_ub_cfg {X : Type} (e : @CFGEtop PaV X) : bool :=
    match e with
    | inl1 _ => false
    | inr1 m => inl_is_ub_mcfg m
    end.

  Definition inl_sync_mcfg (ic : inline_ctx) {X : Type} (e : @MCFGEtop PaV X) : bool :=
    match ic with
    | IC_MemPushed _ _ _ => false
    | IC_Synced _ _ _ =>
        match e with
        | inr1 (inr1 (inl1 (GlobalWrite _ _))) => false
        | inr1 (inr1 (inr1 (inl1 (inl1 _)))) => false
        | inr1 (inr1 (inr1 (inl1 (inr1 (StackPush _))))) => false
        | inr1 (inr1 (inr1 (inl1 (inr1 StackPop)))) => false
        | _ => true
        end
    | IC_Inlined _ _ _ _ =>
        match e with
        | inl1 _ => false
        | inr1 (inl1 _) => false
        | inr1 (inr1 (inl1 (GlobalRead _))) => true
        | inr1 (inr1 (inl1 (GlobalWrite _ _))) => false
        | inr1 (inr1 (inr1 (inl1 _))) => false
        | inr1 (inr1 (inr1 (inr1 (inl1 me)))) => is_callee_sync_mem me
        | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 _))))) => true
        | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 _)))))) => true
        | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 _))))))) => false
        | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 _))))))) => true
        end
    end.

  Definition inl_sync_cfg (ic : inline_ctx) {X : Type} (e : @CFGEtop PaV X) : bool :=
    match e with
    | inl1 _ =>
        match ic with
        | IC_Synced _ _ _ => true
        | _ => false
        end
    | inr1 m => inl_sync_mcfg ic m
    end.

  Lemma EqE_CFG_exc_of_event {X1 X2 : Type}
    (e1 : @CFGEtop PaV X1) (e2 : @CFGEtop PaV X2) :
    EqE_CFG X1 X2 e1 e2 ->
    exc_of_event e1 = exc_of_event e2.
  Proof using.
    intros HE; destruct_sum2 e1 e2 HE;
      cbn in *; try contradiction; try reflexivity.
    destruct e1 as [ex1], e2 as [ex2]; unfold EqE_Exc in HE; subst; reflexivity.
  Qed.

  Lemma inl_is_ub_cfg_no_exc {X : Type} (e : @CFGEtop PaV X) :
    inl_is_ub_cfg e = true ->
    exc_of_event e = None.
  Proof using.
    destruct_sum1 e; try discriminate; destruct e; reflexivity.
  Qed.

  Lemma inl_sync_cfg_inlined_no_exc stk ce1 e1 e2 {X : Type} (e : @CFGEtop PaV X) :
    inl_sync_cfg (IC_Inlined stk ce1 e1 e2) e = true ->
    exc_of_event e = None.
  Proof using.
    destruct_sum1 e; try discriminate; try reflexivity.
  Qed.

  (** ** 8B. Generic Coinductive Inlining Simulation ([gen_inline_sim]) *)

  Section GenInlineSim.
    Context {E : Type -> Type}
            `{@LocalE PaV -< E}
            `{@StackE PaV -< E}
            `{@GlobalE PaV -< E}
            `{@MemoryE PaV -< E}.
    Variable (is_ub : forall X, E X -> bool).
    Variable (is_sync : inline_ctx -> forall X, E X -> bool).
    Variable (EqE : prerel E E).
    Variable (EqA : postrel E E).
    Variable (ev_post : forall X, E X -> X -> Prop).
    Variable (as_loc : forall X, E X -> option (@LocalE PaV X)).
    Variable (as_stk : forall X, E X -> option (@StackE PaV X)).
    Variable (opt_call1 : forall X, E X -> option (itree E X)).
    Variable (g0 : global_env).
    Variable (allow_frame : bool).

    Definition gis_cont {R1 R2 : Type}
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      (ic : inline_ctx) (t1 : itree E R1) (t2 : itree E R2) : Prop :=
      exists m1 m2,
        itree_tau_star t1 m1 /\
        itree_tau_star t2 m2 /\
        r ic m1 m2.

    Lemma gis_cont_mon {R1 R2 : Type}
      (r r' : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      (LE : forall ic a1 a2, r ic a1 a2 -> r' ic a1 a2)
      (ic : inline_ctx) (t1 : itree E R1) (t2 : itree E R2) :
      gis_cont r ic t1 t2 -> gis_cont r' ic t1 t2.
    Proof using.
      intros (m1 & m2 & Hs1 & Hs2 & Hr).
      exists m1, m2; split; [exact Hs1 | split; [exact Hs2 | apply LE, Hr]].
    Qed.

    Lemma gis_cont_obs_eq {R1 R2 : Type}
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      (ic : inline_ctx) (t1 t1' : itree E R1) (t2 t2' : itree E R2) :
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      gis_cont r ic t1 t2 ->
      gis_cont r ic t1' t2'.
    Proof using.
      intros E1 E2 (m1 & m2 & Hs1 & Hs2 & Hr).
      exists m1, m2.
      split; [eapply ITS_Eq; [symmetry; exact E1 | exact Hs1] |].
      split; [eapply ITS_Eq; [symmetry; exact E2 | exact Hs2] | exact Hr].
    Qed.

    Definition gis_vis_both {R1 R2 : Type}
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      (ic : inline_ctx)
      {X1} (e1 : E X1) (k1 : X1 -> itree E R1)
      {X2} (e2 : E X2) (k2 : X2 -> itree E R2) : Prop :=
      (is_sync ic X1 e1 = true /\
       EqE X1 X2 e1 e2 /\
       forall a1 a2,
         EqA X1 X2 e1 a1 e2 a2 ->
         ev_post X1 e1 a1 ->
         gis_cont r ic (k1 a1) (k2 a2)) \/
      match ic with
      | IC_Synced stk env1 env2 =>
          (match as_loc X1 e1, as_loc X2 e2 with
           | Some le1, Some le2 =>
               match le1 in LocalE Y1 return (Y1 -> itree E R1) -> Prop with
               | LocalRead x1 => fun k1' =>
                   match le2 in LocalE Y2 return (Y2 -> itree E R2) -> Prop with
                   | LocalRead x2 => fun k2' =>
                       x1 = x2 /\
                       Maps.lookup x1 env1 = Maps.lookup x2 env2 /\
                       forall v,
                         Maps.lookup x1 env1 = Some v ->
                         gis_cont r (IC_Synced stk env1 env2) (k1' v) (k2' v)
                   | _ => fun _ => False
                   end k2
               | LocalWrite x1 v1 => fun k1' =>
                   match le2 in LocalE Y2 return (Y2 -> itree E R2) -> Prop with
                   | LocalWrite x2 v2 => fun k2' =>
                       x1 = x2 /\ v1 = v2 /\
                       gis_cont r (IC_Synced stk (Maps.add x1 v1 env1) (Maps.add x2 v2 env2))
                         (k1' tt) (k2' tt)
                   | _ => fun _ => False
                   end k2
               end k1
           | _, _ => False
           end) \/
          (allow_frame = true /\
           match as_stk X1 e1, as_stk X2 e2 with
           | Some se1, Some se2 =>
               match se1 in StackE Y1 return (Y1 -> itree E R1) -> Prop with
               | StackPush bs1 => fun k1' =>
                   match se2 in StackE Y2 return (Y2 -> itree E R2) -> Prop with
                   | StackPush bs2 => fun k2' =>
                       bs1 = bs2 /\
                       gis_cont r (IC_Synced ((env1, env2) :: stk)
                                     (init_local_env bs1) (init_local_env bs2))
                         (k1' tt) (k2' tt)
                   | _ => fun _ => False
                   end k2
               | StackPop => fun k1' =>
                   match se2 in StackE Y2 return (Y2 -> itree E R2) -> Prop with
                   | StackPop => fun k2' =>
                       match stk with
                       | [] => True
                       | (p1, p2) :: rest =>
                           gis_cont r (IC_Synced rest p1 p2) (k1' tt) (k2' tt)
                       end
                   | _ => fun _ => False
                   end k2
               | _ => fun _ => False
               end k1
           | _, _ => False
           end)
      | _ => False
      end.

    Definition gis_step_body {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      (ic : inline_ctx)
      (ot1 : itree' E R1) (ot2 : itree' E R2) : Prop :=
      match ot1 with
      | RetF r1 =>
          match ot2 with
          | RetF r2 => RR ic r1 r2
          | _ => False
          end
      | TauF m1 =>
          match ot2 with
          | TauF m2 => gis_cont r ic m1 m2
          | _ => False
          end
      | VisF _ e1 k1 =>
          is_ub _ e1 = true \/
          match ot2 with
          | VisF _ e2 k2 => gis_vis_both r ic e1 k1 e2 k2
          | _ => False
          end
      end.

    Inductive gen_inline_sim_ {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      : inline_ctx -> itree E R1 -> itree E R2 -> Prop :=
    | GIS_Step ic t1 t2 :
        gis_step_body RR r ic (observe t1) (observe t2) ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_TauL ic t1 m1 t2 :
        observe t1 = TauF m1 ->
        gen_inline_sim_ RR r ic m1 t2 ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_TauR ic t1 t2 m2 :
        observe t2 = TauF m2 ->
        gen_inline_sim_ RR r ic t1 m2 ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_ReadL ic env1 t1 x v k1 t2 :
        ic_env1 ic = Some env1 ->
        t1 ≅ ITree.bind (ITree.trigger (subevent _ (LocalRead x))) k1 ->
        Maps.lookup x env1 = Some v ->
        gen_inline_sim_ RR r ic (k1 v) t2 ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_ReadR ic env2 t1 t2 x v k2 :
        ic_env2 ic = Some env2 ->
        t2 ≅ ITree.bind (ITree.trigger (subevent _ (LocalRead x))) k2 ->
        Maps.lookup x env2 = Some v ->
        gen_inline_sim_ RR r ic t1 (k2 v) ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_WriteL ic ic' t1 x v k1 t2 :
        ic_write1 x v ic = Some ic' ->
        t1 ≅ ITree.bind (ITree.trigger (subevent _ (LocalWrite x v))) k1 ->
        gen_inline_sim_ RR r ic' (k1 tt) t2 ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_WriteR ic ic' t1 t2 x v k2 :
        ic_write2 x v ic = Some ic' ->
        t2 ≅ ITree.bind (ITree.trigger (subevent _ (LocalWrite x v))) k2 ->
        gen_inline_sim_ RR r ic' t1 (k2 tt) ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_GReadL ic t1 k v k1 t2 :
        t1 ≅ ITree.bind (ITree.trigger (subevent _ (GlobalRead k))) k1 ->
        Maps.lookup k g0 = Some v ->
        gen_inline_sim_ RR r ic (k1 v) t2 ->
        gen_inline_sim_ RR r ic t1 t2
    | GIS_ZeroStoreL stk ce1 e1 e2 t1 varg k1 t2 :
        t1 ≅ ITree.bind
               (ITree.trigger
                  (subevent _
                     (Store (DTYPE_Struct true [])
                        (DVALUE_Base (DVALUE_Pointer varg))
                        (DVALUE_Struct true [])))) k1 ->
        gen_inline_sim_ RR r (IC_Inlined stk ce1 e1 e2) (k1 tt) t2 ->
        gen_inline_sim_ RR r (IC_Inlined stk ce1 e1 e2) t1 t2
    | GIS_MemPushL stk e1 e2 t1 k1 t2 :
        allow_frame = true ->
        t1 ≅ ITree.bind (ITree.trigger (subevent _ MemPush)) k1 ->
        gen_inline_sim_ RR r (IC_MemPushed stk e1 e2) (k1 tt) t2 ->
        gen_inline_sim_ RR r (IC_Synced stk e1 e2) t1 t2
    | GIS_StackPushL stk ce1 e2 bs t1 k1 t2 :
        allow_frame = true ->
        t1 ≅ ITree.bind (ITree.trigger (subevent _ (StackPush bs))) k1 ->
        gen_inline_sim_ RR r (IC_Inlined stk ce1 (init_local_env bs) e2) (k1 tt) t2 ->
        gen_inline_sim_ RR r (IC_MemPushed stk ce1 e2) t1 t2
    | GIS_StackPopL stk ce1 e1 e2 t1 k1 t2 :
        allow_frame = true ->
        t1 ≅ ITree.bind (ITree.trigger (subevent _ StackPop)) k1 ->
        gen_inline_sim_ RR r (IC_MemPushed stk ce1 e2) (k1 tt) t2 ->
        gen_inline_sim_ RR r (IC_Inlined stk ce1 e1 e2) t1 t2
    | GIS_MemPopL stk ce1 e2 t1 k1 t2 :
        allow_frame = true ->
        t1 ≅ ITree.bind (ITree.trigger (subevent _ MemPop)) k1 ->
        gen_inline_sim_ RR r (IC_Synced stk ce1 e2) (k1 tt) t2 ->
        gen_inline_sim_ RR r (IC_MemPushed stk ce1 e2) t1 t2
    | GIS_InlCallL stk e1 e2 t1 X (ce : E X) body1 k1 t2 :
        allow_frame = true ->
        t1 ≅ ITree.bind (ITree.trigger ce) k1 ->
        opt_call1 X ce = Some body1 ->
        gen_inline_sim_ RR r (IC_Synced stk e1 e2) (ITree.bind body1 k1) t2 ->
        gen_inline_sim_ RR r (IC_Synced stk e1 e2) t1 t2.

    Lemma gen_inline_sim__mon {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop) :
      monotone3 (gen_inline_sim_ RR).
    Proof using.
      intros ic t1 t2 r r' IN LE.
      induction IN as [ic t1 t2 Hstep
                       | ic t1 m1 t2 Ht1 _ IH
                       | ic t1 t2 m2 Ht2 _ IH
                       | ic env1 t1 x v k1 t2 He1 Ht1 Hlk _ IH
                       | ic env2 t1 t2 x v k2 He2 Ht2 Hlk _ IH
                       | ic ic' t1 x v k1 t2 Hw1 Ht1 _ IH
                       | ic ic' t1 t2 x v k2 Hw2 Ht2 _ IH
                       | ic t1 k v k1 t2 Ht1 Hlk _ IH
                       | stk ce1 e1 e2 t1 varg k1 t2 Ht1 _ IH
                       | stk e1 e2 t1 k1 t2 Hfr Ht1 _ IH
                       | stk ce1 e2 bs t1 k1 t2 Hfr Ht1 _ IH
                       | stk ce1 e1 e2 t1 k1 t2 Hfr Ht1 _ IH
                       | stk ce1 e2 t1 k1 t2 Hfr Ht1 _ IH
                       | stk e1 e2 t1 X ce body1 k1 t2 Hfr Ht1 Hopt _ IH].
      - apply GIS_Step; unfold gis_step_body in *.
        destruct (observe t1) as [r1 | m1 | X1 e1 k1].
        + exact Hstep.
        + destruct (observe t2); [exact Hstep | eapply gis_cont_mon; eassumption | exact Hstep].
        + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe t2) as [r2 | m2 | X2 e2 k2]; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | Hls].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; eapply gis_cont_mon; [exact LE | exact (HA a1 a2 Ha Hp)].
          * right; destruct ic as [stk env1 env2 | |]; try contradiction.
            destruct Hls as [Hloc | [Hfr_s Hstk]].
            -- left.
               destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
               destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
               ++ destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv |]].
                  eapply gis_cont_mon; [exact LE | exact Hr].
               ++ destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                  intros v Hv; eapply gis_cont_mon; [exact LE | apply Hrd, Hv].
            -- right; split; [exact Hfr_s |].
               destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
               destruct se1, se2; try contradiction.
               ++ destruct Hstk as [Hbs Hr]; split; [exact Hbs | eapply gis_cont_mon; eassumption].
               ++ destruct stk as [| [p1 p2] rest]; [exact I | eapply gis_cont_mon; eassumption].
      - eapply GIS_TauL; [exact Ht1 | exact IH].
      - eapply GIS_TauR; [exact Ht2 | exact IH].
      - eapply GIS_ReadL; [exact He1 | exact Ht1 | exact Hlk | exact IH].
      - eapply GIS_ReadR; [exact He2 | exact Ht2 | exact Hlk | exact IH].
      - eapply GIS_WriteL; [exact Hw1 | exact Ht1 | exact IH].
      - eapply GIS_WriteR; [exact Hw2 | exact Ht2 | exact IH].
      - eapply GIS_GReadL; [exact Ht1 | exact Hlk | exact IH].
      - eapply GIS_ZeroStoreL; [exact Ht1 | exact IH].
      - eapply GIS_MemPushL; [exact Hfr | exact Ht1 | exact IH].
      - eapply GIS_StackPushL; [exact Hfr | exact Ht1 | exact IH].
      - eapply GIS_StackPopL; [exact Hfr | exact Ht1 | exact IH].
      - eapply GIS_MemPopL; [exact Hfr | exact Ht1 | exact IH].
      - eapply GIS_InlCallL; [exact Hfr | exact Ht1 | exact Hopt | exact IH].
    Qed.

    #[local] Hint Resolve gen_inline_sim__mon : paco.

    Definition gen_inline_sim {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (ic : inline_ctx) (t1 : itree E R1) (t2 : itree E R2) : Prop :=
      paco3 (gen_inline_sim_ RR) bot3 ic t1 t2.

    Lemma gen_inline_sim__obs_eq {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop) :
      forall ic t1 t1' t2 t2',
        t1 ≅ t1' ->
        t2 ≅ t2' ->
        gen_inline_sim_ RR r ic t1 t2 ->
        gen_inline_sim_ RR r ic t1' t2'.
    Proof using.
      intros ic t1 t1' t2 t2' E1 E2 Hsim.
      revert t1' t2' E1 E2;
        induction Hsim as [ic t1 t2 Hstep
                           | ic t1 m1 t2 Ht1 _ IH
                           | ic t1 t2 m2 Ht2 _ IH
                           | ic env1 t1 x v k1 t2 He1 Ht1 Hlk _ IH
                           | ic env2 t1 t2 x v k2 He2 Ht2 Hlk _ IH
                           | ic ic' t1 x v k1 t2 Hw1 Ht1 _ IH
                           | ic ic' t1 t2 x v k2 Hw2 Ht2 _ IH
                           | ic t1 k v k1 t2 Ht1 Hlk _ IH
                           | stk ce1 e1 e2 t1 varg k1 t2 Ht1 _ IH
                           | stk e1 e2 t1 k1 t2 Hfr Ht1 _ IH
                           | stk ce1 e2 bs t1 k1 t2 Hfr Ht1 _ IH
                           | stk ce1 e1 e2 t1 k1 t2 Hfr Ht1 _ IH
                           | stk ce1 e2 t1 k1 t2 Hfr Ht1 _ IH
                           | stk e1 e2 t1 X ce body1 k1 t2 Hfr Ht1 Hopt _ IH];
        intros t1' t2' E1 E2.
      - punfold E1; red in E1; punfold E2; red in E2.
        apply GIS_Step; unfold gis_step_body in *.
        destruct E1 as [r1 r1' <- | m1 m1' Hm1 | X1 e1 k1 k1' Hk1 | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; pclearbot.
        + destruct E2 as [r2 r2' <- | | | ? ? Hchk _ | ? ? Hchk _];
            try inversion Hchk; try contradiction; exact Hstep.
        + destruct E2 as [| m2 m2' Hm2 | | ? ? Hchk _ | ? ? Hchk _];
            try inversion Hchk; try contradiction; pclearbot.
          eapply gis_cont_obs_eq; [exact Hm1 | exact Hm2 | exact Hstep].
        + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct E2 as [| | X2 e2 k2 k2' Hk2 | ? ? Hchk _ | ? ? Hchk _];
            try inversion Hchk; try contradiction; pclearbot.
          destruct Hvis as [(Hsync & HE & HA) | Hls].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; eapply gis_cont_obs_eq;
              [apply Hk1 | apply Hk2 | exact (HA a1 a2 Ha Hp)].
          * right; destruct ic as [stk env1 env2 | |]; try contradiction.
            destruct Hls as [Hloc | [Hfr_s Hstk]].
            -- left.
               destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
               destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
               ++ destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv |]].
                  eapply gis_cont_obs_eq; [apply Hk1 | apply Hk2 | exact Hr].
               ++ destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                  intros v Hv; eapply gis_cont_obs_eq; [apply Hk1 | apply Hk2 | apply Hrd, Hv].
            -- right; split; [exact Hfr_s |].
               destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
               destruct se1, se2; try contradiction.
               ++ destruct Hstk as [Hbs Hr]; split; [exact Hbs |].
                  eapply gis_cont_obs_eq; [apply Hk1 | apply Hk2 | exact Hr].
               ++ destruct stk as [| [p1 p2] rest];
                    [exact I | eapply gis_cont_obs_eq; [apply Hk1 | apply Hk2 | exact Hstk]].
      - punfold E1; red in E1; rewrite Ht1 in E1;
          apply eqitF_inv_Tau_l in E1 as (m1' & E1b & Hm1); pclearbot.
        eapply GIS_TauL; [exact E1b | eapply IH; [exact Hm1 | exact E2]].
      - punfold E2; red in E2; rewrite Ht2 in E2;
          apply eqitF_inv_Tau_l in E2 as (m2' & E2b & Hm2); pclearbot.
        eapply GIS_TauR; [exact E2b | eapply IH; [exact E1 | exact Hm2]].
      - eapply GIS_ReadL;
          [ exact He1 | symmetry; etransitivity; [symmetry; exact Ht1 | exact E1]
          | exact Hlk | apply IH; [reflexivity | exact E2] ].
      - eapply GIS_ReadR;
          [ exact He2 | symmetry; etransitivity; [symmetry; exact Ht2 | exact E2]
          | exact Hlk | apply IH; [exact E1 | reflexivity] ].
      - eapply GIS_WriteL;
          [ exact Hw1 | symmetry; etransitivity; [symmetry; exact Ht1 | exact E1]
          | apply IH; [reflexivity | exact E2] ].
      - eapply GIS_WriteR;
          [ exact Hw2 | symmetry; etransitivity; [symmetry; exact Ht2 | exact E2]
          | apply IH; [exact E1 | reflexivity] ].
      - eapply GIS_GReadL;
          [ symmetry; etransitivity; [symmetry; exact Ht1 | exact E1]
          | exact Hlk | apply IH; [reflexivity | exact E2] ].
      - eapply GIS_ZeroStoreL;
          [ symmetry; etransitivity; [symmetry; exact Ht1 | exact E1]
          | apply IH; [reflexivity | exact E2] ].
      - eapply GIS_MemPushL;
          [ exact Hfr | symmetry; etransitivity; [symmetry; exact Ht1 | exact E1]
          | apply IH; [reflexivity | exact E2] ].
      - eapply GIS_StackPushL;
          [ exact Hfr | symmetry; etransitivity; [symmetry; exact Ht1 | exact E1]
          | apply IH; [reflexivity | exact E2] ].
      - eapply GIS_StackPopL;
          [ exact Hfr | symmetry; etransitivity; [symmetry; exact Ht1 | exact E1]
          | apply IH; [reflexivity | exact E2] ].
      - eapply GIS_MemPopL;
          [ exact Hfr | symmetry; etransitivity; [symmetry; exact Ht1 | exact E1]
          | apply IH; [reflexivity | exact E2] ].
      - eapply GIS_InlCallL;
          [ exact Hfr | symmetry; etransitivity; [symmetry; exact Ht1 | exact E1]
          | exact Hopt | apply IH; [reflexivity | exact E2] ].
    Qed.

    Lemma gen_inline_sim_obs_eq {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (ic : inline_ctx) (t1 t1' : itree E R1) (t2 t2' : itree E R2) :
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      gen_inline_sim RR ic t1 t2 ->
      gen_inline_sim RR ic t1' t2'.
    Proof using.
      intros E1 E2 Hsim; pstep; punfold Hsim.
      eapply gen_inline_sim__obs_eq; eassumption.
    Qed.

    Lemma gen_inline_sim__tau_star_l {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      (ic : inline_ctx) (t1 m1 : itree E R1) (t2 : itree E R2) :
      itree_tau_star t1 m1 ->
      gen_inline_sim_ RR r ic m1 t2 ->
      gen_inline_sim_ RR r ic t1 t2.
    Proof using.
      intros Hs; induction Hs as [a | a b c Hab _ IH | m b _ IH]; intros Hsim.
      - exact Hsim.
      - eapply gen_inline_sim__obs_eq; [symmetry; exact Hab | reflexivity | apply IH, Hsim].
      - eapply GIS_TauL; [reflexivity | apply IH, Hsim].
    Qed.

    Lemma gen_inline_sim__tau_star_r {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (r : inline_ctx -> itree E R1 -> itree E R2 -> Prop)
      (ic : inline_ctx) (t1 : itree E R1) (t2 m2 : itree E R2) :
      itree_tau_star t2 m2 ->
      gen_inline_sim_ RR r ic t1 m2 ->
      gen_inline_sim_ RR r ic t1 t2.
    Proof using.
      intros Hs; induction Hs as [a | a b c Hab _ IH | m b _ IH]; intros Hsim.
      - exact Hsim.
      - eapply gen_inline_sim__obs_eq; [reflexivity | symmetry; exact Hab | apply IH, Hsim].
      - eapply GIS_TauR; [reflexivity | apply IH, Hsim].
    Qed.

    Lemma gen_inline_sim_tau_star_l {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (ic : inline_ctx) (t1 m1 : itree E R1) (t2 : itree E R2) :
      itree_tau_star t1 m1 ->
      gen_inline_sim RR ic m1 t2 ->
      gen_inline_sim RR ic t1 t2.
    Proof using.
      intros Hs Hsim; pstep; punfold Hsim.
      eapply gen_inline_sim__tau_star_l; eassumption.
    Qed.

    Lemma gen_inline_sim_tau_star_r {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (ic : inline_ctx) (t1 : itree E R1) (t2 m2 : itree E R2) :
      itree_tau_star t2 m2 ->
      gen_inline_sim RR ic t1 m2 ->
      gen_inline_sim RR ic t1 t2.
    Proof using.
      intros Hs Hsim; pstep; punfold Hsim.
      eapply gen_inline_sim__tau_star_r; eassumption.
    Qed.

    Lemma gen_inline_sim_ret {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (ic : inline_ctx) (r1 : R1) (r2 : R2)
      (Hrr : RR ic r1 r2) :
      gen_inline_sim RR ic (Ret r1) (Ret r2).
    Proof using.
      pstep; apply GIS_Step; cbn; exact Hrr.
    Qed.

    Lemma gen_inline_sim_weaken {R1 R2 : Type}
      (RR RR' : inline_ctx -> R1 -> R2 -> Prop)
      (Himp : forall ic r1 r2, RR ic r1 r2 -> RR' ic r1 r2) :
      forall ic t1 t2,
        gen_inline_sim RR ic t1 t2 ->
        gen_inline_sim RR' ic t1 t2.
    Proof using.
      pcofix CIH.
      intros ic t1 t2 Hsim; pstep; punfold Hsim.
      eapply gen_inline_sim__mon with
        (r := fun ic0 a1 a2 => upaco3 (gen_inline_sim_ RR) bot3 ic0 a1 a2);
        [| intros ic0 a1 a2 [Hr | Hb]; [right; apply CIH, Hr | inversion Hb]].
      clear r CIH.
      induction Hsim as [ic t1 t2 Hstep
                         | ic t1 m1 t2 Ht1 _ IH
                         | ic t1 t2 m2 Ht2 _ IH
                         | ic env1 t1 x v k1 t2 He1 Ht1 Hlk _ IH
                         | ic env2 t1 t2 x v k2 He2 Ht2 Hlk _ IH
                         | ic ic' t1 x v k1 t2 Hw1 Ht1 _ IH
                         | ic ic' t1 t2 x v k2 Hw2 Ht2 _ IH
                         | ic t1 k v k1 t2 Ht1 Hlk _ IH
                         | stk ce1 e1 e2 t1 varg k1 t2 Ht1 _ IH
                         | stk e1 e2 t1 k1 t2 Hfr Ht1 _ IH
                         | stk ce1 e2 bs t1 k1 t2 Hfr Ht1 _ IH
                         | stk ce1 e1 e2 t1 k1 t2 Hfr Ht1 _ IH
                         | stk ce1 e2 t1 k1 t2 Hfr Ht1 _ IH
                         | stk e1 e2 t1 X ce body1 k1 t2 Hfr Ht1 Hopt _ IH].
      - apply GIS_Step; unfold gis_step_body in *.
        destruct (observe t1); [destruct (observe t2); [apply Himp, Hstep | exact Hstep | exact Hstep]
                               | exact Hstep | exact Hstep].
      - eapply GIS_TauL; eassumption.
      - eapply GIS_TauR; eassumption.
      - eapply GIS_ReadL; eassumption.
      - eapply GIS_ReadR; eassumption.
      - eapply GIS_WriteL; eassumption.
      - eapply GIS_WriteR; eassumption.
      - eapply GIS_GReadL; eassumption.
      - eapply GIS_ZeroStoreL; eassumption.
      - eapply GIS_MemPushL; eassumption.
      - eapply GIS_StackPushL; eassumption.
      - eapply GIS_StackPopL; eassumption.
      - eapply GIS_MemPopL; eassumption.
      - eapply GIS_InlCallL; eassumption.
    Qed.

    Lemma gen_inline_sim_bind {A1 A2 B1 B2 : Type}
      (RA : inline_ctx -> A1 -> A2 -> Prop)
      (RB : inline_ctx -> B1 -> B2 -> Prop)
      (ic : inline_ctx)
      (t1 : itree E A1) (t2 : itree E A2)
      (k1 : A1 -> itree E B1) (k2 : A2 -> itree E B2)
      (Ht : gen_inline_sim RA ic t1 t2)
      (Hk : forall ic' a1 a2, RA ic' a1 a2 -> gen_inline_sim RB ic' (k1 a1) (k2 a2)) :
      gen_inline_sim RB ic (ITree.bind t1 k1) (ITree.bind t2 k2).
    Proof using.
      revert ic t1 t2 Ht; pcofix CIH; intros ic t1 t2 Ht.
      pstep; punfold Ht.
      set (r_bind := fun ic0 (b1 : itree E B1) (b2 : itree E B2) =>
                       upaco3 (gen_inline_sim_ RB) r ic0 b1 b2).
      assert (Hlift_cont :
        forall ic0 u1 u2,
          gis_cont (upaco3 (gen_inline_sim_ RA) bot3) ic0 u1 u2 ->
          gis_cont r_bind ic0 (ITree.bind u1 k1) (ITree.bind u2 k2)).
      { intros ic0 u1 u2 (m1 & m2 & Hs1 & Hs2 & [Hm | Hb]); [| inversion Hb].
        exists (ITree.bind m1 k1), (ITree.bind m2 k2).
        split; [apply itree_tau_star_bind, Hs1 |].
        split; [apply itree_tau_star_bind, Hs2 |].
        right; apply CIH, Hm. }
      induction Ht as [ic t1 t2 Hstep
                       | ic t1 m1 t2 Ht1 _ IH
                       | ic t1 t2 m2 Ht2 _ IH
                       | ic env1 t1 x v f1 t2 He1 Ht1 Hlk _ IH
                       | ic env2 t1 t2 x v f2 He2 Ht2 Hlk _ IH
                       | ic ic' t1 x v f1 t2 Hw1 Ht1 _ IH
                       | ic ic' t1 t2 x v f2 Hw2 Ht2 _ IH
                       | ic t1 k v f1 t2 Ht1 Hlk _ IH
                       | stk ce1 e1 e2 t1 varg f1 t2 Ht1 _ IH
                       | stk e1 e2 t1 f1 t2 Hfr Ht1 _ IH
                       | stk ce1 e2 bs t1 f1 t2 Hfr Ht1 _ IH
                       | stk ce1 e1 e2 t1 f1 t2 Hfr Ht1 _ IH
                       | stk ce1 e2 t1 f1 t2 Hfr Ht1 _ IH
                       | stk e1 e2 t1 X ce body1 f1 t2 Hfr Ht1 Hopt _ IH].
      - unfold gis_step_body in Hstep.
        destruct (observe t1) as [a1 | m1 | X1 e1 f1] eqn:Hot1.
        + destruct (observe t2) as [a2 | m2 | X2 e2 f2] eqn:Hot2; try contradiction.
          assert (Eb1 : ITree.bind t1 k1 ≅ k1 a1).
          { rewrite (itree_eta t1), Hot1, Eqit.bind_ret_l; reflexivity. }
          assert (Eb2 : ITree.bind t2 k2 ≅ k2 a2).
          { rewrite (itree_eta t2), Hot2, Eqit.bind_ret_l; reflexivity. }
          pose proof (Hk ic a1 a2 Hstep) as Hka; punfold Hka.
          eapply gen_inline_sim__obs_eq; [symmetry; exact Eb1 | symmetry; exact Eb2 |].
          eapply gen_inline_sim__mon; [exact Hka |].
          intros ic0 b1 b2 [Hb | []]; left; eapply paco3_mon; [exact Hb | intros ? ? ? []].
        + destruct (observe t2) as [a2 | m2 | X2 e2 f2] eqn:Hot2; try contradiction.
          apply GIS_Step; unfold gis_step_body.
          rewrite !observe_bind, Hot1, Hot2.
          apply Hlift_cont, Hstep.
        + apply GIS_Step; unfold gis_step_body.
          rewrite (observe_bind t1 k1), Hot1.
          destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe t2) as [a2 | m2 | X2 e2 f2] eqn:Hot2; try contradiction.
          rewrite (observe_bind t2 k2), Hot2.
          destruct Hvis as [(Hsync & HE & HA) | Hls].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; apply Hlift_cont, (HA a1 a2 Ha Hp).
          * right; destruct ic as [stk env1 env2 | |]; try contradiction.
            destruct Hls as [Hloc | [Hfr_s Hstk]].
            -- left.
               destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
               destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
               ++ destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv | apply Hlift_cont, Hr]].
               ++ destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                  intros v Hv; apply Hlift_cont, Hrd, Hv.
            -- right; split; [exact Hfr_s |].
               destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
               destruct se1, se2; try contradiction.
               ++ destruct Hstk as [Hbs Hr]; split; [exact Hbs | apply Hlift_cont, Hr].
               ++ destruct stk as [| [p1 p2] rest]; [exact I | apply Hlift_cont, Hstk].
      - eapply GIS_TauL; [rewrite (observe_bind t1 k1), Ht1; reflexivity | exact IH].
      - eapply GIS_TauR; [rewrite (observe_bind t2 k2), Ht2; reflexivity | exact IH].
      - eapply GIS_ReadL; [exact He1 | rewrite Ht1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GIS_ReadR; [exact He2 | rewrite Ht2, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GIS_WriteL; [exact Hw1 | rewrite Ht1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_WriteR; [exact Hw2 | rewrite Ht2, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_GReadL; [rewrite Ht1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GIS_ZeroStoreL; [rewrite Ht1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_MemPushL; [exact Hfr | rewrite Ht1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_StackPushL; [exact Hfr | rewrite Ht1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_StackPopL; [exact Hfr | rewrite Ht1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_MemPopL; [exact Hfr | rewrite Ht1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GIS_InlCallL;
          [exact Hfr | rewrite Ht1, Eqit.bind_bind; reflexivity | exact Hopt |].
        eapply gen_inline_sim__obs_eq;
          [apply Eqit.bind_bind | reflexivity | exact IH].
    Qed.

    Lemma gen_inline_sim_trigger_sync {X1 X2 : Type}
      (e1 : E X1) (e2 : E X2) (ic : inline_ctx)
      (Hsync : is_sync ic X1 e1 = true)
      (HE : EqE X1 X2 e1 e2) :
      gen_inline_sim
        (fun ic' a1 a2 => ic' = ic /\ EqA X1 X2 e1 a1 e2 a2 /\ ev_post X1 e1 a1)
        ic (ITree.trigger e1) (ITree.trigger e2).
    Proof using.
      pstep; apply GIS_Step; unfold gis_step_body, ITree.trigger; cbn [observe].
      right; left; split; [exact Hsync | split; [exact HE |]].
      intros a1 a2 Ha Hp.
      exists (Ret a1), (Ret a2).
      split; [apply ITS_Refl | split; [apply ITS_Refl |]].
      left; apply gen_inline_sim_ret; split; [reflexivity | split; assumption].
    Qed.

  End GenInlineSim.

  #[local] Hint Resolve gen_inline_sim__mon : paco.

  Lemma gen_inline_sim_allow_frame
    {E : Type -> Type}
    `{@LocalE PaV -< E} `{@StackE PaV -< E} `{@GlobalE PaV -< E} `{@MemoryE PaV -< E}
    (is_ub : forall X, E X -> bool)
    (is_sync : inline_ctx -> forall X, E X -> bool)
    (EqE : prerel E E) (EqA : postrel E E)
    (ev_post : forall X, E X -> X -> Prop)
    (as_loc : forall X, E X -> option (@LocalE PaV X))
    (as_stk : forall X, E X -> option (@StackE PaV X))
    (opt_call1 : forall X, E X -> option (itree E X))
    (g0 : global_env) (b1 b2 : bool)
    (Hb : b1 = false \/ b1 = b2)
    {R1 R2 : Type} (RR : inline_ctx -> R1 -> R2 -> Prop) :
    forall ic (t1 : itree E R1) (t2 : itree E R2),
      gen_inline_sim is_ub is_sync EqE EqA ev_post as_loc as_stk opt_call1 g0 b1 RR ic t1 t2 ->
      gen_inline_sim is_ub is_sync EqE EqA ev_post as_loc as_stk opt_call1 g0 b2 RR ic t1 t2.
  Proof using.
    destruct Hb as [-> | ->]; [| intros ic t1 t2 Hsim; exact Hsim].
    pcofix CIH.
    intros ic t1 t2 Hsim; pstep; punfold Hsim.
    eapply gen_inline_sim__mon with
      (r := fun ic0 a1 a2 =>
              upaco3 (gen_inline_sim_ is_ub is_sync EqE EqA ev_post as_loc as_stk opt_call1 g0 false RR)
                bot3 ic0 a1 a2);
      [| intros ic0 a1 a2 [Hr | Hbot]; [right; apply CIH, Hr | inversion Hbot]].
    clear r CIH.
    induction Hsim as [ic t1 t2 Hstep
                       | ic t1 m1 t2 Ht1 _ IH
                       | ic t1 t2 m2 Ht2 _ IH
                       | ic env1 t1 x v k1 t2 He1 Ht1 Hlk _ IH
                       | ic env2 t1 t2 x v k2 He2 Ht2 Hlk _ IH
                       | ic ic' t1 x v k1 t2 Hw1 Ht1 _ IH
                       | ic ic' t1 t2 x v k2 Hw2 Ht2 _ IH
                       | ic t1 k v k1 t2 Ht1 Hlk _ IH
                       | stk ce1 e1 e2 t1 varg k1 t2 Ht1 _ IH
                       | stk e1 e2 t1 k1 t2 Hfr
                       | stk ce1 e2 bs t1 k1 t2 Hfr
                       | stk ce1 e1 e2 t1 k1 t2 Hfr
                       | stk ce1 e2 t1 k1 t2 Hfr
                       | stk e1 e2 t1 X ce body1 k1 t2 Hfr];
      try discriminate Hfr.
    - apply GIS_Step; unfold gis_step_body in *.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1]; [exact Hstep | exact Hstep |].
      destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
      destruct (observe t2) as [r2 | m2 | X2 e2 k2]; [exact Hvis | exact Hvis |].
      destruct Hvis as [Hsync | Hls]; [left; exact Hsync | right].
      destruct ic as [stk env1 env2 | |]; try contradiction.
      destruct Hls as [Hloc | [Hfr _]]; [left; exact Hloc | discriminate Hfr].
    - eapply GIS_TauL; eassumption.
    - eapply GIS_TauR; eassumption.
    - eapply GIS_ReadL; eassumption.
    - eapply GIS_ReadR; eassumption.
    - eapply GIS_WriteL; eassumption.
    - eapply GIS_WriteR; eassumption.
    - eapply GIS_GReadL; eassumption.
    - eapply GIS_ZeroStoreL; eassumption.
  Qed.

  (** ** 8C. Concrete [CFGtop] and [MCFGtop] Instances, [denote_ocfg_map] & [run_exc] *)

  Definition callee_opt_call (p_callee : @ptr (@PROV PaV) (@PTR PaV)) (callee_fn : @function_denotation PaV)
    : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X) :=
    fun X e =>
      match e return option (@CFGtop PaV X) with
      | inl1 ce =>
          match ce in CallE Y return option (@CFGtop PaV Y) with
          | Call _ cc fv args =>
              match fv with
              | DVALUE_Base (DVALUE_Pointer p) =>
                  if Z.eqb (ptr_to_int p) (ptr_to_int p_callee)
                  then Some (callee_fn cc args)
                  else None
              | _ => None
              end
          end
      | inr1 _ => None
      end.

  Definition no_opt_call {E : Type -> Type} : forall X, E X -> option (itree E X) :=
    fun _ _ => None.

  Definition cfg_inline_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (allow_frame : bool)
    {R1 R2 : Type} (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (u1 : @CFGtop PaV R1) (u2 : @CFGtop PaV R2) : Prop :=
    gen_inline_sim (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
      (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
      opt_call1 g0 allow_frame RR ic u1 u2.

  Definition mcfg_inline_sim
    (g0 : global_env) (allow_frame : bool)
    {R1 R2 : Type} (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (u1 : @MCFGtop PaV R1) (u2 : @MCFGtop PaV R2) : Prop :=
    gen_inline_sim (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
      (@inl_mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
      (@no_opt_call (@MCFGEtop PaV)) g0 allow_frame RR ic u1 u2.

  Lemma denote_ocfg_map_unfold_eq (bks : ocfg dtyp) (va : option (@ptr (@PROV PaV) (@PTR PaV)))
    (bid_from bid_src : block_id) :
    denote_ocfg_map (ocfg_map bks) va (bid_from, bid_src) ≅
    match find_block bks bid_src with
    | None => Ret (inl (bid_from, bid_src))
    | Some bk =>
        ITree.bind (denote_block bk bid_from va)
          (fun bd =>
             match bd with
             | inr dv => Ret (inr dv)
             | inl bid_target =>
                 Tau (denote_ocfg_map (ocfg_map bks) va (bid_src, bid_target))
             end)
    end.
  Proof using.
    unfold denote_ocfg_map; rewrite unfold_iter; cbn [fst snd].
    rewrite ocfg_map_find_block.
    destruct (find_block bks bid_src) as [bk |];
      cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    - rewrite Eqit.bind_bind.
      eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [bid_target | dv] _ <-; rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma run_exc_ret_eq {A : Type} (u : @CFGtop PaV A) (a : A)
    (Hou : observe u = RetF a) :
    run_exc u ≅ Ret (inr a).
  Proof using.
    rewrite unfold_run_exc_obs, Hou; reflexivity.
  Qed.

  Lemma run_exc_tau_eq {A : Type} (u m : @CFGtop PaV A)
    (Hou : observe u = TauF m) :
    run_exc u ≅ Tau (run_exc m).
  Proof using.
    rewrite unfold_run_exc_obs, Hou; reflexivity.
  Qed.

  Lemma run_exc_vis_some_eq {A X : Type} (u : @CFGtop PaV A)
    (e : @CFGEtop PaV X) (k : X -> @CFGtop PaV A) (ex : @exc PaV)
    (Hou : observe u = VisF e k)
    (Hex : exc_of_event e = Some ex) :
    run_exc u ≅ Ret (inl ex).
  Proof using.
    rewrite unfold_run_exc_obs, Hou, Hex; reflexivity.
  Qed.

  Lemma run_exc_vis_none_eq {A X : Type} (u : @CFGtop PaV A)
    (e : @CFGEtop PaV X) (k : X -> @CFGtop PaV A)
    (Hou : observe u = VisF e k)
    (Hex : exc_of_event e = None) :
    run_exc u ≅ Vis e (fun y => Tau (run_exc (k y))).
  Proof using.
    rewrite unfold_run_exc_obs, Hou, Hex; reflexivity.
  Qed.

  Lemma run_exc_proper {A : Type} (u1 u2 : @CFGtop PaV A) :
    u1 ≅ u2 -> run_exc u1 ≅ run_exc u2.
  Proof using.
    revert u1 u2; ginit; gcofix CIH; intros u1 u2 Hu.
    punfold Hu; red in Hu.
    remember (observe u1) as ot1 eqn:Hou1;
    remember (observe u2) as ot2 eqn:Hou2.
    destruct Hu as [r1 r2 <- | m1 m2 REL | X e k1 k2 REL | ? ? Hchk _ | ? ? Hchk _];
      try inversion Hchk; symmetry in Hou1, Hou2; pclearbot.
    - rewrite (run_exc_ret_eq _ _ Hou1), (run_exc_ret_eq _ _ Hou2).
      gstep; constructor; reflexivity.
    - rewrite (run_exc_tau_eq _ _ Hou1), (run_exc_tau_eq _ _ Hou2).
      gstep; constructor; gfinal; left; apply CIH, REL.
    - destruct (exc_of_event e) as [ex |] eqn:Eex.
      + rewrite (run_exc_vis_some_eq _ _ _ _ Hou1 Eex), (run_exc_vis_some_eq _ _ _ _ Hou2 Eex).
        gstep; constructor; reflexivity.
      + rewrite (run_exc_vis_none_eq _ _ _ Hou1 Eex), (run_exc_vis_none_eq _ _ _ Hou2 Eex).
        gstep; constructor; intros y;
          gstep; constructor; gfinal; left; apply CIH, REL.
  Qed.

  Lemma run_exc_bind_trigger_none_eq {A X : Type}
    (e : @CFGEtop PaV X) (k : X -> @CFGtop PaV A)
    (Hex : exc_of_event e = None) :
    run_exc (ITree.bind (ITree.trigger e) k) ≅
    ITree.bind (ITree.trigger e) (fun y => Tau (run_exc (k y))).
  Proof using.
    assert (Hou : observe (ITree.bind (ITree.trigger e) k) = VisF e (fun y => ITree.bind (Ret y) k)).
    { unfold ITree.trigger; rewrite observe_bind; cbn [observe]; reflexivity. }
    rewrite (run_exc_vis_none_eq _ e (fun y => ITree.bind (Ret y) k) Hou Hex), <- bind_trigger.
    apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros y _ <-].
    apply eqit_Tau, run_exc_proper, Eqit.bind_ret_l.
  Qed.

  Lemma itree_tau_star_run_exc {A : Type} (u u' : @CFGtop PaV A) :
    itree_tau_star u u' ->
    itree_tau_star (run_exc u) (run_exc u').
  Proof using.
    intros Hs; induction Hs as [a | a b c Hab _ IH | m b _ IH].
    - apply ITS_Refl.
    - eapply ITS_Eq; [apply run_exc_proper, Hab | exact IH].
    - eapply ITS_Eq; [apply (run_exc_tau_eq (Tau m) m Logic.eq_refl) | apply ITS_Tau, IH].
  Qed.

  (** Lift an [allow_frame = false] simulation in [IC_Inlined] through [run_exc]
      on BOTH sides (with an outer bind [K1] on the left for the callee epilogue). *)
  Lemma cfg_inline_sim_bind_run_exc_lr
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool)
    {A1 A2 B1 B2 C1 : Type}
    (RA : inline_ctx -> A1 -> A2 -> Prop)
    (RC : inline_ctx -> C1 -> @exc PaV + B2 -> Prop)
    (k1 : A1 -> @CFGtop PaV B1)
    (K1 : @exc PaV + B1 -> @CFGtop PaV C1)
    (k2 : A2 -> @CFGtop PaV B2)
    (Hk : forall ic' x1 x2,
            is_ic_inlined ic' = true ->
            RA ic' x1 x2 ->
            cfg_inline_sim opt_call1 g0 bf RC ic'
              (ITree.bind (run_exc (k1 x1)) K1)
              (run_exc (k2 x2))) :
    forall ic (a1 : @CFGtop PaV A1) (a2 : @CFGtop PaV A2),
      is_ic_inlined ic = true ->
      cfg_inline_sim opt_call1 g0 false RA ic a1 a2 ->
      cfg_inline_sim opt_call1 g0 bf RC ic
        (ITree.bind (run_exc (ITree.bind a1 k1)) K1)
        (run_exc (ITree.bind a2 k2)).
  Proof using.
    pcofix CIH.
    intros ic a1 a2 Hic Hsim; pstep; punfold Hsim.
    set (r_goal :=
      upaco3
        (gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
           (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
           opt_call1 g0 bf RC) r).
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
        pose proof (Hk ic x1 x2 Hic Hstep) as Hkx; punfold Hkx.
        eapply gen_inline_sim__obs_eq; [symmetry; exact Eb1 | symmetry; exact Eb2 |].
        eapply gen_inline_sim__mon; [exact Hkx |].
        intros ic0 u1 u2 [Hu | []]; left; eapply paco3_mon; [exact Hu | intros ? ? ? []].
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
        right; apply (CIH ic m1 m2 Hic Hm).
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
             ++ right; apply (CIH _ m1 m2 Hic Hm).
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

  Definition ic_synced_stk (stk : env_stack) (ic : inline_ctx) : Prop :=
    exists e1 e2, ic = IC_Synced stk e1 e2.

  (** Lift an [allow_frame = false] simulation in [IC_Synced stk] through [run_exc]
      on BOTH sides (handling synchronous [LLVMExc] unwinds as well as normal returns). *)
  Lemma cfg_inline_sim_bind_run_exc_both
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (stk : env_stack)
    {A1 A2 B1 B2 : Type}
    (RA : inline_ctx -> A1 -> A2 -> Prop)
    (RB : inline_ctx -> @exc PaV + B1 -> @exc PaV + B2 -> Prop)
    (k1 : A1 -> @CFGtop PaV B1)
    (k2 : A2 -> @CFGtop PaV B2)
    (Hexc : forall e1 e2 ex,
              RB (IC_Synced stk e1 e2) (inl ex) (inl ex))
    (Hk : forall ic' x1 x2,
            ic_synced_stk stk ic' ->
            RA ic' x1 x2 ->
            cfg_inline_sim opt_call1 g0 bf RB ic'
              (run_exc (k1 x1))
              (run_exc (k2 x2))) :
    forall ic (a1 : @CFGtop PaV A1) (a2 : @CFGtop PaV A2),
      ic_synced_stk stk ic ->
      cfg_inline_sim opt_call1 g0 false RA ic a1 a2 ->
      cfg_inline_sim opt_call1 g0 bf RB ic
        (run_exc (ITree.bind a1 k1))
        (run_exc (ITree.bind a2 k2)).
  Proof using.
    pcofix CIH.
    intros ic a1 a2 Hic Hsim; pstep; punfold Hsim.
    assert (Hlift_sync_cont :
      forall ic0 u1 u2,
        ic_synced_stk stk ic0 ->
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
                (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
                opt_call1 g0 false RA) bot3)
          ic0 u1 u2 ->
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
                (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
                opt_call1 g0 bf RB) r)
          ic0
          (Tau (run_exc (ITree.bind u1 k1)))
          (Tau (run_exc (ITree.bind u2 k2)))).
    { intros ic0 u1 u2 Hic0 (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
      exists (run_exc (ITree.bind m1 k1)), (run_exc (ITree.bind m2 k2)).
      split; [apply ITS_Tau, itree_tau_star_run_exc, itree_tau_star_bind, Hs1 |].
      split; [apply ITS_Tau, itree_tau_star_run_exc, itree_tau_star_bind, Hs2 |].
      right; apply (CIH ic0 m1 m2 Hic0 Hm). }
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
        pose proof (Hk ic x1 x2 Hic Hstep) as Hkx; punfold Hkx.
        eapply gen_inline_sim__obs_eq; [symmetry; exact Eb1 | symmetry; exact Eb2 |].
        eapply gen_inline_sim__mon; [exact Hkx |].
        intros ic0 u1 u2 [Hu | []]; left; eapply paco3_mon; [exact Hu | intros ? ? ? []].
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
        right; apply (CIH ic m1 m2 Hic Hm).
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
          destruct Hic as (env1 & env2 & ->).
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
                apply (Hlift_sync_cont _ _ _ (ex_intro _ env1 (ex_intro _ env2 Logic.eq_refl)) (HA y1 y2 Hy Hp)).
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
                         (ex_intro _ (Maps.add x1 v1 env1) (ex_intro _ (Maps.add x2 v2 env2) Logic.eq_refl)) Hr).
             ++ destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                intros v Hv.
                apply (Hlift_sync_cont _ _ _ (ex_intro _ env1 (ex_intro _ env2 Logic.eq_refl)) (Hrd v Hv)).
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
      { destruct Hic as (e1_0 & e2_0 & ->); cbn in Hw1; injection Hw1 as <-.
        exists (Maps.add x v e1_0), e2_0; reflexivity. }
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
      { destruct Hic as (e1_0 & e2_0 & ->); cbn in Hw2; injection Hw2 as <-.
        exists e1_0, (Maps.add x v e2_0); reflexivity. }
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
    - destruct Hic as (? & ? & Hbad); discriminate Hbad.
  Qed.

  (** ** 8D. Lifting Across [mrec], [interp_intrinsics], and [interp_state] ([to_model]) *)

  Definition is_ic_active (ic : inline_ctx) : bool :=
    match ic with
    | IC_MemPushed _ _ _ => false
    | _ => true
    end.

  Lemma gis_cont_to_sim
    {E : Type -> Type}
    `{@LocalE PaV -< E} `{@StackE PaV -< E} `{@GlobalE PaV -< E} `{@MemoryE PaV -< E}
    (is_ub : forall X, E X -> bool)
    (is_sync : inline_ctx -> forall X, E X -> bool)
    (EqE : prerel E E) (EqA : postrel E E)
    (ev_post : forall X, E X -> X -> Prop)
    (as_loc : forall X, E X -> option (@LocalE PaV X))
    (as_stk : forall X, E X -> option (@StackE PaV X))
    (opt_call1 : forall X, E X -> option (itree E X))
    (g0 : global_env) (bf : bool)
    {R1 R2 : Type} (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (u1 : itree E R1) (u2 : itree E R2) :
    gis_cont
      (upaco3
         (gen_inline_sim_ is_ub is_sync EqE EqA ev_post as_loc as_stk opt_call1 g0 bf RR)
         bot3)
      ic u1 u2 ->
    gen_inline_sim is_ub is_sync EqE EqA ev_post as_loc as_stk opt_call1 g0 bf RR ic u1 u2.
  Proof using.
    intros (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
    eapply gen_inline_sim_tau_star_l; [exact Hs1 |].
    eapply gen_inline_sim_tau_star_r; [exact Hs2 | exact Hm].
  Qed.

  Lemma cfg_inline_sim_run_exc_both
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) (bf : bool) (stk : env_stack)
    {A1 A2 : Type}
    (RA : inline_ctx -> A1 -> A2 -> Prop)
    (RB : inline_ctx -> @exc PaV + A1 -> @exc PaV + A2 -> Prop)
    (Hexc : forall e1 e2 ex,
              RB (IC_Synced stk e1 e2) (inl ex) (inl ex))
    (Hret : forall ic' x1 x2,
              ic_synced_stk stk ic' ->
              RA ic' x1 x2 ->
              RB ic' (inr x1) (inr x2))
    (ic : inline_ctx) (a1 : @CFGtop PaV A1) (a2 : @CFGtop PaV A2)
    (Hic : ic_synced_stk stk ic)
    (Hsim : cfg_inline_sim opt_call1 g0 false RA ic a1 a2) :
    cfg_inline_sim opt_call1 g0 bf RB ic (run_exc a1) (run_exc a2).
  Proof using.
    eapply gen_inline_sim_obs_eq;
      [apply run_exc_proper, Eqit.bind_ret_r
      | apply run_exc_proper, Eqit.bind_ret_r |].
    eapply (cfg_inline_sim_bind_run_exc_both opt_call1 g0 bf stk RA RB
              (fun x => Ret x) (fun x => Ret x) Hexc);
      [| exact Hic | exact Hsim].
    intros ic' x1 x2 Hic' Hra.
    eapply gen_inline_sim_obs_eq;
      [symmetry; apply (run_exc_ret_eq (Ret x1) x1 Logic.eq_refl)
      | symmetry; apply (run_exc_ret_eq (Ret x2) x2 Logic.eq_refl) |].
    apply gen_inline_sim_ret, (Hret ic' x1 x2 Hic' Hra).
  Qed.

  Lemma mcfg_inline_sim_raise {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (msg1 msg2 : string)
    (Hact : is_ic_active ic = true) :
    mcfg_inline_sim g0 bf RR ic (raise msg1) (raise msg2).
  Proof using.
    unfold raise, trigger_cast, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind; cbn [observe].
    right; left.
    split; [destruct ic; try discriminate Hact; reflexivity |].
    split; [exact I | intros [] [] _ _].
  Qed.

  Lemma mcfg_inline_sim_raiseUB {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (msg1 : string) (t2 : @MCFGtop PaV R2) :
    mcfg_inline_sim g0 bf RR ic (raiseUB msg1) t2.
  Proof using.
    unfold raiseUB, trigger_cast, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind; cbn [observe].
    left; reflexivity.
  Qed.

  Lemma mcfg_inline_sim_raiseOOM {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (msg1 : string) (t2 : @MCFGtop PaV R2) :
    mcfg_inline_sim g0 bf RR ic (raiseOOM msg1) t2.
  Proof using.
    unfold raiseOOM, trigger_cast, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind; cbn [observe].
    left; reflexivity.
  Qed.

  Lemma mcfg_inline_sim_EOU {A : Type}
    (g0 : global_env) (bf : bool)
    (ic : inline_ctx) (m : EOU A)
    (Hact : is_ic_active ic = true) :
    mcfg_inline_sim g0 bf (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
      ic (EOU_to_itree m) (EOU_to_itree m).
  Proof using.
    destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - apply mcfg_inline_sim_raise, Hact.
    - apply mcfg_inline_sim_raiseOOM.
    - apply mcfg_inline_sim_raiseUB.
    - apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma cfg_inline_sim_raise
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (msg1 msg2 : string)
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf RR ic (raise msg1) (raise msg2).
  Proof using.
    unfold raise, trigger_cast, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind; cbn [observe].
    right; left.
    split; [destruct ic; try discriminate Hact; reflexivity |].
    split; [exact I | intros [] [] _ _].
  Qed.

  Lemma cfg_inline_sim_raiseUB
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (msg1 : string) (t2 : @CFGtop PaV R2) :
    cfg_inline_sim opt_call1 g0 bf RR ic (raiseUB msg1) t2.
  Proof using.
    unfold raiseUB, trigger_cast, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind; cbn [observe].
    left; reflexivity.
  Qed.

  Lemma cfg_inline_sim_raiseOOM
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    {R1 R2 : Type}
    (g0 : global_env) (bf : bool)
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (msg1 : string) (t2 : @CFGtop PaV R2) :
    cfg_inline_sim opt_call1 g0 bf RR ic (raiseOOM msg1) t2.
  Proof using.
    unfold raiseOOM, trigger_cast, ITree.trigger.
    pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind; cbn [observe].
    left; reflexivity.
  Qed.

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

  Lemma cfg_inline_sim_EOU
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    {A : Type}
    (g0 : global_env) (bf : bool)
    (ic : inline_ctx) (m : EOU A)
    (Hact : is_ic_active ic = true) :
    cfg_inline_sim opt_call1 g0 bf (fun ic' r1 r2 => ic' = ic /\ r1 = r2)
      ic (EOU_to_itree m) (EOU_to_itree m).
  Proof using.
    destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - apply cfg_inline_sim_raise, Hact.
    - apply cfg_inline_sim_raiseOOM.
    - apply cfg_inline_sim_raiseUB.
    - apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  Lemma mcfg_inline_sim_trigger_refl {X : Type}
    (g0 : global_env) (bf : bool) (ic : inline_ctx) (e : @MCFGEtop PaV X)
    (Hsync : inl_sync_mcfg ic e = true) :
    mcfg_inline_sim g0 bf (fun ic' a1 a2 => ic' = ic /\ a1 = a2)
      ic (ITree.trigger e) (ITree.trigger e).
  Proof using.
    eapply gen_inline_sim_weaken;
      [| apply gen_inline_sim_trigger_sync; [exact Hsync | apply EqE_MCFG_refl]].
    intros ic' a1 a2 (-> & Ha & _); apply EqA_MCFG_eq in Ha; split; [reflexivity | exact Ha].
  Qed.

  Lemma cfg_inline_sim_trigger_refl
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    {X : Type}
    (g0 : global_env) (bf : bool) (ic : inline_ctx) (e : @CFGEtop PaV X)
    (Hsync : inl_sync_cfg ic e = true) :
    cfg_inline_sim opt_call1 g0 bf (fun ic' a1 a2 => ic' = ic /\ a1 = a2)
      ic (ITree.trigger e) (ITree.trigger e).
  Proof using.
    eapply gen_inline_sim_weaken;
      [| apply gen_inline_sim_trigger_sync; [exact Hsync | apply EqE_CFG_refl]].
    intros ic' a1 a2 (-> & Ha & _); apply EqA_CFG_eq in Ha; split; [reflexivity | exact Ha].
  Qed.

  Lemma inl_withCall_proper {R : Type} (u1 u2 : @MCFGtop PaV R) :
    u1 ≅ u2 ->
    @withCall PaV R u1 ≅ @withCall PaV R u2.
  Proof using.
    unfold withCall; intros H; rewrite H; reflexivity.
  Qed.

  Lemma itree_tau_star_withCall {R : Type} (u u' : @MCFGtop PaV R) :
    itree_tau_star u u' ->
    itree_tau_star (@withCall PaV R u) (@withCall PaV R u').
  Proof using.
    intros Hs; induction Hs as [a | a b c Hab _ IH | m b _ IH].
    - apply ITS_Refl.
    - eapply ITS_Eq; [apply inl_withCall_proper, Hab | exact IH].
    - eapply ITS_Eq; [unfold withCall; apply translate_tau | apply ITS_Tau, IH].
  Qed.

  Lemma inl_withCall_bind_trigger {X R : Type}
    (e : @MCFGEtop PaV X) (k : X -> @MCFGtop PaV R) :
    @withCall PaV R (ITree.bind (ITree.trigger e) k) ≅
    ITree.bind (ITree.trigger (subevent _ e)) (fun x => @withCall PaV R (k x)).
  Proof using.
    rewrite inl_withCall_bind.
    apply eq_itree_clo_bind with (UU := Logic.eq); [| intros x _ <-; reflexivity].
    unfold withCall; try unfold trigger; unfold ITree.trigger.
    rewrite translate_vis.
    destruct_sum1 e; norm_subevent;
      apply eqit_Vis; intros x; apply translate_ret.
  Qed.

  Lemma mcfg_to_cfg_withCall_sim
    (opt_call1 : forall X, @CFGEtop PaV X -> option (@CFGtop PaV X))
    (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop) :
    forall ic (u1 : @MCFGtop PaV R1) (u2 : @MCFGtop PaV R2),
      mcfg_inline_sim g0 false RR ic u1 u2 ->
      cfg_inline_sim opt_call1 g0 false RR ic (withCall u1) (withCall u2).
  Proof using.
    pcofix CIH.
    intros ic u1 u2 Hsim; pstep; punfold Hsim.
    assert (Hlift_cont :
      forall ic0 w1 w2,
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
                (@inl_mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
                (@no_opt_call (@MCFGEtop PaV)) g0 false RR) bot3)
          ic0 w1 w2 ->
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
                (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
                opt_call1 g0 false RR) r)
          ic0 (withCall w1) (withCall w2)).
    { intros ic0 w1 w2 (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
      exists (withCall m1), (withCall m2).
      split; [apply itree_tau_star_withCall, Hs1 |].
      split; [apply itree_tau_star_withCall, Hs2 |].
      right; apply CIH, Hm. }
    induction Hsim as [ic u1 u2 Hstep
                       | ic u1 m1 u2 Hu1 _ IH
                       | ic u1 u2 m2 Hu2 _ IH
                       | ic env1 u1 x v k1 u2 He1 Hu1 Hlk _ IH
                       | ic env2 u1 u2 x v k2 He2 Hu2 Hlk _ IH
                       | ic ic' u1 x v k1 u2 Hw1 Hu1 _ IH
                       | ic ic' u1 u2 x v k2 Hw2 Hu2 _ IH
                       | ic u1 k v k1 u2 Hu1 Hlk _ IH
                       | stk ce1 e1 e2 u1 varg k1 u2 Hu1 _ IH
                       | stk e1 e2 u1 k1 u2 Hfr
                       | stk ce1 e2 bs u1 k1 u2 Hfr
                       | stk ce1 e1 e2 u1 k1 u2 Hfr
                       | stk ce1 e2 u1 k1 u2 Hfr
                       | stk e1 e2 u1 X ce body1 k1 u2 Hfr];
      try discriminate Hfr.
    - apply GIS_Step; unfold gis_step_body in *.
      unfold withCall; rewrite !observe_translate.
      destruct (observe u1) as [r1 | m1 | X1 e1 k1].
      + destruct (observe u2); exact Hstep.
      + destruct (observe u2); try contradiction; apply Hlift_cont, Hstep.
      + cbn [observe]; norm_subevent.
        destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct (observe u2) as [r2 | m2 | X2 e2 k2]; try contradiction.
        cbn [observe]; norm_subevent.
        destruct Hvis as [(Hsync & HE & HA) | Hls].
        * left; split; [exact Hsync | split; [exact HE |]].
          intros a1 a2 Ha Hp; apply Hlift_cont, (HA a1 a2 Ha Hp).
        * right; destruct ic as [stk env1 env2 | |]; try contradiction.
          destruct Hls as [Hloc | [Hfr_s _]]; [| discriminate Hfr_s].
          left; cbn [as_local_cfg].
          destruct (as_local_mcfg e1) as [le1 |], (as_local_mcfg e2) as [le2 |]; try contradiction.
          destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
          -- destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv | apply Hlift_cont, Hr]].
          -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
             intros v Hv; apply Hlift_cont, Hrd, Hv.
    - eapply GIS_TauL; [unfold withCall; rewrite observe_translate, Hu1; reflexivity | exact IH].
    - eapply GIS_TauR; [unfold withCall; rewrite observe_translate, Hu2; reflexivity | exact IH].
    - eapply GIS_ReadL;
        [exact He1
        | rewrite (inl_withCall_proper _ _ Hu1), inl_withCall_bind_trigger;
          try unfold trigger; norm_subevent; reflexivity
        | exact Hlk | exact IH].
    - eapply GIS_ReadR;
        [exact He2
        | rewrite (inl_withCall_proper _ _ Hu2), inl_withCall_bind_trigger;
          try unfold trigger; norm_subevent; reflexivity
        | exact Hlk | exact IH].
    - eapply GIS_WriteL;
        [exact Hw1
        | rewrite (inl_withCall_proper _ _ Hu1), inl_withCall_bind_trigger;
          try unfold trigger; norm_subevent; reflexivity
        | exact IH].
    - eapply GIS_WriteR;
        [exact Hw2
        | rewrite (inl_withCall_proper _ _ Hu2), inl_withCall_bind_trigger;
          try unfold trigger; norm_subevent; reflexivity
        | exact IH].
    - eapply GIS_GReadL;
        [rewrite (inl_withCall_proper _ _ Hu1), inl_withCall_bind_trigger;
         try unfold trigger; norm_subevent; reflexivity
        | exact Hlk | exact IH].
    - eapply GIS_ZeroStoreL;
        [rewrite (inl_withCall_proper _ _ Hu1), inl_withCall_bind_trigger;
         try unfold trigger; norm_subevent; reflexivity
        | exact IH].
  Qed.

  Lemma inl_interp_mrec_proper (ctx : @CallE PaV ~> @CFGtop PaV)
    {R : Type} (u1 u2 : @CFGtop PaV R) :
    u1 ≅ u2 ->
    interp_mrec ctx u1 ≅ interp_mrec ctx u2.
  Proof using.
    unfold CFGtop, CFGEtop, MCFGtop, MCFGEtop in *.
    revert u1 u2; ginit; gcofix CIH; intros u1 u2 Hu.
    rewrite (unfold_interp_mrec ctx R u1), (unfold_interp_mrec ctx R u2).
    punfold Hu; red in Hu.
    remember (observe u1) as ot1 eqn:Hou1;
    remember (observe u2) as ot2 eqn:Hou2.
    destruct Hu as [r1 r2 <- | m1 m2 REL | X e k1 k2 REL | ? ? Hchk _ | ? ? Hchk _];
      try inversion Hchk; symmetry in Hou1, Hou2;
      try rewrite Hou1; try rewrite Hou2; pclearbot;
      cbn [_interp_mrec case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
    - gstep; constructor; reflexivity.
    - gstep; constructor; gfinal; left; apply CIH, REL.
    - destruct e as [ce | me].
      + gstep; constructor; gfinal; left; apply CIH.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
        intros x _ <-; apply REL.
      + gstep; constructor; intros x;
          gstep; constructor; gfinal; left; apply CIH, REL.
  Qed.

  Lemma itree_tau_star_interp_mrec (ctx : @CallE PaV ~> @CFGtop PaV)
    {R : Type} (u u' : @CFGtop PaV R) :
    itree_tau_star u u' ->
    itree_tau_star (interp_mrec ctx u) (interp_mrec ctx u').
  Proof using.
    intros Hs; induction Hs as [a | a b c Hab _ IH | m b _ IH].
    - apply ITS_Refl.
    - eapply ITS_Eq; [apply inl_interp_mrec_proper, Hab | exact IH].
    - eapply ITS_Eq; [rewrite unfold_interp_mrec; reflexivity | apply ITS_Tau, IH].
  Qed.

  Lemma interp_mrec_bind_subevent (ctx : @CallE PaV ~> @CFGtop PaV)
    {X R : Type} (me : @MCFGEtop PaV X) (k : X -> @CFGtop PaV R) :
    interp_mrec ctx (ITree.bind (ITree.trigger (inr1 me)) k) ≅
    ITree.bind (ITree.trigger me) (fun y => Tau (interp_mrec ctx (k y))).
  Proof using.
    rewrite bind_trigger, unfold_interp_mrec.
    cbn [observe _interp_mrec case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
    rewrite bind_trigger; reflexivity.
  Qed.

  Local Lemma cfg_to_mcfg_inline_sim_call
    (p_callee : @ptr (@PROV PaV) (@PTR PaV))
    (callee_fn : @function_denotation PaV)
    (ctx1 ctx2 : IntMap (@function_denotation PaV))
    (g0 : global_env)
    (Hctx : forall k,
              option_rel
                (fun f1 f2 =>
                   forall stk e1 e2 cc args,
                     cfg_inline_sim (callee_opt_call p_callee callee_fn) g0 true
                       (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
                       (IC_Synced stk e1 e2) (f1 cc args) (f2 cc args))
                (lookup k ctx1) (lookup k ctx2)) :
    forall stk env1 env2 dt1 cc1 fv1 fas1,
      cfg_inline_sim (callee_opt_call p_callee callee_fn) g0 true
        (fun ic' r1 r2 => ic' = IC_Synced stk env1 env2 /\ r1 = r2)
        (IC_Synced stk env1 env2)
        (inl_mrec_ctx ctx1 _ (Call dt1 cc1 fv1 fas1))
        (inl_mrec_ctx ctx2 _ (Call dt1 cc1 fv1 fas1)).
  Proof using.
    intros stk env1 env2 dt1 cc1 fv1 fas1.
    set (opt_c := callee_opt_call p_callee callee_fn).
    unfold inl_mrec_ctx.
    eapply gen_inline_sim_bind;
      [apply cfg_inline_sim_EOU; reflexivity | intros ? [] _ [-> _]].
    assert (Hext :
      cfg_inline_sim opt_c g0 true
        (fun ic' r1 r2 => ic' = IC_Synced stk env1 env2 /\ r1 = r2)
        (IC_Synced stk env1 env2)
        (Functor.fmap (@inr (@exc PaV) _) (external_call dt1 fv1 fas1))
        (Functor.fmap (@inr (@exc PaV) _) (external_call dt1 fv1 fas1))).
    { cbn [Functor.fmap Functor_itree ITree.map]; unfold external_call, trigger_cast.
      eapply gen_inline_sim_bind.
      - apply cfg_inline_sim_trigger_refl; reflexivity.
      - intros ? rv1 rv2 [-> <-]; apply gen_inline_sim_ret; split; reflexivity. }
    unfold lookup_defn.
    destruct fv1 as [[p | | | | | | |] | |]; try exact Hext.
    pose proof (Hctx (ptr_to_int p)) as Hlk.
    destruct Hlk as [| f1 f2 Hf12].
    - exact Hext.
    - apply Hf12.
  Qed.

  Local Lemma cfg_to_mcfg_inline_sim_step
    (p_callee : @ptr (@PROV PaV) (@PTR PaV))
    (callee_fn : @function_denotation PaV)
    (ctx1 ctx2 : IntMap (@function_denotation PaV))
    (g0 : global_env)
    {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (r_mrec : inline_ctx -> @MCFGtop PaV R1 -> @MCFGtop PaV R2 -> Prop)
    (Hcall :
       forall stk env1 env2 dt1 cc1 fv1 fas1,
         cfg_inline_sim (callee_opt_call p_callee callee_fn) g0 true
           (fun ic' r1 r2 => ic' = IC_Synced stk env1 env2 /\ r1 = r2)
           (IC_Synced stk env1 env2)
           (inl_mrec_ctx ctx1 _ (Call dt1 cc1 fv1 fas1))
           (inl_mrec_ctx ctx2 _ (Call dt1 cc1 fv1 fas1)))
    (Hr_wrap :
       forall ic0 w1 w2,
         cfg_inline_sim (callee_opt_call p_callee callee_fn) g0 true RR ic0 w1 w2 ->
         r_mrec ic0 (interp_mrec (inl_mrec_ctx ctx1) w1) (interp_mrec (inl_mrec_ctx ctx2) w2))
    (ic : inline_ctx)
    (u1 : @CFGtop PaV R1) (u2 : @CFGtop PaV R2) :
    gis_step_body (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
      (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT) true
      RR
      (upaco3
         (gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
            (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
            (callee_opt_call p_callee callee_fn) g0 true RR) bot3)
      ic (observe u1) (observe u2) ->
    gen_inline_sim_ (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
      (@inl_mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
      (@no_opt_call (@MCFGEtop PaV)) g0 true RR r_mrec ic
      (interp_mrec (inl_mrec_ctx ctx1) u1)
      (interp_mrec (inl_mrec_ctx ctx2) u2).
  Proof using.
    intros Hstep.
    set (opt_c := callee_opt_call p_callee callee_fn) in *.
    assert (Hlift_tau_cont :
      forall ic0 w1 w2,
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_cfg) inl_sync_cfg EqE_CFG EqA_CFG
                (@inl_cfg_event_post IP IPT) (@as_local_cfg IP IPT) (@as_stack_cfg IP IPT)
                opt_c g0 true RR) bot3)
          ic0 w1 w2 ->
        gis_cont r_mrec ic0
          (Tau (interp_mrec (inl_mrec_ctx ctx1) w1))
          (Tau (interp_mrec (inl_mrec_ctx ctx2) w2))).
    { intros ic0 w1 w2 (m1 & m2 & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
      exists (interp_mrec (inl_mrec_ctx ctx1) m1),
             (interp_mrec (inl_mrec_ctx ctx2) m2).
      split; [apply ITS_Tau, itree_tau_star_interp_mrec, Hs1 |].
      split; [apply ITS_Tau, itree_tau_star_interp_mrec, Hs2 |].
      apply Hr_wrap, Hm. }
    eapply gen_inline_sim__obs_eq;
      [symmetry; apply unfold_interp_mrec
      | symmetry; apply unfold_interp_mrec |].
    unfold gis_step_body in Hstep.
    destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
    - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
      lazymatch goal with
      | |- context [_interp_mrec (inl_mrec_ctx ctx1) ?o] =>
          let H' := fresh "Ho1" in assert (H' : o = RetF r1) by exact Hou1; rewrite H'; clear H'
      end;
      lazymatch goal with
      | |- context [_interp_mrec (inl_mrec_ctx ctx2) ?o] =>
          let H' := fresh "Ho2" in assert (H' : o = RetF r2) by exact Hou2; rewrite H'; clear H'
      end;
      apply GIS_Step; cbn [gis_step_body observe _interp_mrec]; exact Hstep.
    - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
      destruct Hstep as (m1' & m2' & Hs1 & Hs2 & [Hm | Hbot]); [| inversion Hbot].
      lazymatch goal with
      | |- context [_interp_mrec (inl_mrec_ctx ctx1) ?o] =>
          let H' := fresh "Ho1" in assert (H' : o = TauF m1) by exact Hou1; rewrite H'; clear H'
      end;
      lazymatch goal with
      | |- context [_interp_mrec (inl_mrec_ctx ctx2) ?o] =>
          let H' := fresh "Ho2" in assert (H' : o = TauF m2) by exact Hou2; rewrite H'; clear H'
      end;
      apply GIS_Step; cbn [gis_step_body observe _interp_mrec].
      exists (interp_mrec (inl_mrec_ctx ctx1) m1'),
             (interp_mrec (inl_mrec_ctx ctx2) m2').
      split; [apply itree_tau_star_interp_mrec, Hs1 |].
      split; [apply itree_tau_star_interp_mrec, Hs2 |].
      apply Hr_wrap, Hm.
    - destruct Hstep as [Hub | Hvis].
      + destruct ev1 as [ce1 | me1]; [discriminate Hub |].
        lazymatch goal with
        | |- context [_interp_mrec (inl_mrec_ctx ctx1) ?o] =>
            let H' := fresh "Ho1" in assert (H' : o = VisF (inr1 me1) k1) by exact Hou1; rewrite H'; clear H'
        end;
        apply GIS_Step;
          cbn [gis_step_body observe _interp_mrec case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          left; exact Hub.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        destruct Hvis as [(Hsync & HE & HA) | Hls].
        * destruct ev1 as [ce1 | me1], ev2 as [ce2 | me2]; cbn in HE; try contradiction.
          -- destruct ic as [stk env1 env2 | |]; try discriminate Hsync.
             destruct ce1 as [dt1 cc1 fv1 args1], ce2 as [dt2 cc2 fv2 args2].
             destruct HE as (<- & <- & <- & <-).
             lazymatch goal with
             | |- context [_interp_mrec (inl_mrec_ctx ctx1) ?o] =>
                 let H' := fresh "Ho1" in
                 assert (H' : o = VisF (inl1 (Call dt1 cc1 fv1 args1)) k1) by exact Hou1;
                 rewrite H'; clear H'
             end;
             lazymatch goal with
             | |- context [_interp_mrec (inl_mrec_ctx ctx2) ?o] =>
                 let H' := fresh "Ho2" in
                 assert (H' : o = VisF (inl1 (Call dt1 cc1 fv1 args1)) k2) by exact Hou2;
                 rewrite H'; clear H'
             end;
             apply GIS_Step;
               cbn [gis_step_body observe _interp_mrec case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
             exists (interp_mrec (inl_mrec_ctx ctx1) (ITree.bind (inl_mrec_ctx ctx1 _ (Call dt1 cc1 fv1 args1)) k1)),
                    (interp_mrec (inl_mrec_ctx ctx2) (ITree.bind (inl_mrec_ctx ctx2 _ (Call dt1 cc1 fv1 args1)) k2)).
             split; [apply ITS_Refl | split; [apply ITS_Refl |]].
             apply Hr_wrap.
             eapply gen_inline_sim_bind; [apply Hcall |].
             intros ? rv1 rv2 [-> <-].
             assert (Heqa : EqA_CFG _ _ (inl1 (Call dt1 cc1 fv1 args1)) rv1 (inl1 (Call dt1 cc1 fv1 args1)) rv1).
             { cbn; reflexivity. }
             apply gis_cont_to_sim, (HA rv1 rv1 Heqa I).
          -- lazymatch goal with
             | |- context [_interp_mrec (inl_mrec_ctx ctx1) ?o1] =>
                 let H1 := fresh "Ho" in assert (H1 : o1 = VisF (inr1 me1) k1) by exact Hou1; rewrite H1; clear H1
             end;
             lazymatch goal with
             | |- context [_interp_mrec (inl_mrec_ctx ctx2) ?o2] =>
                 let H2 := fresh "Ho" in assert (H2 : o2 = VisF (inr1 me2) k2) by exact Hou2; rewrite H2; clear H2
             end;
             apply GIS_Step;
               cbn [gis_step_body observe _interp_mrec case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
               right; left.
             split; [exact Hsync | split; [exact HE |]].
             intros a1 a2 Ha Hp; apply Hlift_tau_cont, (HA a1 a2 Ha Hp).
        * destruct ic as [stk env1 env2 | |]; try contradiction.
          destruct Hls as [Hloc | [_ Hstk]].
          -- destruct ev1 as [| me1], ev2 as [| me2]; cbn [as_local_cfg] in Hloc;
               try contradiction; [destruct (as_local_mcfg me1); contradiction |].
             lazymatch goal with
             | |- context [_interp_mrec (inl_mrec_ctx ctx1) ?o1] =>
                 let H1 := fresh "Ho" in assert (H1 : o1 = VisF (inr1 me1) k1) by exact Hou1; rewrite H1; clear H1
             end;
             lazymatch goal with
             | |- context [_interp_mrec (inl_mrec_ctx ctx2) ?o2] =>
                 let H2 := fresh "Ho" in assert (H2 : o2 = VisF (inr1 me2) k2) by exact Hou2; rewrite H2; clear H2
             end;
             apply GIS_Step;
               cbn [gis_step_body observe _interp_mrec case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
               right; right; left.
             destruct (as_local_mcfg me1) as [le1 |] eqn:Ele1,
                      (as_local_mcfg me2) as [le2 |] eqn:Ele2;
               try (rewrite Ele1, Ele2 in Hloc; cbn iota in Hloc); try contradiction.
             destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2];
               cbn iota in Hloc; try contradiction.
             ++ destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv | apply Hlift_tau_cont, Hr]].
             ++ destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                intros v Hv; apply Hlift_tau_cont, Hrd, Hv.
          -- destruct ev1 as [| me1], ev2 as [| me2]; cbn [as_stack_cfg] in Hstk;
               try contradiction; [destruct (as_stack_mcfg me1); contradiction |].
             lazymatch goal with
             | |- context [_interp_mrec (inl_mrec_ctx ctx1) ?o1] =>
                 let H1 := fresh "Ho" in assert (H1 : o1 = VisF (inr1 me1) k1) by exact Hou1; rewrite H1; clear H1
             end;
             lazymatch goal with
             | |- context [_interp_mrec (inl_mrec_ctx ctx2) ?o2] =>
                 let H2 := fresh "Ho" in assert (H2 : o2 = VisF (inr1 me2) k2) by exact Hou2; rewrite H2; clear H2
             end;
             apply GIS_Step;
               cbn [gis_step_body observe _interp_mrec case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
               right; right; right.
             split; [reflexivity |].
             destruct (as_stack_mcfg me1) as [se1 |] eqn:Ese1,
                      (as_stack_mcfg me2) as [se2 |] eqn:Ese2;
               try (rewrite Ese1, Ese2 in Hstk; cbn iota in Hstk); try contradiction.
             destruct se1, se2; cbn iota in Hstk; try contradiction.
             ++ destruct Hstk as [Hbs Hr]; split; [exact Hbs | apply Hlift_tau_cont, Hr].
             ++ destruct stk as [| [p1 p2] rest]; [exact I | apply Hlift_tau_cont, Hstk].
  Qed.

  Lemma cfg_to_mcfg_inline_sim_mrec
    (p_callee : @ptr (@PROV PaV) (@PTR PaV))
    (callee_fn : @function_denotation PaV)
    (ctx1 ctx2 : IntMap (@function_denotation PaV))
    (g0 : global_env)
    (Hp_nn : (ptr_to_int p_callee >= 1)%Z)
    (Hlk_callee : lookup (ptr_to_int p_callee) ctx1 = Some callee_fn)
    (Hctx : forall k,
              option_rel
                (fun f1 f2 =>
                   forall stk e1 e2 cc args,
                     cfg_inline_sim (callee_opt_call p_callee callee_fn) g0 true
                       (fun ic' r1 r2 => ic' = IC_Synced stk e1 e2 /\ r1 = r2)
                       (IC_Synced stk e1 e2) (f1 cc args) (f2 cc args))
                (lookup k ctx1) (lookup k ctx2)) :
    forall {R1 R2 : Type}
      (RR : inline_ctx -> R1 -> R2 -> Prop)
      (ic : inline_ctx)
      (u1 : @CFGtop PaV R1)
      (u2 : @CFGtop PaV R2),
      cfg_inline_sim (callee_opt_call p_callee callee_fn) g0 true RR ic u1 u2 ->
      mcfg_inline_sim g0 true RR ic
        (interp_mrec (inl_mrec_ctx ctx1) u1)
        (interp_mrec (inl_mrec_ctx ctx2) u2).
  Proof using.
    intros R1 R2 RR.
    set (opt_c := callee_opt_call p_callee callee_fn).
    pose proof (cfg_to_mcfg_inline_sim_call p_callee callee_fn ctx1 ctx2 g0 Hctx) as Hcall.
    pcofix CIH.
    intros ic u1 u2 Hsim; pstep.
    set (r_mrec :=
      fun ic0 (a1 : @MCFGtop PaV R1) (a2 : @MCFGtop PaV R2) =>
        exists v1 v2,
          a1 = interp_mrec (inl_mrec_ctx ctx1) v1 /\
          a2 = interp_mrec (inl_mrec_ctx ctx2) v2 /\
          cfg_inline_sim opt_c g0 true RR ic0 v1 v2).
    eapply gen_inline_sim__mon with (r := r_mrec);
      [| intros ic0 a1 a2 (v1 & v2 & -> & -> & Hv); right; apply CIH, Hv].
    punfold Hsim; clear r CIH.
    induction Hsim as [ic u1 u2 Hstep
                       | ic u1 mu1 u2 Hu1 _ IH
                       | ic u1 u2 mu2 Hu2 _ IH
                       | ic env1 u1 x v k1 u2 He1 Hu1 Hlk _ IH
                       | ic env2 u1 u2 x v k2 He2 Hu2 Hlk _ IH
                       | ic ic' u1 x v k1 u2 Hw1 Hu1 _ IH
                       | ic ic' u1 u2 x v k2 Hw2 Hu2 _ IH
                       | ic u1 k v k1 u2 Hu1 Hlk _ IH
                       | stk ce1 e1 e2 u1 varg k1 u2 Hu1 _ IH
                       | stk e1 e2 u1 k1 u2 Hfr Hu1 _ IH
                       | stk ce1 e2 bs u1 k1 u2 Hfr Hu1 _ IH
                       | stk ce1 e1 e2 u1 k1 u2 Hfr Hu1 _ IH
                       | stk ce1 e2 u1 k1 u2 Hfr Hu1 _ IH
                       | stk e1 e2 u1 X ce body1 k1 u2 Hfr Hu1 Hopt _ IH].
    - eapply cfg_to_mcfg_inline_sim_step; [exact Hcall | | exact Hstep].
      intros ic0 w1 w2 Hw; exists w1, w2; split; [reflexivity | split; [reflexivity | exact Hw]].
    - eapply gen_inline_sim__obs_eq;
        [symmetry; rewrite unfold_interp_mrec;
         lazymatch goal with
         | |- context [_interp_mrec (inl_mrec_ctx ctx1) ?o] =>
             lazymatch type of Hu1 with _ = ?rhs =>
               let H := fresh "Ho" in assert (H : o = rhs) by exact Hu1; rewrite H; clear H
             end
         end; reflexivity
        | reflexivity |].
      eapply GIS_TauL; [reflexivity | exact IH].
    - eapply gen_inline_sim__obs_eq;
        [reflexivity
        | symmetry; rewrite unfold_interp_mrec;
          lazymatch goal with
          | |- context [_interp_mrec (inl_mrec_ctx ctx2) ?o] =>
              lazymatch type of Hu2 with _ = ?rhs =>
                let H := fresh "Ho" in assert (H : o = rhs) by exact Hu2; rewrite H; clear H
              end
          end; reflexivity |].
      eapply GIS_TauR; [reflexivity | exact IH].
    - eapply GIS_ReadL;
        [exact He1
        | rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | exact Hlk
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_ReadR;
        [exact He2
        | rewrite (inl_interp_mrec_proper _ _ _ Hu2); apply interp_mrec_bind_subevent
        | exact Hlk
        | eapply GIS_TauR; [reflexivity | exact IH]].
    - eapply GIS_WriteL;
        [exact Hw1
        | rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_WriteR;
        [exact Hw2
        | rewrite (inl_interp_mrec_proper _ _ _ Hu2); apply interp_mrec_bind_subevent
        | eapply GIS_TauR; [reflexivity | exact IH]].
    - eapply GIS_GReadL;
        [rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | exact Hlk
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_ZeroStoreL;
        [rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_MemPushL;
        [exact Hfr
        | rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_StackPushL;
        [exact Hfr
        | rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_StackPopL;
        [exact Hfr
        | rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_MemPopL;
        [exact Hfr
        | rewrite (inl_interp_mrec_proper _ _ _ Hu1); apply interp_mrec_bind_subevent
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - destruct ce as [ce0 | me0]; [| discriminate Hopt].
      destruct ce0 as [dt cc fv args]; cbn [opt_c callee_opt_call] in Hopt.
      destruct fv as [[p | | | | | | |] | |]; try discriminate Hopt.
      destruct (Z.eqb_spec (ptr_to_int p) (ptr_to_int p_callee)) as [Hp_eq | _];
        [| discriminate Hopt].
      injection Hopt as <-.
      assert (Hp_gt0 : (ptr_to_int p > 0)%Z) by (cbn [ptr_to_int P2I ParamsV PIV PointerV fst] in *; lia).
      assert (Emrec_step :
        interp_mrec (inl_mrec_ctx ctx1) u1 ≅
        Tau (interp_mrec (inl_mrec_ctx ctx1) (ITree.bind (callee_fn cc args) k1))).
      { rewrite (inl_interp_mrec_proper _ _ _ Hu1), bind_trigger, unfold_interp_mrec.
        cbn [observe _interp_mrec case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
        apply eqit_Tau, inl_interp_mrec_proper.
        eapply eq_itree_clo_bind with (UU := Logic.eq); [| intros ? _ <-; reflexivity].
        unfold inl_mrec_ctx; rewrite (check_callee_nonnull_ptr p Hp_gt0).
        cbn [EOU_to_itree lookup_defn ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
        rewrite Eqit.bind_ret_l;
          first [rewrite Hp_eq | cbn [ptr_to_int P2I ParamsV PIV PointerV fst] in Hp_eq |- *; rewrite Hp_eq];
          rewrite Hlk_callee; reflexivity. }
      eapply gen_inline_sim__obs_eq; [symmetry; exact Emrec_step | reflexivity |].
      eapply GIS_TauL; [reflexivity | exact IH].
  Qed.

  (** *** Lifting [mcfg_inline_sim] Across [interp_intrinsics] *)

  Definition inl_sem_fn_sync
    (g0 : global_env)
    (sem : @semantic_function PaV (@MCFGEtop PaV)) : Prop :=
    forall args va stk env1 env2,
      mcfg_inline_sim g0 true
        (fun ic' r1 r2 => ic' = IC_Synced stk env1 env2 /\ r1 = r2)
        (IC_Synced stk env1 env2) (sem args va) (sem args va).

  Lemma inl_pure_to_semantic_sync (g0 : global_env) pf :
    inl_sem_fn_sync g0 (pure_to_semantic pf).
  Proof using.
    intros args va stk env1 env2; unfold pure_to_semantic.
    apply mcfg_inline_sim_EOU; reflexivity.
  Qed.

  Lemma inl_pure_base_to_semantic_sync (g0 : global_env) pbf :
    inl_sem_fn_sync g0 (pure_base_to_semantic pbf).
  Proof using.
    unfold pure_base_to_semantic; apply inl_pure_to_semantic_sync.
  Qed.

  Lemma inl_Forall_map_pure_to_semantic {A B : Type} (g0 : global_env)
    (f : A -> B * _) (l : list A)
    (Hf : forall x, inl_sem_fn_sync g0 (snd (f x))) :
    Forall (fun p => inl_sem_fn_sync g0 (snd p)) (List.map f l).
  Proof using.
    induction l as [| x xs IH]; constructor; [apply Hf | exact IH].
  Qed.

  #[local] Lemma inl_mk_int_unop_defs_sync g0 op_name widths op :
    Forall (fun p => inl_sem_fn_sync g0 (snd p)) (mk_int_unop_defs op_name widths op).
  Proof using.
    unfold mk_int_unop_defs; apply inl_Forall_map_pure_to_semantic; intros; apply inl_pure_base_to_semantic_sync.
  Qed.

  #[local] Lemma inl_mk_int_unop_flag_defs_sync g0 op_name widths op :
    Forall (fun p => inl_sem_fn_sync g0 (snd p)) (mk_int_unop_flag_defs op_name widths op).
  Proof using.
    unfold mk_int_unop_flag_defs; apply inl_Forall_map_pure_to_semantic; intros; apply inl_pure_base_to_semantic_sync.
  Qed.

  #[local] Lemma inl_mk_int_binop_defs_sync g0 op_name widths op :
    Forall (fun p => inl_sem_fn_sync g0 (snd p)) (mk_int_binop_defs op_name widths op).
  Proof using.
    unfold mk_int_binop_defs; apply inl_Forall_map_pure_to_semantic; intros; apply inl_pure_base_to_semantic_sync.
  Qed.

  #[local] Lemma inl_mk_expect_int_defs_sync g0 widths :
    Forall (fun p => inl_sem_fn_sync g0 (snd p)) (mk_expect_int_defs widths).
  Proof using.
    unfold mk_expect_int_defs; apply inl_Forall_map_pure_to_semantic; intros; apply inl_pure_base_to_semantic_sync.
  Qed.

  #[local] Lemma inl_mk_int_ternop_defs_sync g0 op_name widths op :
    Forall (fun p => inl_sem_fn_sync g0 (snd p)) (mk_int_ternop_defs op_name widths op).
  Proof using.
    unfold mk_int_ternop_defs; apply inl_Forall_map_pure_to_semantic; intros; apply inl_pure_base_to_semantic_sync.
  Qed.

  #[local] Lemma inl_mk_int_ovf_binop_defs_sync g0 op_name widths op :
    Forall (fun p => inl_sem_fn_sync g0 (snd p)) (mk_int_ovf_binop_defs op_name widths op).
  Proof using.
    unfold mk_int_ovf_binop_defs; apply inl_Forall_map_pure_to_semantic; intros; apply inl_pure_to_semantic_sync.
  Qed.

  #[local] Opaque mk_int_unop_defs mk_int_unop_flag_defs mk_int_binop_defs
    mk_expect_int_defs mk_int_ternop_defs mk_int_ovf_binop_defs.

  #[local] Lemma inl_extra_fp_intrinsics_sync (g0 : global_env) :
    Forall (fun p => inl_sem_fn_sync g0 (snd p)) extra_fp_intrinsics.
  Proof using.
    unfold extra_fp_intrinsics;
      repeat (apply Forall_cons; [apply inl_pure_base_to_semantic_sync |]);
      try apply Forall_nil.
  Qed.

  #[local] Lemma inl_Forall_app_intro {A : Type} (P : A -> Prop) (l1 l2 : list A) :
    Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
  Proof using.
    intros H1 H2; apply Forall_app; split; assumption.
  Qed.

  #[local] Lemma inl_extra_int_intrinsics_sync (g0 : global_env) :
    Forall (fun p => inl_sem_fn_sync g0 (snd p)) extra_int_intrinsics.
  Proof using.
    unfold extra_int_intrinsics; repeat apply inl_Forall_app_intro;
      first [ apply inl_mk_int_binop_defs_sync
            | apply inl_mk_int_unop_flag_defs_sync
            | apply inl_mk_int_ovf_binop_defs_sync
            | apply inl_mk_int_unop_defs_sync
            | apply inl_mk_int_ternop_defs_sync
            | apply inl_mk_expect_int_defs_sync ].
  Qed.

  #[local] Opaque extra_fp_intrinsics extra_int_intrinsics.

  Lemma inl_defined_intrinsics_sync (g0 : global_env) :
    Forall (fun p => inl_sem_fn_sync g0 (snd p))
      (@defined_intrinsics PaV (@MCFGEtop PaV) _ _ _ _).
  Proof using.
    unfold defined_intrinsics.
    repeat apply inl_Forall_app_intro;
      [ repeat (apply Forall_cons; [apply inl_pure_base_to_semantic_sync |]); try apply Forall_nil
      | apply inl_extra_fp_intrinsics_sync
      | apply inl_extra_int_intrinsics_sync
      | ].
    repeat (apply Forall_cons;
              [try first [apply inl_pure_to_semantic_sync | apply inl_pure_base_to_semantic_sync] |]);
      try apply Forall_nil.
    - (* llvm_va_start *)
      cbn [snd]; intros fargs va stk env1 env2; unfold llvm_va_start.
      destruct fargs as [| a [| ? ?]], va as [vp |]; cbv beta iota;
        try (apply mcfg_inline_sim_raise; reflexivity).
      destruct a as [[| | | | | | |] | |]; cbv beta iota;
        try apply mcfg_inline_sim_raiseUB;
        (eapply gen_inline_sim_bind;
         [unfold store; try unfold trigger; apply mcfg_inline_sim_trigger_refl; reflexivity
         | intros ? [] _ [-> _]; apply gen_inline_sim_ret; split; reflexivity]).
    - (* llvm_va_end *)
      cbn [snd]; intros fargs va stk env1 env2; unfold llvm_va_end.
      apply gen_inline_sim_ret; split; reflexivity.
    - (* llvm_va_copy *)
      cbn [snd]; intros fargs va stk env1 env2; unfold llvm_va_copy.
      destruct fargs as [| dst [| src [| ? ?]]]; cbv beta iota;
        try (apply mcfg_inline_sim_raise; reflexivity).
      eapply gen_inline_sim_bind.
      + unfold load; try unfold trigger; apply mcfg_inline_sim_trigger_refl; reflexivity.
      + intros ? vargs _ [-> <-].
        eapply gen_inline_sim_bind.
        * unfold store; try unfold trigger; apply mcfg_inline_sim_trigger_refl; reflexivity.
        * intros ? [] _ [-> _]; apply gen_inline_sim_ret; split; reflexivity.
  Qed.

  #[local] Opaque defined_intrinsics.

  #[local] Lemma inl_assoc_defs_sync (g0 : global_env) (fname : string)
    (defs : list (declaration typ * @semantic_function PaV (@MCFGEtop PaV)))
    (Hdefs : Forall (fun p => inl_sem_fn_sync g0 (snd p)) defs)
    (f : @semantic_function PaV (@MCFGEtop PaV)) :
    assoc fname
      (List.map (fun '(a, b) => match dc_name a with Name s => (s, b) | _ => (""%string, b) end) defs) =
      Some f ->
    inl_sem_fn_sync g0 f.
  Proof using.
    induction Hdefs as [| [decl sem] rest Hsem _ IH]; cbn [List.map assoc]; [discriminate |].
    cbn [snd] in Hsem; destruct (dc_name decl); cbn iota zeta;
      (match goal with |- (if ?b then _ else _) = _ -> _ => destruct b end;
       [intros H;
        exact (eq_ind sem (inl_sem_fn_sync g0) Hsem f
                 (f_equal (fun o => match o with Some g => g | None => sem end) H))
       | exact IH]).
  Qed.

  Lemma mcfg_inline_sim_handle_intrinsics {X : Type}
    (g0 : global_env) (ie : @IntrinsicE PaV X) stk env1 env2 :
    mcfg_inline_sim g0 true
      (fun ic' r1 r2 => ic' = IC_Synced stk env1 env2 /\ r1 = r2)
      (IC_Synced stk env1 env2)
      (handle_intrinsics ie) (handle_intrinsics ie).
  Proof using.
    destruct ie as [dt fname args va]; cbn [handle_intrinsics].
    destruct (assoc fname defs_assoc) as [f |] eqn:Eassoc; cbn [eq_rect].
    - unfold defs_assoc in Eassoc;
        exact (inl_assoc_defs_sync g0 fname _ (inl_defined_intrinsics_sync g0) f Eassoc args va stk env1 env2).
    - apply mcfg_inline_sim_trigger_refl; reflexivity.
  Qed.

  #[local] Transparent defined_intrinsics extra_fp_intrinsics extra_int_intrinsics
    mk_int_unop_defs mk_int_unop_flag_defs mk_int_binop_defs
    mk_expect_int_defs mk_int_ternop_defs mk_int_ovf_binop_defs.

  Lemma interp_intrinsics_bind_non_intr {X R : Type}
    (me : @MCFGEtop PaV X) (k : X -> @MCFGtop PaV R)
    (Hni : interp_intrinsics_h me = ITree.trigger me) :
    interp_intrinsics (ITree.bind (ITree.trigger me) k) ≅
    ITree.bind (ITree.trigger me) (fun x => Tau (interp_intrinsics (k x))).
  Proof using.
    unfold interp_intrinsics.
    rewrite bind_trigger, interp_vis, Hni.
    reflexivity.
  Qed.

  #[local] Lemma interp_intrinsics_proper {R : Type} (u1 u2 : @MCFGtop PaV R) :
    u1 ≅ u2 ->
    interp_intrinsics u1 ≅ interp_intrinsics u2.
  Proof using.
    unfold interp_intrinsics; intros H; rewrite H; reflexivity.
  Qed.

  #[local] Lemma interp_intrinsics_tau {R : Type} (u : @MCFGtop PaV R) :
    interp_intrinsics (Tau u) ≅ Tau (interp_intrinsics u).
  Proof using.
    unfold interp_intrinsics; rewrite unfold_interp; reflexivity.
  Qed.

  #[local] Lemma interp_intrinsics_bind_non_intr_obs {X R : Type}
    (v : @MCFGtop PaV R) (me : @MCFGEtop PaV X) (k : X -> @MCFGtop PaV R)
    (Hv : v ≅ ITree.bind (ITree.trigger me) k)
    (Hni : interp_intrinsics_h me = ITree.trigger me) :
    interp_intrinsics v ≅
    ITree.bind (ITree.trigger me) (fun x => Tau (interp_intrinsics (k x))).
  Proof using.
    rewrite (interp_intrinsics_proper _ _ Hv); exact (interp_intrinsics_bind_non_intr me k Hni).
  Qed.

  #[local] Definition inl_intr_rel (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic0 : inline_ctx) (x1 : R1 + @MCFGtop PaV R1) (x2 : R2 + @MCFGtop PaV R2) : Prop :=
    match x1, x2 with
    | inl r1, inl r2 => RR ic0 r1 r2
    | inr v1, inr v2 => mcfg_inline_sim g0 true RR ic0 v1 v2
    | _, _ => False
    end.

  #[local] Definition inl_intr_r_both (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic0 : inline_ctx) (a1 : @MCFGtop PaV R1) (a2 : @MCFGtop PaV R2) : Prop :=
    (exists v1 v2,
       a1 = interp_intrinsics v1 /\
       a2 = interp_intrinsics v2 /\
       mcfg_inline_sim g0 true RR ic0 v1 v2) \/
    (exists w1 w2,
       a1 = ITree.bind w1 intr_cont /\
       a2 = ITree.bind w2 intr_cont /\
       mcfg_inline_sim g0 true (inl_intr_rel g0 RR) ic0 w1 w2).

  #[local] Lemma inl_intr_step_decomp (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic : inline_ctx) (u1 : @MCFGtop PaV R1) (u2 : @MCFGtop PaV R2) :
    gis_step_body (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
      (@inl_mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT) true
      RR
      (upaco3
         (gen_inline_sim_ (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
            (@inl_mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
            (@no_opt_call (@MCFGEtop PaV)) g0 true RR) bot3)
      ic (observe u1) (observe u2) ->
    mcfg_inline_sim g0 true (inl_intr_rel g0 RR) ic (decomp_intr u1) (decomp_intr u2).
  Proof using.
    intros Hstep.
    unfold gis_step_body, decomp_intr in *.
    destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
    - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
      apply gen_inline_sim_ret; exact Hstep.
    - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
      apply gen_inline_sim_ret; apply gis_cont_to_sim, Hstep.
    - destruct Hstep as [Hub | Hvis].
      + destruct_sum1 ev1; try discriminate Hub; destruct ev1 as [u];
          cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ E_trigger F_trigger];
          try unfold trigger; unfold ITree.trigger;
          pstep; apply GIS_Step; unfold gis_step_body; rewrite observe_bind;
          norm_subevent;
          cbn [observe inl_is_ub_mcfg];
          left; reflexivity.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        destruct Hvis as [(Hsync & HE & HA) | Hls].
        * destruct ev1 as [ec1 | [ie1 | rest1]], ev2 as [ec2 | [ie2 | rest2]];
            cbn in HE; try contradiction.
          -- cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ E_trigger];
             try unfold trigger; unfold ITree.trigger;
             pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind;
             norm_subevent;
             cbn [observe].
             right; left; split; [exact Hsync | split; [exact HE |]].
             intros a1 a2 Ha Hp.
             exists (Ret (inr (k1 a1))), (Ret (inr (k2 a2))).
             split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
             split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
             left; apply gen_inline_sim_ret; apply gis_cont_to_sim, (HA a1 a2 Ha Hp).
          -- destruct ic as [stk env1 env2 | |]; try discriminate Hsync.
             destruct ie1, ie2; destruct HE as (<- & <- & <- & <-);
               cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
             eapply gen_inline_sim_bind;
               [apply mcfg_inline_sim_handle_intrinsics |].
             intros ? a1 a2 [-> <-]; apply gen_inline_sim_ret; cbn [inl_intr_rel].
             apply gis_cont_to_sim, (HA a1 a1 (EqA_MCFG_refl _ a1) I).
          -- cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ F_trigger];
             try unfold trigger; unfold ITree.trigger;
             pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind;
             norm_subevent;
             cbn [observe].
             right; left; split; [exact Hsync | split; [exact HE |]].
             intros a1 a2 Ha Hp.
             exists (Ret (inr (k1 a1))), (Ret (inr (k2 a2))).
             split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
             split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
             left; apply gen_inline_sim_ret; apply gis_cont_to_sim, (HA a1 a2 Ha Hp).
        * destruct ic as [stk env1 env2 | |]; try contradiction.
          destruct Hls as [Hloc | [_ Hstk]].
          -- destruct (as_local_mcfg ev1) as [le1 |] eqn:Ele1,
                      (as_local_mcfg ev2) as [le2 |] eqn:Ele2;
               try (rewrite Ele1, Ele2 in Hloc; cbn iota in Hloc); try contradiction.
             destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2];
               cbn iota in Hloc; try contradiction;
               destruct_sum1 ev1; try discriminate Ele1;
               destruct_sum1 ev2; try discriminate Ele2;
               inversion Ele1; subst; inversion Ele2; subst;
               cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ F_trigger];
               try unfold trigger; unfold ITree.trigger;
               pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind;
               norm_subevent;
               cbn [observe as_local_mcfg];
               right; right; left.
             ++ destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv |]].
                exists (Ret (inr (k1 tt))), (Ret (inr (k2 tt))).
                split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                left; apply gen_inline_sim_ret; apply gis_cont_to_sim, Hr.
             ++ destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                intros v Hv.
                exists (Ret (inr (k1 v))), (Ret (inr (k2 v))).
                split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                left; apply gen_inline_sim_ret; apply gis_cont_to_sim, Hrd, Hv.
          -- destruct (as_stack_mcfg ev1) as [se1 |] eqn:Ese1,
                      (as_stack_mcfg ev2) as [se2 |] eqn:Ese2;
               try (rewrite Ese1, Ese2 in Hstk; cbn iota in Hstk); try contradiction.
             destruct se1, se2; cbn iota in Hstk; try contradiction;
               destruct_sum1 ev1; try discriminate Ese1;
               destruct_sum1 ev2; try discriminate Ese2;
               inversion Ese1; subst; inversion Ese2; subst;
               cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_ F_trigger];
               try unfold trigger; unfold ITree.trigger;
               pstep; apply GIS_Step; unfold gis_step_body; rewrite !observe_bind;
               norm_subevent;
               cbn [observe as_stack_mcfg];
               right; right; right.
             ++ split; [reflexivity |].
                destruct Hstk as [Hbs Hr]; split; [exact Hbs |].
                exists (Ret (inr (k1 tt))), (Ret (inr (k2 tt))).
                split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                left; apply gen_inline_sim_ret; apply gis_cont_to_sim, Hr.
             ++ split; [reflexivity |].
                destruct stk as [| [p1 p2] rest]; [exact I |].
                exists (Ret (inr (k1 tt))), (Ret (inr (k2 tt))).
                split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                split; [eapply ITS_Eq; [apply Eqit.bind_ret_l | apply ITS_Refl] |].
                left; apply gen_inline_sim_ret; apply gis_cont_to_sim, Hstk.
  Qed.

  #[local] Lemma inl_intr_branch_b (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic0 : inline_ctx) (w1 : @MCFGtop PaV (R1 + @MCFGtop PaV R1))
    (w2 : @MCFGtop PaV (R2 + @MCFGtop PaV R2)) :
    mcfg_inline_sim g0 true (inl_intr_rel g0 RR) ic0 w1 w2 ->
    gen_inline_sim_ (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
      (@inl_mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
      (@no_opt_call (@MCFGEtop PaV)) g0 true RR (inl_intr_r_both g0 RR)
      ic0 (ITree.bind w1 intr_cont) (ITree.bind w2 intr_cont).
  Proof using.
    intros Hw; punfold Hw.
    assert (Hlift_b :
      forall ic1 q1 q2,
        gis_cont
          (upaco3
             (gen_inline_sim_ (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
                (@inl_mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
                (@no_opt_call (@MCFGEtop PaV)) g0 true (inl_intr_rel g0 RR)) bot3)
          ic1 q1 q2 ->
        gis_cont (inl_intr_r_both g0 RR) ic1 (ITree.bind q1 intr_cont) (ITree.bind q2 intr_cont)).
    { intros ic1 q1 q2 Hc.
      exists (ITree.bind q1 intr_cont), (ITree.bind q2 intr_cont).
      split; [apply ITS_Refl | split; [apply ITS_Refl |]].
      right; exists q1, q2; split; [reflexivity | split; [reflexivity | apply gis_cont_to_sim, Hc]]. }
    induction Hw as [ic0 w1 w2 Hstep
                     | ic0 w1 mw1 w2 Hw1 _ IH
                     | ic0 w1 w2 mw2 Hw2 _ IH
                     | ic0 env1 w1 x v fw1 w2 He1 Hw1 Hlk _ IH
                     | ic0 env2 w1 w2 x v fw2 He2 Hw2 Hlk _ IH
                     | ic0 ic' w1 x v fw1 w2 Hw_ic Hw1 _ IH
                     | ic0 ic' w1 w2 x v fw2 Hw_ic Hw2 _ IH
                     | ic0 w1 k v fw1 w2 Hw1 Hlk _ IH
                     | stk ce1 e1 e2 w1 varg fw1 w2 Hw1 _ IH
                     | stk e1 e2 w1 fw1 w2 Hfr Hw1 _ IH
                     | stk ce1 e2 bs w1 fw1 w2 Hfr Hw1 _ IH
                     | stk ce1 e1 e2 w1 fw1 w2 Hfr Hw1 _ IH
                     | stk ce1 e2 w1 fw1 w2 Hfr Hw1 _ IH
                     | stk e1 e2 w1 X ce body1 fw1 w2 Hfr Hw1 Hopt];
      [| | | | | | | | | | | | | discriminate Hopt].
    - unfold gis_step_body in Hstep.
      destruct (observe w1) as [x1 | mw1 | X1 ev1 fw1] eqn:How1.
      + destruct (observe w2) as [x2 | mw2 | X2 ev2 fw2] eqn:How2; try contradiction.
        destruct x1 as [r1 | v1], x2 as [r2 | v2]; cbn [inl_intr_rel] in Hstep; try contradiction.
        * apply GIS_Step; unfold gis_step_body; rewrite !observe_bind, How1, How2; cbn [observe intr_cont]; exact Hstep.
        * apply GIS_Step; unfold gis_step_body; rewrite !observe_bind, How1, How2; cbn [observe intr_cont].
          exists (interp_intrinsics v1), (interp_intrinsics v2).
          split; [apply ITS_Refl | split; [apply ITS_Refl |]].
          left; exists v1, v2; split; [reflexivity | split; [reflexivity | exact Hstep]].
      + destruct (observe w2) as [x2 | mw2 | X2 ev2 fw2] eqn:How2; try contradiction.
        apply GIS_Step; unfold gis_step_body; rewrite !observe_bind, How1, How2.
        apply Hlift_b, Hstep.
      + apply GIS_Step; unfold gis_step_body; rewrite (observe_bind w1 intr_cont), How1.
        destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct (observe w2) as [x2 | mw2 | X2 ev2 fw2] eqn:How2; try contradiction.
        rewrite (observe_bind w2 intr_cont), How2.
        destruct Hvis as [(Hsync & HE & HA) | Hls].
        * left; split; [exact Hsync | split; [exact HE |]].
          intros a1 a2 Ha Hp; apply Hlift_b, (HA a1 a2 Ha Hp).
        * right; destruct ic0 as [stk env1 env2 | |]; try contradiction.
          destruct Hls as [Hloc | [_ Hstk]].
          -- left; destruct (as_local_mcfg ev1) as [le1 |], (as_local_mcfg ev2) as [le2 |]; try contradiction.
             destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
             ++ destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv | apply Hlift_b, Hr]].
             ++ destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
                intros v Hv; apply Hlift_b, Hrd, Hv.
          -- right; split; [reflexivity |];
             destruct (as_stack_mcfg ev1) as [se1 |], (as_stack_mcfg ev2) as [se2 |]; try contradiction.
             destruct se1, se2; try contradiction.
             ++ destruct Hstk as [Hbs Hr]; split; [exact Hbs | apply Hlift_b, Hr].
             ++ destruct stk as [| [p1 p2] rest]; [exact I | apply Hlift_b, Hstk].
    - eapply GIS_TauL; [rewrite (observe_bind w1 intr_cont), Hw1; reflexivity | exact IH].
    - eapply GIS_TauR; [rewrite (observe_bind w2 intr_cont), Hw2; reflexivity | exact IH].
    - eapply GIS_ReadL; [exact He1 | rewrite Hw1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
    - eapply GIS_ReadR; [exact He2 | rewrite Hw2, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
    - eapply GIS_WriteL; [exact Hw_ic | rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
    - eapply GIS_WriteR; [exact Hw_ic | rewrite Hw2, Eqit.bind_bind; reflexivity | exact IH].
    - eapply GIS_GReadL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
    - eapply GIS_ZeroStoreL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
    - eapply GIS_MemPushL; [exact Hfr | rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
    - eapply GIS_StackPushL; [exact Hfr | rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
    - eapply GIS_StackPopL; [exact Hfr | rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
    - eapply GIS_MemPopL; [exact Hfr | rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
  Qed.

  #[local] Lemma inl_intr_branch_a (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (ic0 : inline_ctx) (v1 : @MCFGtop PaV R1) (v2 : @MCFGtop PaV R2) :
    mcfg_inline_sim g0 true RR ic0 v1 v2 ->
    gen_inline_sim_ (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
      (@inl_mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
      (@no_opt_call (@MCFGEtop PaV)) g0 true RR (inl_intr_r_both g0 RR)
      ic0 (interp_intrinsics v1) (interp_intrinsics v2).
  Proof using.
    intros Hv; punfold Hv.
    induction Hv as [ic0 v1 v2 Hstep
                     | ic0 v1 mv1 v2 Hv1 _ IH
                     | ic0 v1 v2 mv2 Hv2 _ IH
                     | ic0 env1 v1 x v kv1 v2 He1 Hv1 Hlk _ IH
                     | ic0 env2 v1 v2 x v kv2 He2 Hv2 Hlk _ IH
                     | ic0 ic' v1 x v kv1 v2 Hw_ic Hv1 _ IH
                     | ic0 ic' v1 v2 x v kv2 Hw_ic Hv2 _ IH
                     | ic0 v1 k v kv1 v2 Hv1 Hlk _ IH
                     | stk ce1 e1 e2 v1 varg kv1 v2 Hv1 _ IH
                     | stk e1 e2 v1 kv1 v2 Hfr Hv1 _ IH
                     | stk ce1 e2 bs v1 kv1 v2 Hfr Hv1 _ IH
                     | stk ce1 e1 e2 v1 kv1 v2 Hfr Hv1 _ IH
                     | stk ce1 e2 v1 kv1 v2 Hfr Hv1 _ IH
                     | stk e1 e2 v1 X ce body1 kv1 v2 Hfr Hv1 Hopt];
      [| | | | | | | | | | | | | discriminate Hopt].
    - eapply gen_inline_sim__obs_eq;
        [apply decomp_intr_spec | apply decomp_intr_spec |].
      apply inl_intr_branch_b, inl_intr_step_decomp, Hstep.
    - assert (Hv1_eq : v1 ≅ Tau mv1) by (rewrite (itree_eta v1), Hv1; reflexivity).
      eapply gen_inline_sim__obs_eq;
        [symmetry; rewrite (interp_intrinsics_proper _ _ Hv1_eq); apply interp_intrinsics_tau
        | reflexivity |].
      eapply GIS_TauL; [reflexivity | exact IH].
    - assert (Hv2_eq : v2 ≅ Tau mv2) by (rewrite (itree_eta v2), Hv2; reflexivity).
      eapply gen_inline_sim__obs_eq;
        [reflexivity
        | symmetry; rewrite (interp_intrinsics_proper _ _ Hv2_eq); apply interp_intrinsics_tau |].
      eapply GIS_TauR; [reflexivity | exact IH].
    - eapply GIS_ReadL;
        [exact He1
        | eapply interp_intrinsics_bind_non_intr_obs; [exact Hv1 | reflexivity]
        | exact Hlk
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_ReadR;
        [exact He2
        | eapply interp_intrinsics_bind_non_intr_obs; [exact Hv2 | reflexivity]
        | exact Hlk
        | eapply GIS_TauR; [reflexivity | exact IH]].
    - eapply GIS_WriteL;
        [exact Hw_ic
        | eapply interp_intrinsics_bind_non_intr_obs; [exact Hv1 | reflexivity]
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_WriteR;
        [exact Hw_ic
        | eapply interp_intrinsics_bind_non_intr_obs; [exact Hv2 | reflexivity]
        | eapply GIS_TauR; [reflexivity | exact IH]].
    - eapply GIS_GReadL;
        [eapply interp_intrinsics_bind_non_intr_obs; [exact Hv1 | reflexivity]
        | exact Hlk
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_ZeroStoreL;
        [eapply interp_intrinsics_bind_non_intr_obs; [exact Hv1 | reflexivity]
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_MemPushL;
        [exact Hfr
        | eapply interp_intrinsics_bind_non_intr_obs; [exact Hv1 | reflexivity]
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_StackPushL;
        [exact Hfr
        | eapply interp_intrinsics_bind_non_intr_obs; [exact Hv1 | reflexivity]
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_StackPopL;
        [exact Hfr
        | eapply interp_intrinsics_bind_non_intr_obs; [exact Hv1 | reflexivity]
        | eapply GIS_TauL; [reflexivity | exact IH]].
    - eapply GIS_MemPopL;
        [exact Hfr
        | eapply interp_intrinsics_bind_non_intr_obs; [exact Hv1 | reflexivity]
        | eapply GIS_TauL; [reflexivity | exact IH]].
  Qed.

  Lemma mcfg_inline_sim_interp_intrinsics (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop) :
    forall ic (u1 : @MCFGtop PaV R1) (u2 : @MCFGtop PaV R2),
      mcfg_inline_sim g0 true RR ic u1 u2 ->
      mcfg_inline_sim g0 true RR ic (interp_intrinsics u1) (interp_intrinsics u2).
  Proof using.
    assert (Hmain :
      forall ic0 t1 t2,
        inl_intr_r_both g0 RR ic0 t1 t2 ->
        mcfg_inline_sim g0 true RR ic0 t1 t2).
    { pcofix CIH.
      intros ic0 t1 t2 Hrb; pstep.
      eapply gen_inline_sim__mon with (r := inl_intr_r_both g0 RR);
        [| intros ic1 a1 a2 Hr; right; apply CIH, Hr].
      destruct Hrb as [(v1 & v2 & -> & -> & Hv) | (w1 & w2 & -> & -> & Hw)].
      - apply inl_intr_branch_a, Hv.
      - apply inl_intr_branch_b, Hw. }
    intros ic u1 u2 Hsim.
    apply Hmain; left; exists u1, u2;
      split; [reflexivity | split; [reflexivity | exact Hsim]].
  Qed.

  (** *** Soundness of [mcfg_inline_sim] over [interp_state interp_vellvm_prov_h] *)

  Lemma interp_vellvm_prov_h_inline_sync {X1 X2 : Type}
    (g0 : global_env) (ic : inline_ctx)
    (e1 : @MCFGEtop PaV X1) (e2 : @MCFGEtop PaV X2)
    (Hsync : inl_sync_mcfg ic e1 = true)
    (HE : EqE_MCFG X1 X2 e1 e2)
    (s1 s2 : FusedS)
    (Hmatch : inline_fused_match g0 ic s1 s2)
    (U : list N) :
    refine_prov
      (fun _ '(s1', a1) '(s2', a2) =>
         inline_fused_match g0 ic s1' s2' /\
         EqA_MCFG X1 X2 e1 a1 e2 a2 /\
         inl_mcfg_event_post e1 a1)
      U (interp_vellvm_prov_h _ e1 s1) (interp_vellvm_prov_h _ e2 s2).
  Proof using.
    destruct s1 as [m1 [[sf1 fstk1] g1]], s2 as [m2 [[sf2 fstk2] g2]].
    destruct ic as [stk env1 env2 | stk env1 env2 | stk ce1 env1 env2];
      [| discriminate Hsync |].
    - (* IC_Synced *)
      destruct Hmatch as (-> & -> & -> & Hsf & Hsfm).
      destruct_sum2 e1 e2 HE; try discriminate Hsync.
      + (* ExternalCallE *)
        destruct e1, e2; cbn in HE; try contradiction;
          repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
          unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_trigger_prov;
          (eapply refine_prov_bind;
           [apply refine_prov_refl with (RR := fun _ a1 a2 => a1 = a2); intros; reflexivity
           | intros U' a1 a2 _ <-; pstep; apply RP_Step; cbn;
             repeat (first [exact Hsf | exact Hsfm | reflexivity | split])]).
      + (* IntrinsicE *)
        destruct e1, e2; destruct HE as (<- & <- & <- & <-).
        unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_intrinsic_prov, on_mem_prov.
        eapply refine_prov_bind;
          [apply refine_prov_refl with (RR := fun _ p1 p2 => p1 = p2); intros; reflexivity |].
        intros U' [m' r] _ _ <-; pstep; apply RP_Step; cbn.
        repeat (first [exact Hsf | exact Hsfm | reflexivity | split]).
      + (* GlobalE: only GlobalRead *)
        destruct e1 as [k1 v1 | k1], e2 as [k2 v2 | k2];
          cbn in HE; try contradiction; try discriminate Hsync.
        subst k2; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
        destruct (Maps.lookup k1 g0) as [gv |] eqn:Egv.
        * eapply refine_prov_obs_eq;
            [symmetry; apply (fused_global_prov_read_some k1 gv (m2, ((sf1, fstk1), g0)) Egv)
            | symmetry; apply (fused_global_prov_read_some k1 gv (m2, ((sf2, fstk2), g0)) Egv) |].
          pstep; apply RP_Step; cbn; repeat (first [exact Hsf | exact Hsfm | reflexivity | split]).
        * destruct (fused_global_prov_read_none k1 (m2, ((sf1, fstk1), g0)) Egv) as (u1 & kf1 & Ef1).
          destruct (fused_global_prov_read_none k1 (m2, ((sf2, fstk2), g0)) Egv) as (u2 & kf2 & Ef2).
          eapply refine_prov_obs_eq; [symmetry; exact Ef1 | symmetry; exact Ef2 |].
          pstep; apply RP_Step; cbn;
            right; right; split; [exact I | intros [] [] _].
      + (* StackE: StackRaise / StackGetExc *)
        destruct e1, e2; cbn in HE; try contradiction; try discriminate Hsync.
        * subst; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
            unfold fused_stack_prov, on_ls_prov, handle_stack; cbn - [lift_bot_prov].
          eapply refine_prov_obs_eq;
            [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
            | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
          destruct Hsf as (Hv1 & Hv2 & Hexc & Hloc).
          pstep; apply RP_Step; cbn;
            repeat split; try exact Hv1; try exact Hv2;
            try exact Hloc; try exact Hsfm; reflexivity.
        * unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
            unfold fused_stack_prov, on_ls_prov, handle_stack; cbn - [lift_bot_prov].
          destruct Hsf as (Hv1 & Hv2 & Hexc & Hloc).
          rewrite <- Hexc.
          eapply refine_prov_obs_eq;
            [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
            | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
          pstep; apply RP_Step; cbn;
            repeat split; try exact Hv1; try exact Hv2;
            try exact Hloc; try exact Hsfm; reflexivity.
      + (* MemoryE *)
        destruct e1, e2; cbn in HE; try contradiction;
          repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
          unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_memory_prov, on_mem_prov, handle_memory;
          (eapply refine_prov_bind;
           [apply (memM_interp_prov_post _ _ (handle_memoryM_inl_post _))
           | intros U' [m1' r1] [m2' r2] _ (-> & <- & Hpost);
             pstep; apply RP_Step; cbn [rp_step_body observe inline_fused_match inl_mcfg_event_post];
             split; [repeat (first [exact Hsf | exact Hsfm | reflexivity | split]) |];
             split; [cbn; reflexivity | exact Hpost]]).
      + (* DrawE *)
        destruct e1 as [dt1], e2 as [dt2]; cbn in HE; subst dt2.
        unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_draw_prov, handle_draw; cbn beta iota.
        destruct (default_dvalue_of_dtyp dt1) as [s | s | s | dv];
          cbn [EOU_to_itree ExtLib.Structures.Monad.ret Monad_itree].
        * unfold raise, trigger_cast, ITree.trigger, lift_bot_prov.
          pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate);
            norm_subevent;
            cbn [match_vis_both is_ub_prov is_ub_bot observe];
            right; right; split; [first [exact Logic.I | apply EqE_bot_refl] | intros [] [] _].
        * unfold raiseOOM, trigger_cast, ITree.trigger, lift_bot_prov.
          pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate);
            norm_subevent;
            cbn [observe is_ub_prov is_ub_bot];
            left; reflexivity.
        * unfold raiseUB, trigger_cast, ITree.trigger, lift_bot_prov.
          pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate);
            norm_subevent;
            cbn [observe is_ub_prov is_ub_bot];
            left; reflexivity.
        * eapply refine_prov_obs_eq;
            [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
            | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
          pstep; apply RP_Step; cbn;
            repeat (first [exact Hsf | exact Hsfm | reflexivity | split]).
      + (* OOME *)
        destruct e1, e2; unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body;
          rewrite !observe_bind; cbn; left; reflexivity.
      + (* LLVMExcE *)
        destruct e1, e2; cbn in HE; subst; unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body;
          rewrite !observe_bind; cbn;
          right; right; split; [reflexivity | intros [] [] _].
      + (* UBE *)
        destruct e1, e2; unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body;
          rewrite !observe_bind; cbn; left; reflexivity.
      + (* DebugE *)
        destruct e1, e2; unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn.
        right; right; split; [exact I | intros [] [] _].
        left; eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        pstep; apply RP_Step; cbn.
        repeat (first [exact Hsf | exact Hsfm | reflexivity | split]).
      + (* FailureE *)
        destruct e1, e2; unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body;
          rewrite !observe_bind; cbn;
          right; right; split; [exact I | intros [] [] _].
    - (* IC_Inlined *)
      destruct Hmatch as (-> & -> & -> & Hvars1 & csf1 & fstk1' & -> & Hcsf & Hsfm).
      destruct_sum2 e1 e2 HE; try discriminate Hsync.
      + (* GlobalE: GlobalRead *)
        destruct e1 as [k1 v1 | k1], e2 as [k2 v2 | k2];
          cbn in HE; try contradiction; try discriminate Hsync.
        subst k2; unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
        destruct (Maps.lookup k1 g0) as [gv |] eqn:Egv.
        * eapply refine_prov_obs_eq;
            [symmetry; apply (fused_global_prov_read_some k1 gv (push_empty_frame m2, ((sf1, csf1 :: fstk1'), g0)) Egv)
            | symmetry; apply (fused_global_prov_read_some k1 gv (m2, ((sf2, fstk2), g0)) Egv) |].
          pstep; apply RP_Step; cbn.
          split;
            [ split; [reflexivity | split; [reflexivity | split; [reflexivity |]]]
            | split; [reflexivity | exact I] ].
          split; [exact Hvars1 | exists csf1, fstk1'; auto].
        * destruct (fused_global_prov_read_none k1
                      (push_empty_frame m2, ((sf1, csf1 :: fstk1'), g0)) Egv)
            as (u1 & kf1 & Ef1).
          destruct (fused_global_prov_read_none k1 (m2, ((sf2, fstk2), g0)) Egv) as (u2 & kf2 & Ef2).
          eapply refine_prov_obs_eq; [symmetry; exact Ef1 | symmetry; exact Ef2 |].
          pstep; apply RP_Step; cbn;
            right; right; split; [exact I | intros [] [] _].
      + (* MemoryE: is_callee_sync_mem e1 = true *)
        destruct e1, e2; cbn in HE; try contradiction;
          repeat match type of HE with _ /\ _ => destruct HE as [<- HE] end;
          try match type of HE with _ = _ => destruct HE end;
          unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_memory_prov, on_mem_prov, handle_memory;
          (eapply refine_prov_bind;
           [apply (handle_memoryM_empty_frame _ Hsync m2 U)
           | intros U' [m1' r1] [m2' r2] _ (-> & <- & Hpost);
             pstep; apply RP_Step; cbn [rp_step_body observe inline_fused_match inl_mcfg_event_post];
             split;
               [ split;
                   [ reflexivity
                   | split; [reflexivity | split; [reflexivity | split; [exact Hvars1 | exists csf1, fstk1'; auto]]] ]
               | ];
             split; [cbn; reflexivity | exact Hpost]]).
      + (* DrawE *)
        destruct e1 as [dt1], e2 as [dt2]; cbn in HE; subst dt2.
        unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_draw_prov, handle_draw; cbn beta iota.
        destruct (default_dvalue_of_dtyp dt1) as [s | s | s | dv];
          cbn [EOU_to_itree ExtLib.Structures.Monad.ret Monad_itree].
        * unfold raise, trigger_cast, ITree.trigger, lift_bot_prov.
          pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate);
            norm_subevent;
            cbn [match_vis_both is_ub_prov is_ub_bot observe];
            right; right; split; [first [exact Logic.I | apply EqE_bot_refl] | intros [] [] _].
        * unfold raiseOOM, trigger_cast, ITree.trigger, lift_bot_prov.
          pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate);
            norm_subevent;
            cbn [observe is_ub_prov is_ub_bot];
            left; reflexivity.
        * unfold raiseUB, trigger_cast, ITree.trigger, lift_bot_prov.
          pstep; apply RP_Step; unfold rp_step_body; repeat (rewrite observe_bind || rewrite observe_translate);
            norm_subevent;
            cbn [observe is_ub_prov is_ub_bot];
            left; reflexivity.
        * eapply refine_prov_obs_eq;
            [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
            | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
          pstep; apply RP_Step; cbn;
            split;
              [ split;
                  [ reflexivity
                  | split; [reflexivity | split; [reflexivity | split; [exact Hvars1 | exists csf1, fstk1'; auto]]] ]
              | ].
          split; [reflexivity | exact I].
      + (* OOME *)
        destruct e1, e2; unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body;
          rewrite !observe_bind; cbn; left; reflexivity.
      + (* UBE *)
        destruct e1, e2; unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body;
          rewrite !observe_bind; cbn; left; reflexivity.
      + (* DebugE *)
        destruct e1, e2; unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn.
        right; right; split; [exact I | intros [] [] _].
        left; eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
        pstep; apply RP_Step; cbn.
        split;
          [ split;
              [ reflexivity
              | split; [reflexivity | split; [reflexivity | split; [exact Hvars1 | exists csf1, fstk1'; auto]]] ]
          | ].
        split; [reflexivity | exact I].
      + (* FailureE *)
        destruct e1, e2; unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_trigger_prov, ITree.trigger.
        pstep; apply RP_Step; unfold rp_step_body;
          rewrite !observe_bind; cbn;
          right; right; split; [exact I | intros [] [] _].
  Qed.

  Definition model_inline_step_rel (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    : list N -> model_step_state R1 -> model_step_state R2 -> Prop :=
    fun _ x1 x2 =>
      match x1, x2 with
      | inl (s1, r1), inl (s2, r2) =>
          exists ic, inline_fused_match g0 ic s1 s2 /\ RR ic r1 r2
      | inr (s1, u1), inr (s2, u2) =>
          exists ic, inline_fused_match g0 ic s1 s2 /\ mcfg_inline_sim g0 true RR ic u1 u2
      | _, _ => False
      end.

  #[local] Definition inl_model_rr_out (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop) :
    list N -> FusedS * R1 -> FusedS * R2 -> Prop :=
    fun (_ : list N) '(s1', r1) '(s2', r2) =>
      exists ic', inline_fused_match g0 ic' s1' s2' /\ RR ic' r1 r2.

  #[local] Definition inl_model_r_both (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (U0 : list N) (a1 : itree ProvBotE (FusedS * R1)) (a2 : itree ProvBotE (FusedS * R2)) : Prop :=
    (exists ic s1 s2 v1 v2,
       interp_state interp_vellvm_prov_h v1 s1 ≅ a1 /\
       interp_state interp_vellvm_prov_h v2 s2 ≅ a2 /\
       inline_fused_match g0 ic s1 s2 /\
       mcfg_inline_sim g0 true RR ic v1 v2) \/
    (exists w1 w2,
       ITree.bind w1 (model_cont R1) ≅ a1 /\
       ITree.bind w2 (model_cont R2) ≅ a2 /\
       refine_prov (model_inline_step_rel g0 RR) U0 w1 w2).

  #[local] Lemma inl_model_r_both_obs_eq (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop) :
    forall U0 a1 a1' a2 a2',
      a1 ≅ a1' -> a2 ≅ a2' -> inl_model_r_both g0 RR U0 a1 a2 -> inl_model_r_both g0 RR U0 a1' a2'.
  Proof using.
    intros U0 a1 a1' a2 a2' Ea1 Ea2
      [(ic & s1 & s2 & v1 & v2 & Ev1 & Ev2 & Hm & Hv) | (w1 & w2 & Ew1 & Ew2 & Hw)].
    - left; exists ic, s1, s2, v1, v2.
      split;
        [etransitivity; eassumption | split; [etransitivity; eassumption | split; assumption]].
    - right; exists w1, w2.
      split; [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hw]].
  Qed.

  #[local] Lemma inl_model_step_decomp (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (U : list N) (ic : inline_ctx) (s1 s2 : FusedS)
    (u1 : @MCFGtop PaV R1) (u2 : @MCFGtop PaV R2) :
    inline_fused_match g0 ic s1 s2 ->
    gis_step_body (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
      (@inl_mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT) true
      RR
      (upaco3
         (gen_inline_sim_ (@inl_is_ub_mcfg) inl_sync_mcfg EqE_MCFG EqA_MCFG
            (@inl_mcfg_event_post IP IPT) (@as_local_mcfg IP IPT) (@as_stack_mcfg IP IPT)
            (@no_opt_call (@MCFGEtop PaV)) g0 true RR) bot3)
      ic (observe u1) (observe u2) ->
    refine_prov (model_inline_step_rel g0 RR) U (decomp_model u1 s1) (decomp_model u2 s2).
  Proof using.
    intros Hmatch Hstep.
    unfold gis_step_body, decomp_model in *.
    destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
    - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
      pstep; apply RP_Step; cbn;
        exists ic; split; assumption.
    - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
      pstep; apply RP_Step; cbn;
        exists ic; split; [exact Hmatch | apply gis_cont_to_sim, Hstep].
    - destruct Hstep as [Hub | Hvis].
      + destruct_sum1 ev1; try discriminate Hub; destruct ev1 as [msg];
          unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_trigger_prov; try unfold trigger; unfold ITree.trigger;
          pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind;
          norm_subevent;
          cbn [observe is_ub_prov is_ub_bot];
          left; reflexivity.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        destruct Hvis as [(Hsync & HE & HA) | Hls].
        * eapply refine_prov_bind;
            [eapply interp_vellvm_prov_h_inline_sync; eassumption |].
          intros U' [s1' a1] [s2' a2] _ (Hm' & Ha & Hp).
          pstep; apply RP_Step; cbn; exists ic;
            split; [exact Hm' | apply gis_cont_to_sim, (HA a1 a2 Ha Hp)].
        * destruct ic as [stk env1 env2 | |]; try contradiction.
          destruct Hls as [Hloc | [_ Hstk]].
          -- destruct (as_local_mcfg ev1) as [le1 |] eqn:Ele1,
                      (as_local_mcfg ev2) as [le2 |] eqn:Ele2; try contradiction.
             destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction;
               destruct_sum1 ev1; try discriminate Ele1;
               destruct_sum1 ev2; try discriminate Ele2;
               inversion Ele1; subst; inversion Ele2; subst;
               unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
               destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
             ++ destruct Hloc as (<- & <- & Hr).
                destruct Hmatch as (-> & -> & -> & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
                eapply refine_prov_obs_eq;
                  [symmetry; rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity
                  | symmetry; rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity |].
                pstep; apply RP_Step; cbn.
                exists (IC_Synced stk (Maps.add x1 v1 env1) (Maps.add x1 v1 env2)).
                split; [| apply gis_cont_to_sim, Hr].
                rewrite Hvars1, Hvars2;
                  repeat split; try exact Hexc; try exact Hloc; try exact Hsfm; reflexivity.
             ++ destruct Hloc as (<- & Hlk_eq & Hrd).
                pose proof Hmatch as (Hg1 & Hg2 & Hmm & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
                destruct (Maps.lookup x1 env1) as [v |] eqn:Elkv.
                ** assert (Elkv2 : Maps.lookup x1 env2 = Some v) by congruence.
                   eapply refine_prov_obs_eq.
                   --- symmetry; rewrite (fused_local_prov_read_some x1 v (mm1, ((sf1, fstk1), gg1))
                                            (ltac:(cbn iota; rewrite Hvars1; exact Elkv))),
                                          Eqit.bind_ret_l; reflexivity.
                   --- symmetry; rewrite (fused_local_prov_read_some x1 v (mm2, ((sf2, fstk2), gg2))
                                            (ltac:(cbn iota; rewrite Hvars2; exact Elkv2))),
                                          Eqit.bind_ret_l; reflexivity.
                   --- pstep; apply RP_Step; cbn; exists (IC_Synced stk env1 env2);
                         split; [exact Hmatch | apply gis_cont_to_sim, (Hrd v Logic.eq_refl)].
                ** assert (Elkv2 : Maps.lookup x1 env2 = None) by congruence.
                   destruct (fused_local_prov_read_none x1 (mm1, ((sf1, fstk1), gg1))
                               (ltac:(cbn iota; rewrite Hvars1; exact Elkv))) as (msg1 & kf1 & Ef1).
                   destruct (fused_local_prov_read_none x1 (mm2, ((sf2, fstk2), gg2))
                               (ltac:(cbn iota; rewrite Hvars2; exact Elkv2))) as (msg2 & kf2 & Ef2).
                   eapply refine_prov_obs_eq;
                     [symmetry; rewrite Ef1, Eqit.bind_vis; reflexivity
                     | symmetry; rewrite Ef2, Eqit.bind_vis; reflexivity |].
                   pstep; apply RP_Step; cbn [rp_step_body observe match_vis_both is_ub_prov is_ub_bot];
                     right; right; split; [first [exact Logic.I | apply EqE_bot_refl] | intros [] [] _].
          -- destruct (as_stack_mcfg ev1) as [se1 |] eqn:Ese1,
                      (as_stack_mcfg ev2) as [se2 |] eqn:Ese2;
               try (rewrite Ese1, Ese2 in Hstk; cbn iota in Hstk); try contradiction.
             destruct se1, se2; cbn iota in Hstk; try contradiction;
               destruct_sum1 ev1; try discriminate Ese1;
               destruct_sum1 ev2; try discriminate Ese2;
               inversion Ese1; subst; inversion Ese2; subst;
               unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
               destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]];
               destruct Hmatch as (-> & -> & -> & Hsf & Hsfm).
             ++ destruct Hstk as [<- Hr].
                unfold fused_stack_prov, on_ls_prov, handle_stack.
                cbn - [Maps.lookup Maps.add lift_bot_prov init_local_env].
                eapply refine_prov_obs_eq;
                  [symmetry; rewrite ?lift_bot_prov_bind_ret, ?lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity
                  | symmetry; rewrite ?lift_bot_prov_bind_ret, ?lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity |].
                pstep; apply RP_Step; cbn.
                exists (IC_Synced ((env1, env2) :: stk) (init_local_env args) (init_local_env args)).
                split; [| apply gis_cont_to_sim, Hr].
                repeat split; try reflexivity.
                apply SFM_cons; [exact Hsf | exact Hsfm].
             ++ destruct stk as [| [p1 p2] rest].
                ** inversion Hsfm; subst.
                   unfold fused_stack_prov, on_ls_prov, handle_stack, raise, trigger_cast, ITree.trigger, lift_bot_prov;
                     cbn - [Maps.lookup Maps.add lift_bot_prov].
                   pstep; apply RP_Step; unfold rp_step_body;
                     repeat (rewrite observe_bind || rewrite observe_translate);
                     norm_subevent;
                     cbn [observe match_vis_both is_ub_prov is_ub_bot];
                     right; right; split; [first [exact Logic.I | apply EqE_bot_refl] | intros [] [] _].
                ** inversion Hsfm as [| ? ? sf1' sf2' ? fstk1' fstk2' Hsf' Hsfm']; subst.
                   unfold fused_stack_prov, on_ls_prov, handle_stack.
                   cbn - [Maps.lookup Maps.add lift_bot_prov init_local_env].
                   eapply refine_prov_obs_eq;
                     [symmetry; rewrite ?lift_bot_prov_bind_ret, ?lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity
                     | symmetry; rewrite ?lift_bot_prov_bind_ret, ?lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity |].
                   pstep; apply RP_Step; cbn.
                   exists (IC_Synced rest p1 p2); split; [| apply gis_cont_to_sim, Hstk].
                   repeat (first [exact Hsf' | exact Hsfm' | reflexivity | split]).
  Qed.

  #[local] Lemma inl_model_branch_b (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (U0 : list N)
    (w1 : itree ProvBotE (FusedS * R1 + FusedS * @MCFGtop PaV R1))
    (w2 : itree ProvBotE (FusedS * R2 + FusedS * @MCFGtop PaV R2))
    (t1 : itree ProvBotE (FusedS * R1)) (t2 : itree ProvBotE (FusedS * R2)) :
    ITree.bind w1 (model_cont R1) ≅ t1 ->
    ITree.bind w2 (model_cont R2) ≅ t2 ->
    refine_prov (model_inline_step_rel g0 RR) U0 w1 w2 ->
    refine_prov_ (inl_model_rr_out g0 RR) (inl_model_r_both g0 RR) U0 t1 t2.
  Proof using.
    intros Et1 Et2 Hw.
    change (FusedS * R1 + FusedS * @MCFGtop PaV R1) with (model_step_state R1) in *.
    change (FusedS * R2 + FusedS * @MCFGtop PaV R2) with (model_step_state R2) in *.
    eapply refine_prov__obs_eq; [apply inl_model_r_both_obs_eq | exact Et1 | exact Et2 |].
    punfold Hw; clear t1 t2 Et1 Et2.
    induction Hw as [U0 w1 w2 Hstep | U0 w1 mw1 w2 Hw1 _ IH | U0 w1 w2 mw2 Hw2 _ IH].
    - unfold rp_step_body in Hstep.
      destruct (observe w1) as [x1 | mw1 | X1 ev1 kw1] eqn:How1.
      + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
        destruct x1 as [[s1 r1] | [s1 v1]], x2 as [[s2 r2] | [s2 v2]]; cbn in Hstep; try contradiction.
        * apply RP_Step; unfold rp_step_body;
            rewrite (observe_bind w1 (model_cont R1)), (observe_bind w2 (model_cont R2)), How1, How2;
            cbn [observe model_cont]; exact Hstep.
        * destruct Hstep as (ic & Hm & Hv).
          apply RP_Step; unfold rp_step_body;
            rewrite (observe_bind w1 (model_cont R1)), (observe_bind w2 (model_cont R2)), How1, How2;
            cbn [observe model_cont].
          left; exists ic, s1, s2, v1, v2;
            split; [reflexivity | split; [reflexivity | split; assumption]].
      + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction; pclearbot.
        apply RP_Step; unfold rp_step_body;
          rewrite (observe_bind w1 (model_cont R1)), (observe_bind w2 (model_cont R2)), How1, How2.
        right; exists mw1, mw2; split; [reflexivity | split; [reflexivity | exact Hstep]].
      + apply RP_Step; unfold rp_step_body;
          rewrite (observe_bind w1 (model_cont R1)), How1.
        destruct Hstep as [Hub | [Hleft | Hboth]].
        * left; exact Hub.
        * right; left; destruct ev1 as [p1 | b1]; [| contradiction]; destruct p1.
          intros p Hp; specialize (Hleft p Hp); pclearbot.
          right; exists (kw1 p), w2; split; [reflexivity | split; [reflexivity | exact Hleft]].
        * right; right.
          destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          rewrite (observe_bind w2 (model_cont R2)), How2.
          destruct ev1 as [p1 | b1], ev2 as [p2 | b2]; cbn in *; try contradiction.
          -- destruct p1, p2; intros p Hp; specialize (Hboth p Hp); pclearbot.
             right; exists (kw1 p), (kw2 p); split; [reflexivity | split; [reflexivity | exact Hboth]].
          -- destruct Hboth as [HE HA]; split; [exact HE |].
             intros a1 a2 Ha; specialize (HA a1 a2 Ha); pclearbot.
             right; exists (kw1 a1), (kw2 a2); split; [reflexivity | split; [reflexivity | exact HA]].
    - eapply RP_TauL; [rewrite (observe_bind w1 (model_cont R1)), Hw1; reflexivity | exact IH].
    - eapply RP_TauR; [rewrite (observe_bind w2 (model_cont R2)), Hw2; reflexivity | exact IH].
  Qed.

  #[local] Lemma inl_model_branch_a (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop)
    (U0 : list N) (ic : inline_ctx) (s1 s2 : FusedS)
    (u1 : @MCFGtop PaV R1) (u2 : @MCFGtop PaV R2)
    (t1 : itree ProvBotE (FusedS * R1)) (t2 : itree ProvBotE (FusedS * R2)) :
    interp_state interp_vellvm_prov_h u1 s1 ≅ t1 ->
    interp_state interp_vellvm_prov_h u2 s2 ≅ t2 ->
    inline_fused_match g0 ic s1 s2 ->
    mcfg_inline_sim g0 true RR ic u1 u2 ->
    refine_prov_ (inl_model_rr_out g0 RR) (inl_model_r_both g0 RR) U0 t1 t2.
  Proof using.
    intros Et1 Et2 Hmatch Hu.
    eapply refine_prov__obs_eq; [apply inl_model_r_both_obs_eq | exact Et1 | exact Et2 |].
    punfold Hu; clear t1 t2 Et1 Et2.
    revert s1 s2 Hmatch;
      induction Hu as [ic u1 u2 Hstep
                       | ic u1 mu1 u2 Hu1 _ IH
                       | ic u1 u2 mu2 Hu2 _ IH
                       | ic env1 u1 x v k1 u2 He1 Hu1 Hlk _ IH
                       | ic env2 u1 u2 x v k2 He2 Hu2 Hlk _ IH
                       | ic ic' u1 x v k1 u2 Hw1 Hu1 _ IH
                       | ic ic' u1 u2 x v k2 Hw2 Hu2 _ IH
                       | ic u1 k v k1 u2 Hu1 Hlk _ IH
                       | stk ce1 e1 e2 u1 varg k1 u2 Hu1 _ IH
                       | stk e1 e2 u1 k1 u2 Hfr Hu1 _ IH
                       | stk ce1 e2 bs u1 k1 u2 Hfr Hu1 _ IH
                       | stk ce1 e1 e2 u1 k1 u2 Hfr Hu1 _ IH
                       | stk ce1 e2 u1 k1 u2 Hfr Hu1 _ IH
                       | stk e1 e2 u1 X ce body1 k1 u2 Hfr Hu1 Hopt];
      [| | | | | | | | | | | | | discriminate Hopt];
      intros s1 s2 Hmatch.
    - eapply inl_model_branch_b;
        [apply decomp_model_spec | apply decomp_model_spec | eapply inl_model_step_decomp; eassumption].
    - eapply refine_prov__obs_eq with
        (t1 := Tau (interp_state interp_vellvm_prov_h mu1 s1))
        (t2 := interp_state interp_vellvm_prov_h u2 s2);
        [apply inl_model_r_both_obs_eq
        | symmetry; rewrite (unfold_interp_state interp_vellvm_prov_h u1 s1), Hu1; reflexivity
        | reflexivity |].
      eapply RP_TauL; [reflexivity | apply IH, Hmatch].
    - eapply refine_prov__obs_eq with
        (t1 := interp_state interp_vellvm_prov_h u1 s1)
        (t2 := Tau (interp_state interp_vellvm_prov_h mu2 s2));
        [apply inl_model_r_both_obs_eq
        | reflexivity
        | symmetry; rewrite (unfold_interp_state interp_vellvm_prov_h u2 s2), Hu2; reflexivity |].
      eapply RP_TauR; [reflexivity | apply IH, Hmatch].
    - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
      assert (Hvars1 : sf1.(stack_vars) = env1).
      { destruct ic as [stk e1_0 e2_0 | | stk ce1 e1_0 e2_0]; try discriminate He1;
          cbn in He1; injection He1 as <-;
          [destruct Hmatch as (_ & _ & _ & [Hv1 _] & _); exact Hv1
          | destruct Hmatch as (_ & _ & _ & Hv1 & _); exact Hv1]. }
      eapply refine_prov__obs_eq with
        (t1 := Tau (interp_state interp_vellvm_prov_h (k1 v) (mm1, ((sf1, fstk1), gg1))))
        (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), gg2))).
      + apply inl_model_r_both_obs_eq.
      + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
          norm_subevent;
          cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          norm_subevent.
        rewrite (fused_local_prov_read_some x v (mm1, ((sf1, fstk1), gg1))
                   (ltac:(cbn iota; rewrite Hvars1; exact Hlk))), Eqit.bind_ret_l; reflexivity.
      + reflexivity.
      + eapply RP_TauL; [reflexivity | apply IH, Hmatch].
    - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
      assert (Hvars2 : sf2.(stack_vars) = env2).
      { destruct ic as [stk e1_0 e2_0 | | stk ce1 e1_0 e2_0]; try discriminate He2;
          cbn in He2; injection He2 as <-;
          [destruct Hmatch as (_ & _ & _ & (_ & Hv2 & _) & _); exact Hv2
          | destruct Hmatch as (_ & _ & _ & _ & csf1 & fstk1' & _ & (_ & Hv2 & _) & _); exact Hv2]. }
      eapply refine_prov__obs_eq with
        (t1 := interp_state interp_vellvm_prov_h u1 (mm1, ((sf1, fstk1), gg1)))
        (t2 := Tau (interp_state interp_vellvm_prov_h (k2 v) (mm2, ((sf2, fstk2), gg2)))).
      + apply inl_model_r_both_obs_eq.
      + reflexivity.
      + symmetry; rewrite Hu2, bind_trigger, interp_state_vis;
          norm_subevent;
          cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          norm_subevent.
        rewrite (fused_local_prov_read_some x v (mm2, ((sf2, fstk2), gg2))
                   (ltac:(cbn iota; rewrite Hvars2; exact Hlk))), Eqit.bind_ret_l; reflexivity.
      + eapply RP_TauR; [reflexivity | apply IH, Hmatch].
    - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
      assert (Hl :
                interp_state interp_vellvm_prov_h u1 (mm1, ((sf1, fstk1), gg1)) ≅
                Tau (interp_state interp_vellvm_prov_h (k1 tt)
                       (mm1, ((upd_local_sf sf1 (Maps.add x v sf1.(stack_vars)), fstk1), gg1)))).
      { rewrite Hu1, bind_trigger, interp_state_vis;
          norm_subevent;
          cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity. }
      eapply refine_prov__obs_eq with
        (t1 := Tau (interp_state interp_vellvm_prov_h (k1 tt)
                      (mm1, ((upd_local_sf sf1 (Maps.add x v sf1.(stack_vars)), fstk1), gg1))))
        (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), gg2)));
        [apply inl_model_r_both_obs_eq | symmetry; exact Hl | reflexivity |]; clear Hl.
      eapply RP_TauL; [reflexivity | apply IH].
        destruct ic as [stk e1_0 e2_0 | | stk ce1 e1_0 e2_0]; try discriminate Hw1;
          cbn in Hw1; injection Hw1 as <-.
        * destruct Hmatch as (-> & -> & -> & (Hv1 & Hv2 & Hexc & Hloc) & Hsfm).
          rewrite Hv1; repeat split;
            try exact Hv2; try exact Hexc; try exact Hloc; try exact Hsfm; reflexivity.
        * destruct Hmatch as (-> & -> & -> & Hv1 & csf1 & fstk1' & -> & Hcsf & Hsfm).
          rewrite Hv1;
            split;
              [ reflexivity
              | split; [reflexivity | split; [reflexivity | split; [reflexivity |]]] ];
            exists csf1, fstk1'; auto.
    - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
      assert (Hr :
                interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), gg2)) ≅
                Tau (interp_state interp_vellvm_prov_h (k2 tt)
                       (mm2, ((upd_local_sf sf2 (Maps.add x v sf2.(stack_vars)), fstk2), gg2)))).
      { rewrite Hu2, bind_trigger, interp_state_vis;
          norm_subevent;
          cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity. }
      eapply refine_prov__obs_eq with
        (t1 := interp_state interp_vellvm_prov_h u1 (mm1, ((sf1, fstk1), gg1)))
        (t2 := Tau (interp_state interp_vellvm_prov_h (k2 tt)
                      (mm2, ((upd_local_sf sf2 (Maps.add x v sf2.(stack_vars)), fstk2), gg2))));
        [apply inl_model_r_both_obs_eq | reflexivity | symmetry; exact Hr |]; clear Hr.
      eapply RP_TauR; [reflexivity | apply IH].
        destruct ic as [stk e1_0 e2_0 | | stk ce1 e1_0 e2_0]; try discriminate Hw2;
          cbn in Hw2; injection Hw2 as <-.
        * destruct Hmatch as (-> & -> & -> & (Hv1 & Hv2 & Hexc & Hloc) & Hsfm).
          rewrite Hv2; repeat split;
            try exact Hv1; try exact Hexc; try exact Hloc; try exact Hsfm; reflexivity.
        * destruct Hmatch as (-> & -> & -> & Hv1 & csf1 & fstk1' & -> & (Hcv1 & Hv2 & Hexc & Hloc) & Hsfm).
          rewrite Hv2;
            split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [exact Hv1 |]]]].
          exists csf1, fstk1'; split; [reflexivity | split; [| exact Hsfm]].
          repeat split; try exact Hcv1; try exact Hexc; try exact Hloc; reflexivity.
    - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
      assert (Hg1 : gg1 = g0).
      { destruct Hmatch as (Hg1 & _); exact Hg1. }
      eapply refine_prov__obs_eq with
        (t1 := Tau (interp_state interp_vellvm_prov_h (k1 v) (mm1, ((sf1, fstk1), gg1))))
        (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), gg2))).
      + apply inl_model_r_both_obs_eq.
      + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
          norm_subevent;
          cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          norm_subevent.
        rewrite (fused_global_prov_read_some k v (mm1, ((sf1, fstk1), gg1))
                   (ltac:(cbn [snd]; rewrite Hg1; exact Hlk))), Eqit.bind_ret_l; reflexivity.
      + reflexivity.
      + eapply RP_TauL; [reflexivity | apply IH, Hmatch].
    - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
      eapply refine_prov__obs_eq with
        (t1 := Tau (interp_state interp_vellvm_prov_h (k1 tt) (mm1, ((sf1, fstk1), gg1))))
        (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), gg2))).
      + apply inl_model_r_both_obs_eq.
      + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
          norm_subevent;
          cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          norm_subevent.
        unfold fused_memory_prov, on_mem_prov, handle_memory.
        rewrite (store_zero_struct_noop varg mm1), !Eqit.bind_ret_l; reflexivity.
      + reflexivity.
      + eapply RP_TauL; [reflexivity | apply IH, Hmatch].
    - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
      destruct Hmatch as (-> & -> & -> & Hsf & Hsfm).
      eapply refine_prov__obs_eq with
        (t1 := Tau (interp_state interp_vellvm_prov_h (k1 tt)
                      (push_empty_frame mm2, ((sf1, fstk1), g0))))
        (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), g0))).
      + apply inl_model_r_both_obs_eq.
      + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
          norm_subevent;
          cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          norm_subevent.
        unfold fused_memory_prov, on_mem_prov, handle_memory.
        rewrite (mempush_empty_frame mm2), !Eqit.bind_ret_l; reflexivity.
      + reflexivity.
      + eapply RP_TauL; [reflexivity | apply IH].
        cbn [inline_fused_match]; repeat (first [exact Hsf | exact Hsfm | reflexivity | split]).
    - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
      destruct Hmatch as (-> & -> & -> & Hsf & Hsfm).
      set (new_sf1 := {| stack_vars := init_local_env bs;
                         stack_exc  := None;
                         stack_loc  := Some (printer_object.(printer_get_loc) tt) |}).
      eapply refine_prov__obs_eq with
        (t1 := Tau (interp_state interp_vellvm_prov_h (k1 tt)
                      (push_empty_frame mm2, ((new_sf1, sf1 :: fstk1), g0))))
        (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), g0))).
      + apply inl_model_r_both_obs_eq.
      + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
          norm_subevent;
          cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          norm_subevent.
        unfold fused_stack_prov, on_ls_prov, handle_stack.
        cbn - [Maps.lookup Maps.add lift_bot_prov init_local_env].
        rewrite ?lift_bot_prov_bind_ret, ?lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity.
      + reflexivity.
      + eapply RP_TauL; [reflexivity | apply IH].
        cbn [inline_fused_match stack_vars new_sf1].
        split; [reflexivity | split; [reflexivity | split; [reflexivity | split; [reflexivity |]]]].
        exists sf1, fstk1; split; [reflexivity | split; assumption].
    - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
      destruct Hmatch as (-> & -> & -> & _ & csf1 & fstk1' & -> & Hcsf & Hsfm).
      eapply refine_prov__obs_eq with
        (t1 := Tau (interp_state interp_vellvm_prov_h (k1 tt)
                      (push_empty_frame mm2, ((csf1, fstk1'), g0))))
        (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), g0))).
      + apply inl_model_r_both_obs_eq.
      + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
          norm_subevent;
          cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          norm_subevent.
        unfold fused_stack_prov, on_ls_prov, handle_stack.
        cbn - [Maps.lookup Maps.add lift_bot_prov init_local_env].
        rewrite ?lift_bot_prov_bind_ret, ?lift_bot_prov_ret, !Eqit.bind_ret_l; reflexivity.
      + reflexivity.
      + eapply RP_TauL; [reflexivity | apply IH].
        cbn [inline_fused_match]; repeat (first [exact Hcsf | exact Hsfm | reflexivity | split]).
    - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
      destruct Hmatch as (-> & -> & -> & Hsf & Hsfm).
      eapply refine_prov__obs_eq with
        (t1 := Tau (interp_state interp_vellvm_prov_h (k1 tt)
                      (mm2, ((sf1, fstk1), g0))))
        (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), g0))).
      + apply inl_model_r_both_obs_eq.
      + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
          norm_subevent;
          cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          norm_subevent.
        unfold fused_memory_prov, on_mem_prov, handle_memory.
        rewrite (mempop_empty_frame mm2), !Eqit.bind_ret_l; reflexivity.
      + reflexivity.
      + eapply RP_TauL; [reflexivity | apply IH].
        cbn [inline_fused_match]; repeat (first [exact Hsf | exact Hsfm | reflexivity | split]).
  Qed.

  Lemma mcfg_inline_sim_to_model (g0 : global_env) {R1 R2 : Type}
    (RR : inline_ctx -> R1 -> R2 -> Prop) :
    forall U ic (s1 s2 : FusedS)
      (u1 : @MCFGtop PaV R1)
      (u2 : @MCFGtop PaV R2),
      inline_fused_match g0 ic s1 s2 ->
      mcfg_inline_sim g0 true RR ic u1 u2 ->
      refine_prov
        (fun _ '(s1', r1) '(s2', r2) =>
           exists ic', inline_fused_match g0 ic' s1' s2' /\ RR ic' r1 r2)
        U
        (interp_state interp_vellvm_prov_h u1 s1)
        (interp_state interp_vellvm_prov_h u2 s2).
  Proof using.
    assert (Hmain :
      forall U0 t1 t2,
        inl_model_r_both g0 RR U0 t1 t2 ->
        refine_prov (inl_model_rr_out g0 RR) U0 t1 t2).
    { pcofix CIH.
      intros U0 t1 t2 Hrb; pstep.
      eapply refine_prov__mon with (r := inl_model_r_both g0 RR);
        [| intros U1 a1 a2 Hr; right; apply CIH, Hr].
      destruct Hrb as [(ic & s1 & s2 & v1 & v2 & Ev1 & Ev2 & Hm & Hv) | (w1 & w2 & Ew1 & Ew2 & Hw)].
      - eapply inl_model_branch_a; eassumption.
      - eapply inl_model_branch_b; eassumption. }
    intros U ic s1 s2 u1 u2 Hmatch Hsim.
    apply Hmain; left; exists ic, s1, s2, u1, u2;
      split; [reflexivity | split; [reflexivity | split; assumption]].
  Qed.


  (** * 9. Expression, Attribute, Callee Block, and Parameter-Copy Simulations *)

End InliningSemantics.
