(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Shared Pass Infrastructure & Refinement Framework ([CertPasses.PassCommon])

    Purpose:
      Re-exports [ItreeTactics], [PassCommonSyntax], and [PassCommonModel], and
      adds scalar runtime type guarantees, local/stack simulations, the local
      CFG lifter ([lift_cfg_with_args_local_pass]), and [IPtrWellBehaved].

    Trust Contract & Fail-Closed Boundary:
      Proof-only infrastructure and facade module; not extracted to OCaml.
      Lifts per-function [cfg_local_sim]/[cfg_stack_sim] to [prog_refines].

    Assumptions:
      Parametric over [IP : IPtr] and [IPT : @IPtrTheory IP] (plus
      [IPtrWellBehaved] instances for [IPZ]/[IP64Bit]); zero custom axioms.

    Section Outline:
      - [ModelSemantics]: scalar type guarantees, [cfg_local_sim], [IterSim],
        [GenStackSim], [cfg_stack_sim]/[mcfg_stack_sim], and local lifters.
      - [IPtrWellBehaved] class and [IPZ]/[IP64Bit] instances. *)

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
  Structures.Monads
  Structures.Functor.

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
  Semantics.Implementations.IPtrInfinite
  Semantics.Implementations.IPtrFinite
  Semantics.Implementations.Provenance
  Semantics.Implementations.Pointer
  Semantics.Implementations.ParamsV
  Semantics.Implementations.Memory
  Semantics.Handlers
  Semantics.InterpretationStack
  Semantics.TopLevel
  Semantics.Libraries.
From CertPasses.common Require Export
  ItreeTactics.
Export LLVMAst.
Import Logic.

Arguments exp_block_addresses {T} _.
Arguments texps_block_addresses {T} _.
Arguments instr_block_addresses {T} _.
Arguments term_block_addresses {T} _.
Arguments block_block_addresses {T} _.

Set Default Goal Selector "!".
Unset Implicit Arguments.

From CertPasses Require Export PassCommonSyntax PassCommonModel.

Section ModelSemantics.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  Existing Instance MemoryModelStateV.
  Existing Instance MemoryModelPrimitivesV.
  #[local] Hint Resolve refine_prov__mon : paco.
  Arguments memM_interp_prov {_ _} [T] _ _.
  Arguments interp_vellvm_prov_h {_ _} [T] _ _.

  (** ** Scalar Runtime Type Guarantees & Local-Environment Simulation ([cfg_local_sim]) *)

  Definition is_scalar_dtyp_base (dtb : dtyp_base) : bool :=
    match dtb with
    | DTYPE_I _ => true
    | DTYPE_Pointer => true
    | DTYPE_FP FP_float => true
    | DTYPE_FP FP_double => true
    | _ => false
    end.

  Definition is_scalar_dtyp (dt : dtyp) : bool :=
    match dt with
    | DTYPE_Base dtb => is_scalar_dtyp_base dtb
    | _ => false
    end.

  Lemma memory_bytes_to_dvalue_scalar_typ
    (dbs : list (@memory_byte (@ParamsV IP IPT))) (dt : dtyp)
    (dv : @dvalue (@ParamsV IP IPT))
    (Hsc : is_scalar_dtyp dt = true)
    (Hrd : memory_bytes_to_dvalue dbs dt = raise_ret dv) :
    dvalue_has_dtyp dv dt.
  Proof using.
    destruct dt as [dtb | |]; [| discriminate Hsc | discriminate Hsc].
    cbn [is_scalar_dtyp] in Hsc.
    cbn [memory_bytes_to_dvalue] in Hrd.
    destruct dtb as [sz | | | | fp | | | | | | bsz];
      try discriminate Hsc; cbn [memory_bytes_to_dvalue_base] in Hrd.
    - unfold absorb_pois, catch_pois in Hrd.
      destruct (memory_bytes_to_int sz _) as [| | | [z |]]; cbn in Hrd; try discriminate Hrd;
        inversion Hrd; subst dv;
        [apply DVALUE_Base_typ; cbn; [apply Pos.eqb_refl | reflexivity] | apply DVALUE_Poison_typ_agg].
    - unfold absorb_pois, catch_pois in Hrd.
      destruct (memory_bytes_to_pointer _) as [| | | [p |]]; cbn in Hrd; try discriminate Hrd;
        inversion Hrd; subst dv;
        [apply DVALUE_Base_typ; reflexivity | apply DVALUE_Poison_typ_agg].
    - destruct fp; try discriminate Hsc;
        (cbn [memory_bytes_to_dvalue_base] in Hrd;
         unfold absorb_pois, catch_pois in Hrd;
         destruct (map_monad memory_byte_to_Z _) as [| | | [zs |]]; cbn in Hrd; try discriminate Hrd;
         inversion Hrd; subst dv;
         [apply DVALUE_Base_typ; reflexivity | apply DVALUE_Poison_typ_agg]).
  Qed.

  Lemma default_dvalue_scalar_typ (dt : dtyp) (dv : @dvalue (@ParamsV IP IPT))
    (Hsc : is_scalar_dtyp dt = true)
    (Hdef : default_dvalue_of_dtyp dt = raise_ret dv) :
    dvalue_has_dtyp dv dt.
  Proof using.
    destruct dt as [dtb | |]; [| discriminate Hsc | discriminate Hsc].
    cbn [is_scalar_dtyp] in Hsc; cbn [default_dvalue_of_dtyp] in Hdef.
    destruct dtb as [sz | | | | fp | | | | | | bsz]; try discriminate Hsc;
      try (destruct fp; try discriminate Hsc);
      cbn in Hdef; inversion Hdef; subst dv;
      apply DVALUE_Base_typ; cbn; try apply Pos.eqb_refl; reflexivity.
  Qed.

  Fixpoint memM_all_ret {X : Type} (P : X -> Prop)
    (m : @memM (@ParamsV IP IPT) _ X) : Prop :=
    match m with
    | Mret x => P x
    | Moom _ | Mub _ | Merr _ => True
    | Mget k => forall σ, memM_all_ret P (k σ)
    | Mput _ k => memM_all_ret P (k tt)
    | Mchoose _ k => forall c, memM_all_ret P (k c)
    end.

  Lemma memM_all_ret_bind {X Y : Type} (P : X -> Prop) (Q : Y -> Prop)
    (m : @memM (@ParamsV IP IPT) _ X)
    (f : X -> @memM (@ParamsV IP IPT) _ Y)
    (Hm : memM_all_ret P m)
    (Hf : forall x, P x -> memM_all_ret Q (f x)) :
    memM_all_ret Q (ExtLib.Structures.Monad.bind m f).
  Proof using.
    induction m as [x | s | s | s | k IH | σ' k IH | c k IH]; cbn in *;
      [apply Hf, Hm | exact I | exact I | exact I
      | intros σ; apply IH, Hm
      | apply IH, Hm
      | intros ch; apply IH, Hm].
  Qed.

  Lemma memM_all_ret_true {X : Type} (m : @memM (@ParamsV IP IPT) _ X) :
    memM_all_ret (fun _ => True) m.
  Proof using.
    induction m; cbn; auto.
  Qed.

  Definition mcfg_event_post {X : Type} (e : @MCFGEtop (@ParamsV IP IPT) X) (a : X) : Prop :=
    match e return X -> Prop with
    | inl1 _ => fun _ => True
    | inr1 e1 =>
        match e1 return X -> Prop with
        | inl1 _ => fun _ => True
        | inr1 e2 =>
            match e2 return X -> Prop with
            | inl1 _ => fun _ => True
            | inr1 e3 =>
                match e3 return X -> Prop with
                | inl1 _ => fun _ => True
                | inr1 e4 =>
                    match e4 return X -> Prop with
                    | inl1 me =>
                        match me in MemoryE Y return Y -> Prop with
                        | Load dt _ => fun dv => is_scalar_dtyp dt = true -> dvalue_has_dtyp dv dt
                        | Alloca _ _ _ => fun dv => dvalue_has_dtyp dv (DTYPE_Base DTYPE_Pointer)
                        | _ => fun _ => True
                        end
                    | inr1 e5 =>
                        match e5 return X -> Prop with
                        | inl1 de =>
                            match de in DrawE Y return Y -> Prop with
                            | Draw dt => fun dv => is_scalar_dtyp dt = true -> dvalue_has_dtyp dv dt
                            end
                        | inr1 _ => fun _ => True
                        end
                    end
                end
            end
        end
    end a.

  Definition cfg_event_post {X : Type} (e : @CFGEtop (@ParamsV IP IPT) X) (a : X) : Prop :=
    match e return X -> Prop with
    | inl1 _ => fun _ => True
    | inr1 m => mcfg_event_post m
    end a.

  Lemma handle_memoryM_post {X : Type} (me : @MemoryE (@ParamsV IP IPT) X) :
    memM_all_ret
      (match me in MemoryE Y return Y -> Prop with
       | Load dt _ => fun dv => is_scalar_dtyp dt = true -> dvalue_has_dtyp dv dt
       | Alloca _ _ _ => fun dv => dvalue_has_dtyp dv (DTYPE_Base DTYPE_Pointer)
       | _ => fun _ => True
       end)
      (handle_memoryM me).
  Proof using.
    destruct me as [| | t n al | dt a | dt a v | cv tf v tt0]; cbn [handle_memoryM];
      try apply memM_all_ret_true.
    - eapply memM_all_ret_bind; [apply memM_all_ret_true |].
      intros ptr _; cbn; apply DVALUE_Base_typ; reflexivity.
    - destruct a as [[p | | | | | | |] | |]; cbn; try exact I.
      unfold read_dvalue.
      eapply memM_all_ret_bind; [apply memM_all_ret_true |].
      intros bytes _.
      destruct (memory_bytes_to_dvalue bytes dt) as [| | | dv] eqn:Erd; cbn; auto.
      intros Hsc; eapply memory_bytes_to_dvalue_scalar_typ; eassumption.
  Qed.

  Definition not_local_or_stack_push_pop_mcfg {X} (e : @MCFGEtop (@ParamsV IP IPT) X) : bool :=
    match e with
    | inr1 (inr1 (inr1 (inl1 _))) => false
    | _ => true
    end.

  (** Note: [StackRaise] and [StackGetExc] touch only [stack_exc], leaving
      [stack_vars] and the caller stack [stk] intact; we allow them in
      [sync_non_local_mcfg] alongside all non-[LocalE]/[StackE] events. *)
  Definition sync_non_local_mcfg {X} (e : @MCFGEtop (@ParamsV IP IPT) X) : bool :=
    match e with
    | inr1 (inr1 (inr1 (inl1 (inl1 _)))) => false
    | inr1 (inr1 (inr1 (inl1 (inr1 (StackPush _))))) => false
    | inr1 (inr1 (inr1 (inl1 (inr1 StackPop)))) => false
    | _ => true
    end.

  Definition sync_non_local_cfg {X} (e : @CFGEtop (@ParamsV IP IPT) X) : bool :=
    match e with
    | inl1 _ => true
    | inr1 m => sync_non_local_mcfg m
    end.

  Definition is_ub_mcfg {X} (e : @MCFGEtop (@ParamsV IP IPT) X) : bool :=
    match e with
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 (ThrowUB _))))))))) => true
    | _ => false
    end.

  Definition is_ub_cfg {X} (e : @CFGEtop (@ParamsV IP IPT) X) : bool :=
    match e with
    | inl1 _ => false
    | inr1 m => is_ub_mcfg m
    end.

  Lemma lookup_add_eq {V} (k : raw_id) (v : V) (m : rmap V) :
    Maps.lookup k (Maps.add k v m) = Some v.
  Proof using.
    change (RM.find k (RM.add k v m) = Some v).
    apply RMF.F.add_eq_o; reflexivity.
  Qed.

  Lemma lookup_add_neq {V} (k k' : raw_id) (v : V) (m : rmap V) :
    k <> k' ->
    Maps.lookup k' (Maps.add k v m) = Maps.lookup k' m.
  Proof using.
    intros Hne.
    change (RM.find k' (RM.add k v m) = RM.find k' m).
    apply RMF.F.add_neq_o; exact Hne.
  Qed.

  Lemma lookup_empty {V} (k : raw_id) :
    Maps.lookup k (@Maps.empty raw_id V (rmap V) _) = None.
  Proof using.
    change (RM.find k (@RM.empty V) = None).
    apply RMF.F.empty_o.
  Qed.

  Definition init_local_env
    (bs : list (local_id * @dvalue (@ParamsV IP IPT))) : @local_env (@ParamsV IP IPT) :=
    List.fold_right (fun '(x, dv) => Maps.add x dv) Maps.empty bs.

  Lemma init_local_env_in (bs : list (local_id * @dvalue (@ParamsV IP IPT))) (x : local_id) :
    In x (List.map fst bs) ->
    exists v, Maps.lookup x (init_local_env bs) = Some v.
  Proof using.
    induction bs as [| [k dv] rest IH]; intros Hin; [contradiction |].
    cbn [List.map fst] in Hin; change (init_local_env ((k, dv) :: rest)) with (Maps.add k dv (init_local_env rest)).
    destruct (RawIDOrd.eq_dec k x) as [<- | Hne].
    - exists dv; apply lookup_add_eq.
    - destruct Hin as [Heq | Hin]; [contradiction |].
      destruct (IH Hin) as [v Hv]; exists v.
      change (RM.find x (RM.add k dv (init_local_env rest)) = Some v);
      rewrite RMF.F.add_neq_o by exact Hne; exact Hv.
  Qed.

  Lemma combine_lists_varargs_dom {A B} (l1 : list A) (l2 : list B)
    (bs : list (A * B)) (vs : list B) :
    combine_lists_varargs l1 l2 = raise_ret (bs, vs) ->
    List.map fst bs = l1.
  Proof using.
    revert l2 bs vs; induction l1 as [| x xs IH]; intros [| y ys] bs vs Hc; cbn in Hc.
    - inversion Hc; reflexivity.
    - inversion Hc; reflexivity.
    - discriminate Hc.
    - destruct (combine_lists_varargs xs ys) as [| | | [l vargs]] eqn:E; cbn in Hc; try discriminate Hc.
      inversion Hc; subst; cbn; f_equal; eapply IH, E.
  Qed.

  (** *** Per-CFG Local-Environment Simulation ([cfg_local_sim]) *)

  Definition cls_vis_both {R1 R2}
    (r : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
         @CFGtop (@ParamsV IP IPT) R1 -> @CFGtop (@ParamsV IP IPT) R2 -> Prop)
    (env1 env2 : @local_env (@ParamsV IP IPT))
    {X1} (e1 : @CFGEtop (@ParamsV IP IPT) X1) (k1 : X1 -> @CFGtop (@ParamsV IP IPT) R1)
    {X2} (e2 : @CFGEtop (@ParamsV IP IPT) X2) (k2 : X2 -> @CFGtop (@ParamsV IP IPT) R2) : Prop :=
    (sync_non_local_cfg e1 = true /\
     EqE_CFG X1 X2 e1 e2 /\
     forall a1 a2,
       EqA_CFG X1 X2 e1 a1 e2 a2 ->
       cfg_event_post e1 a1 ->
       r env1 env2 (k1 a1) (k2 a2))
    \/
    (match e1 return (X1 -> @CFGtop (@ParamsV IP IPT) R1) -> Prop with
     | inr1 (inr1 (inr1 (inr1 (inl1 (inl1 le1))))) => fun k10 =>
         match e2 return (X2 -> @CFGtop (@ParamsV IP IPT) R2) -> Prop with
         | inr1 (inr1 (inr1 (inr1 (inl1 (inl1 le2))))) => fun k20 =>
             match le1 in LocalE Y1 return (Y1 -> @CFGtop (@ParamsV IP IPT) R1) -> Prop with
             | LocalRead x1 => fun k1' =>
                 match le2 in LocalE Y2 return (Y2 -> @CFGtop (@ParamsV IP IPT) R2) -> Prop with
                 | LocalRead x2 => fun k2' =>
                     x1 = x2 /\
                     Maps.lookup x1 env1 = Maps.lookup x1 env2 /\
                     forall v, Maps.lookup x1 env1 = Some v -> r env1 env2 (k1' v) (k2' v)
                 | _ => fun _ => False
                 end k20
             | _ => fun _ => False
             end k10
         | _ => fun _ => False
         end k2
     | _ => fun _ => False
     end k1).

  Definition cls_step_body {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    (r : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
         @CFGtop (@ParamsV IP IPT) R1 -> @CFGtop (@ParamsV IP IPT) R2 -> Prop)
    (env1 env2 : @local_env (@ParamsV IP IPT))
    (ot1 : itree' (@CFGEtop (@ParamsV IP IPT)) R1)
    (ot2 : itree' (@CFGEtop (@ParamsV IP IPT)) R2) : Prop :=
    match ot1 with
    | RetF r1 =>
        match ot2 with
        | RetF r2 => RR env1 env2 r1 r2
        | _ => False
        end
    | TauF m1 =>
        match ot2 with
        | TauF m2 => r env1 env2 m1 m2
        | _ => False
        end
    | VisF _ e1 k1 =>
        is_ub_cfg e1 = true \/
        match ot2 with
        | VisF _ e2 k2 => cls_vis_both r env1 env2 e1 k1 e2 k2
        | _ => False
        end
    end.

  Inductive cfg_local_sim_ {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    (r : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
         @CFGtop (@ParamsV IP IPT) R1 -> @CFGtop (@ParamsV IP IPT) R2 -> Prop)
    : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
      @CFGtop (@ParamsV IP IPT) R1 -> @CFGtop (@ParamsV IP IPT) R2 -> Prop :=
  | CLS_Step env1 env2 t1 t2 :
      cls_step_body RR r env1 env2 (observe t1) (observe t2) ->
      cfg_local_sim_ RR r env1 env2 t1 t2
  | CLS_TauL env1 env2 t1 m1 t2 :
      observe t1 = TauF m1 ->
      cfg_local_sim_ RR r env1 env2 m1 t2 ->
      cfg_local_sim_ RR r env1 env2 t1 t2
  | CLS_TauR env1 env2 t1 t2 m2 :
      observe t2 = TauF m2 ->
      cfg_local_sim_ RR r env1 env2 t1 m2 ->
      cfg_local_sim_ RR r env1 env2 t1 t2
  | CLS_ReadL env1 env2 t1 x v k1 t2 :
      t1 ≅ ITree.bind (ITree.trigger (subevent _ (LocalRead x))) k1 ->
      Maps.lookup x env1 = Some v ->
      cfg_local_sim_ RR r env1 env2 (k1 v) t2 ->
      cfg_local_sim_ RR r env1 env2 t1 t2
  | CLS_ReadR env1 env2 t1 t2 x v k2 :
      t2 ≅ ITree.bind (ITree.trigger (subevent _ (LocalRead x))) k2 ->
      Maps.lookup x env2 = Some v ->
      cfg_local_sim_ RR r env1 env2 t1 (k2 v) ->
      cfg_local_sim_ RR r env1 env2 t1 t2
  | CLS_WriteL env1 env2 t1 x v k1 t2 :
      t1 ≅ ITree.bind (ITree.trigger (subevent _ (LocalWrite x v))) k1 ->
      cfg_local_sim_ RR r (Maps.add x v env1) env2 (k1 tt) t2 ->
      cfg_local_sim_ RR r env1 env2 t1 t2
  | CLS_WriteR env1 env2 t1 t2 x v k2 :
      t2 ≅ ITree.bind (ITree.trigger (subevent _ (LocalWrite x v))) k2 ->
      cfg_local_sim_ RR r env1 (Maps.add x v env2) t1 (k2 tt) ->
      cfg_local_sim_ RR r env1 env2 t1 t2.

  Lemma cfg_local_sim__mon {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    monotone4 (cfg_local_sim_ RR).
  Proof using.
    intros env1 env2 t1 t2 r r' IN LE.
    induction IN as [env1 env2 t1 t2 Hstep
                     | env1 env2 t1 m1 t2 Ht1 _ IH
                     | env1 env2 t1 t2 m2 Ht2 _ IH
                     | env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                     | env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                     | env1 env2 t1 x v k1 t2 Ht1 _ IH
                     | env1 env2 t1 t2 x v k2 Ht2 _ IH].
    - apply CLS_Step; unfold cls_step_body in *.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1].
      + exact Hstep.
      + destruct (observe t2); [exact Hstep | apply LE, Hstep | exact Hstep].
      + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct (observe t2) as [r2 | m2 | X2 e2 k2]; try contradiction.
        destruct Hvis as [(Hsync & HE & HA) | Hrd].
        * left; split; [exact Hsync | split; [exact HE | intros a1 a2 Ha Hp; apply LE, (HA a1 a2 Ha Hp)]].
        * right.
          destruct_sum1 e1; try contradiction;
            destruct e1 as [x1 |]; try contradiction;
            destruct_sum1 e2; try contradiction;
            destruct e2 as [x2 |]; try contradiction.
          destruct Hrd as (Hx & Hlk & Hk); split; [exact Hx | split; [exact Hlk | intros v Hv; apply LE, Hk, Hv]].
    - eapply CLS_TauL; [exact Ht1 | exact IH].
    - eapply CLS_TauR; [exact Ht2 | exact IH].
    - eapply CLS_ReadL; [exact Ht1 | exact Hlk | exact IH].
    - eapply CLS_ReadR; [exact Ht2 | exact Hlk | exact IH].
    - eapply CLS_WriteL; [exact Ht1 | exact IH].
    - eapply CLS_WriteR; [exact Ht2 | exact IH].
  Qed.
  #[local] Hint Resolve cfg_local_sim__mon : paco.

  Definition cfg_local_sim {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    (env1 env2 : @local_env (@ParamsV IP IPT))
    (t1 : @CFGtop (@ParamsV IP IPT) R1)
    (t2 : @CFGtop (@ParamsV IP IPT) R2) : Prop :=
    paco4 (cfg_local_sim_ RR) bot4 env1 env2 t1 t2.

  Lemma cfg_local_sim__obs_eq {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    (r r' : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
            @CFGtop (@ParamsV IP IPT) R1 -> @CFGtop (@ParamsV IP IPT) R2 -> Prop)
    (Hr_eq : forall env1 env2 a1 a1' a2 a2',
               a1 ≅ a1' -> a2 ≅ a2' -> r env1 env2 a1 a2 -> r' env1 env2 a1' a2') :
    forall env1 env2 t1 t1' t2 t2',
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      cfg_local_sim_ RR r env1 env2 t1 t2 ->
      cfg_local_sim_ RR r' env1 env2 t1' t2'.
  Proof using.
    intros env1 env2 t1 t1' t2 t2' E1 E2 Hsim.
    revert t1' t2' E1 E2;
      induction Hsim as [env1 env2 t1 t2 Hstep
                         | env1 env2 t1 m1 t2 Ht1 _ IH
                         | env1 env2 t1 t2 m2 Ht2 _ IH
                         | env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                         | env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                         | env1 env2 t1 x v k1 t2 Ht1 _ IH
                         | env1 env2 t1 t2 x v k2 Ht2 _ IH];
      intros t1' t2' E1 E2.
    - punfold E1; red in E1; punfold E2; red in E2.
      apply CLS_Step; unfold cls_step_body in *.
      destruct E1 as [r1 r1' <- | m1 m1' Hm1 | X1 e1 k1 k1' Hk1 | ? ? Hchk _ | ? ? Hchk _];
        try inversion Hchk; pclearbot.
      + destruct E2 as [r2 r2' <- | | | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; try contradiction; exact Hstep.
      + destruct E2 as [| m2 m2' Hm2 | | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; try contradiction; pclearbot.
        eapply Hr_eq; [exact Hm1 | exact Hm2 | exact Hstep].
      + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct E2 as [| | X2 e2 k2 k2' Hk2 | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; try contradiction; pclearbot.
        destruct Hvis as [(Hsync & HE & HA) | Hrd].
        * left; split; [exact Hsync | split; [exact HE |]].
          intros a1 a2 Ha Hp; eapply Hr_eq; [apply Hk1 | apply Hk2 | exact (HA a1 a2 Ha Hp)].
        * right.
          destruct_sum1 e1; try contradiction;
            destruct e1 as [x1 |]; try contradiction;
            destruct_sum1 e2; try contradiction;
            destruct e2 as [x2 |]; try contradiction.
          destruct Hrd as (Hx & Hlk & Hk); split; [exact Hx | split; [exact Hlk |]].
          intros v Hv; eapply Hr_eq; [apply Hk1 | apply Hk2 | apply Hk, Hv].
    - punfold E1; red in E1; rewrite Ht1 in E1;
        apply eqitF_inv_Tau_l in E1 as (m1' & E1b & Hm1); pclearbot.
      eapply CLS_TauL; [exact E1b | eapply IH; [exact Hm1 | exact E2]].
    - punfold E2; red in E2; rewrite Ht2 in E2;
        apply eqitF_inv_Tau_l in E2 as (m2' & E2b & Hm2); pclearbot.
      eapply CLS_TauR; [exact E2b | eapply IH; [exact E1 | exact Hm2]].
    - eapply CLS_ReadL;
        [ symmetry; etransitivity; [symmetry; exact Ht1 | exact E1]
        | exact Hlk
        | apply IH; [reflexivity | exact E2] ].
    - eapply CLS_ReadR;
        [ symmetry; etransitivity; [symmetry; exact Ht2 | exact E2]
        | exact Hlk
        | apply IH; [exact E1 | reflexivity] ].
    - eapply CLS_WriteL;
        [ symmetry; etransitivity; [symmetry; exact Ht1 | exact E1]
        | apply IH; [reflexivity | exact E2] ].
    - eapply CLS_WriteR;
        [ symmetry; etransitivity; [symmetry; exact Ht2 | exact E2]
        | apply IH; [exact E1 | reflexivity] ].
  Qed.

  Lemma cfg_local_sim_obs_eq {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    forall env1 env2 t1 t1' t2 t2',
      t1 ≅ t1' ->
      t2 ≅ t2' ->
      cfg_local_sim RR env1 env2 t1 t2 ->
      cfg_local_sim RR env1 env2 t1' t2'.
  Proof using.
    pcofix CIH.
    intros env1 env2 t1 t1' t2 t2' E1 E2 Hsim.
    pstep; punfold Hsim.
    eapply cfg_local_sim__obs_eq; [| exact E1 | exact E2 | exact Hsim].
    intros e1 e2 a1 a1' a2 a2' Ea1 Ea2 Hr; pclearbot.
    right; eapply CIH; [exact Ea1 | exact Ea2 | exact Hr].
  Qed.

  Lemma cfg_local_sim_ret {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    env1 env2 (r1 : R1) (r2 : R2) :
    RR env1 env2 r1 r2 ->
    cfg_local_sim RR env1 env2 (Ret r1) (Ret r2).
  Proof using.
    intros HRR; pstep; apply CLS_Step; cbn; exact HRR.
  Qed.

  Lemma cfg_local_sim_bind {R1 R2 S1 S2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    (RS : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> S1 -> S2 -> Prop)
    env1 env2
    (t1 : @CFGtop (@ParamsV IP IPT) R1) (t2 : @CFGtop (@ParamsV IP IPT) R2)
    (k1 : R1 -> @CFGtop (@ParamsV IP IPT) S1) (k2 : R2 -> @CFGtop (@ParamsV IP IPT) S2)
    (Ht : cfg_local_sim RR env1 env2 t1 t2)
    (Hk : forall env1' env2' r1 r2,
            RR env1' env2' r1 r2 -> cfg_local_sim RS env1' env2' (k1 r1) (k2 r2)) :
    cfg_local_sim RS env1 env2 (ITree.bind t1 k1) (ITree.bind t2 k2).
  Proof using.
    revert env1 env2 t1 t2 Ht Hk; pcofix CIH; intros env1 env2 t1 t2 Ht Hk.
    punfold Ht.
    revert Hk;
      induction Ht as [env1 env2 t1 t2 Hstep
                       | env1 env2 t1 m1 t2 Ht1 _ IH
                       | env1 env2 t1 t2 m2 Ht2 _ IH
                       | env1 env2 t1 x v k1' t2 Ht1 Hlk _ IH
                       | env1 env2 t1 t2 x v k2' Ht2 Hlk _ IH
                       | env1 env2 t1 x v k1' t2 Ht1 _ IH
                       | env1 env2 t1 t2 x v k2' Ht2 _ IH];
      intros Hk.
    - unfold cls_step_body in Hstep.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1'] eqn:Hot1.
      + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
        eapply paco4_mon;
          [eapply cfg_local_sim_obs_eq;
             [symmetry; rewrite (itree_eta t1), Hot1, Eqit.bind_ret_l; reflexivity
             | symmetry; rewrite (itree_eta t2), Hot2, Eqit.bind_ret_l; reflexivity
             | exact (Hk env1 env2 r1 r2 Hstep)]
          | intros ? ? ? ? []].
      + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction; pclearbot.
        pstep; apply CLS_Step; unfold cls_step_body.
        rewrite (observe_bind t1 k1), Hot1, (observe_bind t2 k2), Hot2.
        right; eapply CIH; [exact Hstep | exact Hk].
      + pstep; apply CLS_Step; unfold cls_step_body.
        rewrite (observe_bind t1 k1), Hot1.
        destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
        rewrite (observe_bind t2 k2), Hot2.
        destruct Hvis as [(Hsync & HE & HA) | Hrd].
        * left; split; [exact Hsync | split; [exact HE |]].
          intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); pclearbot.
          right; eapply CIH; [exact HA | exact Hk].
        * right.
          destruct_sum1 e1; try contradiction;
            destruct e1 as [x1 |]; try contradiction;
            destruct_sum1 e2; try contradiction;
            destruct e2 as [x2 |]; try contradiction.
          destruct Hrd as (Hx & Hlk & Hrd'); split; [exact Hx | split; [exact Hlk |]].
          intros v Hv; specialize (Hrd' v Hv); pclearbot.
          right; eapply CIH; [exact Hrd' | exact Hk].
    - specialize (IH Hk); punfold IH; pstep.
      eapply CLS_TauL; [rewrite (observe_bind t1 k1), Ht1; reflexivity | exact IH].
    - specialize (IH Hk); punfold IH; pstep.
      eapply CLS_TauR; [rewrite (observe_bind t2 k2), Ht2; reflexivity | exact IH].
    - specialize (IH Hk); punfold IH; pstep.
      eapply CLS_ReadL; [rewrite Ht1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
    - specialize (IH Hk); punfold IH; pstep.
      eapply CLS_ReadR; [rewrite Ht2, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
    - specialize (IH Hk); punfold IH; pstep.
      eapply CLS_WriteL; [rewrite Ht1, Eqit.bind_bind; reflexivity | exact IH].
    - specialize (IH Hk); punfold IH; pstep.
      eapply CLS_WriteR; [rewrite Ht2, Eqit.bind_bind; reflexivity | exact IH].
  Qed.

  Lemma cfg_local_sim_weaken {R1 R2}
    (RR RS : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    (HRR : forall env1 env2 r1 r2, RR env1 env2 r1 r2 -> RS env1 env2 r1 r2) :
    forall env1 env2 t1 t2,
      cfg_local_sim RR env1 env2 t1 t2 ->
      cfg_local_sim RS env1 env2 t1 t2.
  Proof using.
    intros env1 env2 t1 t2 Hsim.
    eapply cfg_local_sim_obs_eq;
      [apply Eqit.bind_ret_r | apply Eqit.bind_ret_r |].
    eapply cfg_local_sim_bind; [exact Hsim |].
    intros e1 e2 r1 r2 Hr; apply cfg_local_sim_ret, HRR, Hr.
  Qed.

  Section IterSim.
    Context {I1 I2 R1 R2 : Type}.
    Variable (RI : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> I1 -> I2 -> Prop).
    Variable (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop).
    Variable (body1 : I1 -> @CFGtop (@ParamsV IP IPT) (I1 + R1)).
    Variable (body2 : I2 -> @CFGtop (@ParamsV IP IPT) (I2 + R2)).

    Definition iter_cont1 (lr : I1 + R1) : @CFGtop (@ParamsV IP IPT) R1 :=
      match lr with
      | inl j1 => Tau (ITree.iter body1 j1)
      | inr r1 => Ret r1
      end.

    Definition iter_cont2 (lr : I2 + R2) : @CFGtop (@ParamsV IP IPT) R2 :=
      match lr with
      | inl j2 => Tau (ITree.iter body2 j2)
      | inr r2 => Ret r2
      end.

    Definition iter_step_rel
      (e1 e2 : @local_env (@ParamsV IP IPT)) (s1 : I1 + R1) (s2 : I2 + R2) : Prop :=
      match s1, s2 with
      | inl j1, inl j2 => RI e1 e2 j1 j2
      | inr r1, inr r2 => RR e1 e2 r1 r2
      | _, _ => False
      end.

    Lemma cfg_local_sim_iter_aux
      (Hbody : forall env1 env2 i1 i2,
                 RI env1 env2 i1 i2 ->
                 cfg_local_sim iter_step_rel env1 env2 (body1 i1) (body2 i2)) :
      forall env1 env2
        (w1 : @CFGtop (@ParamsV IP IPT) (I1 + R1))
        (w2 : @CFGtop (@ParamsV IP IPT) (I2 + R2))
        (t1 : @CFGtop (@ParamsV IP IPT) R1)
        (t2 : @CFGtop (@ParamsV IP IPT) R2),
        ITree.bind w1 iter_cont1 ≅ t1 ->
        ITree.bind w2 iter_cont2 ≅ t2 ->
        cfg_local_sim iter_step_rel env1 env2 w1 w2 ->
        cfg_local_sim RR env1 env2 t1 t2.
    Proof using.
      pcofix CIH.
      intros env1 env2 w1 w2 t1 t2 Et1 Et2 Hw.
      pstep.
      set (r_rel := fun e1 e2 a1 a2 =>
                      exists v1 v2,
                        ITree.bind v1 iter_cont1 ≅ a1 /\
                        ITree.bind v2 iter_cont2 ≅ a2 /\
                        cfg_local_sim iter_step_rel e1 e2 v1 v2).
      assert (Hr_eq : forall e1 e2 a1 a1' a2 a2',
                a1 ≅ a1' -> a2 ≅ a2' -> r_rel e1 e2 a1 a2 -> r_rel e1 e2 a1' a2').
      { intros e1 e2 a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv).
        exists v1, v2; split;
          [ etransitivity; [exact Ev1 | exact Ea1]
          | split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv] ]. }
      eapply cfg_local_sim__mon with (r := r_rel);
        [| intros e1 e2 a1 a2 (v1 & v2 & Ev1 & Ev2 & Hv);
           right; eapply CIH; [exact Ev1 | exact Ev2 | exact Hv]].
      eapply cfg_local_sim__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
      punfold Hw; clear t1 t2 Et1 Et2 CIH r.
      induction Hw as [e1 e2 w1 w2 Hstep
                       | e1 e2 w1 mw1 w2 Hw1 _ IH
                       | e1 e2 w1 w2 mw2 Hw2 _ IH
                       | e1 e2 w1 x v kw1 w2 Hw1 Hlk _ IH
                       | e1 e2 w1 w2 x v kw2 Hw2 Hlk _ IH
                       | e1 e2 w1 x v kw1 w2 Hw1 _ IH
                       | e1 e2 w1 w2 x v kw2 Hw2 _ IH].
      - unfold cls_step_body in Hstep.
        destruct (observe w1) as [x1 | mw1 | X1 ev1 kw1] eqn:How1.
        + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          destruct x1 as [j1 | r1], x2 as [j2 | r2]; cbn in Hstep; try contradiction.
          * apply CLS_Step; unfold cls_step_body.
            rewrite (observe_bind w1 iter_cont1), How1,
                    (observe_bind w2 iter_cont2), How2; cbn.
            exists (body1 j1), (body2 j2).
            split; [symmetry; apply unfold_iter |].
            split; [symmetry; apply unfold_iter |].
            apply Hbody, Hstep.
          * apply CLS_Step; unfold cls_step_body.
            rewrite (observe_bind w1 iter_cont1), How1,
                    (observe_bind w2 iter_cont2), How2; cbn.
            exact Hstep.
        + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction; pclearbot.
          apply CLS_Step; unfold cls_step_body.
          rewrite (observe_bind w1 iter_cont1), How1,
                  (observe_bind w2 iter_cont2), How2.
          exists mw1, mw2; split; [reflexivity | split; [reflexivity | exact Hstep]].
        + apply CLS_Step; unfold cls_step_body.
          rewrite (observe_bind w1 iter_cont1), How1.
          destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          rewrite (observe_bind w2 iter_cont2), How2.
          destruct Hvis as [(Hsync & HE & HA) | Hrd].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); pclearbot.
            exists (kw1 a1), (kw2 a2); split; [reflexivity | split; [reflexivity | exact HA]].
          * right.
            destruct_sum1 ev1; try contradiction;
              destruct ev1 as [x1 |]; try contradiction;
              destruct_sum1 ev2; try contradiction;
              destruct ev2 as [x2 |]; try contradiction.
            destruct Hrd as (Hx & Hlk & Hrd'); split; [exact Hx | split; [exact Hlk |]].
            intros v Hv; specialize (Hrd' v Hv); pclearbot.
            exists (kw1 v), (kw2 v); split; [reflexivity | split; [reflexivity | exact Hrd']].
      - eapply CLS_TauL; [rewrite (observe_bind w1 iter_cont1), Hw1; reflexivity | exact IH].
      - eapply CLS_TauR; [rewrite (observe_bind w2 iter_cont2), Hw2; reflexivity | exact IH].
      - eapply CLS_ReadL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply CLS_ReadR; [rewrite Hw2, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply CLS_WriteL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply CLS_WriteR; [rewrite Hw2, Eqit.bind_bind; reflexivity | exact IH].
    Qed.
  End IterSim.

  Lemma cfg_local_sim_iter {I1 I2 R1 R2}
    (RI : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> I1 -> I2 -> Prop)
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    (body1 : I1 -> @CFGtop (@ParamsV IP IPT) (I1 + R1))
    (body2 : I2 -> @CFGtop (@ParamsV IP IPT) (I2 + R2))
    (Hbody : forall env1 env2 i1 i2,
               RI env1 env2 i1 i2 ->
               cfg_local_sim (iter_step_rel RI RR) env1 env2 (body1 i1) (body2 i2)) :
    forall env1 env2 i1 i2,
      RI env1 env2 i1 i2 ->
      cfg_local_sim RR env1 env2 (ITree.iter body1 i1) (ITree.iter body2 i2).
  Proof using.
    intros env1 env2 i1 i2 Hi.
    eapply (cfg_local_sim_iter_aux RI RR body1 body2 Hbody).
    - symmetry; apply unfold_iter.
    - symmetry; apply unfold_iter.
    - apply Hbody, Hi.
  Qed.

  Lemma is_ub_cfg_exc_none {X} (e : @CFGEtop (@ParamsV IP IPT) X) :
    is_ub_cfg e = true -> exc_of_event e = None.
  Proof using.
    destruct e as [c | m]; [discriminate |].
    destruct_sum1 m; try discriminate; destruct m; reflexivity.
  Qed.

  #[local] Instance Proper_run_exc {A : Type} :
    Proper (eq_itree Logic.eq ==> eq_itree Logic.eq)
      (@run_exc (@ParamsV IP IPT) A).
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
          gstep; constructor; gfinal; left; exact (CIH (k1 y) (k2 y) (Hk y)).
  Qed.

  #[local] Lemma run_exc_vis_eq {A X} (e : @CFGEtop (@ParamsV IP IPT) X) (k : X -> @CFGtop (@ParamsV IP IPT) A) :
    exc_of_event e = None ->
    run_exc (Vis e k) ≅ Vis e (fun y => Tau (run_exc (k y))).
  Proof using.
    intros Hnone; rewrite unfold_run_exc_obs; cbn - [exc_of_event run_exc]; rewrite Hnone; reflexivity.
  Qed.

  Lemma cfg_local_sim_run_exc_aux {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    let Rexc := fun e1 e2 (s1 : exc + R1) (s2 : exc + R2) =>
                  match s1 with
                  | inl x1 => match s2 with inl x2 => x1 = x2 | inr _ => False end
                  | inr r1 => match s2 with inl _ => False | inr r2 => RR e1 e2 r1 r2 end
                  end in
    forall env1 env2
      (u1 : @CFGtop (@ParamsV IP IPT) R1)
      (u2 : @CFGtop (@ParamsV IP IPT) R2)
      (t1 : @CFGtop (@ParamsV IP IPT) (exc + R1))
      (t2 : @CFGtop (@ParamsV IP IPT) (exc + R2)),
      run_exc u1 ≅ t1 ->
      run_exc u2 ≅ t2 ->
      cfg_local_sim RR env1 env2 u1 u2 ->
      cfg_local_sim Rexc env1 env2 t1 t2.
  Proof using.
    cbv zeta; set (Rexc := fun e1 e2 (s1 : exc + R1) (s2 : exc + R2) =>
                             match s1 with
                             | inl x1 => match s2 with inl x2 => x1 = x2 | inr _ => False end
                             | inr r1 => match s2 with inl _ => False | inr r2 => RR e1 e2 r1 r2 end
                             end).
    pcofix CIH.
    intros env1 env2 u1 u2 t1 t2 Et1 Et2 Hsim.
    pstep.
    set (r_rel := fun e1 e2 a1 a2 =>
                    exists v1 v2,
                      run_exc v1 ≅ a1 /\
                      run_exc v2 ≅ a2 /\
                      cfg_local_sim RR e1 e2 v1 v2).
    assert (Hr_eq : forall e1 e2 a1 a1' a2 a2',
              a1 ≅ a1' -> a2 ≅ a2' -> r_rel e1 e2 a1 a2 -> r_rel e1 e2 a1' a2').
    { intros e1 e2 a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv).
      exists v1, v2; split;
        [ etransitivity; [exact Ev1 | exact Ea1]
        | split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv] ]. }
    eapply cfg_local_sim__mon with (r := r_rel);
      [| intros e1 e2 a1 a2 (v1 & v2 & Ev1 & Ev2 & Hv);
         right; eapply CIH; [exact Ev1 | exact Ev2 | exact Hv]].
    eapply cfg_local_sim__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
    punfold Hsim; clear t1 t2 Et1 Et2 CIH r.
    induction Hsim as [e1 e2 u1 u2 Hstep
                       | e1 e2 u1 mu1 u2 Hu1 _ IH
                       | e1 e2 u1 u2 mu2 Hu2 _ IH
                       | e1 e2 u1 x v k1 u2 Hu1 Hlk _ IH
                       | e1 e2 u1 u2 x v k2 Hu2 Hlk _ IH
                       | e1 e2 u1 x v k1 u2 Hu1 _ IH
                       | e1 e2 u1 u2 x v k2 Hu2 _ IH].
    - eapply cfg_local_sim__obs_eq;
        [exact Hr_eq | symmetry; apply unfold_run_exc_obs | symmetry; apply unfold_run_exc_obs |].
      unfold cls_step_body in Hstep.
      destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        apply CLS_Step; cbn; exact Hstep.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction; pclearbot.
        apply CLS_Step; cbn.
        exists m1, m2; split; [reflexivity | split; [reflexivity | exact Hstep]].
      + destruct Hstep as [Hub | Hvis].
        * rewrite (is_ub_cfg_exc_none ev1 Hub).
          apply CLS_Step; cbn; left; exact Hub.
        * destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | Hrd].
          -- rewrite (EqE_CFG_exc_of_event ev1 ev2 HE).
             destruct (exc_of_event ev2) as [ex |].
             ++ apply CLS_Step; cbn; reflexivity.
             ++ apply CLS_Step; cbn; right; left.
                split; [exact Hsync | split; [exact HE |]].
                intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); pclearbot.
                exists (Tau (k1 a1)), (Tau (k2 a2)).
                split; [rewrite unfold_run_exc_obs; reflexivity |].
                split; [rewrite unfold_run_exc_obs; reflexivity |].
                pstep; eapply CLS_TauL; [reflexivity |];
                  eapply CLS_TauR; [reflexivity |].
                punfold HA; exact HA.
          -- destruct_sum1 ev1; try contradiction;
               destruct ev1 as [x1 |]; try contradiction;
               destruct_sum1 ev2; try contradiction;
               destruct ev2 as [x2 |]; try contradiction.
             destruct Hrd as (Hx & Hlk & Hrd'); cbn [exc_of_event].
             apply CLS_Step; cbn; right; right.
             split; [exact Hx | split; [exact Hlk |]].
             intros v Hv; specialize (Hrd' v Hv); pclearbot.
             exists (Tau (k1 v)), (Tau (k2 v)).
             split; [rewrite unfold_run_exc_obs; reflexivity |].
             split; [rewrite unfold_run_exc_obs; reflexivity |].
             pstep; eapply CLS_TauL; [reflexivity |];
               eapply CLS_TauR; [reflexivity |].
             punfold Hrd'; exact Hrd'.
    - eapply cfg_local_sim__obs_eq with (t1 := Tau (run_exc mu1)) (t2 := run_exc u2);
        [exact Hr_eq | symmetry; rewrite (unfold_run_exc_obs u1), Hu1; reflexivity | reflexivity |].
      eapply CLS_TauL; [reflexivity | exact IH].
    - eapply cfg_local_sim__obs_eq with (t1 := run_exc u1) (t2 := Tau (run_exc mu2));
        [exact Hr_eq | reflexivity | symmetry; rewrite (unfold_run_exc_obs u2), Hu2; reflexivity |].
      eapply CLS_TauR; [reflexivity | exact IH].
    - eapply CLS_ReadL with (x := x) (k1 := fun y => Tau (run_exc (k1 y))).
      + rewrite Hu1, !bind_trigger, run_exc_vis_eq; [reflexivity | reflexivity].
      + exact Hlk.
      + eapply CLS_TauL; [reflexivity | exact IH].
    - eapply CLS_ReadR with (x := x) (k2 := fun y => Tau (run_exc (k2 y))).
      + rewrite Hu2, !bind_trigger, run_exc_vis_eq; [reflexivity | reflexivity].
      + exact Hlk.
      + eapply CLS_TauR; [reflexivity | exact IH].
    - eapply CLS_WriteL with (x := x) (v := v) (k1 := fun y => Tau (run_exc (k1 y))).
      + rewrite Hu1, !bind_trigger, run_exc_vis_eq; [reflexivity | reflexivity].
      + eapply CLS_TauL; [reflexivity | exact IH].
    - eapply CLS_WriteR with (x := x) (v := v) (k2 := fun y => Tau (run_exc (k2 y))).
      + rewrite Hu2, !bind_trigger, run_exc_vis_eq; [reflexivity | reflexivity].
      + eapply CLS_TauR; [reflexivity | exact IH].
  Qed.

  Lemma cfg_local_sim_run_exc {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    forall env1 env2
      (t1 : @CFGtop (@ParamsV IP IPT) R1)
      (t2 : @CFGtop (@ParamsV IP IPT) R2),
      cfg_local_sim RR env1 env2 t1 t2 ->
      cfg_local_sim
        (fun e1 e2 (s1 : exc + R1) (s2 : exc + R2) =>
           match s1 with
           | inl x1 => match s2 with inl x2 => x1 = x2 | inr _ => False end
           | inr r1 => match s2 with inl _ => False | inr r2 => RR e1 e2 r1 r2 end
           end)
        env1 env2 (run_exc t1) (run_exc t2).
  Proof using.
    intros env1 env2 t1 t2 Hsim.
    eapply (cfg_local_sim_run_exc_aux RR); [reflexivity | reflexivity | exact Hsim].
  Qed.

  (** *** Call-Stack Simulation ([cfg_stack_sim] / [mcfg_stack_sim]) & [lift_cfg_local_pass] *)

  Definition env_stack := list (@local_env (@ParamsV IP IPT) * @local_env (@ParamsV IP IPT)).

  Definition css_vis_both {E : Type -> Type}
    (is_sync : forall X, E X -> bool)
    (EqE : prerel E E) (EqA : postrel E E)
    (ev_post : forall X, E X -> X -> Prop)
    (as_local : forall X, E X -> option (LocalE X))
    (as_stack : forall X, E X -> option (@StackE (@ParamsV IP IPT) X))
    {R1 R2}
    (r : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
         itree E R1 -> itree E R2 -> Prop)
    (stk : env_stack)
    (env1 env2 : @local_env (@ParamsV IP IPT))
    {X1} (e1 : E X1) (k1 : X1 -> itree E R1)
    {X2} (e2 : E X2) (k2 : X2 -> itree E R2) : Prop :=
    (is_sync X1 e1 = true /\
     EqE X1 X2 e1 e2 /\
     forall a1 a2,
       EqA X1 X2 e1 a1 e2 a2 ->
       ev_post X1 e1 a1 ->
       r stk env1 env2 (k1 a1) (k2 a2))
    \/
    (match as_local X1 e1, as_local X2 e2 with
     | Some le1, Some le2 =>
         match le1 in LocalE Y1 return (Y1 -> itree E R1) -> Prop with
         | LocalRead x1 => fun k1' =>
             match le2 in LocalE Y2 return (Y2 -> itree E R2) -> Prop with
             | LocalRead x2 => fun k2' =>
                 x1 = x2 /\
                 Maps.lookup x1 env1 = Maps.lookup x1 env2 /\
                 forall v, Maps.lookup x1 env1 = Some v -> r stk env1 env2 (k1' v) (k2' v)
             | _ => fun _ => False
             end k2
         | LocalWrite x1 v1 => fun k1' =>
             match le2 in LocalE Y2 return (Y2 -> itree E R2) -> Prop with
             | LocalWrite x2 v2 => fun k2' =>
                 x1 = x2 /\ v1 = v2 /\
                 r stk (Maps.add x1 v1 env1) (Maps.add x1 v1 env2) (k1' tt) (k2' tt)
             | _ => fun _ => False
             end k2
         end k1
     | _, _ => False
     end)
    \/
    (match as_stack X1 e1, as_stack X2 e2 with
     | Some se1, Some se2 =>
         match se1 in StackE Y1 return (Y1 -> itree E R1) -> Prop with
         | StackPush bs1 => fun k1' =>
             match se2 in StackE Y2 return (Y2 -> itree E R2) -> Prop with
             | StackPush bs2 => fun k2' =>
                 bs1 = bs2 /\
                 r ((env1, env2) :: stk) (init_local_env bs1) (init_local_env bs1) (k1' tt) (k2' tt)
             | _ => fun _ => False
             end k2
         | StackPop => fun k1' =>
             match se2 in StackE Y2 return (Y2 -> itree E R2) -> Prop with
             | StackPop => fun k2' =>
                 match stk with
                 | (p1, p2) :: rest => r rest p1 p2 (k1' tt) (k2' tt)
                 | [] => True
                 end
             | _ => fun _ => False
             end k2
         | _ => fun _ => False
         end k1
     | _, _ => False
     end).

  Definition as_local_mcfg {X} (e : @MCFGEtop (@ParamsV IP IPT) X) : option (@LocalE (@ParamsV IP IPT) X) :=
    match e with
    | inr1 (inr1 (inr1 (inl1 (inl1 le)))) => Some le
    | _ => None
    end.

  Definition as_stack_mcfg {X} (e : @MCFGEtop (@ParamsV IP IPT) X) : option (@StackE (@ParamsV IP IPT) X) :=
    match e with
    | inr1 (inr1 (inr1 (inl1 (inr1 se)))) => Some se
    | _ => None
    end.

  Definition as_local_cfg {X} (e : @CFGEtop (@ParamsV IP IPT) X) : option (@LocalE (@ParamsV IP IPT) X) :=
    match e with
    | inl1 _ => None
    | inr1 m => as_local_mcfg m
    end.

  Definition as_stack_cfg {X} (e : @CFGEtop (@ParamsV IP IPT) X) : option (@StackE (@ParamsV IP IPT) X) :=
    match e with
    | inl1 _ => None
    | inr1 m => as_stack_mcfg m
    end.

  Section GenStackSim.
    Context {E : Type -> Type} `{@LocalE (@ParamsV IP IPT) -< E}.
    Variable (is_ub : forall X, E X -> bool).
    Variable (is_sync : forall X, E X -> bool).
    Variable (EqE : prerel E E).
    Variable (EqA : postrel E E).
    Variable (ev_post : forall X, E X -> X -> Prop).
    Variable (as_loc : forall X, E X -> option (@LocalE (@ParamsV IP IPT) X)).
    Variable (as_stk : forall X, E X -> option (@StackE (@ParamsV IP IPT) X)).

    Definition gss_step_body {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
      (r : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
           itree E R1 -> itree E R2 -> Prop)
      (stk : env_stack) (env1 env2 : @local_env (@ParamsV IP IPT))
      (ot1 : itree' E R1) (ot2 : itree' E R2) : Prop :=
      match ot1 with
      | RetF r1 =>
          match ot2 with
          | RetF r2 => RR stk env1 env2 r1 r2
          | _ => False
          end
      | TauF m1 =>
          match ot2 with
          | TauF m2 => r stk env1 env2 m1 m2
          | _ => False
          end
      | VisF _ e1 k1 =>
          is_ub _ e1 = true \/
          match ot2 with
          | VisF _ e2 k2 => css_vis_both is_sync EqE EqA ev_post as_loc as_stk r stk env1 env2 e1 k1 e2 k2
          | _ => False
          end
      end.

    Inductive gen_stack_sim_ {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
      (r : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
           itree E R1 -> itree E R2 -> Prop)
      : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
        itree E R1 -> itree E R2 -> Prop :=
    | GSS_Step stk env1 env2 t1 t2 :
        gss_step_body RR r stk env1 env2 (observe t1) (observe t2) ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2
    | GSS_TauL stk env1 env2 t1 m1 t2 :
        observe t1 = TauF m1 ->
        gen_stack_sim_ RR r stk env1 env2 m1 t2 ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2
    | GSS_TauR stk env1 env2 t1 t2 m2 :
        observe t2 = TauF m2 ->
        gen_stack_sim_ RR r stk env1 env2 t1 m2 ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2
    | GSS_ReadL stk env1 env2 t1 x v k1 t2 :
        t1 ≅ ITree.bind (ITree.trigger (subevent _ (LocalRead x))) k1 ->
        Maps.lookup x env1 = Some v ->
        gen_stack_sim_ RR r stk env1 env2 (k1 v) t2 ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2
    | GSS_ReadR stk env1 env2 t1 t2 x v k2 :
        t2 ≅ ITree.bind (ITree.trigger (subevent _ (LocalRead x))) k2 ->
        Maps.lookup x env2 = Some v ->
        gen_stack_sim_ RR r stk env1 env2 t1 (k2 v) ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2
    | GSS_WriteL stk env1 env2 t1 x v k1 t2 :
        t1 ≅ ITree.bind (ITree.trigger (subevent _ (LocalWrite x v))) k1 ->
        gen_stack_sim_ RR r stk (Maps.add x v env1) env2 (k1 tt) t2 ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2
    | GSS_WriteR stk env1 env2 t1 t2 x v k2 :
        t2 ≅ ITree.bind (ITree.trigger (subevent _ (LocalWrite x v))) k2 ->
        gen_stack_sim_ RR r stk env1 (Maps.add x v env2) t1 (k2 tt) ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2.

    Lemma gen_stack_sim__mon {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
      monotone5 (gen_stack_sim_ RR).
    Proof using.
      intros stk env1 env2 t1 t2 r r' IN LE.
      induction IN as [stk env1 env2 t1 t2 Hstep
                       | stk env1 env2 t1 m1 t2 Ht1 _ IH
                       | stk env1 env2 t1 t2 m2 Ht2 _ IH
                       | stk env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                       | stk env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                       | stk env1 env2 t1 x v k1 t2 Ht1 _ IH
                       | stk env1 env2 t1 t2 x v k2 Ht2 _ IH].
      - apply GSS_Step; unfold gss_step_body in *.
        destruct (observe t1) as [r1 | m1 | X1 e1 k1].
        + exact Hstep.
        + destruct (observe t2); [exact Hstep | apply LE, Hstep | exact Hstep].
        + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe t2) as [r2 | m2 | X2 e2 k2]; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          * left; split; [exact Hsync | split; [exact HE | intros a1 a2 Ha Hp; apply LE, (HA a1 a2 Ha Hp)]].
          * right; left.
            destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
            destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
            -- destruct Hloc as (Hx & Hv & Hr); split; [exact Hx | split; [exact Hv | apply LE, Hr]].
            -- destruct Hloc as (Hx & Hlk & Hrd); split;
                 [exact Hx | split; [exact Hlk | intros v Hv; apply LE, Hrd, Hv]].
          * right; right.
            destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
            destruct se1, se2; try contradiction.
            -- destruct Hstk as [Hbs Hr]; split; [exact Hbs | apply LE, Hr].
            -- destruct stk as [| [p1 p2] rest]; [exact I | apply LE, Hstk].
      - eapply GSS_TauL; [exact Ht1 | exact IH].
      - eapply GSS_TauR; [exact Ht2 | exact IH].
      - eapply GSS_ReadL; [exact Ht1 | exact Hlk | exact IH].
      - eapply GSS_ReadR; [exact Ht2 | exact Hlk | exact IH].
      - eapply GSS_WriteL; [exact Ht1 | exact IH].
      - eapply GSS_WriteR; [exact Ht2 | exact IH].
    Qed.

    #[local] Hint Resolve gen_stack_sim__mon : paco.

    Definition gen_stack_sim {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
      (stk : env_stack) (env1 env2 : @local_env (@ParamsV IP IPT))
      (t1 : itree E R1) (t2 : itree E R2) : Prop :=
      paco5 (gen_stack_sim_ RR) bot5 stk env1 env2 t1 t2.

    Lemma gen_stack_sim__obs_eq {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
      (r r' : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) ->
              itree E R1 -> itree E R2 -> Prop)
      (Hr_eq : forall stk e1 e2 a1 a1' a2 a2',
                 a1 ≅ a1' -> a2 ≅ a2' -> r stk e1 e2 a1 a2 -> r' stk e1 e2 a1' a2') :
      forall stk env1 env2 t1 t1' t2 t2',
        t1 ≅ t1' ->
        t2 ≅ t2' ->
        gen_stack_sim_ RR r stk env1 env2 t1 t2 ->
        gen_stack_sim_ RR r' stk env1 env2 t1' t2'.
    Proof using.
      intros stk env1 env2 t1 t1' t2 t2' E1 E2 Hsim.
      revert t1' t2' E1 E2;
        induction Hsim as [stk env1 env2 t1 t2 Hstep
                           | stk env1 env2 t1 m1 t2 Ht1 _ IH
                           | stk env1 env2 t1 t2 m2 Ht2 _ IH
                           | stk env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                           | stk env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                           | stk env1 env2 t1 x v k1 t2 Ht1 _ IH
                           | stk env1 env2 t1 t2 x v k2 Ht2 _ IH];
        intros t1' t2' E1 E2.
      - punfold E1; red in E1; punfold E2; red in E2.
        apply GSS_Step; unfold gss_step_body in *.
        destruct E1 as [r1 r1' <- | m1 m1' Hm1 | X1 e1 k1 k1' Hk1 | ? ? Hchk _ | ? ? Hchk _];
          try inversion Hchk; pclearbot.
        + destruct E2 as [r2 r2' <- | | | ? ? Hchk _ | ? ? Hchk _];
            try inversion Hchk; try contradiction; exact Hstep.
        + destruct E2 as [| m2 m2' Hm2 | | ? ? Hchk _ | ? ? Hchk _];
            try inversion Hchk; try contradiction; pclearbot.
          eapply Hr_eq; [exact Hm1 | exact Hm2 | exact Hstep].
        + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct E2 as [| | X2 e2 k2 k2' Hk2 | ? ? Hchk _ | ? ? Hchk _];
            try inversion Hchk; try contradiction; pclearbot.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; eapply Hr_eq; [apply Hk1 | apply Hk2 | exact (HA a1 a2 Ha Hp)].
          * right; left.
            destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
            destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
            -- destruct Hloc as (Hx & Hv & Hr); split;
                 [exact Hx | split; [exact Hv | eapply Hr_eq; [apply Hk1 | apply Hk2 | exact Hr]]].
            -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
               intros v Hv; eapply Hr_eq; [apply Hk1 | apply Hk2 | apply Hrd, Hv].
          * right; right.
            destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
            destruct se1, se2; try contradiction.
            -- destruct Hstk as [Hbs Hr]; split; [exact Hbs | eapply Hr_eq; [apply Hk1 | apply Hk2 | exact Hr]].
            -- destruct stk as [| [p1 p2] rest]; [exact I | eapply Hr_eq; [apply Hk1 | apply Hk2 | exact Hstk]].
      - punfold E1; red in E1; rewrite Ht1 in E1;
          apply eqitF_inv_Tau_l in E1 as (m1' & E1b & Hm1); pclearbot.
        eapply GSS_TauL; [exact E1b | eapply IH; [exact Hm1 | exact E2]].
      - punfold E2; red in E2; rewrite Ht2 in E2;
          apply eqitF_inv_Tau_l in E2 as (m2' & E2b & Hm2); pclearbot.
        eapply GSS_TauR; [exact E2b | eapply IH; [exact E1 | exact Hm2]].
      - eapply GSS_ReadL;
          [ symmetry; etransitivity; [symmetry; exact Ht1 | exact E1]
          | exact Hlk
          | apply IH; [reflexivity | exact E2] ].
      - eapply GSS_ReadR;
          [ symmetry; etransitivity; [symmetry; exact Ht2 | exact E2]
          | exact Hlk
          | apply IH; [exact E1 | reflexivity] ].
      - eapply GSS_WriteL;
          [ symmetry; etransitivity; [symmetry; exact Ht1 | exact E1]
          | apply IH; [reflexivity | exact E2] ].
      - eapply GSS_WriteR;
          [ symmetry; etransitivity; [symmetry; exact Ht2 | exact E2]
          | apply IH; [exact E1 | reflexivity] ].
    Qed.

    Lemma gen_stack_sim_obs_eq {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
      forall stk env1 env2 t1 t1' t2 t2',
        t1 ≅ t1' ->
        t2 ≅ t2' ->
        gen_stack_sim RR stk env1 env2 t1 t2 ->
        gen_stack_sim RR stk env1 env2 t1' t2'.
    Proof using.
      pcofix CIH.
      intros stk env1 env2 t1 t1' t2 t2' E1 E2 Hsim.
      pstep; punfold Hsim.
      eapply gen_stack_sim__obs_eq; [| exact E1 | exact E2 | exact Hsim].
      intros s0 e1 e2 a1 a1' a2 a2' Ea1 Ea2 [Hr | Hr];
        [| inversion Hr].
      right; eapply CIH; [exact Ea1 | exact Ea2 | exact Hr].
    Qed.

    Lemma gen_stack_sim_bind {R1 R2 S1 S2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
      (RS : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> S1 -> S2 -> Prop)
      stk env1 env2
      (t1 : itree E R1) (t2 : itree E R2)
      (k1 : R1 -> itree E S1) (k2 : R2 -> itree E S2)
      (Ht : gen_stack_sim RR stk env1 env2 t1 t2)
      (Hk : forall stk' e1' e2' r1 r2,
              RR stk' e1' e2' r1 r2 -> gen_stack_sim RS stk' e1' e2' (k1 r1) (k2 r2)) :
      gen_stack_sim RS stk env1 env2 (ITree.bind t1 k1) (ITree.bind t2 k2).
    Proof using.
      pose proof (@gen_stack_sim__mon) as Hmon.
      revert stk env1 env2 t1 t2 Ht Hk; pcofix CIH; intros stk env1 env2 t1 t2 Ht Hk.
      punfold Ht.
      revert Hk;
        induction Ht as [stk env1 env2 t1 t2 Hstep
                         | stk env1 env2 t1 m1 t2 Ht1 _ IH
                         | stk env1 env2 t1 t2 m2 Ht2 _ IH
                         | stk env1 env2 t1 x v k1' t2 Ht1 Hlk _ IH
                         | stk env1 env2 t1 t2 x v k2' Ht2 Hlk _ IH
                         | stk env1 env2 t1 x v k1' t2 Ht1 _ IH
                         | stk env1 env2 t1 t2 x v k2' Ht2 _ IH];
        intros Hk.
      - unfold gss_step_body in Hstep.
        destruct (observe t1) as [r1 | m1 | X1 e1 k1'] eqn:Hot1.
        + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
          eapply paco5_mon;
            [eapply gen_stack_sim_obs_eq;
               [symmetry; rewrite (itree_eta t1), Hot1, Eqit.bind_ret_l; reflexivity
               | symmetry; rewrite (itree_eta t2), Hot2, Eqit.bind_ret_l; reflexivity
               | exact (Hk stk env1 env2 r1 r2 Hstep)]
            | intros ? ? ? ? ? []].
        + destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
          destruct Hstep as [Hstep | Hbot]; [| inversion Hbot].
          pstep; apply GSS_Step; unfold gss_step_body.
          rewrite (observe_bind t1 k1), Hot1, (observe_bind t2 k2), Hot2.
          right; eapply CIH; [exact Hstep | exact Hk].
        + pstep; apply GSS_Step; unfold gss_step_body.
          rewrite (observe_bind t1 k1), Hot1.
          destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe t2) as [r2 | m2 | X2 e2 k2'] eqn:Hot2; try contradiction.
          rewrite (observe_bind t2 k2), Hot2.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
            right; eapply CIH; [exact HA | exact Hk].
          * right; left.
            destruct (as_loc X1 e1) as [le1 |], (as_loc X2 e2) as [le2 |]; try contradiction.
            destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
            -- destruct Hloc as (Hx & Hv & [Hr | Hb]); [| inversion Hb].
               split; [exact Hx | split; [exact Hv | right; eapply CIH; [exact Hr | exact Hk]]].
            -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
               intros v Hv; specialize (Hrd v Hv); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
               right; eapply CIH; [exact Hrd | exact Hk].
          * right; right.
            destruct (as_stk X1 e1) as [se1 |], (as_stk X2 e2) as [se2 |]; try contradiction.
            destruct se1, se2; try contradiction.
            -- destruct Hstk as [Hbs [Hr | Hb]]; [| inversion Hb].
               split; [exact Hbs | right; eapply CIH; [exact Hr | exact Hk]].
            -- destruct stk as [| [p1 p2] rest]; [exact I |].
               destruct Hstk as [Hr | Hb]; [| inversion Hb].
               right; eapply CIH; [exact Hr | exact Hk].
      - specialize (IH Hk); punfold IH; pstep.
        eapply GSS_TauL; [rewrite (observe_bind t1 k1), Ht1; reflexivity | eapply Hmon; [exact IH | auto]].
      - specialize (IH Hk); punfold IH; pstep.
        eapply GSS_TauR; [rewrite (observe_bind t2 k2), Ht2; reflexivity | eapply Hmon; [exact IH | auto]].
      - specialize (IH Hk); punfold IH; pstep.
        eapply GSS_ReadL; [rewrite Ht1, Eqit.bind_bind; reflexivity | exact Hlk | eapply Hmon; [exact IH | auto]].
      - specialize (IH Hk); punfold IH; pstep.
        eapply GSS_ReadR; [rewrite Ht2, Eqit.bind_bind; reflexivity | exact Hlk | eapply Hmon; [exact IH | auto]].
      - specialize (IH Hk); punfold IH; pstep.
        eapply GSS_WriteL; [rewrite Ht1, Eqit.bind_bind; reflexivity | eapply Hmon; [exact IH | auto]].
      - specialize (IH Hk); punfold IH; pstep.
        eapply GSS_WriteR; [rewrite Ht2, Eqit.bind_bind; reflexivity | eapply Hmon; [exact IH | auto]].
    Qed.

    Lemma gen_stack_sim_ret {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
      stk env1 env2 (r1 : R1) (r2 : R2) :
      RR stk env1 env2 r1 r2 ->
      gen_stack_sim RR stk env1 env2 (Ret r1) (Ret r2).
    Proof using.
      intros HRR; pstep; apply GSS_Step; cbn; exact HRR.
    Qed.

    Lemma gen_stack_sim_trigger_sync {X} (e : E X)
      (Hsync : is_sync X e = true)
      (Hrefl : EqE X X e e)
      (Heq   : forall a1 a2, EqA X X e a1 e a2 -> a1 = a2)
      stk env1 env2 :
      gen_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2 (ITree.trigger e) (ITree.trigger e).
    Proof using.
      pstep; apply GSS_Step; unfold gss_step_body, ITree.trigger; cbn.
      right; left; split; [exact Hsync | split; [exact Hrefl |]].
      intros a1 a2 Ha _; apply Heq in Ha; subst a2.
      left; apply gen_stack_sim_ret; repeat split; reflexivity.
    Qed.

    Lemma gen_stack_sim_trigger_cast_sync {F : Type -> Type} `{F -< E} (e : F void)
      (Hsync : is_sync void (subevent _ e) = true)
      (Hrefl : EqE void void (subevent _ e) (subevent _ e))
      {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
      stk env1 env2 :
      gen_stack_sim RR stk env1 env2 (trigger_cast e) (trigger_cast e).
    Proof using.
      unfold trigger_cast, ITree.trigger.
      pstep; apply GSS_Step; unfold gss_step_body; rewrite !observe_bind; cbn.
      right; left; split; [exact Hsync | split; [exact Hrefl | intros []]].
    Qed.
  End GenStackSim.

  #[local] Hint Resolve gen_stack_sim__mon : paco.

  Definition cfg_stack_sim {R1 R2} :=
    @gen_stack_sim (@CFGEtop (@ParamsV IP IPT)) _
      (@is_ub_cfg) (@sync_non_local_cfg) EqE_CFG EqA_CFG (@cfg_event_post)
      (@as_local_cfg) (@as_stack_cfg) R1 R2.

  Definition mcfg_stack_sim {R1 R2} :=
    @gen_stack_sim (@MCFGEtop (@ParamsV IP IPT)) _
      (@is_ub_mcfg) (@sync_non_local_mcfg) EqE_MCFG EqA_MCFG (@mcfg_event_post)
      (@as_local_mcfg) (@as_stack_mcfg) R1 R2.

  Lemma cfg_local_to_stack_sim {R1 R2}
    (RR : @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    forall (stk : env_stack) env1 env2
      (t1 : @CFGtop (@ParamsV IP IPT) R1)
      (t2 : @CFGtop (@ParamsV IP IPT) R2),
      cfg_local_sim RR env1 env2 t1 t2 ->
      cfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ RR e1' e2' r1 r2)
        stk env1 env2 t1 t2.
  Proof using.
    intros stk; pcofix CIH; intros env1 env2 t1 t2 Hsim.
    pstep; punfold Hsim.
    induction Hsim as [env1 env2 t1 t2 Hstep
                       | env1 env2 t1 m1 t2 Ht1 _ IH
                       | env1 env2 t1 t2 m2 Ht2 _ IH
                       | env1 env2 t1 x v k1 t2 Ht1 Hlk _ IH
                       | env1 env2 t1 t2 x v k2 Ht2 Hlk _ IH
                       | env1 env2 t1 x v k1 t2 Ht1 _ IH
                       | env1 env2 t1 t2 x v k2 Ht2 _ IH].
    - apply GSS_Step; unfold gss_step_body; unfold cls_step_body in Hstep.
      destruct (observe t1) as [r1 | m1 | X1 e1 k1].
      + destruct (observe t2); try contradiction; split; [reflexivity | exact Hstep].
      + destruct (observe t2); try contradiction; pclearbot; right; apply CIH, Hstep.
      + destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
        destruct (observe t2) as [r2 | m2 | X2 e2 k2]; try contradiction.
        destruct Hvis as [(Hsync & HE & HA) | Hrd].
        * left; split; [exact Hsync | split; [exact HE |]].
          intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); pclearbot; right; apply CIH, HA.
        * right; left.
          destruct_sum1 e1; try contradiction;
            destruct e1 as [x1 |]; try contradiction;
            destruct_sum1 e2; try contradiction;
            destruct e2 as [x2 |]; try contradiction.
          cbn [as_local_cfg as_local_mcfg].
          destruct Hrd as (Hx & Hlk & Hrd'); split; [exact Hx | split; [exact Hlk |]].
          intros v Hv; specialize (Hrd' v Hv); pclearbot; right; apply CIH, Hrd'.
    - eapply GSS_TauL; [exact Ht1 | exact IH].
    - eapply GSS_TauR; [exact Ht2 | exact IH].
    - eapply GSS_ReadL; [exact Ht1 | exact Hlk | exact IH].
    - eapply GSS_ReadR; [exact Ht2 | exact Hlk | exact IH].
    - eapply GSS_WriteL; [exact Ht1 | exact IH].
    - eapply GSS_WriteR; [exact Ht2 | exact IH].
  Qed.

  Lemma cfg_stack_sim_EOU {A} (m : EOU A) stk env1 env2 :
    cfg_stack_sim
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2 (EOU_to_itree m) (EOU_to_itree m).
  Proof using.
    destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - unfold raise; apply gen_stack_sim_trigger_cast_sync;
        [reflexivity | apply EqE_CFG_refl].
    - unfold raiseOOM; apply gen_stack_sim_trigger_cast_sync;
        [reflexivity | apply EqE_CFG_refl].
    - unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply GSS_Step;
        unfold gss_step_body; rewrite !observe_bind; cbn; left; reflexivity.
    - apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_stack_sim_apply_attrs attrs msg v stk env1 env2 :
    cfg_stack_sim
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2 (apply_attrs attrs msg v) (apply_attrs attrs msg v).
  Proof using.
    unfold apply_attrs.
    eapply gen_stack_sim_bind; [apply cfg_stack_sim_EOU |].
    intros ? ? ? v' _ (-> & -> & -> & <-).
    eapply gen_stack_sim_bind with
      (RR := fun stk' e1' e2' (r1 r2 : unit) => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2).
    - unfold assert_attrs_dereferenceable.
      destruct (find_option attr_dereferenceable attrs) as [[on n] |], v' as [[p | | | | | | |] | |];
        try (apply gen_stack_sim_ret; repeat split; reflexivity).
      unfold assert_dereferenceable.
      destruct ((on && (ptr_to_int p =? ptr_to_int null)%Z) || (Z.to_N (denote_int_syntax n) =? 0)%N).
      + apply gen_stack_sim_ret; repeat split; reflexivity.
      + eapply gen_stack_sim_bind.
        * unfold load, trigger_cast; apply gen_stack_sim_trigger_sync;
            [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq].
        * intros ? ? ? _ _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity.
    - intros ? ? ? [] _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_stack_sim_apply_args_attrs attrss msg args :
    forall stk env1 env2,
      cfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2 (apply_args_attrs attrss msg args) (apply_args_attrs attrss msg args).
  Proof using.
    revert attrss; induction args as [| v vs IH]; intros attrss stk env1 env2; cbn [apply_args_attrs].
    - apply gen_stack_sim_ret; repeat split; reflexivity.
    - destruct attrss as [| a r];
        (eapply gen_stack_sim_bind; [apply cfg_stack_sim_apply_attrs |];
         intros ? ? ? v' _ (-> & -> & -> & <-);
         eapply gen_stack_sim_bind; [apply IH |];
         intros ? ? ? vs' _ (-> & -> & -> & <-);
         apply gen_stack_sim_ret; repeat split; reflexivity).
  Qed.

  Lemma cfg_stack_sim_check_call_return fattrs ret_attrs ranges loc args rv stk env1 env2 :
    cfg_stack_sim
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2
      (check_call_return fattrs ret_attrs ranges loc args rv)
      (check_call_return fattrs ret_attrs ranges loc args rv).
  Proof using.
    unfold check_call_return.
    eapply gen_stack_sim_bind; [apply cfg_stack_sim_EOU |].
    intros ? ? ? [] _ (-> & -> & -> & <-).
    destruct rv as [ex | v].
    - apply gen_stack_sim_ret; repeat split; reflexivity.
    - eapply gen_stack_sim_bind; [apply cfg_stack_sim_apply_attrs |].
      intros ? ? ? v' _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_stack_sim_EOU_ret {A} (m : EOU A) stk env1 env2 :
    cfg_stack_sim
      (fun stk' e1' e2' r1 r2 =>
         stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2 /\ m = raise_ret r1)
      stk env1 env2 (EOU_to_itree m) (EOU_to_itree m).
  Proof using.
    destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - unfold raise; apply gen_stack_sim_trigger_cast_sync;
        [reflexivity | apply EqE_CFG_refl].
    - unfold raiseOOM; apply gen_stack_sim_trigger_cast_sync;
        [reflexivity | apply EqE_CFG_refl].
    - unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply GSS_Step;
        unfold gss_step_body; rewrite !observe_bind; cbn; left; reflexivity.
    - apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma cfg_stack_sim_denote_function (df1 df2 : definition dtyp (CFG.cfg dtyp))
    (Hproto : df_prototype df1 = df_prototype df2)
    (Hargs  : df_args df1 = df_args df2)
    (Hbody  : forall env va,
                (forall x, In x (df_args df1) -> exists v, Maps.lookup x env = Some v) ->
                cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                  env env (denote_cfg (df_instrs df1) va) (denote_cfg (df_instrs df2) va)) :
    forall stk env1 env2 cc args,
      cfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2 (denote_function df1 cc args) (denote_function df2 cc args).
  Proof using.
    intros stk env1 env2 cc args.
    unfold denote_function; cbv zeta; rewrite Hproto.
    destruct (dc_param_attrs (df_prototype df2)) as [ret_attrs args_attrs].
    cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
    eapply gen_stack_sim_bind; [apply cfg_stack_sim_EOU | intros ? ? ? [] _ (-> & -> & -> & <-)].
    eapply gen_stack_sim_bind; [apply cfg_stack_sim_apply_args_attrs | intros ? ? ? args' _ (-> & -> & -> & <-)].
    eapply gen_stack_sim_bind with
      (RR := fun stk' e1' e2' varg1 varg2 =>
               stk' = (env1, env2) :: stk /\
               (exists bs vs,
                  combine_lists_varargs (df_args df2) args' = raise_ret (bs, vs) /\
                  e1' = init_local_env bs /\ e2' = init_local_env bs) /\
               varg1 = varg2).
    { unfold push_call_frame; rewrite Hargs;
        cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree].
      eapply gen_stack_sim_bind;
        [apply cfg_stack_sim_EOU_ret | intros ? ? ? [bs vs] _ (-> & -> & -> & <- & Ecomb)];
        cbv beta iota zeta.
      eapply gen_stack_sim_bind; [apply cfg_stack_sim_EOU | intros ? ? ? dts _ (-> & -> & -> & <-)].
      eapply gen_stack_sim_bind.
      { unfold mem_push, trigger_cast; apply gen_stack_sim_trigger_sync;
          [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]. }
      intros ? ? ? [] _ (-> & -> & -> & <-).
      eapply gen_stack_sim_bind with
        (RR := fun stk' e1' e2' (r1 r2 : unit) =>
                 stk' = (env1, env2) :: stk /\
                 e1' = init_local_env bs /\ e2' = init_local_env bs /\ r1 = r2).
      { unfold stack_push, trigger_cast; pstep; apply GSS_Step; unfold gss_step_body, ITree.trigger; cbn.
        right; right; right; split; [reflexivity |].
        left; apply gen_stack_sim_ret; repeat split; reflexivity. }
      intros ? ? ? [] _ (-> & -> & -> & <-).
      eapply gen_stack_sim_bind.
      { unfold alloca, trigger_cast; apply gen_stack_sim_trigger_sync;
          [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]. }
      intros ? ? ? varargs _ (-> & -> & -> & <-).
      eapply gen_stack_sim_bind.
      { unfold store, trigger_cast; apply gen_stack_sim_trigger_sync;
          [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]. }
      intros ? ? ? [] _ (-> & -> & -> & <-).
      destruct varargs as [[p | | | | | | |] | |];
        try (unfold raise; apply gen_stack_sim_trigger_cast_sync;
             [reflexivity | apply EqE_CFG_refl]).
      apply gen_stack_sim_ret;
        split; [reflexivity | split; [exists bs, vs; repeat split; assumption | reflexivity]]. }
    intros ? ? ? varg _ (-> & (bs & vs & Ecomb & -> & ->) & <-).
    eapply gen_stack_sim_bind with
      (RR := fun stk' _ _ (r1 r2 : exc + @dvalue (@ParamsV IP IPT)) =>
               stk' = (env1, env2) :: stk /\ r1 = r2).
    { apply cfg_local_to_stack_sim.
      eapply cfg_local_sim_weaken; [| apply cfg_local_sim_run_exc].
      { intros e1 e2 s1 s2 Hs; destruct s1, s2; try contradiction; f_equal; exact Hs. }
      change (denote_cfg_map (ocfg_map (blks (df_instrs df1))) (df_instrs df1) (Some varg))
        with (denote_cfg (df_instrs df1) (Some varg)).
      change (denote_cfg_map (ocfg_map (blks (df_instrs df2))) (df_instrs df2) (Some varg))
        with (denote_cfg (df_instrs df2) (Some varg)).
      apply Hbody.
      intros x Hx; rewrite Hargs in Hx.
      apply init_local_env_in.
      rewrite (combine_lists_varargs_dom _ _ _ _ Ecomb); exact Hx. }
    intros ? final_e1 final_e2 rv _ (-> & <-).
    eapply gen_stack_sim_bind with
      (RR := fun stk' e1' e2' (r1 r2 : unit) =>
               stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2).
    { unfold pop_call_frame; cbn [ExtLib.Structures.Monad.bind Monad_itree].
      eapply gen_stack_sim_bind with
        (RR := fun stk' e1' e2' (r1 r2 : unit) =>
                 stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2).
      - unfold stack_pop, trigger_cast; pstep; apply GSS_Step; unfold gss_step_body, ITree.trigger; cbn.
        right; right; right; left;
          apply gen_stack_sim_ret; repeat split; reflexivity.
      - intros ? ? ? [] _ (-> & -> & -> & <-).
        unfold mem_pop, trigger_cast; apply gen_stack_sim_trigger_sync;
          [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]. }
    intros ? ? ? [] _ (-> & -> & -> & <-).
    apply cfg_stack_sim_check_call_return.
  Qed.

  #[local] Definition mrec_ctx
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

  #[local] Lemma denote_mcfg_eq_interp_mrec
    (fundefs : IntMap (@function_denotation (@ParamsV IP IPT)))
    (dt : dtyp) (fv : @dvalue (@ParamsV IP IPT))
    (args : list (@dvalue (@ParamsV IP IPT))) :
    denote_mcfg fundefs dt fv args =
    interp_mrec (mrec_ctx fundefs) (mrec_ctx fundefs _ (Call dt CC_Ccc fv args)).
  Proof using.
    unfold denote_mcfg, mrec; reflexivity.
  Qed.

  #[local] Lemma cfg_stack_sim_mrec_ctx
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (Hctx : forall k,
              option_rel
                (fun f1 f2 =>
                   forall stk env1 env2 cc args,
                     cfg_stack_sim
                       (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
                       stk env1 env2 (f1 cc args) (f2 cc args))
                (lookup k ctx1) (lookup k ctx2)) :
    forall stk env1 env2 dt1 cc1 fv1 fas1,
      cfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2
        (mrec_ctx ctx1 _ (Call dt1 cc1 fv1 fas1))
        (mrec_ctx ctx2 _ (Call dt1 cc1 fv1 fas1)).
  Proof using.
    intros stk env1 env2 dt1 cc1 fv1 fas1.
    unfold mrec_ctx; cbn [ExtLib.Structures.Monad.bind Monad_itree].
    eapply gen_stack_sim_bind;
      [apply cfg_stack_sim_EOU | intros ? ? ? [] _ (-> & -> & -> & <-)].
    assert (Hext :
      cfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2
        (Functor.fmap (@inr exc _) (external_call dt1 fv1 fas1))
        (Functor.fmap (@inr exc _) (external_call dt1 fv1 fas1))).
    { cbn [Functor.fmap Functor_itree ITree.map]; unfold external_call, trigger_cast.
      eapply gen_stack_sim_bind.
      - apply gen_stack_sim_trigger_sync; [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq].
      - intros ? ? ? dv _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity. }
    unfold lookup_defn.
    destruct fv1 as [[p | | | | | | |] | |]; try exact Hext.
    pose proof (Hctx (ptr_to_int p)) as Hlk.
    destruct (lookup (ptr_to_int p) ctx1) as [f1 |],
             (lookup (ptr_to_int p) ctx2) as [f2 |];
      inversion Hlk; subst.
    - match goal with H : forall s _ _ _ _, cfg_stack_sim _ s _ _ _ _ |- _ => apply H end.
    - exact Hext.
  Qed.

  (** Lift [cfg_stack_sim] across [interp_mrec] (`denote_mcfg`). *)
  Lemma cfg_to_mcfg_stack_sim_mrec
    (ctx1 ctx2 : IntMap (@function_denotation (@ParamsV IP IPT)))
    (Hctx : forall k,
              option_rel
                (fun f1 f2 =>
                   forall stk env1 env2 cc args,
                     cfg_stack_sim
                       (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
                       stk env1 env2 (f1 cc args) (f2 cc args))
                (lookup k ctx1) (lookup k ctx2)) :
    forall {R1 R2}
      (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
      stk env1 env2
      (u1 : @CFGtop (@ParamsV IP IPT) R1)
      (u2 : @CFGtop (@ParamsV IP IPT) R2)
      (t1 : @MCFGtop (@ParamsV IP IPT) R1)
      (t2 : @MCFGtop (@ParamsV IP IPT) R2),
      interp_mrec (mrec_ctx ctx1) u1 ≅ t1 ->
      interp_mrec (mrec_ctx ctx2) u2 ≅ t2 ->
      cfg_stack_sim RR stk env1 env2 u1 u2 ->
      mcfg_stack_sim RR stk env1 env2 t1 t2.
  Proof using.
    intros R1 R2 RR.
    pose proof (cfg_stack_sim_mrec_ctx ctx1 ctx2 Hctx) as Hcall.
    pcofix CIH.
    intros stk env1 env2 u1 u2 t1 t2 Et1 Et2 Hsim.
    pstep.
    set (r_rel := fun s0 e1 e2 a1 a2 =>
                    exists v1 v2,
                      interp_mrec (mrec_ctx ctx1) v1 ≅ a1 /\
                      interp_mrec (mrec_ctx ctx2) v2 ≅ a2 /\
                      cfg_stack_sim RR s0 e1 e2 v1 v2).
    assert (Hr_eq : forall s0 e1 e2 a1 a1' a2 a2',
              a1 ≅ a1' -> a2 ≅ a2' -> r_rel s0 e1 e2 a1 a2 -> r_rel s0 e1 e2 a1' a2').
    { intros s0 e1 e2 a1 a1' a2 a2' Ea1 Ea2 (v1 & v2 & Ev1 & Ev2 & Hv).
      exists v1, v2; split;
        [ etransitivity; [exact Ev1 | exact Ea1]
        | split; [etransitivity; [exact Ev2 | exact Ea2] | exact Hv] ]. }
    eapply gen_stack_sim__mon with (r := r_rel);
      [| intros s0 e1 e2 a1 a2 (v1 & v2 & Ev1 & Ev2 & Hv);
         right; eapply CIH; [exact Ev1 | exact Ev2 | exact Hv]].
    eapply gen_stack_sim__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
    punfold Hsim; clear t1 t2 Et1 Et2 CIH r.
    induction Hsim as [stk env1 env2 u1 u2 Hstep
                       | stk env1 env2 u1 mu1 u2 Hu1 _ IH
                       | stk env1 env2 u1 u2 mu2 Hu2 _ IH
                       | stk env1 env2 u1 x v k1 u2 Hu1 Hlk _ IH
                       | stk env1 env2 u1 u2 x v k2 Hu2 Hlk _ IH
                       | stk env1 env2 u1 x v k1 u2 Hu1 _ IH
                       | stk env1 env2 u1 u2 x v k2 Hu2 _ IH].
    - eapply gen_stack_sim__obs_eq;
        [exact Hr_eq | symmetry; apply unfold_interp_mrec | symmetry; apply unfold_interp_mrec |].
      unfold CFGtop, CFGEtop, MCFGtop, MCFGEtop in *.
      unfold gss_step_body in Hstep.
      destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        apply GSS_Step; cbn; exact Hstep.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        destruct Hstep as [Hstep | Hb]; [| inversion Hb].
        apply GSS_Step; cbn.
        exists m1, m2; split; [reflexivity | split; [reflexivity | exact Hstep]].
      + destruct Hstep as [Hub | Hvis].
        * destruct ev1 as [ce1 | me1]; [discriminate Hub |].
          apply GSS_Step; cbn; left; exact Hub.
        * destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          -- destruct ev1 as [ce1 | me1], ev2 as [ce2 | me2]; cbn in HE; try contradiction.
             ++ (* CallE! [unfold_interp_mrec] produces [Tau (interp_mrec ... (bind ...))]! *)
                destruct ce1 as [dt1 cc1 fv1 fas1], ce2 as [dt2 cc2 fv2 fas2].
                destruct HE as (<- & <- & <- & <-).
                apply GSS_Step; cbn.
                exists (ITree.bind (mrec_ctx ctx1 _ (Call dt1 cc1 fv1 fas1)) k1),
                       (ITree.bind (mrec_ctx ctx2 _ (Call dt1 cc1 fv1 fas1)) k2).
                split; [reflexivity | split; [reflexivity |]].
                eapply gen_stack_sim_bind.
                ** apply Hcall.
                ** intros ? ? ? rv1 rv2 (-> & -> & -> & <-).
                   specialize (HA rv1 rv1 Logic.eq_refl I); destruct HA as [HA | Hb]; [exact HA | inversion Hb].
             ++ (* Non-Call MCFGEtop sync event *)
                apply GSS_Step; cbn; right; left.
                split; [exact Hsync | split; [exact HE |]].
                intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
                exists (Tau (k1 a1)), (Tau (k2 a2)).
                split; [rewrite unfold_interp_mrec; reflexivity |].
                split; [rewrite unfold_interp_mrec; reflexivity |].
                pstep; eapply GSS_TauL; [reflexivity |]; eapply GSS_TauR; [reflexivity |].
                punfold HA; exact HA.
          -- destruct ev1 as [| me1], ev2 as [| me2]; cbn in Hloc;
               try (destruct (as_local_mcfg me1); contradiction); try contradiction.
             destruct (as_local_mcfg me1) as [le1 |] eqn:Ele1,
                      (as_local_mcfg me2) as [le2 |] eqn:Ele2; try contradiction.
             destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
             ++ destruct Hloc as (Hx & Hv & [Hr | Hb]); [| inversion Hb].
                apply GSS_Step; cbn; right; right; left.
                rewrite Ele1, Ele2; split; [exact Hx | split; [exact Hv |]].
                exists (Tau (k1 tt)), (Tau (k2 tt)).
                split; [rewrite unfold_interp_mrec; reflexivity |].
                split; [rewrite unfold_interp_mrec; reflexivity |].
                pstep; eapply GSS_TauL; [reflexivity |]; eapply GSS_TauR; [reflexivity |].
                punfold Hr; exact Hr.
             ++ destruct Hloc as (Hx & Hlk & Hrd).
                apply GSS_Step; cbn; right; right; left.
                rewrite Ele1, Ele2; split; [exact Hx | split; [exact Hlk |]].
                intros v Hv; specialize (Hrd v Hv); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
                exists (Tau (k1 v)), (Tau (k2 v)).
                split; [rewrite unfold_interp_mrec; reflexivity |].
                split; [rewrite unfold_interp_mrec; reflexivity |].
                pstep; eapply GSS_TauL; [reflexivity |]; eapply GSS_TauR; [reflexivity |].
                punfold Hrd; exact Hrd.
          -- destruct ev1 as [| me1], ev2 as [| me2]; cbn in Hstk;
               try (destruct (as_stack_mcfg me1); contradiction); try contradiction.
             destruct (as_stack_mcfg me1) as [se1 |] eqn:Ese1,
                      (as_stack_mcfg me2) as [se2 |] eqn:Ese2; try contradiction.
             destruct se1, se2; try contradiction.
             ++ destruct Hstk as [Hbs [Hr | Hb]]; [| inversion Hb].
                apply GSS_Step; cbn;
                  right; right; right; rewrite Ese1, Ese2.
                split; [exact Hbs |].
                exists (Tau (k1 tt)), (Tau (k2 tt)).
                split; [rewrite unfold_interp_mrec; reflexivity |].
                split; [rewrite unfold_interp_mrec; reflexivity |].
                pstep; eapply GSS_TauL; [reflexivity |]; eapply GSS_TauR; [reflexivity |].
                punfold Hr; exact Hr.
             ++ apply GSS_Step; cbn;
                  right; right; right; rewrite Ese1, Ese2.
                destruct stk as [| [p1 p2] rest]; [exact I |].
                destruct Hstk as [Hr | Hb]; [| inversion Hb].
                exists (Tau (k1 tt)), (Tau (k2 tt)).
                split; [rewrite unfold_interp_mrec; reflexivity |].
                split; [rewrite unfold_interp_mrec; reflexivity |].
                pstep; eapply GSS_TauL; [reflexivity |]; eapply GSS_TauR; [reflexivity |].
                punfold Hr; exact Hr.
    - eapply gen_stack_sim__obs_eq with (t1 := Tau (interp_mrec (mrec_ctx ctx1) mu1))
                                        (t2 := interp_mrec (mrec_ctx ctx2) u2);
        [ exact Hr_eq
        | unfold CFGtop, CFGEtop in Hu1; symmetry; rewrite unfold_interp_mrec, Hu1; reflexivity
        | reflexivity | ].
      eapply GSS_TauL; [reflexivity | exact IH].
    - eapply gen_stack_sim__obs_eq with (t1 := interp_mrec (mrec_ctx ctx1) u1)
                                        (t2 := Tau (interp_mrec (mrec_ctx ctx2) mu2));
        [ exact Hr_eq
        | reflexivity
        | unfold CFGtop, CFGEtop in Hu2; symmetry; rewrite unfold_interp_mrec, Hu2; reflexivity | ].
      eapply GSS_TauR; [reflexivity | exact IH].
    - eapply GSS_ReadL with (x := x) (k1 := fun y => Tau (interp_mrec (mrec_ctx ctx1) (k1 y))).
      + unfold CFGtop, CFGEtop in *; rewrite Hu1, !bind_trigger, unfold_interp_mrec;
          cbn [observe _interp_mrec subevent resum ReSum_id ReSum_sum
               ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1
               id_ Id_IFun case_ Case_sum1 case_sum1];
          reflexivity.
      + exact Hlk.
      + eapply GSS_TauL; [reflexivity | exact IH].
    - eapply GSS_ReadR with (x := x) (k2 := fun y => Tau (interp_mrec (mrec_ctx ctx2) (k2 y))).
      + unfold CFGtop, CFGEtop in *; rewrite Hu2, !bind_trigger, unfold_interp_mrec;
          cbn [observe _interp_mrec subevent resum ReSum_id ReSum_sum
               ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1
               id_ Id_IFun case_ Case_sum1 case_sum1];
          reflexivity.
      + exact Hlk.
      + eapply GSS_TauR; [reflexivity | exact IH].
    - eapply GSS_WriteL with (x := x) (v := v) (k1 := fun y => Tau (interp_mrec (mrec_ctx ctx1) (k1 y))).
      + unfold CFGtop, CFGEtop in *; rewrite Hu1, !bind_trigger, unfold_interp_mrec;
          cbn [observe _interp_mrec subevent resum ReSum_id ReSum_sum
               ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1
               id_ Id_IFun case_ Case_sum1 case_sum1];
          reflexivity.
      + eapply GSS_TauL; [reflexivity | exact IH].
    - eapply GSS_WriteR with (x := x) (v := v) (k2 := fun y => Tau (interp_mrec (mrec_ctx ctx2) (k2 y))).
      + unfold CFGtop, CFGEtop in *; rewrite Hu2, !bind_trigger, unfold_interp_mrec;
          cbn [observe _interp_mrec subevent resum ReSum_id ReSum_sum
               ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1
               id_ Id_IFun case_ Case_sum1 case_sum1];
          reflexivity.
      + eapply GSS_TauR; [reflexivity | exact IH].
  Qed.

  (** Lift [mcfg_stack_sim] across [interp_intrinsics]. *)
  Lemma mcfg_stack_sim_EOU {A} (m : EOU A) stk env1 env2 :
    mcfg_stack_sim
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2 (EOU_to_itree m) (EOU_to_itree m).
  Proof using.
    destruct m as [s | s | s | x]; cbn [EOU_to_itree].
    - unfold raise; apply gen_stack_sim_trigger_cast_sync;
        [reflexivity | apply EqE_MCFG_refl].
    - unfold raiseOOM; apply gen_stack_sim_trigger_cast_sync;
        [reflexivity | apply EqE_MCFG_refl].
    - unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply GSS_Step;
        unfold gss_step_body; rewrite !observe_bind; cbn; left; reflexivity.
    - apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Definition sem_fn_sync (sem : @semantic_function (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT))) : Prop :=
    forall args va stk env1 env2,
      mcfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2 (sem args va) (sem args va).

  Lemma pure_to_semantic_sync pf :
    sem_fn_sync (pure_to_semantic pf).
  Proof using.
    intros args va stk env1 env2; unfold pure_to_semantic; apply mcfg_stack_sim_EOU.
  Qed.

  Lemma pure_base_to_semantic_sync pbf :
    sem_fn_sync (pure_base_to_semantic pbf).
  Proof using.
    unfold pure_base_to_semantic; apply pure_to_semantic_sync.
  Qed.

  Lemma Forall_map_pure_to_semantic {A B} (f : A -> B * _) (l : list A)
    (Hf : forall x, sem_fn_sync (snd (f x))) :
    Forall (fun p => sem_fn_sync (snd p)) (List.map f l).
  Proof using.
    induction l as [| x xs IH]; constructor; [apply Hf | exact IH].
  Qed.

  #[local] Lemma mk_int_unop_defs_sync op_name widths op :
    Forall (fun p => sem_fn_sync (snd p)) (mk_int_unop_defs op_name widths op).
  Proof using.
    unfold mk_int_unop_defs; apply Forall_map_pure_to_semantic; intros; apply pure_base_to_semantic_sync.
  Qed.

  #[local] Lemma mk_int_unop_flag_defs_sync op_name widths op :
    Forall (fun p => sem_fn_sync (snd p)) (mk_int_unop_flag_defs op_name widths op).
  Proof using.
    unfold mk_int_unop_flag_defs; apply Forall_map_pure_to_semantic; intros; apply pure_base_to_semantic_sync.
  Qed.

  #[local] Lemma mk_int_binop_defs_sync op_name widths op :
    Forall (fun p => sem_fn_sync (snd p)) (mk_int_binop_defs op_name widths op).
  Proof using.
    unfold mk_int_binop_defs; apply Forall_map_pure_to_semantic; intros; apply pure_base_to_semantic_sync.
  Qed.

  #[local] Lemma mk_expect_int_defs_sync widths :
    Forall (fun p => sem_fn_sync (snd p)) (mk_expect_int_defs widths).
  Proof using.
    unfold mk_expect_int_defs; apply Forall_map_pure_to_semantic; intros; apply pure_base_to_semantic_sync.
  Qed.

  #[local] Lemma mk_int_ternop_defs_sync op_name widths op :
    Forall (fun p => sem_fn_sync (snd p)) (mk_int_ternop_defs op_name widths op).
  Proof using.
    unfold mk_int_ternop_defs; apply Forall_map_pure_to_semantic; intros; apply pure_base_to_semantic_sync.
  Qed.

  #[local] Lemma mk_int_ovf_binop_defs_sync op_name widths op :
    Forall (fun p => sem_fn_sync (snd p)) (mk_int_ovf_binop_defs op_name widths op).
  Proof using.
    unfold mk_int_ovf_binop_defs; apply Forall_map_pure_to_semantic; intros; apply pure_to_semantic_sync.
  Qed.

  #[local] Opaque mk_int_unop_defs mk_int_unop_flag_defs mk_int_binop_defs
    mk_expect_int_defs mk_int_ternop_defs mk_int_ovf_binop_defs.

  #[local] Lemma extra_fp_intrinsics_sync :
    Forall (fun p => sem_fn_sync (snd p)) extra_fp_intrinsics.
  Proof using.
    unfold extra_fp_intrinsics; repeat constructor; apply pure_base_to_semantic_sync.
  Qed.

  #[local] Lemma Forall_app_intro {A} (P : A -> Prop) (l1 l2 : list A) :
    Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
  Proof using.
    intros H1 H2; apply Forall_app; split; assumption.
  Qed.

  #[local] Lemma extra_int_intrinsics_sync :
    Forall (fun p => sem_fn_sync (snd p)) extra_int_intrinsics.
  Proof using.
    unfold extra_int_intrinsics; repeat apply Forall_app_intro;
      first [ apply mk_int_binop_defs_sync
            | apply mk_int_unop_flag_defs_sync
            | apply mk_int_ovf_binop_defs_sync
            | apply mk_int_unop_defs_sync
            | apply mk_int_ternop_defs_sync
            | apply mk_expect_int_defs_sync ].
  Qed.

  #[local] Opaque extra_fp_intrinsics extra_int_intrinsics.

  Lemma defined_intrinsics_sync :
    Forall (fun p => sem_fn_sync (snd p))
      (defined_intrinsics (E := @MCFGEtop (@ParamsV IP IPT))).
  Proof using.
    unfold defined_intrinsics.
    repeat apply Forall_app_intro;
      [ repeat constructor; apply pure_base_to_semantic_sync
      | apply extra_fp_intrinsics_sync
      | apply extra_int_intrinsics_sync
      | ].
    repeat (apply Forall_cons; [try apply pure_base_to_semantic_sync |]); try apply Forall_nil.
    - (* llvm_va_start *)
      intros args va stk env1 env2; unfold llvm_va_start.
      destruct args as [| a [| ? ?]], va as [vp |];
        try (unfold raise; apply gen_stack_sim_trigger_cast_sync;
             [reflexivity | apply EqE_MCFG_refl]).
      destruct a as [[| | | | | | | ] | |];
        try (unfold raiseUB; apply gen_stack_sim_trigger_cast_sync;
             [reflexivity | apply EqE_MCFG_refl]);
        (eapply gen_stack_sim_bind;
         [unfold store, trigger_cast; apply gen_stack_sim_trigger_sync;
          [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq]
         | intros ? ? ? [] _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity]).
    - (* llvm_va_end *)
      intros args va stk env1 env2; unfold llvm_va_end; apply gen_stack_sim_ret; repeat split; reflexivity.
    - (* llvm_va_copy *)
      intros args va stk env1 env2; unfold llvm_va_copy.
      destruct args as [| dst [| src [| ? ?]]];
        try (unfold raise; apply gen_stack_sim_trigger_cast_sync;
             [reflexivity | apply EqE_MCFG_refl]).
      eapply gen_stack_sim_bind.
      + unfold load, trigger_cast; apply gen_stack_sim_trigger_sync;
          [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
      + intros ? ? ? vargs _ (-> & -> & -> & <-).
        eapply gen_stack_sim_bind.
        * unfold store, trigger_cast; apply gen_stack_sim_trigger_sync;
            [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
        * intros ? ? ? [] _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  #[local] Opaque defined_intrinsics.

  #[local] Lemma assoc_defs_sync (fname : string)
    (defs : list (declaration typ * @semantic_function (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT))))
    (Hdefs : Forall (fun p => sem_fn_sync (snd p)) defs)
    (f : @semantic_function (@ParamsV IP IPT) (@MCFGEtop (@ParamsV IP IPT))) :
    assoc fname
      (List.map (fun '(a, b) => match dc_name a with Name s => (s, b) | _ => (""%string, b) end) defs) =
      Some f ->
    sem_fn_sync f.
  Proof using.
    induction Hdefs as [| [decl sem] rest Hsem _ IH]; cbn [List.map assoc]; [discriminate |].
    cbn [snd] in Hsem; destruct (dc_name decl); cbn iota zeta;
      (match goal with |- (if ?b then _ else _) = _ -> _ => destruct b end;
       [intros H; exact (eq_ind sem sem_fn_sync Hsem f
                          (f_equal (fun o => match o with Some g => g | None => sem end) H))
       | exact IH]).
  Qed.

  Lemma handle_intrinsics_sync {X} (ie : @IntrinsicE (@ParamsV IP IPT) X) stk env1 env2 :
    mcfg_stack_sim
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2
      (handle_intrinsics ie) (handle_intrinsics ie).
  Proof using.
    destruct ie as [dt fname args va]; cbn [handle_intrinsics].
    destruct (assoc fname defs_assoc) as [f |] eqn:Eassoc; cbn [eq_rect].
    - unfold defs_assoc in Eassoc;
        exact (assoc_defs_sync fname _ defined_intrinsics_sync f Eassoc args va stk env1 env2).
    - apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
  Qed.

  Definition intr_cont {R : Type} (x : R + @MCFGtop (@ParamsV IP IPT) R)
    : @MCFGtop (@ParamsV IP IPT) R :=
    match x with
    | inl r => Ret r
    | inr u => Tau (interp_intrinsics u)
    end.

  Definition decomp_intr {R : Type} (u : @MCFGtop (@ParamsV IP IPT) R)
    : @MCFGtop (@ParamsV IP IPT) (R + @MCFGtop (@ParamsV IP IPT) R) :=
    match observe u with
    | RetF r => Ret (inl r)
    | TauF m => Ret (inr m)
    | VisF _ ev k => ITree.bind (interp_intrinsics_h ev) (fun x => Ret (inr (k x)))
    end.

  Lemma decomp_intr_spec {R : Type} (u : @MCFGtop (@ParamsV IP IPT) R) :
    ITree.bind (decomp_intr u) intr_cont ≅ interp_intrinsics u.
  Proof using.
    unfold interp_intrinsics, decomp_intr, MCFGtop, MCFGEtop in *; rewrite unfold_interp.
    destruct (observe u) as [r | m | X ev k]; cbn -[interp_intrinsics_h].
    - rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_bind; apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros x ? <-; rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Local Lemma mcfg_stack_sim_interp_intrinsics_step_decomp {R1 R2}
    (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    let intr_rel :=
      fun s0 e1 e2 (x1 : R1 + @MCFGtop (@ParamsV IP IPT) R1)
                   (x2 : R2 + @MCFGtop (@ParamsV IP IPT) R2) =>
        match x1, x2 with
        | inl r1, inl r2 => RR s0 e1 e2 r1 r2
        | inr v1, inr v2 => mcfg_stack_sim RR s0 e1 e2 v1 v2
        | _, _ => False
        end in
    forall stk env1 env2
      (u1 : @MCFGtop (@ParamsV IP IPT) R1)
      (u2 : @MCFGtop (@ParamsV IP IPT) R2),
      gss_step_body (@is_ub_mcfg) (@sync_non_local_mcfg) EqE_MCFG EqA_MCFG
        (@mcfg_event_post) (@as_local_mcfg) (@as_stack_mcfg)
        RR (upaco5 (gen_stack_sim_ (@is_ub_mcfg) (@sync_non_local_mcfg) EqE_MCFG EqA_MCFG
                      (@mcfg_event_post) (@as_local_mcfg) (@as_stack_mcfg) RR) bot5)
        stk env1 env2 (observe u1) (observe u2) ->
      mcfg_stack_sim intr_rel stk env1 env2 (decomp_intr u1) (decomp_intr u2).
  Proof using.
    cbv zeta; intros stk env1 env2 u1 u2 Hstep.
    unfold gss_step_body, decomp_intr in *.
    destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
    - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
      apply gen_stack_sim_ret; exact Hstep.
    - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
      destruct Hstep as [Hstep | Hb]; [| inversion Hb].
      apply gen_stack_sim_ret; exact Hstep.
    - destruct Hstep as [Hub | Hvis].
      + destruct_sum1 ev1; try discriminate Hub; destruct ev1 as [u].
        pstep; apply GSS_Step; unfold gss_step_body;
          rewrite observe_bind; cbn; left; reflexivity.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
        * destruct ev1 as [ec1 | [ie1 | re1]], ev2 as [ec2 | [ie2 | re2]]; cbn in HE; try contradiction.
          -- cbn [interp_intrinsics_h case_ Case_sum1 case_sum1
                  Case_sum1_Handler Handler.case_ E_trigger];
               unfold ITree.trigger.
             pstep; apply GSS_Step; unfold gss_step_body; rewrite !observe_bind; cbn.
             right; left; split; [reflexivity | split; [exact HE |]].
             intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
             left; eapply gen_stack_sim_obs_eq;
               [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
             apply gen_stack_sim_ret; exact HA.
          -- destruct ie1 as [dt1 fn1 args1 va1], ie2 as [dt2 fn2 args2 va2].
             destruct HE as (<- & <- & <- & <-);
               cbn [interp_intrinsics_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_].
             eapply gen_stack_sim_bind; [apply handle_intrinsics_sync |].
             intros ? ? ? a1 _ (-> & -> & -> & <-).
             specialize (HA a1 a1 Logic.eq_refl I); destruct HA as [HA | Hb]; [| inversion Hb].
             apply gen_stack_sim_ret; exact HA.
          -- cbn [interp_intrinsics_h case_ Case_sum1 case_sum1
                  Case_sum1_Handler Handler.case_ F_trigger];
               unfold ITree.trigger.
             pstep; apply GSS_Step; unfold gss_step_body; rewrite !observe_bind; cbn.
             right; left; split; [exact Hsync | split; [exact HE |]].
             intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
             left; eapply gen_stack_sim_obs_eq;
               [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
             apply gen_stack_sim_ret; exact HA.
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
             pstep; apply GSS_Step; unfold gss_step_body; rewrite !observe_bind; cbn.
             right; right; left; split;
               [reflexivity | split; [reflexivity |]].
             left; eapply gen_stack_sim_obs_eq;
               [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
             apply gen_stack_sim_ret; exact Hr.
          -- destruct Hloc as (<- & Hlk & Hrd).
             pstep; apply GSS_Step; unfold gss_step_body; rewrite !observe_bind; cbn.
             right; right; left; split;
               [reflexivity | split; [exact Hlk |]].
             intros v Hv; specialize (Hrd v Hv); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
             left; eapply gen_stack_sim_obs_eq;
               [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
             apply gen_stack_sim_ret; exact Hrd.
        * destruct (as_stack_mcfg ev1) as [se1 |] eqn:Ese1,
                   (as_stack_mcfg ev2) as [se2 |] eqn:Ese2; try contradiction.
          destruct se1, se2; try contradiction;
            destruct_sum1 ev1; try discriminate Ese1;
            destruct_sum1 ev2; try discriminate Ese2;
            inversion Ese1; subst; inversion Ese2; subst;
            cbn [interp_intrinsics_h case_ Case_sum1 case_sum1
                 Case_sum1_Handler Handler.case_ F_trigger];
            unfold ITree.trigger.
          -- destruct Hstk as [<- [Hr | Hb]]; [| inversion Hb].
             pstep; apply GSS_Step; unfold gss_step_body; rewrite !observe_bind; cbn.
             right; right; right; split; [reflexivity |].
             left; eapply gen_stack_sim_obs_eq;
               [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
             apply gen_stack_sim_ret; exact Hr.
          -- pstep; apply GSS_Step; unfold gss_step_body; rewrite !observe_bind; cbn.
             right; right; right.
             destruct stk as [| [p1 p2] rest]; [exact I |].
             destruct Hstk as [Hr | Hb]; [| inversion Hb].
             left; eapply gen_stack_sim_obs_eq;
               [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
             apply gen_stack_sim_ret; exact Hr.
  Qed.

  Lemma mcfg_stack_sim_interp_intrinsics {R1 R2}
    (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    forall stk env1 env2
      (u1 : @MCFGtop (@ParamsV IP IPT) R1)
      (u2 : @MCFGtop (@ParamsV IP IPT) R2),
      mcfg_stack_sim RR stk env1 env2 u1 u2 ->
      mcfg_stack_sim RR stk env1 env2 (interp_intrinsics u1) (interp_intrinsics u2).
  Proof using.
    set (intr_rel := fun s0 e1 e2 (x1 : R1 + @MCFGtop (@ParamsV IP IPT) R1)
                                  (x2 : R2 + @MCFGtop (@ParamsV IP IPT) R2) =>
                       match x1, x2 with
                       | inl r1, inl r2 => RR s0 e1 e2 r1 r2
                       | inr v1, inr v2 => mcfg_stack_sim RR s0 e1 e2 v1 v2
                       | _, _ => False
                       end).
    pose proof (@mcfg_stack_sim_interp_intrinsics_step_decomp R1 R2 RR) as Hstep_decomp.
    set (r_both := fun s0 e1 e2 (a1 : @MCFGtop (@ParamsV IP IPT) R1)
                                (a2 : @MCFGtop (@ParamsV IP IPT) R2) =>
                     (exists v1 v2,
                        interp_intrinsics v1 ≅ a1 /\
                        interp_intrinsics v2 ≅ a2 /\
                        mcfg_stack_sim RR s0 e1 e2 v1 v2) \/
                     (exists w1 w2,
                        ITree.bind w1 intr_cont ≅ a1 /\
                        ITree.bind w2 intr_cont ≅ a2 /\
                        mcfg_stack_sim intr_rel s0 e1 e2 w1 w2)).
    assert (Hr_eq :
      forall s0 e1 e2 a1 a1' a2 a2',
        a1 ≅ a1' -> a2 ≅ a2' -> r_both s0 e1 e2 a1 a2 -> r_both s0 e1 e2 a1' a2').
    { intros s0 e1 e2 a1 a1' a2 a2' Ea1 Ea2 [(v1 & v2 & Ev1 & Ev2 & Hv) | (w1 & w2 & Ew1 & Ew2 & Hw)].
      - left; exists v1, v2; split;
          [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hv]].
      - right; exists w1, w2; split;
          [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hw]]. }
    assert (Hbranch_b :
      forall stk env1 env2 w1 w2 t1 t2,
        ITree.bind w1 intr_cont ≅ t1 ->
        ITree.bind w2 intr_cont ≅ t2 ->
        mcfg_stack_sim intr_rel stk env1 env2 w1 w2 ->
        gen_stack_sim_ (@is_ub_mcfg) (@sync_non_local_mcfg) EqE_MCFG EqA_MCFG
          (@mcfg_event_post) (@as_local_mcfg) (@as_stack_mcfg) RR r_both
          stk env1 env2 t1 t2).
    { intros stk env1 env2 w1 w2 t1 t2 Et1 Et2 Hw.
      eapply gen_stack_sim__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
      punfold Hw; clear t1 t2 Et1 Et2.
      induction Hw as [stk env1 env2 w1 w2 Hstep
                       | stk env1 env2 w1 mw1 w2 Hw1 _ IH
                       | stk env1 env2 w1 w2 mw2 Hw2 _ IH
                       | stk env1 env2 w1 x v kw1 w2 Hw1 Hlk _ IH
                       | stk env1 env2 w1 w2 x v kw2 Hw2 Hlk _ IH
                       | stk env1 env2 w1 x v kw1 w2 Hw1 _ IH
                       | stk env1 env2 w1 w2 x v kw2 Hw2 _ IH].
      - unfold gss_step_body in Hstep.
        destruct (observe w1) as [x1 | mw1 | X1 ev1 kw1] eqn:How1.
        + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          destruct x1 as [r1 | v1], x2 as [r2 | v2]; cbn in Hstep; try contradiction.
          * apply GSS_Step; unfold gss_step_body; rewrite !observe_bind, How1, How2; cbn; exact Hstep.
          * apply GSS_Step; unfold gss_step_body; rewrite !observe_bind, How1, How2; cbn.
            left; exists v1, v2; split; [reflexivity | split; [reflexivity | exact Hstep]].
        + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          destruct Hstep as [Hstep | Hb]; [| inversion Hb].
          apply GSS_Step; unfold gss_step_body; rewrite !observe_bind, How1, How2.
          right; exists mw1, mw2; split; [reflexivity | split; [reflexivity | exact Hstep]].
        + apply GSS_Step; unfold gss_step_body; rewrite (observe_bind w1 intr_cont), How1.
          destruct Hstep as [Hub | Hvis]; [left; exact Hub | right].
          destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          rewrite (observe_bind w2 intr_cont), How2.
          destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
          * left; split; [exact Hsync | split; [exact HE |]].
            intros a1 a2 Ha Hp; specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
            right; exists (kw1 a1), (kw2 a2); split; [reflexivity | split; [reflexivity | exact HA]].
          * right; left.
            destruct (as_local_mcfg ev1) as [le1 |], (as_local_mcfg ev2) as [le2 |]; try contradiction.
            destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction.
            -- destruct Hloc as (Hx & Hv & [Hr | Hb]); [| inversion Hb].
               split; [exact Hx | split; [exact Hv |]].
               right; exists (kw1 tt), (kw2 tt);
                 split; [reflexivity | split; [reflexivity | exact Hr]].
            -- destruct Hloc as (Hx & Hlk & Hrd); split; [exact Hx | split; [exact Hlk |]].
               intros v Hv; specialize (Hrd v Hv); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
               right; exists (kw1 v), (kw2 v); split; [reflexivity | split; [reflexivity | exact Hrd]].
          * right; right.
            destruct (as_stack_mcfg ev1) as [se1 |], (as_stack_mcfg ev2) as [se2 |]; try contradiction.
            destruct se1, se2; try contradiction.
            -- destruct Hstk as [Hbs [Hr | Hb]]; [| inversion Hb].
               split; [exact Hbs |].
               right; exists (kw1 tt), (kw2 tt);
                 split; [reflexivity | split; [reflexivity | exact Hr]].
            -- destruct stk as [| [p1 p2] rest]; [exact I |].
               destruct Hstk as [Hr | Hb]; [| inversion Hb].
               right; exists (kw1 tt), (kw2 tt); split; [reflexivity | split; [reflexivity | exact Hr]].
      - eapply GSS_TauL; [rewrite (observe_bind w1 intr_cont), Hw1; reflexivity | exact IH].
      - eapply GSS_TauR; [rewrite (observe_bind w2 intr_cont), Hw2; reflexivity | exact IH].
      - eapply GSS_ReadL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GSS_ReadR; [rewrite Hw2, Eqit.bind_bind; reflexivity | exact Hlk | exact IH].
      - eapply GSS_WriteL; [rewrite Hw1, Eqit.bind_bind; reflexivity | exact IH].
      - eapply GSS_WriteR; [rewrite Hw2, Eqit.bind_bind; reflexivity | exact IH]. }
    assert (Hbranch_a :
      forall stk env1 env2 u1 u2 t1 t2,
        interp_intrinsics u1 ≅ t1 ->
        interp_intrinsics u2 ≅ t2 ->
        mcfg_stack_sim RR stk env1 env2 u1 u2 ->
        gen_stack_sim_ (@is_ub_mcfg) (@sync_non_local_mcfg) EqE_MCFG EqA_MCFG
          (@mcfg_event_post) (@as_local_mcfg) (@as_stack_mcfg) RR r_both
          stk env1 env2 t1 t2).
    { intros stk env1 env2 u1 u2 t1 t2 Et1 Et2 Hu.
      eapply gen_stack_sim__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
      punfold Hu; clear t1 t2 Et1 Et2.
      induction Hu as [stk env1 env2 u1 u2 Hstep
                       | stk env1 env2 u1 mu1 u2 Hu1 _ IH
                       | stk env1 env2 u1 u2 mu2 Hu2 _ IH
                       | stk env1 env2 u1 x v k1 u2 Hu1 Hlk _ IH
                       | stk env1 env2 u1 u2 x v k2 Hu2 Hlk _ IH
                       | stk env1 env2 u1 x v k1 u2 Hu1 _ IH
                       | stk env1 env2 u1 u2 x v k2 Hu2 _ IH].
      - eapply Hbranch_b; [apply decomp_intr_spec | apply decomp_intr_spec | apply Hstep_decomp, Hstep].
      - eapply gen_stack_sim__obs_eq with (t1 := Tau (interp_intrinsics mu1))
                                          (t2 := interp_intrinsics u2);
          [exact Hr_eq | symmetry; rewrite (itree_eta u1), Hu1, interp_intrinsics_Tau; reflexivity | reflexivity |].
        eapply GSS_TauL; [reflexivity | exact IH].
      - eapply gen_stack_sim__obs_eq with (t1 := interp_intrinsics u1)
                                          (t2 := Tau (interp_intrinsics mu2));
          [exact Hr_eq | reflexivity | symmetry; rewrite (itree_eta u2), Hu2, interp_intrinsics_Tau; reflexivity |].
        eapply GSS_TauR; [reflexivity | exact IH].
      - eapply GSS_ReadL with (x := x) (k1 := fun y => Tau (interp_intrinsics (k1 y))).
        + rewrite Hu1, !bind_trigger, interp_intrinsics_vis_eqit;
            cbn - [interp_intrinsics ITree.trigger ITree.bind];
            unfold F_trigger; cbn - [interp_intrinsics ITree.trigger ITree.bind];
            rewrite bind_trigger; reflexivity.
        + exact Hlk.
        + eapply GSS_TauL; [reflexivity | exact IH].
      - eapply GSS_ReadR with (x := x) (k2 := fun y => Tau (interp_intrinsics (k2 y))).
        + rewrite Hu2, !bind_trigger, interp_intrinsics_vis_eqit;
            cbn - [interp_intrinsics ITree.trigger ITree.bind];
            unfold F_trigger; cbn - [interp_intrinsics ITree.trigger ITree.bind];
            rewrite bind_trigger; reflexivity.
        + exact Hlk.
        + eapply GSS_TauR; [reflexivity | exact IH].
      - eapply GSS_WriteL with (x := x) (v := v) (k1 := fun y => Tau (interp_intrinsics (k1 y))).
        + rewrite Hu1, !bind_trigger, interp_intrinsics_vis_eqit;
            cbn - [interp_intrinsics ITree.trigger ITree.bind];
            unfold F_trigger; cbn - [interp_intrinsics ITree.trigger ITree.bind];
            rewrite bind_trigger; reflexivity.
        + eapply GSS_TauL; [reflexivity | exact IH].
      - eapply GSS_WriteR with (x := x) (v := v) (k2 := fun y => Tau (interp_intrinsics (k2 y))).
        + rewrite Hu2, !bind_trigger, interp_intrinsics_vis_eqit;
            cbn - [interp_intrinsics ITree.trigger ITree.bind];
            unfold F_trigger; cbn - [interp_intrinsics ITree.trigger ITree.bind];
            rewrite bind_trigger; reflexivity.
        + eapply GSS_TauR; [reflexivity | exact IH]. }
    assert (Hmain :
      forall stk env1 env2 t1 t2,
        r_both stk env1 env2 t1 t2 ->
        mcfg_stack_sim RR stk env1 env2 t1 t2).
    { pcofix CIH.
      intros stk env1 env2 t1 t2 Hrb; pstep.
      eapply gen_stack_sim__mon with (r := r_both);
        [| intros s0 e1 e2 a1 a2 Hr; right; apply CIH, Hr].
      destruct Hrb as [(v1 & v2 & Ev1 & Ev2 & Hv) | (w1 & w2 & Ew1 & Ew2 & Hw)].
      - eapply Hbranch_a; eassumption.
      - eapply Hbranch_b; eassumption. }
    intros stk env1 env2 u1 u2 Hsim.
    apply Hmain; left; exists u1, u2;
      split; [reflexivity | split; [reflexivity | exact Hsim]].
  Qed.

  (** *** Lowering [mcfg_stack_sim] to [interp_state interp_vellvm_prov_h] *)

  Definition sf_match (e1 e2 : @local_env (@ParamsV IP IPT))
    (sf1 sf2 : @stack_frame (@ParamsV IP IPT)) : Prop :=
    sf1.(stack_vars) = e1 /\
    sf2.(stack_vars) = e2 /\
    sf1.(stack_exc) = sf2.(stack_exc) /\
    sf1.(stack_loc) = sf2.(stack_loc).

  Inductive stk_frames_match :
    env_stack -> list (@stack_frame (@ParamsV IP IPT)) -> list (@stack_frame (@ParamsV IP IPT)) -> Prop :=
  | SFM_nil : stk_frames_match [] [] []
  | SFM_cons p1 p2 sf1 sf2 rest fstk1 fstk2 :
      sf_match p1 p2 sf1 sf2 ->
      stk_frames_match rest fstk1 fstk2 ->
      stk_frames_match ((p1, p2) :: rest) (sf1 :: fstk1) (sf2 :: fstk2).

  Definition fused_state_match
    (stk : env_stack) (env1 env2 : @local_env (@ParamsV IP IPT))
    (s1 s2 : FusedS) : Prop :=
    let '(m1, ((sf1, fstk1), g1)) := s1 in
    let '(m2, ((sf2, fstk2), g2)) := s2 in
    m1 = m2 /\
    g1 = g2 /\
    sf_match env1 env2 sf1 sf2 /\
    stk_frames_match stk fstk1 fstk2.

  Lemma lift_bot_prov_ret {T} (x : T) :
    lift_bot_prov (Ret x) ≅ Ret x.
  Proof using.
    unfold lift_bot_prov; rewrite unfold_translate; reflexivity.
  Qed.

  Lemma lift_bot_prov_bind_ret {A B} (x : A) (k : A -> itree MCFGEbot B) :
    lift_bot_prov (ITree.bind (Ret x) k) ≅ lift_bot_prov (k x).
  Proof using.
    unfold lift_bot_prov; rewrite translate_bind, translate_ret, Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma fused_local_prov_read_some (x : local_id) (v : @dvalue (@ParamsV IP IPT)) (s : FusedS)
    (Hlk : let '(_, ((sf, _), _)) := s in Maps.lookup x sf.(stack_vars) = Some v) :
    fused_local_prov _ (LocalRead x) s ≅ Ret (s, v).
  Proof using.
    destruct s as [m [[sf fstk] g]]; cbn - [RM.find] in Hlk.
    unfold fused_local_prov, on_ls_prov, handle_local_stack, handle_local_debug,
           handle_local, update_locals_ref; cbn - [RM.find Maps.add lift_bot_prov upd_local_sf].
    rewrite Hlk.
    unfold lift_bot_prov; rewrite !Eqit.bind_ret_l, translate_ret, !Eqit.bind_ret_l.
    destruct sf; unfold upd_local_sf; cbn [fst snd]; reflexivity.
  Qed.

  Lemma fused_local_prov_read_none (x : local_id) (s : FusedS)
    (Hlk : let '(_, ((sf, _), _)) := s in Maps.lookup x sf.(stack_vars) = None) :
    exists msg k,
      fused_local_prov _ (LocalRead x) s ≅
        Vis (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (Throw msg))))))) k.
  Proof using.
    destruct s as [m [[sf fstk] g]]; cbn - [RM.find] in Hlk.
    unfold fused_local_prov, on_ls_prov, handle_local_stack, handle_local_debug,
           handle_local, update_locals_ref, raise, trigger_cast, ITree.trigger;
      cbn - [RM.find Maps.add lift_bot_prov].
    rewrite Hlk.
    exists tt; eexists; unfold lift_bot_prov; rewrite !Eqit.bind_vis, translate_vis, Eqit.bind_vis;
      cbn [subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun];
      reflexivity.
  Qed.

  Lemma fused_local_prov_write (x : local_id) (v : @dvalue (@ParamsV IP IPT))
    (m : state) (sf : @stack_frame (@ParamsV IP IPT)) (fstk : stack) (g : global_env) :
    fused_local_prov _ (LocalWrite x v) (m, ((sf, fstk), g)) ≅
      Ret ((m, ((upd_local_sf sf (Maps.add x v sf.(stack_vars)), fstk), g)), tt).
  Proof using.
    unfold fused_local_prov, on_ls_prov, handle_local_stack, handle_local_debug,
           handle_local, update_locals_ref; cbn - [Maps.lookup Maps.add lift_bot_prov upd_local_sf].
    unfold lift_bot_prov; rewrite !Eqit.bind_ret_l, translate_ret, !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma memM_interp_prov_post {X} (P : X -> Prop)
    (m : @memM (@ParamsV IP IPT) _ X) (Hm : memM_all_ret P m) :
    forall (σ : state) (U : list N),
      refine_prov (fun _ '(σ1, r1) '(σ2, r2) => σ1 = σ2 /\ r1 = r2 /\ P r1)
        U (memM_interp_prov m σ) (memM_interp_prov m σ).
  Proof using.
    induction m as [x | s | s | s | k IH | σ' k IH | c k IH]; intros σ U; cbn in *.
    - pstep; apply RP_Step; cbn; split;
        [reflexivity | split; [reflexivity | exact Hm]].
    - unfold raiseOOM, trigger_cast, ITree.trigger; pstep; apply RP_Step;
        unfold rp_step_body; rewrite !observe_bind; cbn;
        right; right; split; [exact I | intros [] [] _].
    - unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply RP_Step;
        unfold rp_step_body; rewrite !observe_bind; cbn; left; reflexivity.
    - unfold raise, trigger_cast, ITree.trigger; pstep; apply RP_Step;
        unfold rp_step_body; rewrite !observe_bind; cbn;
        right; right; split; [exact I | intros [] [] _].
    - apply IH, Hm.
    - apply (IH tt Hm).
    - destruct c as [sz align | |]; cbn in *.
      + apply IH, Hm.
      + pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn.
        right; right; intros p _.
        left; eapply refine_prov_obs_eq;
          [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l | apply IH, Hm].
      + apply IH, Hm.
  Qed.

  Lemma interp_vellvm_prov_h_stack_sync {X1 X2}
    (e1 : @MCFGEtop (@ParamsV IP IPT) X1) (e2 : @MCFGEtop (@ParamsV IP IPT) X2)
    (Hsync : sync_non_local_mcfg e1 = true)
    (HE : EqE_MCFG X1 X2 e1 e2)
    stk env1 env2 (s1 s2 : FusedS)
    (Hmatch : fused_state_match stk env1 env2 s1 s2)
    (U : list N) :
    refine_prov
      (fun _ '(s1', a1) '(s2', a2) =>
         fused_state_match stk env1 env2 s1' s2' /\
         EqA_MCFG X1 X2 e1 a1 e2 a2 /\
         mcfg_event_post e1 a1)
      U (interp_vellvm_prov_h e1 s1) (interp_vellvm_prov_h e2 s2).
  Proof using.
    destruct s1 as [m1 [[sf1 fstk1] g1]], s2 as [m2 [[sf2 fstk2] g2]].
    destruct Hmatch as (<- & <- & Hsf & Hsfm).
    destruct_sum2 e1 e2 HE; try discriminate Hsync.
    - (* ExternalCallE *)
      destruct e1, e2; cbn in HE; try contradiction;
        repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
        unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_trigger_prov;
        (eapply refine_prov_bind;
         [apply refine_prov_refl with (RR := fun _ a1 a2 => a1 = a2); intros; reflexivity
         | intros U' a1 a2 _ <-; pstep; apply RP_Step; cbn;
           repeat (first [exact Hsf | exact Hsfm | reflexivity | split])]).
    - (* IntrinsicE *)
      destruct e1, e2; destruct HE as (<- & <- & <- & <-).
      unfold interp_vellvm_prov_h;
        cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
        unfold fused_intrinsic_prov, on_mem_prov.
      eapply refine_prov_bind;
        [apply refine_prov_refl with (RR := fun _ p1 p2 => p1 = p2); intros; reflexivity |].
      intros U' [m' r] _ _ <-; pstep; apply RP_Step; cbn.
      repeat (first [exact Hsf | exact Hsfm | reflexivity | split]).
    - (* GlobalE *)
      destruct e1, e2; cbn in HE; try contradiction;
        repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
        unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_global_prov, on_genv_prov;
        (eapply refine_prov_bind;
         [apply refine_prov_refl with (RR := fun _ p1 p2 => p1 = p2); intros; reflexivity
         | intros U' [g' r] _ _ <-; pstep; apply RP_Step; cbn;
           repeat (first [exact Hsf | exact Hsfm | reflexivity | split])]).
    - (* StackE: only StackRaise / StackGetExc satisfy Hsync *)
      destruct e1, e2; cbn in HE; try contradiction; try discriminate Hsync.
      + subst; unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_stack_prov, on_ls_prov, handle_stack.
        eapply refine_prov_obs_eq;
          [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
        destruct Hsf as (Hv1 & Hv2 & Hexc & Hloc).
        pstep; apply RP_Step; cbn; repeat split;
          try exact Hv1; try exact Hv2; try exact Hloc; try exact Hsfm; reflexivity.
      + unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_stack_prov, on_ls_prov, handle_stack.
        destruct Hsf as (Hv1 & Hv2 & Hexc & Hloc).
        rewrite <- Hexc.
        eapply refine_prov_obs_eq;
          [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
        pstep; apply RP_Step; cbn; repeat split;
          try exact Hv1; try exact Hv2; try exact Hloc; try exact Hsfm; reflexivity.
    - (* MemoryE *)
      destruct e1, e2; cbn in HE; try contradiction;
        repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end; subst;
        unfold interp_vellvm_prov_h;
          cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
          unfold fused_memory_prov, on_mem_prov, handle_memory;
        (eapply refine_prov_bind;
         [match goal with
          | |- context [handle_memoryM ?me] =>
              apply (memM_interp_prov_post _ _ (handle_memoryM_post me))
          end
         | intros U' [m1' r1] [m2' r2] _ (-> & <- & Hpost);
           pstep; apply RP_Step; cbn [rp_step_body observe fused_state_match mcfg_event_post];
           split; [repeat (first [exact Hsf | exact Hsfm | reflexivity | split]) |];
           split; [cbn; reflexivity | exact Hpost]]).
    - (* DrawE *)
      destruct e1 as [dt1], e2 as [dt2]; cbn in HE; subst dt2.
      unfold interp_vellvm_prov_h;
        cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
        unfold fused_draw_prov, handle_draw.
      destruct (default_dvalue_of_dtyp dt1) as [s | s | s | dv] eqn:Edef;
        cbn [EOU_to_itree ExtLib.Structures.Monad.ret Monad_itree].
      + unfold raise, trigger_cast, ITree.trigger, lift_bot_prov.
        pstep; apply RP_Step; unfold rp_step_body.
        repeat (rewrite observe_bind || rewrite observe_translate); cbn;
          right; right; split; [exact I | intros [] [] _].
      + unfold raiseOOM, trigger_cast, ITree.trigger, lift_bot_prov.
        pstep; apply RP_Step; unfold rp_step_body.
        repeat (rewrite observe_bind || rewrite observe_translate); cbn;
          right; right; split; [exact I | intros [] [] _].
      + unfold raiseUB, trigger_cast, ITree.trigger, lift_bot_prov.
        pstep; apply RP_Step; unfold rp_step_body.
        repeat (rewrite observe_bind || rewrite observe_translate); cbn; left; reflexivity.
      + eapply refine_prov_obs_eq;
          [symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
          | symmetry; rewrite lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
        pstep; apply RP_Step; cbn.
        split; [repeat (first [exact Hsf | exact Hsfm | reflexivity | split]) |].
        split; [reflexivity | intros Hsc; eapply default_dvalue_scalar_typ; eassumption].
    - (* OOME *)
      destruct e1, e2; unfold interp_vellvm_prov_h;
        cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
        unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body;
        rewrite !observe_bind; cbn;
        right; right; split; [exact I | intros [] [] _].
    - (* LLVMExcE *)
      destruct e1, e2; cbn in HE; subst; unfold interp_vellvm_prov_h;
        cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
        unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body;
        rewrite !observe_bind; cbn;
        right; right; split; [reflexivity | intros [] [] _].
    - (* UBE *)
      destruct e1, e2; unfold interp_vellvm_prov_h;
        cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
        unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body;
        rewrite !observe_bind; cbn; left; reflexivity.
    - (* DebugE *)
      destruct e1, e2; unfold interp_vellvm_prov_h;
        cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
        unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body; rewrite !observe_bind; cbn.
      right; right; split; [exact I | intros [] [] _].
      left; eapply refine_prov_obs_eq;
        [symmetry; apply Eqit.bind_ret_l | symmetry; apply Eqit.bind_ret_l |].
      pstep; apply RP_Step; cbn.
      repeat (first [exact Hsf | exact Hsfm | reflexivity | split]).
    - (* FailureE *)
      destruct e1, e2; unfold interp_vellvm_prov_h;
        cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
        unfold fused_trigger_prov, ITree.trigger.
      pstep; apply RP_Step; unfold rp_step_body;
        rewrite !observe_bind; cbn;
        right; right; split; [exact I | intros [] [] _].
  Qed.

  Definition decomp_model {R : Type} (u : @MCFGtop (@ParamsV IP IPT) R) (s : FusedS)
    : itree ProvBotE (model_step_state R) :=
    match observe u with
    | RetF r => Ret (inl (s, r))
    | TauF m => Ret (inr (s, m))
    | VisF _ e k => ITree.bind (interp_vellvm_prov_h e s) (fun '(s', x) => Ret (inr (s', k x)))
    end.

  Lemma decomp_model_spec {R : Type} (u : @MCFGtop (@ParamsV IP IPT) R) (s : FusedS) :
    ITree.bind (decomp_model u s) (model_cont R) ≅ interp_state interp_vellvm_prov_h u s.
  Proof using.
    unfold decomp_model; rewrite (unfold_interp_state interp_vellvm_prov_h u s).
    destruct (observe u) as [r | m | X e k]; cbn -[interp_vellvm_prov_h].
    - rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_ret_l; reflexivity.
    - rewrite Eqit.bind_bind; apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity |].
      intros [s' x] ? <-; rewrite Eqit.bind_ret_l; reflexivity.
  Qed.

  Definition model_stack_step_rel {R1 R2}
    (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop)
    : list N -> model_step_state R1 -> model_step_state R2 -> Prop :=
    fun _ x1 x2 =>
      match x1, x2 with
      | inl (s1, r1), inl (s2, r2) =>
          exists stk e1 e2, fused_state_match stk e1 e2 s1 s2 /\ RR stk e1 e2 r1 r2
      | inr (s1, u1), inr (s2, u2) =>
          exists stk e1 e2, fused_state_match stk e1 e2 s1 s2 /\ mcfg_stack_sim RR stk e1 e2 u1 u2
      | _, _ => False
      end.

  Local Lemma mcfg_stack_sim_to_model_step_decomp {R1 R2}
    (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    forall U stk env1 env2 (s1 s2 : FusedS)
      (u1 : @MCFGtop (@ParamsV IP IPT) R1)
      (u2 : @MCFGtop (@ParamsV IP IPT) R2),
      fused_state_match stk env1 env2 s1 s2 ->
      gss_step_body (@is_ub_mcfg) (@sync_non_local_mcfg) EqE_MCFG EqA_MCFG
        (@mcfg_event_post) (@as_local_mcfg) (@as_stack_mcfg)
        RR (upaco5 (gen_stack_sim_ (@is_ub_mcfg) (@sync_non_local_mcfg) EqE_MCFG EqA_MCFG
                      (@mcfg_event_post) (@as_local_mcfg) (@as_stack_mcfg) RR) bot5)
        stk env1 env2 (observe u1) (observe u2) ->
      refine_prov (model_stack_step_rel RR) U (decomp_model u1 s1) (decomp_model u2 s2).
  Proof using.
    intros U stk env1 env2 s1 s2 u1 u2 Hmatch Hstep.
    unfold gss_step_body, decomp_model in *.
    destruct (observe u1) as [r1 | m1 | X1 ev1 k1] eqn:Hou1.
    - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
      pstep; apply RP_Step; cbn;
        exists stk, env1, env2; split; assumption.
    - destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
      destruct Hstep as [Hstep | Hb]; [| inversion Hb].
      pstep; apply RP_Step; cbn;
        exists stk, env1, env2; split; assumption.
    - destruct Hstep as [Hub | Hvis].
      + destruct_sum1 ev1; try discriminate Hub; destruct ev1 as [u].
        pstep; apply RP_Step; unfold rp_step_body;
          rewrite !observe_bind; cbn; left; reflexivity.
      + destruct (observe u2) as [r2 | m2 | X2 ev2 k2] eqn:Hou2; try contradiction.
        destruct Hvis as [(Hsync & HE & HA) | [Hloc | Hstk]].
        * eapply refine_prov_bind;
            [eapply interp_vellvm_prov_h_stack_sync; eassumption |].
          intros U' [s1' a1] [s2' a2] _ (Hm' & Ha & Hp).
          specialize (HA a1 a2 Ha Hp); destruct HA as [HA | Hb]; [| inversion Hb].
          pstep; apply RP_Step; cbn;
            exists stk, env1, env2; split; [exact Hm' | exact HA].
        * destruct (as_local_mcfg ev1) as [le1 |] eqn:Ele1,
                   (as_local_mcfg ev2) as [le2 |] eqn:Ele2; try contradiction.
          destruct le1 as [x1 v1 | x1], le2 as [x2 v2 | x2]; try contradiction;
            destruct_sum1 ev1; try discriminate Ele1;
            destruct_sum1 ev2; try discriminate Ele2;
            inversion Ele1; subst; inversion Ele2; subst;
            unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
            destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
          -- destruct Hloc as (<- & <- & [Hr | Hb]); [| inversion Hb].
             destruct Hmatch as (<- & <- & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
             eapply refine_prov_obs_eq;
               [symmetry; rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity
               | symmetry; rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity |].
             pstep; apply RP_Step; cbn.
             exists stk, (Maps.add x1 v1 env1), (Maps.add x1 v1 env2); split; [| exact Hr].
             rewrite Hvars1, Hvars2; repeat split;
               try exact Hexc; try exact Hloc; try exact Hsfm; reflexivity.
          -- destruct Hloc as (<- & Hlk_eq & Hrd).
             pose proof Hmatch as (Hmm & Hgg & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
             destruct (Maps.lookup x1 env1) as [v |] eqn:Elkv.
             ++ assert (Elkv2 : Maps.lookup x1 env2 = Some v) by congruence.
                eapply refine_prov_obs_eq.
                ** symmetry; rewrite (fused_local_prov_read_some x1 v (mm1, ((sf1, fstk1), gg1))
                                       (ltac:(cbn; rewrite Hvars1; exact Elkv))), Eqit.bind_ret_l; reflexivity.
                ** symmetry; rewrite (fused_local_prov_read_some x1 v (mm2, ((sf2, fstk2), gg2))
                                       (ltac:(cbn; rewrite Hvars2; exact Elkv2))), Eqit.bind_ret_l; reflexivity.
                ** specialize (Hrd v Logic.eq_refl); destruct Hrd as [Hrd | Hb]; [| inversion Hb].
                   pstep; apply RP_Step; cbn;
                     exists stk, env1, env2; split; [exact Hmatch | exact Hrd].
             ++ assert (Elkv2 : Maps.lookup x1 env2 = None) by congruence.
                destruct (fused_local_prov_read_none x1 (mm1, ((sf1, fstk1), gg1))
                            (ltac:(cbn; rewrite Hvars1; exact Elkv))) as (msg1 & kf1 & Ef1).
                destruct (fused_local_prov_read_none x1 (mm2, ((sf2, fstk2), gg2))
                            (ltac:(cbn; rewrite Hvars2; exact Elkv2))) as (msg2 & kf2 & Ef2).
                eapply refine_prov_obs_eq;
                  [symmetry; rewrite Ef1, Eqit.bind_vis; reflexivity
                  | symmetry; rewrite Ef2, Eqit.bind_vis; reflexivity |].
                pstep; apply RP_Step; cbn;
                  right; right; split; [exact I | intros [] [] _].
        * destruct (as_stack_mcfg ev1) as [se1 |] eqn:Ese1,
                   (as_stack_mcfg ev2) as [se2 |] eqn:Ese2; try contradiction.
          destruct se1, se2; try contradiction;
            destruct_sum1 ev1; try discriminate Ese1;
            destruct_sum1 ev2; try discriminate Ese2;
            inversion Ese1; subst; inversion Ese2; subst;
            unfold interp_vellvm_prov_h; cbn [case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_];
            destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]];
            destruct Hmatch as (<- & <- & Hsf & Hsfm).
          -- destruct Hstk as [<- [Hr | Hb]]; [| inversion Hb].
             unfold fused_stack_prov, on_ls_prov, handle_stack;
               cbn - [Maps.lookup Maps.add lift_bot_prov init_local_env].
             eapply refine_prov_obs_eq;
               [symmetry; rewrite lift_bot_prov_bind_ret, lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
               | symmetry; rewrite lift_bot_prov_bind_ret, lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
             pstep; apply RP_Step; cbn.
             eexists ((env1, env2) :: stk), _, _.
             split; [| exact Hr].
             repeat split; try reflexivity.
             apply SFM_cons; [exact Hsf | exact Hsfm].
          -- destruct stk as [| [p1 p2] rest].
             ++ inversion Hsfm; subst.
                unfold fused_stack_prov, on_ls_prov, handle_stack, raise, trigger_cast, ITree.trigger, lift_bot_prov;
                  cbn - [Maps.lookup Maps.add lift_bot_prov].
                pstep; apply RP_Step; unfold rp_step_body;
                  repeat (rewrite observe_bind || rewrite observe_translate); cbn.
                right; right; split; [exact I | intros [] [] _].
             ++ destruct Hstk as [Hr | Hb]; [| inversion Hb].
                inversion Hsfm as [| ? ? sf1' sf2' ? fstk1' fstk2' Hsf' Hsfm']; subst.
                unfold fused_stack_prov, on_ls_prov, handle_stack;
                  cbn - [Maps.lookup Maps.add lift_bot_prov init_local_env].
                eapply refine_prov_obs_eq;
                  [symmetry; rewrite lift_bot_prov_bind_ret, lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity
                  | symmetry; rewrite lift_bot_prov_bind_ret, lift_bot_prov_ret, Eqit.bind_ret_l; reflexivity |].
                pstep; apply RP_Step; cbn.
                exists rest, p1, p2; split; [| exact Hr].
                repeat (first [exact Hsf' | exact Hsfm' | reflexivity | split]).
  Qed.

  Lemma mcfg_stack_sim_to_model {R1 R2}
    (RR : env_stack -> @local_env (@ParamsV IP IPT) -> @local_env (@ParamsV IP IPT) -> R1 -> R2 -> Prop) :
    forall U stk env1 env2 (s1 s2 : FusedS)
      (u1 : @MCFGtop (@ParamsV IP IPT) R1)
      (u2 : @MCFGtop (@ParamsV IP IPT) R2),
      fused_state_match stk env1 env2 s1 s2 ->
      mcfg_stack_sim RR stk env1 env2 u1 u2 ->
      refine_prov
        (fun _ '(s1', r1) '(s2', r2) =>
           exists stk' e1' e2', fused_state_match stk' e1' e2' s1' s2' /\ RR stk' e1' e2' r1 r2)
        U
        (interp_state interp_vellvm_prov_h u1 s1)
        (interp_state interp_vellvm_prov_h u2 s2).
  Proof using.
    set (RR_out := fun (_ : list N) '(s1', r1) '(s2', r2) =>
                     exists stk' e1' e2',
                       fused_state_match stk' e1' e2' s1' s2' /\ RR stk' e1' e2' r1 r2).
    pose proof (@mcfg_stack_sim_to_model_step_decomp R1 R2 RR) as Hstep_decomp.
    set (r_both := fun U0 (a1 : itree ProvBotE (FusedS * R1)) (a2 : itree ProvBotE (FusedS * R2)) =>
                     (exists stk e1 e2 s1 s2 v1 v2,
                        interp_state interp_vellvm_prov_h v1 s1 ≅ a1 /\
                        interp_state interp_vellvm_prov_h v2 s2 ≅ a2 /\
                        fused_state_match stk e1 e2 s1 s2 /\
                        mcfg_stack_sim RR stk e1 e2 v1 v2) \/
                     (exists w1 w2,
                        ITree.bind w1 (model_cont R1) ≅ a1 /\
                        ITree.bind w2 (model_cont R2) ≅ a2 /\
                        refine_prov (model_stack_step_rel RR) U0 w1 w2)).
    assert (Hr_eq :
      forall U0 a1 a1' a2 a2',
        a1 ≅ a1' -> a2 ≅ a2' -> r_both U0 a1 a2 -> r_both U0 a1' a2').
    { intros U0 a1 a1' a2 a2' Ea1 Ea2
        [(stk & e1 & e2 & s1 & s2 & v1 & v2 & Ev1 & Ev2 & Hm & Hv) | (w1 & w2 & Ew1 & Ew2 & Hw)].
      - left; exists stk, e1, e2, s1, s2, v1, v2.
        split;
          [ etransitivity; eassumption
          | split; [etransitivity; eassumption | split; assumption] ].
      - right; exists w1, w2.
        split; [etransitivity; eassumption | split; [etransitivity; eassumption | exact Hw]]. }
    assert (Hbranch_b :
      forall U0 w1 w2 t1 t2,
        ITree.bind w1 (model_cont R1) ≅ t1 ->
        ITree.bind w2 (model_cont R2) ≅ t2 ->
        refine_prov (model_stack_step_rel RR) U0 w1 w2 ->
        refine_prov_ RR_out r_both U0 t1 t2).
    { intros U0 w1 w2 t1 t2 Et1 Et2 Hw.
      eapply refine_prov__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
      punfold Hw; clear t1 t2 Et1 Et2.
      induction Hw as [U0 w1 w2 Hstep | U0 w1 mw1 w2 Hw1 _ IH | U0 w1 w2 mw2 Hw2 _ IH].
      - unfold rp_step_body in Hstep.
        destruct (observe w1) as [x1 | mw1 | X1 ev1 kw1] eqn:How1.
        + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction.
          destruct x1 as [[s1 r1] | [s1 v1]], x2 as [[s2 r2] | [s2 v2]]; cbn in Hstep; try contradiction.
          * apply RP_Step; unfold rp_step_body; rewrite !observe_bind, How1, How2; cbn; exact Hstep.
          * destruct Hstep as (stk & e1 & e2 & Hm & Hv).
            apply RP_Step; unfold rp_step_body; rewrite !observe_bind, How1, How2; cbn.
            left; exists stk, e1, e2, s1, s2, v1, v2;
              split; [reflexivity | split; [reflexivity | split; assumption]].
        + destruct (observe w2) as [x2 | mw2 | X2 ev2 kw2] eqn:How2; try contradiction; pclearbot.
          apply RP_Step; unfold rp_step_body; rewrite !observe_bind, How1, How2.
          right; exists mw1, mw2; split; [reflexivity | split; [reflexivity | exact Hstep]].
        + apply RP_Step; unfold rp_step_body; rewrite (observe_bind w1 (model_cont R1)), How1.
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
      - eapply RP_TauR; [rewrite (observe_bind w2 (model_cont R2)), Hw2; reflexivity | exact IH]. }
    assert (Hbranch_a :
      forall U0 stk env1 env2 s1 s2 u1 u2 t1 t2,
        interp_state interp_vellvm_prov_h u1 s1 ≅ t1 ->
        interp_state interp_vellvm_prov_h u2 s2 ≅ t2 ->
        fused_state_match stk env1 env2 s1 s2 ->
        mcfg_stack_sim RR stk env1 env2 u1 u2 ->
        refine_prov_ RR_out r_both U0 t1 t2).
    { intros U0 stk env1 env2 s1 s2 u1 u2 t1 t2 Et1 Et2 Hmatch Hu.
      eapply refine_prov__obs_eq; [exact Hr_eq | exact Et1 | exact Et2 |].
      punfold Hu; clear t1 t2 Et1 Et2.
      revert s1 s2 Hmatch;
        induction Hu as [stk env1 env2 u1 u2 Hstep
                         | stk env1 env2 u1 mu1 u2 Hu1 _ IH
                         | stk env1 env2 u1 u2 mu2 Hu2 _ IH
                         | stk env1 env2 u1 x v k1 u2 Hu1 Hlk _ IH
                         | stk env1 env2 u1 u2 x v k2 Hu2 Hlk _ IH
                         | stk env1 env2 u1 x v k1 u2 Hu1 _ IH
                         | stk env1 env2 u1 u2 x v k2 Hu2 _ IH];
        intros s1 s2 Hmatch.
      - eapply Hbranch_b;
          [apply decomp_model_spec | apply decomp_model_spec | eapply Hstep_decomp; eassumption].
      - eapply refine_prov__obs_eq with (t1 := Tau (interp_state interp_vellvm_prov_h mu1 s1))
                                        (t2 := interp_state interp_vellvm_prov_h u2 s2);
          [exact Hr_eq
          | symmetry; rewrite (unfold_interp_state interp_vellvm_prov_h u1 s1), Hu1; reflexivity
          | reflexivity |].
        eapply RP_TauL; [reflexivity | apply IH, Hmatch].
      - eapply refine_prov__obs_eq with (t1 := interp_state interp_vellvm_prov_h u1 s1)
                                        (t2 := Tau (interp_state interp_vellvm_prov_h mu2 s2));
          [exact Hr_eq
          | reflexivity
          | symmetry; rewrite (unfold_interp_state interp_vellvm_prov_h u2 s2), Hu2; reflexivity |].
        eapply RP_TauR; [reflexivity | apply IH, Hmatch].
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        pose proof Hmatch as (_ & _ & (Hvars1 & _) & _).
        eapply refine_prov__obs_eq
          with (t1 := Tau (interp_state interp_vellvm_prov_h (k1 v) (mm1, ((sf1, fstk1), gg1))))
               (t2 := interp_state interp_vellvm_prov_h u2 (mm2, ((sf2, fstk2), gg2))).
        + exact Hr_eq.
        + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
            cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_
                 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun
                 inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
          rewrite (fused_local_prov_read_some x v (mm1, ((sf1, fstk1), gg1))
                     (ltac:(cbn - [Maps.lookup]; rewrite Hvars1; exact Hlk))),
                  Eqit.bind_ret_l; reflexivity.
        + reflexivity.
        + eapply RP_TauL; [reflexivity | apply IH, Hmatch].
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        pose proof Hmatch as (_ & _ & (_ & Hvars2 & _) & _).
        eapply refine_prov__obs_eq
          with (t1 := interp_state interp_vellvm_prov_h u1 (mm1, ((sf1, fstk1), gg1)))
               (t2 := Tau (interp_state interp_vellvm_prov_h (k2 v) (mm2, ((sf2, fstk2), gg2)))).
        + exact Hr_eq.
        + reflexivity.
        + symmetry; rewrite Hu2, bind_trigger, interp_state_vis;
            cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_
                 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun
                 inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
          rewrite (fused_local_prov_read_some x v (mm2, ((sf2, fstk2), gg2))
                     (ltac:(cbn - [Maps.lookup]; rewrite Hvars2; exact Hlk))),
                  Eqit.bind_ret_l; reflexivity.
        + eapply RP_TauR; [reflexivity | apply IH, Hmatch].
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        destruct Hmatch as (<- & <- & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
        eapply refine_prov__obs_eq with
          (t1 := Tau (interp_state interp_vellvm_prov_h (k1 tt)
                        (mm1, ((upd_local_sf sf1 (Maps.add x v sf1.(stack_vars)), fstk1), gg1))))
          (t2 := interp_state interp_vellvm_prov_h u2 (mm1, ((sf2, fstk2), gg1))).
        + exact Hr_eq.
        + symmetry; rewrite Hu1, bind_trigger, interp_state_vis;
            cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_
                 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun
                 inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
          try change (resum IFun unit (LocalWrite x v)) with (LocalWrite x v);
          rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity.
        + reflexivity.
        + eapply RP_TauL; [reflexivity | apply IH].
          rewrite Hvars1; repeat split;
            try exact Hvars2; try exact Hexc; try exact Hloc; try exact Hsfm; reflexivity.
      - destruct s1 as [mm1 [[sf1 fstk1] gg1]], s2 as [mm2 [[sf2 fstk2] gg2]].
        destruct Hmatch as (<- & <- & (Hvars1 & Hvars2 & Hexc & Hloc) & Hsfm).
        eapply refine_prov__obs_eq with
          (t1 := interp_state interp_vellvm_prov_h u1 (mm1, ((sf1, fstk1), gg1)))
          (t2 := Tau (interp_state interp_vellvm_prov_h (k2 tt)
                        (mm1, ((upd_local_sf sf2 (Maps.add x v sf2.(stack_vars)), fstk2), gg1)))).
        + exact Hr_eq.
        + reflexivity.
        + symmetry; rewrite Hu2, bind_trigger, interp_state_vis;
            cbn [interp_vellvm_prov_h case_ Case_sum1 case_sum1 Case_sum1_Handler Handler.case_
                 subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun
                 inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
          try change (resum IFun unit (LocalWrite x v)) with (LocalWrite x v);
          rewrite fused_local_prov_write, Eqit.bind_ret_l; reflexivity.
        + eapply RP_TauR; [reflexivity | apply IH].
          rewrite Hvars2; repeat split;
            try exact Hvars1; try exact Hexc; try exact Hloc; try exact Hsfm; reflexivity. }
    assert (Hmain :
      forall U0 t1 t2,
        r_both U0 t1 t2 ->
        refine_prov RR_out U0 t1 t2).
    { pcofix CIH.
      intros U0 t1 t2 Hrb; pstep.
      eapply refine_prov__mon with (r := r_both);
        [| intros U1 a1 a2 Hr; right; apply CIH, Hr].
      destruct Hrb as [(stk & e1 & e2 & s1 & s2 & v1 & v2 & Ev1 & Ev2 & Hm & Hv) | (w1 & w2 & Ew1 & Ew2 & Hw)].
      - eapply Hbranch_a; eassumption.
      - eapply Hbranch_b; eassumption. }
    intros U stk env1 env2 s1 s2 u1 u2 Hmatch Hsim.
    apply Hmain; left; exists stk, env1, env2, s1, s2, u1, u2;
      split; [reflexivity | split; [reflexivity | split; assumption]].
  Qed.

  (** ** Modular Per-CFG Local-Environment Lifter ([lift_cfg_with_args_local_pass] & [lift_cfg_local_pass]) *)

  Lemma mcfg_stack_sim_refl_diag {R} :
    forall stk env (t : @MCFGtop (@ParamsV IP IPT) R),
      Forall (fun '(p1, p2) => p1 = p2) stk ->
      mcfg_stack_sim
        (fun stk' e1' e2' r1 r2 =>
           Forall (fun '(p1, p2) => p1 = p2) stk' /\ e1' = e2' /\ r1 = r2)
        stk env env t t.
  Proof using.
    pcofix CIH.
    intros stk env t Hstk; pstep; apply GSS_Step; unfold gss_step_body.
    destruct (observe t) as [x | m | X ev k].
    - split; [exact Hstk | split; reflexivity].
    - right; apply CIH, Hstk.
    - right.
      destruct (sync_non_local_mcfg ev) eqn:Esync.
      + left; split; [exact Esync | split; [apply EqE_MCFG_refl |]].
        intros a1 a2 Ha _; apply EqA_MCFG_eq in Ha; subst a2; right; apply CIH, Hstk.
      + destruct_sum1 ev; try discriminate Esync.
        * destruct ev as [x v | x]; right; left; cbn.
          -- split; [reflexivity | split; [reflexivity | right; apply CIH, Hstk]].
          -- split; [reflexivity | split; [reflexivity | intros v _; right; apply CIH, Hstk]].
        * destruct ev as [bs | | |]; try discriminate Esync; right; right; cbn.
          -- split; [reflexivity | right; apply CIH; constructor; [reflexivity | exact Hstk]].
          -- destruct stk as [| [p1 p2] rest]; [exact I |].
             pose proof (Forall_inv Hstk) as Heq; cbn in Heq; subst p2; right; apply CIH, (Forall_inv_tail Hstk).
  Qed.

  Lemma i8_str_index_stack_sync strptr index stk env1 env2 :
    cfg_stack_sim
      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
      stk env1 env2 (i8_str_index strptr index) (i8_str_index strptr index).
  Proof using.
    unfold i8_str_index.
    eapply gen_stack_sim_bind; [apply cfg_stack_sim_EOU | intros ? ? ? iptr _ (-> & -> & -> & <-)].
    eapply gen_stack_sim_bind; [apply cfg_stack_sim_EOU | intros ? ? ? addr _ (-> & -> & -> & <-)].
    eapply gen_stack_sim_bind.
    { unfold load, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq]. }
    intros ? ? ? d_byte _ (-> & -> & -> & <-).
    destruct d_byte as [[| sz b | | | | | |] | |];
      try (unfold raise; apply gen_stack_sim_trigger_cast_sync;
           [reflexivity | apply EqE_CFG_refl]).
    destruct sz as [p | p |];
      try (unfold raise; apply gen_stack_sim_trigger_cast_sync;
           [reflexivity | apply EqE_CFG_refl]);
      destruct p as [p | p |];
      try (unfold raise; apply gen_stack_sim_trigger_cast_sync;
           [reflexivity | apply EqE_CFG_refl]);
      destruct p as [p | p |];
      try (unfold raise; apply gen_stack_sim_trigger_cast_sync;
           [reflexivity | apply EqE_CFG_refl]);
      destruct p as [p | p |];
      try (unfold raise; apply gen_stack_sim_trigger_cast_sync;
           [reflexivity | apply EqE_CFG_refl]).
    apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma i8_str_index_local_sync strptr index env1 env2 :
    cfg_local_sim
      (fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2)
      env1 env2 (i8_str_index strptr index) (i8_str_index strptr index).
  Proof using.
    assert (Heou : forall A (m : EOU A) e1 e2,
              cfg_local_sim (fun e1' e2' r1 r2 => e1' = e1 /\ e2' = e2 /\ r1 = r2)
                e1 e2 (EOU_to_itree m) (EOU_to_itree m)).
    { intros A [s | s | s | x] e1 e2; cbn [EOU_to_itree].
      - unfold raise, trigger_cast, ITree.trigger; pstep; apply CLS_Step;
          unfold cls_step_body; rewrite !observe_bind; cbn;
          right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
      - unfold raiseOOM, trigger_cast, ITree.trigger; pstep; apply CLS_Step;
          unfold cls_step_body; rewrite !observe_bind; cbn;
          right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]].
      - unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply CLS_Step;
          unfold cls_step_body; rewrite !observe_bind; cbn; left; reflexivity.
      - apply cfg_local_sim_ret; repeat split; reflexivity. }
    assert (Herr : forall msg A e1 e2,
              cfg_local_sim (fun e1' e2' (r1 r2 : A) => e1' = e1 /\ e2' = e2 /\ r1 = r2)
                e1 e2 (raise msg) (raise msg)).
    { intros msg A e1 e2; unfold raise, trigger_cast, ITree.trigger; pstep; apply CLS_Step;
        unfold cls_step_body; rewrite !observe_bind; cbn;
        right; left; split; [reflexivity | split; [apply EqE_CFG_refl | intros [] [] _ _]]. }
    unfold i8_str_index.
    eapply cfg_local_sim_bind; [apply Heou | intros ? ? iptr _ (-> & -> & <-)].
    eapply cfg_local_sim_bind; [apply Heou | intros ? ? addr _ (-> & -> & <-)].
    eapply cfg_local_sim_bind with
      (RR := fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2).
    { unfold load, trigger_cast, ITree.trigger; pstep; apply CLS_Step; cbn;
        right; left; split; [reflexivity | split; [apply EqE_CFG_refl |]].
      intros a1 a2 Ha _; apply EqA_CFG_eq in Ha; subst a2;
        left; apply cfg_local_sim_ret; repeat split; reflexivity. }
    intros ? ? d_byte _ (-> & -> & <-).
    destruct d_byte as [[| sz b | | | | | |] | |]; try apply Herr.
    destruct sz as [p | p |]; try apply Herr;
      destruct p as [p | p |]; try apply Herr;
      destruct p as [p | p |]; try apply Herr;
      destruct p as [p | p |]; try apply Herr.
    apply cfg_local_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma putchar_denotation_sync :
    forall stk env1 env2 cc args,
      cfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2 (putchar_denotation cc args) (putchar_denotation cc args).
  Proof using.
    intros stk env1 env2 cc args; unfold putchar_denotation.
    destruct args as [| ch [| ? ?]];
      try (unfold raise; apply gen_stack_sim_trigger_cast_sync;
           [reflexivity | apply EqE_CFG_refl]).
    cbn [Functor.fmap Functor_itree]; unfold ITree.map.
    eapply gen_stack_sim_bind with
      (RR := fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2);
      [| intros ? ? ? dv _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity].
    destruct ch as [[| sz x32 | | | | | |] | |];
      try (unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply GSS_Step;
           unfold gss_step_body; rewrite !observe_bind; cbn; left; reflexivity).
    destruct (Pos.eq_dec 32 sz) as [<- | _];
      [| unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply GSS_Step;
         unfold gss_step_body; rewrite !observe_bind; cbn; left; reflexivity].
    eapply gen_stack_sim_bind.
    - unfold io_stdout, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq].
    - intros ? ? ? _ _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma puts_denotation_sync :
    forall stk env1 env2 cc args,
      cfg_stack_sim
        (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
        stk env1 env2 (puts_denotation cc args) (puts_denotation cc args).
  Proof using.
    intros stk env1 env2 cc args; unfold puts_denotation.
    destruct args as [| u_strptr [| ? ?]];
      try (unfold raise; apply gen_stack_sim_trigger_cast_sync;
           [reflexivity | apply EqE_CFG_refl]).
    cbn [Functor.fmap Functor_itree]; unfold ITree.map.
    eapply gen_stack_sim_bind with
      (RR := fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2);
      [| intros ? ? ? dv _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity].
    destruct u_strptr as [[strptr | | | | | | |] | |];
      try (unfold raiseUB, trigger_cast, ITree.trigger; pstep; apply GSS_Step;
           unfold gss_step_body; rewrite !observe_bind; cbn; left; reflexivity).
    eapply gen_stack_sim_bind; [apply i8_str_index_stack_sync |].
    intros ? ? ? ch _ (-> & -> & -> & <-).
    eapply gen_stack_sim_bind with
      (RR := fun stk' e1' e2' r1 r2 => stk' = stk /\ (e1' = env1 /\ e2' = env2 /\ r1 = r2)).
    - apply cfg_local_to_stack_sim.
      eapply cfg_local_sim_iter with
        (RI := fun e1' e2' s1 s2 => e1' = env1 /\ e2' = env2 /\ s1 = s2)
        (RR := fun e1' e2' r1 r2 => e1' = env1 /\ e2' = env2 /\ r1 = r2);
        [| repeat split; reflexivity].
      intros e1' e2' [[c bytes] offset] _ (-> & -> & <-).
      destruct (@Integers.eq 8 c (@Integers.zero 8)).
      + apply cfg_local_sim_ret; cbn; repeat split; reflexivity.
      + eapply cfg_local_sim_bind; [apply i8_str_index_local_sync |].
        intros ? ? next_char _ (-> & -> & <-); apply cfg_local_sim_ret; cbn; repeat split; reflexivity.
    - intros ? ? ? bytes _ (-> & -> & -> & <-).
      eapply gen_stack_sim_bind.
      + unfold io_stdout, trigger_cast; apply gen_stack_sim_trigger_sync;
          [reflexivity | apply EqE_CFG_refl | apply EqA_CFG_eq].
      + intros ? ? ? _ _ (-> & -> & -> & <-); apply gen_stack_sim_ret; repeat split; reflexivity.
  Qed.

  Lemma library_functions_stack_sync (decls : list (declaration dtyp)) :
    Forall
      (fun '(_, den) =>
         forall stk env1 env2 cc args,
           cfg_stack_sim
             (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
             stk env1 env2 (den cc args) (den cc args))
      (library_functions decls).
  Proof using.
    unfold library_functions, _LIBRARIES; cbn [List.filter].
    destruct (existsb _ _); destruct (existsb _ _);
      repeat constructor;
      first [apply puts_denotation_sync | apply putchar_denotation_sync].
  Qed.

  Definition map_defn_with_args {T : Set}
    (f : list local_id -> CFG.cfg T -> CFG.cfg T)
    (df : definition T (CFG.cfg T)) : definition T (CFG.cfg T) :=
    {| df_prototype := df_prototype df;
       df_args      := df_args df;
       df_instrs    := f (df_args df) (df_instrs df) |}.

  Definition map_mcfg_with_args {T : Set}
    (f : list local_id -> CFG.cfg T -> CFG.cfg T) (M : CFG.mcfg T) : CFG.mcfg T :=
    {| m_name         := m_name M;
       m_target       := m_target M;
       m_datalayout   := m_datalayout M;
       m_type_defs    := m_type_defs M;
       m_globals      := m_globals M;
       m_declarations := m_declarations M;
       m_definitions  := List.map (map_defn_with_args f) (m_definitions M) |}.

  Lemma map_mcfg_with_args_prototypes {T : Set}
    (f : list local_id -> CFG.cfg T -> CFG.cfg T) (M : CFG.mcfg T) :
    List.map df_prototype (m_definitions (map_mcfg_with_args f M)) =
    List.map df_prototype (m_definitions M).
  Proof using.
    cbn [map_mcfg_with_args m_definitions]; rewrite map_map; reflexivity.
  Qed.

  Lemma map_mcfg_with_args_block_addresses {T : Set}
    (f : list local_id -> CFG.cfg T -> CFG.cfg T) (M : CFG.mcfg T)
    (Hba : forall fargs c,
             flat_map block_block_addresses (blks (f fargs c)) =
             flat_map block_block_addresses (blks c)) :
    mcfg_block_addresses (map_mcfg_with_args f M) = mcfg_block_addresses M.
  Proof using.
    unfold mcfg_block_addresses; cbn [map_mcfg_with_args m_globals m_definitions].
    f_equal.
    induction (m_definitions M) as [| d ds IH]; [reflexivity |].
    cbn [List.map flat_map map_defn_with_args df_instrs].
    rewrite Hba, IH; reflexivity.
  Qed.

  Lemma of_list_fn_ctx_stack_sim
    (l1 l2 : list (Z * @function_denotation (@ParamsV IP IPT)))
    (Hl : Forall2
            (fun '(k1, f1) '(k2, f2) =>
               k1 = k2 /\
               forall stk env1 env2 cc args,
                 cfg_stack_sim
                   (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
                   stk env1 env2 (f1 cc args) (f2 cc args))
            l1 l2) :
    forall k,
      option_rel
        (fun f1 f2 =>
           forall stk env1 env2 cc args,
             cfg_stack_sim
               (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
               stk env1 env2 (f1 cc args) (f2 cc args))
        (lookup k (IntMaps.IP.of_list l1))
        (lookup k (IntMaps.IP.of_list l2)).
  Proof using.
    induction Hl as [| [k1 f1] [k2 f2] l1' l2' [<- Hf] _ IH]; intros k.
    - cbn; constructor.
    - cbn [IntMaps.IP.of_list fold_right]; unfold IntMaps.IP.uncurry, lookup; cbn [fst snd].
      destruct (Z.eq_dec k1 k) as [<- | Hne].
      + rewrite !IntMaps.IP.F.add_eq_o by reflexivity; constructor; exact Hf.
      + rewrite !IntMaps.IP.F.add_neq_o by exact Hne; apply IH.
  Qed.

  Lemma map_monad_address_one_function_stack_sim
    (f : list local_id -> CFG.cfg dtyp -> CFG.cfg dtyp)
    (Hbody : forall fargs c env va,
               (forall x, In x fargs -> exists v, Maps.lookup x env = Some v) ->
               cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                 env env (denote_cfg c va) (denote_cfg (f fargs c) va)) :
    forall (defs : list (definition dtyp (CFG.cfg dtyp))) stk env1 env2,
      mcfg_stack_sim
        (fun stk' e1' e2' l1 l2 =>
           stk' = stk /\ e1' = env1 /\ e2' = env2 /\
           Forall2
             (fun '(k1, fn1) '(k2, fn2) =>
                k1 = k2 /\
                forall s0 a1 a2 cc args,
                  cfg_stack_sim
                    (fun s0' a1' a2' r1 r2 => s0' = s0 /\ a1' = a1 /\ a2' = a2 /\ r1 = r2)
                    s0 a1 a2 (fn1 cc args) (fn2 cc args))
             l1 l2)
        stk env1 env2
        (map_monad address_one_function defs)
        (map_monad address_one_function (List.map (map_defn_with_args f) defs)).
  Proof using.
    induction defs as [| df defs' IH]; intros stk env1 env2; cbn [List.map map_monad].
    - apply gen_stack_sim_ret; repeat split; constructor.
    - eapply gen_stack_sim_bind with
        (RR := fun stk' e1' e2'
                 (p1 p2 : Z * @function_denotation (@ParamsV IP IPT)) =>
                 stk' = stk /\ e1' = env1 /\ e2' = env2 /\
                 fst p1 = fst p2 /\
                 forall s0 a1 a2 cc args,
                   cfg_stack_sim
                     (fun s0' a1' a2' r1 r2 => s0' = s0 /\ a1' = a1 /\ a2' = a2 /\ r1 = r2)
                     s0 a1 a2 (snd p1 cc args) (snd p2 cc args)).
      + unfold address_one_function; cbn [map_defn_with_args df_prototype].
        eapply gen_stack_sim_bind.
        * unfold gread, trigger_cast; apply gen_stack_sim_trigger_sync;
            [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
        * intros ? ? ? fv _ (-> & -> & -> & <-).
          destruct fv as [[p | | | | | | |] | |];
            try (unfold raise; apply gen_stack_sim_trigger_cast_sync;
                 [reflexivity | apply EqE_MCFG_refl]).
          apply gen_stack_sim_ret; cbn [fst snd]; repeat split; try reflexivity.
          apply cfg_stack_sim_denote_function; [reflexivity | reflexivity |].
          intros env0 va Henv0; apply Hbody, Henv0.
      + intros ? ? ? [k1 fn1] [k2 fn2] (-> & -> & -> & Hk & Hhd); cbn [fst snd] in Hk, Hhd.
        eapply gen_stack_sim_bind; [apply IH |].
        intros ? ? ? tl1 tl2 (-> & -> & -> & Htl).
        apply gen_stack_sim_ret; repeat split; constructor; [split; assumption | assumption].
  Qed.

  Lemma map_monad_address_library_stack_sim
    (libs : list (function_id * @function_denotation (@ParamsV IP IPT)))
    (Hlibs : Forall
               (fun '(_, den) =>
                  forall stk env1 env2 cc args,
                    cfg_stack_sim
                      (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
                      stk env1 env2 (den cc args) (den cc args))
               libs) :
    forall stk env1 env2,
      mcfg_stack_sim
        (fun stk' e1' e2' l1 l2 =>
           stk' = stk /\ e1' = env1 /\ e2' = env2 /\
           Forall2
             (fun '(k1, fn1) '(k2, fn2) =>
                k1 = k2 /\
                forall s0 a1 a2 cc args,
                  cfg_stack_sim
                    (fun s0' a1' a2' r1 r2 => s0' = s0 /\ a1' = a1 /\ a2' = a2 /\ r1 = r2)
                    s0 a1 a2 (fn1 cc args) (fn2 cc args))
             l1 l2)
        stk env1 env2
        (map_monad address_one_library_function libs)
        (map_monad address_one_library_function libs).
  Proof using.
    induction Hlibs as [| [fid den] rest Hden _ IH]; intros stk env1 env2; cbn [map_monad].
    - apply gen_stack_sim_ret; repeat split; constructor.
    - eapply gen_stack_sim_bind with
        (RR := fun stk' e1' e2'
                 (p1 p2 : Z * @function_denotation (@ParamsV IP IPT)) =>
                 stk' = stk /\ e1' = env1 /\ e2' = env2 /\
                 fst p1 = fst p2 /\
                 forall s0 a1 a2 cc args,
                   cfg_stack_sim
                     (fun s0' a1' a2' r1 r2 => s0' = s0 /\ a1' = a1 /\ a2' = a2 /\ r1 = r2)
                     s0 a1 a2 (snd p1 cc args) (snd p2 cc args)).
      + unfold address_one_library_function.
        eapply gen_stack_sim_bind.
        * unfold gread, trigger_cast; apply gen_stack_sim_trigger_sync;
            [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq].
        * intros ? ? ? fv _ (-> & -> & -> & <-).
          destruct fv as [[p | | | | | | |] | |];
            try (unfold raise; apply gen_stack_sim_trigger_cast_sync;
                 [reflexivity | apply EqE_MCFG_refl]).
          apply gen_stack_sim_ret; cbn [fst snd]; repeat apply conj; try reflexivity; exact Hden.
      + intros ? ? ? [k1 fn1] [k2 fn2] (-> & -> & -> & Hk & Hhd); cbn [fst snd] in Hk, Hhd.
        eapply gen_stack_sim_bind; [apply IH |].
        intros ? ? ? tl1 tl2 (-> & -> & -> & Htl).
        apply gen_stack_sim_ret; repeat split; constructor; [split; assumption | assumption].
  Qed.

  Theorem lift_cfg_with_args_local_pass
    (f : list local_id -> CFG.cfg dtyp -> CFG.cfg dtyp)
    (Hba : forall fargs c,
             flat_map block_block_addresses (blks (f fargs c)) =
             flat_map block_block_addresses (blks c))
    (Hbody : forall fargs c env va,
               (forall x, In x fargs -> exists v, Maps.lookup x env = Some v) ->
               cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                 env env (denote_cfg c va) (denote_cfg (f fargs c) va)) :
    forall M : CFG.mcfg dtyp, prog_refines M (map_mcfg_with_args f M).
  Proof using.
    intros M ret_typ entry args U.
    unfold run_mcfg_model, interp_mcfg_model.
    eapply refine_prov_antitone with (U := U);
      [| apply incl_refl
       | eapply mcfg_stack_sim_to_model with
           (RR := fun _ _ _ r1 r2 => r1 = r2) (stk := []) (env1 := Maps.empty) (env2 := Maps.empty)];
      [intros _ _ [s1 r1] [s2 r2] _ (_ & _ & _ & _ & <-); reflexivity | ..].
    { unfold init_fused_state, fused_state_match; repeat split; try reflexivity; constructor. }
    apply mcfg_stack_sim_interp_intrinsics.
    unfold denote_vellvm.
    assert (Hbg : @build_global_environment (@ParamsV IP IPT) (map_mcfg_with_args f M) =
                  @build_global_environment (@ParamsV IP IPT) M).
    { unfold build_global_environment.
      rewrite map_mcfg_with_args_prototypes, (map_mcfg_with_args_block_addresses f M Hba).
      reflexivity. }
    rewrite Hbg.
    eapply gen_stack_sim_bind;
      [apply mcfg_stack_sim_refl_diag; constructor |].
    intros stk1 e1 e2 [] _ (Hstk1 & <- & _).
    cbn [m_definitions m_declarations map_mcfg_with_args].
    eapply gen_stack_sim_bind;
      [apply (map_monad_address_one_function_stack_sim f Hbody) |].
    intros ? ? ? defns1 defns2 (-> & -> & -> & Hdefns).
    eapply gen_stack_sim_bind;
      [apply (map_monad_address_library_stack_sim _ (library_functions_stack_sync (m_declarations M))) |].
    intros ? ? ? libs1 libs2 (-> & -> & -> & Hlibs).
    eapply gen_stack_sim_bind.
    { unfold gread, trigger_cast; apply gen_stack_sim_trigger_sync;
        [reflexivity | apply EqE_MCFG_refl | apply EqA_MCFG_eq]. }
    intros ? ? ? addr _ (-> & -> & -> & <-).
    eapply gen_stack_sim_bind.
    - rewrite !denote_mcfg_eq_interp_mrec.
      assert (Hctx : forall k,
                option_rel
                  (fun f1 f2 =>
                     forall stk env1 env2 cc fargs,
                       cfg_stack_sim
                         (fun stk' e1' e2' r1 r2 => stk' = stk /\ e1' = env1 /\ e2' = env2 /\ r1 = r2)
                         stk env1 env2 (f1 cc fargs) (f2 cc fargs))
                  (lookup k (IntMaps.IP.of_list (defns1 ++ libs1)))
                  (lookup k (IntMaps.IP.of_list (defns2 ++ libs2)))).
      { apply of_list_fn_ctx_stack_sim, Forall2_app; assumption. }
      eapply cfg_to_mcfg_stack_sim_mrec with
        (ctx1 := IntMaps.IP.of_list (defns1 ++ libs1))
        (ctx2 := IntMaps.IP.of_list (defns2 ++ libs2));
        [exact Hctx | reflexivity | reflexivity |].
      apply (cfg_stack_sim_mrec_ctx _ _ Hctx).
    - intros ? ? ? rv _ (-> & -> & -> & <-).
      destruct rv as [ex | v].
      + unfold raiseLLVM; apply gen_stack_sim_trigger_cast_sync; [reflexivity | apply EqE_MCFG_refl].
      + apply gen_stack_sim_ret; reflexivity.
  Qed.

  Theorem lift_cfg_local_pass
    (f : CFG.cfg dtyp -> CFG.cfg dtyp)
    (Hba : forall c,
             flat_map block_block_addresses (blks (f c)) =
             flat_map block_block_addresses (blks c))
    (Hbody : forall c env va,
               cfg_local_sim (fun _ _ r1 r2 => r1 = r2)
                 env env (denote_cfg c va) (denote_cfg (f c) va)) :
    forall M : CFG.mcfg dtyp, prog_refines M (map_mcfg_cfg f M).
  Proof using.
    intros M.
    change (map_mcfg_cfg f M) with (map_mcfg_with_args (fun _ => f) M).
    apply lift_cfg_with_args_local_pass;
      [intros _ c; apply Hba | intros _ c env va _; apply Hbody].
  Qed.

End ModelSemantics.

(** Well-behaved pointer-integer models ([IPZ] in [IPtrInfinite.v] and
    [IP64Bit] in [IPtrFinite.v]) never return [raise_error] ([FailureE]) or
    [raise_ub] from [from_Z]: integer-to-address conversion either succeeds
    ([raise_ret]) or signals out-of-memory ([raise_oom]). Capturing this as a
    [Prop] typeclass allows [Mem2Reg] to delete dead stack allocations without
    weakening [is_ub_bot] to cut [FailureE]. *)
Class IPtrWellBehaved (IP : IPtr) : Prop := {
  from_Z_ret_or_oom :
    forall z : Z,
      (exists i : @iptr IP, @from_Z IP z = raise_ret i) \/
      (exists msg : string, @from_Z IP z = raise_oom msg)
}.

#[export] Instance IPZ_WellBehaved : IPtrWellBehaved IPZ.
Proof.
  constructor; intros z; left; exists z; reflexivity.
Qed.

#[export] Instance IPtrWellBehaved_IPZ : IPtrWellBehaved IPZ := IPZ_WellBehaved.

#[export] Instance IP64Bit_WellBehaved : IPtrWellBehaved IP64Bit.
Proof.
  constructor; intros z; cbn [from_Z IP64Bit]; unfold from_Z_bits.
  destruct ((z <=? @Integers.max_unsigned 64)%Z && (z >=? 0)%Z).
  - left; eexists; reflexivity.
  - right; eexists; reflexivity.
Qed.

