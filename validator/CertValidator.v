(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Top-Level Verified CFG Translation Validator ([F-44] Relational [DrawE] & [F-33] Open-World [CallE])

    Implements:
    1. Open-world per-function event interpretation ([run_cfg_locals],
       [eval_cfg_open]) keeping [CallE], [ExternalCallE], [IntrinsicE],
       [GlobalE], [StackE], [MemoryE], and [DrawE] uninterpreted ([F-33]).
    2. Relational [DrawE] refinement ([ow_itree_refines], [F-44]) over
       well-formed [Draw] strategies ([valid_draw_value]), proving reflexivity,
       transitivity, source existential / universal [Draw] introduction,
       target universal [Draw] inversion, refutation of target-invented
       [0 -> freeze poison], and soundness of [or(freeze x, 1) -> -1] (on [i1])
       and [or(freeze x, -1) -> -1] (at arbitrary width [sz : positive]).
    3. Small-step/big-step operational stepping ([mcfg_steps_to_ret],
       [mcfg_steps_to_ub], [cfg_steps_to_ret], [cfg_steps_to_ub]) bridging
       Vellvm's [denote_cfg] to [det_ref] with zero dependent-equality axioms.
    4. Reflexive and transitive per-function open-world refinement
       [validator_cfg_refines].
    5. Computable bounded-DAG SSA reification, distinct target [freeze]-key
       checking, source-verified UB assumption discharge, [cert-v1] block &
       return obligation checking ([check_cert_cfg_with_lrat], [check_cert_cfg],
       [check_cert_defn]), and [check_cert_cfg_sound] ([0 Admitted]).
    6. Extraction-ready module and string-level entrypoints
       ([validate_mcfg_with_cert], [validate_tle_pair_with_cert],
       [validate_tle_pair_with_cert_str]) and [validate_tle_pair_with_cert_str_sound]. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.String
  Ascii
  List
  Bool
  Lia
  PeanoNat
  Numbers.DecimalString.

From Paco Require Import paco.

From ITree Require Import
  ITree
  ITreeFacts
  Eq.Eqit.

From ExtLib Require Import
  Structures.Maps
  Structures.Monads
  Structures.Functor.

From Vellvm Require Import
  Utils
  Utils.ITreeUtil
  Utils.Assoc
  Utils.ListUtil
  Syntax.LLVMAst
  Syntax.AstLib
  Syntax.DynamicTypes
  Syntax.CFG
  Syntax.TypToDtyp
  Syntax.RawIdMaps
  Syntax.ModuleRefs
  Numeric.Integers
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.LLVMEvents
  Semantics.Attributes
  Semantics.Denotation
  Semantics.Operations.Compare
  Semantics.Operations.Conversion
  Semantics.Operations.Select
  Semantics.Operations.Freeze.

From CertValidator Require Import
  CertFormat
  AigLrat
  AlgRules.

Import ListNotations.
Import Sum.
Import Subevent.

Unset Implicit Arguments.
Unset Strict Implicit.
Set Default Goal Selector "!".

Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.

(** ** 1. ITree Observation Primitives, Open-World Event Signatures & [DrawE] Strategies *)

Section ITreeObsLemmas.
  Lemma observe_bind {E : Type -> Type} {R S : Type}
    (t : itree E R) (k : R -> itree E S) :
    observe (ITree.bind t k) =
    match observe t with
    | RetF r => observe (k r)
    | TauF t' => TauF (ITree.bind t' k)
    | VisF e ke => VisF e (fun x => ITree.bind (ke x) k)
    end.
  Proof using Type.
    unfold ITree.bind, ITree.subst; cbn; destruct (observe t); reflexivity.
  Qed.

  Lemma observe_translate {E F : Type -> Type} {R : Type}
    (h : E ~> F) (t : itree E R) :
    observe (translate h t) =
    match observe t with
    | RetF r => RetF r
    | TauF t' => TauF (translate h t')
    | VisF e ke => VisF (h _ e) (fun x => translate h (ke x))
    end.
  Proof using Type.
    unfold translate; cbn; destruct (observe t); reflexivity.
  Qed.

  Lemma observe_iter {E : Type -> Type} {I R : Type}
    (step : I -> itree E (I + R)) (i : I) :
    observe (ITree.iter step i) =
    observe (ITree.bind (step i) (fun lr =>
      match lr with
      | inl j => Tau (ITree.iter step j)
      | inr r => Ret r
      end)).
  Proof using Type.
    unfold ITree.iter; reflexivity.
  Qed.
End ITreeObsLemmas.

Section OpenWorldEvents.
  Context {Pa : Params}.

  (** Open-world function effect signature ([F-33] & [F-44]):
      interprets only frame-local [LocalE], keeping [CallE], [ExternalCallE],
      [IntrinsicE], [GlobalE], [StackE], [MemoryE], and [DrawE] uninterpreted. *)
  Definition OW_E : Type -> Type :=
    CallE +' ExternalCallE +' IntrinsicE +' GlobalE +' StackE +'
    MemoryE +' DrawE +' OOME +' LLVMExcE +' UBE +' DebugE +' FailureE.

  (** Deterministic open-world signature obtained after resolving [DrawE]
      against a concrete [draw_strat]. *)
  Definition Det_OW_E : Type -> Type :=
    CallE +' ExternalCallE +' IntrinsicE +' GlobalE +' StackE +'
    MemoryE +' OOME +' LLVMExcE +' UBE +' DebugE +' FailureE.

  Definition classify_cfg_event {X : Type} (e : CFGEtop X) : LocalE X + OW_E X :=
    match e with
    | inl1 c => inr (inl1 c)
    | inr1 (inl1 ec) => inr (inr1 (inl1 ec))
    | inr1 (inr1 (inl1 ic)) => inr (inr1 (inr1 (inl1 ic)))
    | inr1 (inr1 (inr1 (inl1 ge))) => inr (inr1 (inr1 (inr1 (inl1 ge))))
    | inr1 (inr1 (inr1 (inr1 (inl1 (inl1 le))))) => inl le
    | inr1 (inr1 (inr1 (inr1 (inl1 (inr1 se))))) =>
        inr (inr1 (inr1 (inr1 (inr1 (inl1 se)))))
    | inr1 (inr1 (inr1 (inr1 (inr1 rest)))) =>
        inr (inr1 (inr1 (inr1 (inr1 (inr1 rest)))))
    end.

  Definition classify_ow_event {X : Type} (e : OW_E X) : DrawE X + Det_OW_E X :=
    match e with
    | inl1 c => inr (inl1 c)
    | inr1 (inl1 ec) => inr (inr1 (inl1 ec))
    | inr1 (inr1 (inl1 ic)) => inr (inr1 (inr1 (inl1 ic)))
    | inr1 (inr1 (inr1 (inl1 ge))) => inr (inr1 (inr1 (inr1 (inl1 ge))))
    | inr1 (inr1 (inr1 (inr1 (inl1 se)))) =>
        inr (inr1 (inr1 (inr1 (inr1 (inl1 se)))))
    | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 me))))) =>
        inr (inr1 (inr1 (inr1 (inr1 (inl1 me)))))
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 de)))))) => inl de
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 rest)))))) =>
        inr (inr1 (inr1 (inr1 (inr1 (inr1 rest)))))
    end.

  CoFixpoint run_cfg_locals {R : Type}
    (env : rmap dvalue) (t : CFGtop R) : itree OW_E R :=
    match observe t with
    | RetF r => Ret r
    | TauF t' => Tau (run_cfg_locals env t')
    | VisF e k =>
        match classify_cfg_event e with
        | inl le =>
            match le in LocalE Y return (Y -> CFGtop R) -> itree OW_E R with
            | LocalWrite id dv => fun k' =>
                Tau (run_cfg_locals (RM.add id dv env) (k' tt))
            | LocalRead id => fun k' =>
                match RM.find id env with
                | Some dv => Tau (run_cfg_locals env (k' dv))
                | None => Vis (@subevent FailureE OW_E _ void (Throw tt)) void_elim
                end
            end k
        | inr oe =>
            Vis oe (fun x => run_cfg_locals env (k x))
        end
    end.

  Lemma observe_run_cfg_locals {R : Type}
    (env : rmap dvalue) (t : CFGtop R) :
    observe (run_cfg_locals env t) =
    match observe t with
    | RetF r => RetF r
    | TauF t' => TauF (run_cfg_locals env t')
    | VisF e k =>
        match classify_cfg_event e with
        | inl le =>
            match le in LocalE Y return (Y -> CFGtop R) -> itree' OW_E R with
            | LocalWrite id dv => fun k' =>
                TauF (run_cfg_locals (RM.add id dv env) (k' tt))
            | LocalRead id => fun k' =>
                match RM.find id env with
                | Some dv => TauF (run_cfg_locals env (k' dv))
                | None => VisF (@subevent FailureE OW_E _ void (Throw tt)) void_elim
                end
            end k
        | inr oe =>
            VisF oe (fun x => run_cfg_locals env (k x))
        end
    end.
  Proof using Type.
    cbn; destruct (observe t) as [r | t' | X e k]; [reflexivity | reflexivity |].
    destruct (classify_cfg_event e) as [le | oe]; [| reflexivity].
    destruct le as [id dv | id]; [reflexivity |].
    destruct (RM.find id env); reflexivity.
  Qed.

  Fixpoint init_cfg_locals (params : list raw_id) (vs : list dvalue) : rmap dvalue :=
    match params, vs with
    | p :: pr, v :: vr => RM.add p v (init_cfg_locals pr vr)
    | _, _ => RM.empty dvalue
    end.

  Definition eval_cfg_open (f : CFG.cfg dtyp) (vs : list dvalue) : itree OW_E dvalue :=
    run_cfg_locals (init_cfg_locals (args f) vs) (denote_cfg f None).

  (** *** 1.1 Well-Defined [DrawE] Values & Constructive Default [Draw] Strategy *)

  Definition valid_draw_value (dt : dtyp) (v : dvalue) : Prop :=
    dvalue_has_dtyp v dt /\ dvalue_well_defined v = true.

  Definition inhabited_draw_dtyp (dt : dtyp) : Prop :=
    exists v, valid_draw_value dt v.

  Definition wf_draw_choice (dt : dtyp) (v : dvalue) : Prop :=
    inhabited_draw_dtyp dt -> valid_draw_value dt v.

  Lemma dvalue_has_dtyp_i_iff_wf_scalar :
    forall (w : positive) (v : dvalue),
      dvalue_has_dtyp v (DTYPE_Base (DTYPE_I w)) <-> wf_scalar_dvalue w v.
  Proof using Type.
    intros w v; split.
    - intros Hty; inversion Hty as [dv tb Hb Hc Heqv Heqt | t Heqv | |]; subst.
      + destruct dv as [| sz i | | | | | |]; cbn in Hb; try discriminate.
        * apply Pos.eqb_eq in Hb; subst sz; right; exists i; reflexivity.
        * left; reflexivity.
      + left; reflexivity.
    - intros [-> | [i ->]].
      + apply DVALUE_Poison_typ_agg.
      + apply DVALUE_Base_typ; [cbn; apply Pos.eqb_refl | reflexivity].
  Qed.

  Lemma valid_draw_i_iff :
    forall (w : positive) (v : dvalue),
      valid_draw_value (DTYPE_Base (DTYPE_I w)) v <->
      exists i : @Integers.bit_int w, v = DVALUE_Base (@DVALUE_I Pa w i).
  Proof using Type.
    intros w v; unfold valid_draw_value; rewrite dvalue_has_dtyp_i_iff_wf_scalar.
    split.
    - intros [[-> | [i ->]] Hwd]; [cbn in Hwd; discriminate | exists i; reflexivity].
    - intros [i ->]; split; [right; exists i; reflexivity | reflexivity].
  Qed.

  Lemma inhabited_draw_dtyp_i : forall (w : positive),
    inhabited_draw_dtyp (DTYPE_Base (DTYPE_I w)).
  Proof using Type.
    intros w; exists (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w 0))).
    apply valid_draw_i_iff; exists (@Integers.repr w 0); reflexivity.
  Qed.

  Lemma well_defined_not_poison : forall (v : dvalue),
    dvalue_well_defined v = true -> dvalue_is_poison v = false.
  Proof using Type.
    intros [db | p fs | b es] Hwd; try reflexivity.
    destruct db; cbn in Hwd |- *; try reflexivity; discriminate.
  Qed.

  Definition default_draw_base_val (tb : dtyp_base) : dvalue :=
    match default_dvalue_base_of_dtyp_base tb with
    | raise_ret db => DVALUE_Base db
    | _ => DVALUE_Base DVALUE_None
    end.

  Fixpoint default_draw_val (dt : dtyp) : dvalue :=
    match dt with
    | DTYPE_Base tb => default_draw_base_val tb
    | DTYPE_Struct p fields =>
        DVALUE_Struct p (List.map default_draw_val fields)
    | DTYPE_Array v sz t =>
        DVALUE_Array v (List.repeat (default_draw_val t) (N.to_nat sz))
    end.

  Lemma default_draw_base_val_wf : forall (tb : dtyp_base),
    wf_draw_choice (DTYPE_Base tb) (default_draw_base_val tb).
  Proof using Type.
    intros tb Hinh; unfold default_draw_base_val.
    destruct tb as [sz | | | | fp | | | | | | sz].
    - split; [apply DVALUE_Base_typ; [cbn; apply Pos.eqb_refl | reflexivity] | reflexivity].
    - split; [apply DVALUE_Base_typ; reflexivity | reflexivity].
    - split; [apply DVALUE_Base_typ; reflexivity | reflexivity].
    - split; [apply DVALUE_Base_typ; reflexivity | reflexivity].
    - destruct fp;
        try (split; [apply DVALUE_Base_typ; reflexivity | reflexivity]);
        (exfalso; destruct Hinh as [v [Hty Hwd]];
         inversion Hty as [dv ? Hb _ Heqv _ | ? Heqv | |]; subst;
         [destruct dv; cbn in Hb, Hwd; discriminate | discriminate]).
    - exfalso; destruct Hinh as [v [Hty Hwd]];
        inversion Hty as [dv ? Hb _ Heqv _ | ? Heqv | |]; subst;
        [destruct dv; cbn in Hb, Hwd; discriminate | discriminate].
    - exfalso; destruct Hinh as [v [Hty Hwd]];
        inversion Hty as [dv ? Hb _ Heqv _ | ? Heqv | |]; subst;
        [destruct dv; cbn in Hb, Hwd; discriminate | discriminate].
    - exfalso; destruct Hinh as [v [Hty Hwd]];
        inversion Hty as [dv ? Hb _ Heqv _ | ? Heqv | |]; subst;
        [destruct dv; cbn in Hb, Hwd; discriminate | discriminate].
    - exfalso; destruct Hinh as [v [Hty Hwd]];
        inversion Hty as [dv ? Hb _ Heqv _ | ? Heqv | |]; subst;
        [destruct dv; cbn in Hb, Hwd; discriminate | discriminate].
    - exfalso; destruct Hinh as [v [Hty Hwd]];
        inversion Hty as [dv ? Hb _ Heqv _ | ? Heqv | |]; subst;
        [destruct dv; cbn in Hb, Hwd; discriminate | discriminate].
    - split; [apply DVALUE_Base_typ; [cbn; apply Pos.eqb_refl | reflexivity] | reflexivity].
  Qed.

  Lemma default_draw_val_wf : forall (dt : dtyp),
    wf_draw_choice dt (default_draw_val dt).
  Proof using Type.
    apply dtyp_ind.
    - exact default_draw_base_val_wf.
    - intros p fields IH Hinh.
      destruct Hinh as [v [Hty Hwd]].
      inversion Hty as [| ? Heqv | ? vs ? Hnp Hfa2 Heqv |]; subst.
      + discriminate Hwd.
      + cbn in Hwd.
        assert (Hall : Forall (fun u => valid_draw_value u (default_draw_val u)) fields).
        { apply Forall_forall; intros u Hu.
          assert (Hex : exists x, In x vs /\ dvalue_has_dtyp x u).
          { clear Hwd Hnp IH; revert u Hu.
            induction Hfa2 as [| x f rx rf Hxf _ IHfa]; intros u Hu; [contradiction |].
            destruct Hu as [<- | Hur].
            - exists x; split; [left; reflexivity | exact Hxf].
            - destruct (IHfa u Hur) as [x' [Hx' Hty']]; exists x'; split; [right; exact Hx' | exact Hty']. }
          destruct Hex as [x [Hx Hxu]].
          rewrite forallb_forall in Hwd.
          apply (IH u Hu); exists x; split; [exact Hxu | exact (Hwd x Hx)]. }
        destruct fields as [| f0 frest].
        * inversion Hfa2; subst; discriminate Hnp.
        * inversion Hall as [| ? ? Hf0 Hrest]; subst.
          destruct Hf0 as [Hty0 Hwd0].
          split.
          -- cbn [default_draw_val]; apply DVALUE_Struct_typ.
             ++ cbn; rewrite (well_defined_not_poison _ Hwd0); reflexivity.
             ++ constructor; [exact Hty0 |].
                clear -Hrest; induction Hrest as [| f rf [Ht _] _ IHr]; cbn; constructor; auto.
          -- cbn; rewrite Hwd0; cbn.
             rewrite forallb_forall; intros d Hd.
             apply in_map_iff in Hd as [f [<- Hf]].
             rewrite Forall_forall in Hrest; exact (proj2 (Hrest f Hf)).
    - intros vec sz t IH Hinh.
      destruct Hinh as [val [Hty Hwd]].
      inversion Hty as [| ? Heqv | | ? xs ? ? Hnv Hnp Hfa Hlen Heqv]; subst.
      + discriminate Hwd.
      + cbn in Hwd.
        destruct xs as [| x0 xrest]; [discriminate Hnp |].
        cbn in Hwd; apply andb_true_iff in Hwd as [Hwd0 _].
        inversion Hfa as [| ? ? Hty0 _]; subst.
        destruct (IH (ex_intro _ x0 (conj Hty0 Hwd0))) as [Hdt Hdw].
        cbn in Hlen; destruct (N.to_nat sz) as [| k] eqn:Esz; [discriminate Hlen |].
        split.
        * cbn [default_draw_val]; rewrite Esz; apply DVALUE_Array_typ.
          -- exact Hnv.
          -- cbn; rewrite (well_defined_not_poison _ Hdw); reflexivity.
          -- constructor; [exact Hdt | apply Forall_forall; intros z Hz; apply repeat_spec in Hz; subst; exact Hdt].
          -- cbn; f_equal; apply repeat_length.
        * cbn [default_draw_val dvalue_well_defined]; rewrite Esz; cbn; rewrite Hdw; cbn.
          rewrite forallb_forall; intros z Hz; apply repeat_spec in Hz; subst; exact Hdw.
  Qed.

  Definition draw_strat : Type := nat -> dtyp -> dvalue.

  Definition wf_draw_strat (sigma : draw_strat) : Prop :=
    forall (n : nat) (dt : dtyp), wf_draw_choice dt (sigma n dt).

  Definition default_draw_strat : draw_strat :=
    fun _ dt => default_draw_val dt.

  Lemma default_draw_strat_wf : wf_draw_strat default_draw_strat.
  Proof using Type.
    intros _ dt; apply default_draw_val_wf.
  Qed.

  Definition shift_draw_strat (sigma : draw_strat) : draw_strat :=
    fun n dt => sigma (S n) dt.

  Lemma shift_draw_strat_wf : forall sigma,
    wf_draw_strat sigma -> wf_draw_strat (shift_draw_strat sigma).
  Proof using Type.
    intros sigma Hwf n dt; exact (Hwf (S n) dt).
  Qed.

  Fixpoint prepend_draws (draws : list (dtyp * dvalue)) (tail_s : draw_strat)
    : draw_strat :=
    match draws with
    | [] => tail_s
    | (dt0, v0) :: rest =>
        fun n dt =>
          match n with
          | O => if dtyp_eq_dec dt dt0 then v0 else default_draw_val dt
          | S n' => prepend_draws rest tail_s n' dt
          end
    end.

  Lemma prepend_draws_wf : forall draws tail_s,
    Forall (fun '(dt, v) => valid_draw_value dt v) draws ->
    wf_draw_strat tail_s ->
    wf_draw_strat (prepend_draws draws tail_s).
  Proof using Type.
    intros draws tail_s Hfa Htail.
    induction Hfa as [| [dt0 v0] rest Hv0 _ IH]; [exact Htail |].
    intros [| n'] dt; cbn.
    - destruct (dtyp_eq_dec dt dt0) as [-> | _];
        [intros _; exact Hv0 | apply default_draw_val_wf].
    - exact (IH n' dt).
  Qed.

  Lemma prepend_draws_app : forall d1 d2 tail_s n dt,
    prepend_draws (d1 ++ d2) tail_s n dt =
    prepend_draws d1 (prepend_draws d2 tail_s) n dt.
  Proof using Type.
    induction d1 as [| [dt0 v0] rest IH]; intros d2 tail_s n dt; [reflexivity |].
    destruct n as [| n']; cbn; [reflexivity | apply IH].
  Qed.

  CoFixpoint run_draws {R : Type}
    (sigma : draw_strat) (t : itree OW_E R) : itree Det_OW_E R :=
    match observe t with
    | RetF r => Ret r
    | TauF t' => Tau (run_draws sigma t')
    | VisF e k =>
        match classify_ow_event e with
        | inl de =>
            match de in DrawE Y return (Y -> itree OW_E R) -> itree Det_OW_E R with
            | Draw dt => fun k' =>
                Tau (run_draws (shift_draw_strat sigma) (k' (sigma 0%nat dt)))
            end k
        | inr de' =>
            Vis de' (fun x => run_draws sigma (k x))
        end
    end.

  Lemma observe_run_draws {R : Type}
    (sigma : draw_strat) (t : itree OW_E R) :
    observe (run_draws sigma t) =
    match observe t with
    | RetF r => RetF r
    | TauF t' => TauF (run_draws sigma t')
    | VisF e k =>
        match classify_ow_event e with
        | inl de =>
            match de in DrawE Y return (Y -> itree OW_E R) -> itree' Det_OW_E R with
            | Draw dt => fun k' =>
                TauF (run_draws (shift_draw_strat sigma) (k' (sigma 0%nat dt)))
            end k
        | inr de' =>
            VisF de' (fun x => run_draws sigma (k x))
        end
    end.
  Proof using Type.
    cbn; destruct (observe t) as [r | t' | X e k]; [reflexivity | reflexivity |].
    destruct (classify_ow_event e) as [de | de']; [destruct de; reflexivity | reflexivity].
  Qed.

(** ** 2. Deterministic Open-World Refinement [det_ref] & Relational [DrawE] ([F-44]) *)

  Definition sync_call {R1 R2 : Type}
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    {X1 X2 : Type}
    (e1 : CallE X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : CallE X2) (k2 : X2 -> itree Det_OW_E R2) : Prop :=
    match e1 in CallE Y1 return (Y1 -> itree Det_OW_E R1) -> Prop with
    | Call t1 cc1 f1 a1 => fun k1' =>
        match e2 in CallE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | Call t2 cc2 f2 a2 => fun k2' =>
            t1 = t2 /\ cc1 = cc2 /\ f1 = f2 /\ a1 = a2 /\
            forall res, r (k1' res) (k2' res)
        end k2
    end k1.

  Definition sync_extcall {R1 R2 : Type}
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    {X1 X2 : Type}
    (e1 : ExternalCallE X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : ExternalCallE X2) (k2 : X2 -> itree Det_OW_E R2) : Prop :=
    match e1 in ExternalCallE Y1 return (Y1 -> itree Det_OW_E R1) -> Prop with
    | ExternalCall t1 f1 a1 => fun k1' =>
        match e2 in ExternalCallE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | ExternalCall t2 f2 a2 => fun k2' =>
            t1 = t2 /\ f1 = f2 /\ a1 = a2 /\ forall res, r (k1' res) (k2' res)
        | _ => fun _ => False
        end k2
    | IO_stdout s1 => fun k1' =>
        match e2 in ExternalCallE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | IO_stdout s2 => fun k2' => s1 = s2 /\ forall u, r (k1' u) (k2' u)
        | _ => fun _ => False
        end k2
    | IO_stderr s1 => fun k1' =>
        match e2 in ExternalCallE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | IO_stderr s2 => fun k2' => s1 = s2 /\ forall u, r (k1' u) (k2' u)
        | _ => fun _ => False
        end k2
    end k1.

  Definition sync_intrinsic {R1 R2 : Type}
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    {X1 X2 : Type}
    (e1 : IntrinsicE X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : IntrinsicE X2) (k2 : X2 -> itree Det_OW_E R2) : Prop :=
    match e1 in IntrinsicE Y1 return (Y1 -> itree Det_OW_E R1) -> Prop with
    | Intrinsic t1 f1 a1 va1 => fun k1' =>
        match e2 in IntrinsicE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | Intrinsic t2 f2 a2 va2 => fun k2' =>
            t1 = t2 /\ f1 = f2 /\ a1 = a2 /\ va1 = va2 /\
            forall res, r (k1' res) (k2' res)
        end k2
    end k1.

  Definition sync_global {R1 R2 : Type}
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    {X1 X2 : Type}
    (e1 : GlobalE X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : GlobalE X2) (k2 : X2 -> itree Det_OW_E R2) : Prop :=
    match e1 in GlobalE Y1 return (Y1 -> itree Det_OW_E R1) -> Prop with
    | GlobalWrite id1 dv1 => fun k1' =>
        match e2 in GlobalE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | GlobalWrite id2 dv2 => fun k2' =>
            id1 = id2 /\ dv1 = dv2 /\ forall u, r (k1' u) (k2' u)
        | _ => fun _ => False
        end k2
    | GlobalRead id1 => fun k1' =>
        match e2 in GlobalE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | GlobalRead id2 => fun k2' =>
            id1 = id2 /\ forall res, r (k1' res) (k2' res)
        | _ => fun _ => False
        end k2
    end k1.

  Definition sync_stack {R1 R2 : Type}
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    {X1 X2 : Type}
    (e1 : StackE X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : StackE X2) (k2 : X2 -> itree Det_OW_E R2) : Prop :=
    match e1 in StackE Y1 return (Y1 -> itree Det_OW_E R1) -> Prop with
    | StackPush a1 => fun k1' =>
        match e2 in StackE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | StackPush a2 => fun k2' => a1 = a2 /\ forall u, r (k1' u) (k2' u)
        | _ => fun _ => False
        end k2
    | StackPop => fun k1' =>
        match e2 in StackE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | StackPop => fun k2' => forall u, r (k1' u) (k2' u)
        | _ => fun _ => False
        end k2
    | StackRaise x1 => fun k1' =>
        match e2 in StackE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | StackRaise x2 => fun k2' => x1 = x2 /\ forall u, r (k1' u) (k2' u)
        | _ => fun _ => False
        end k2
    | StackGetExc => fun k1' =>
        match e2 in StackE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | StackGetExc => fun k2' => forall res, r (k1' res) (k2' res)
        | _ => fun _ => False
        end k2
    end k1.

  Definition sync_memory {R1 R2 : Type}
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    {X1 X2 : Type}
    (e1 : MemoryE X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : MemoryE X2) (k2 : X2 -> itree Det_OW_E R2) : Prop :=
    match e1 in MemoryE Y1 return (Y1 -> itree Det_OW_E R1) -> Prop with
    | MemPush => fun k1' =>
        match e2 in MemoryE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | MemPush => fun k2' => forall u, r (k1' u) (k2' u)
        | _ => fun _ => False
        end k2
    | MemPop => fun k1' =>
        match e2 in MemoryE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | MemPop => fun k2' => forall u, r (k1' u) (k2' u)
        | _ => fun _ => False
        end k2
    | Alloca t1 n1 al1 => fun k1' =>
        match e2 in MemoryE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | Alloca t2 n2 al2 => fun k2' =>
            t1 = t2 /\ n1 = n2 /\ al1 = al2 /\ forall res, r (k1' res) (k2' res)
        | _ => fun _ => False
        end k2
    | Load t1 a1 => fun k1' =>
        match e2 in MemoryE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | Load t2 a2 => fun k2' =>
            t1 = t2 /\ a1 = a2 /\ forall res, r (k1' res) (k2' res)
        | _ => fun _ => False
        end k2
    | Store t1 a1 v1 => fun k1' =>
        match e2 in MemoryE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | Store t2 a2 v2 => fun k2' =>
            t1 = t2 /\ a1 = a2 /\ v1 = v2 /\ forall u, r (k1' u) (k2' u)
        | _ => fun _ => False
        end k2
    | Conv cv1 tf1 v1 tt1 => fun k1' =>
        match e2 in MemoryE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | Conv cv2 tf2 v2 tt2 => fun k2' =>
            cv1 = cv2 /\ tf1 = tf2 /\ v1 = v2 /\ tt1 = tt2 /\
            forall res, r (k1' res) (k2' res)
        | _ => fun _ => False
        end k2
    end k1.

  Definition sync_oom {R1 R2 : Type}
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    {X1 X2 : Type}
    (e1 : OOME X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : OOME X2) (k2 : X2 -> itree Det_OW_E R2) : Prop :=
    match e1 in OOME Y1 return (Y1 -> itree Det_OW_E R1) -> Prop with
    | ThrowOOM u1 => fun k1' =>
        match e2 in OOME Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | ThrowOOM u2 => fun k2' => u1 = u2 /\ forall v : void, r (k1' v) (k2' v)
        end k2
    end k1.

  Definition sync_llvmexc {R1 R2 : Type}
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    {X1 X2 : Type}
    (e1 : LLVMExcE X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : LLVMExcE X2) (k2 : X2 -> itree Det_OW_E R2) : Prop :=
    match e1 in LLVMExcE Y1 return (Y1 -> itree Det_OW_E R1) -> Prop with
    | LLVMExc x1 => fun k1' =>
        match e2 in LLVMExcE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | LLVMExc x2 => fun k2' => x1 = x2 /\ forall v : void, r (k1' v) (k2' v)
        end k2
    end k1.

  Definition sync_ub {R1 R2 : Type}
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    {X1 X2 : Type}
    (e1 : UBE X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : UBE X2) (k2 : X2 -> itree Det_OW_E R2) : Prop :=
    match e1 in UBE Y1 return (Y1 -> itree Det_OW_E R1) -> Prop with
    | ThrowUB u1 => fun k1' =>
        match e2 in UBE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | ThrowUB u2 => fun k2' => u1 = u2 /\ forall v : void, r (k1' v) (k2' v)
        end k2
    end k1.

  Definition sync_debug {R1 R2 : Type}
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    {X1 X2 : Type}
    (e1 : DebugE X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : DebugE X2) (k2 : X2 -> itree Det_OW_E R2) : Prop :=
    match e1 in DebugE Y1 return (Y1 -> itree Det_OW_E R1) -> Prop with
    | Debug u1 => fun k1' =>
        match e2 in DebugE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | Debug u2 => fun k2' => u1 = u2 /\ forall x, r (k1' x) (k2' x)
        end k2
    end k1.

  Definition sync_failure {R1 R2 : Type}
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    {X1 X2 : Type}
    (e1 : FailureE X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : FailureE X2) (k2 : X2 -> itree Det_OW_E R2) : Prop :=
    match e1 in FailureE Y1 return (Y1 -> itree Det_OW_E R1) -> Prop with
    | Throw u1 => fun k1' =>
        match e2 in FailureE Y2 return (Y2 -> itree Det_OW_E R2) -> Prop with
        | Throw u2 => fun k2' => u1 = u2 /\ forall v : void, r (k1' v) (k2' v)
        end k2
    end k1.

  Definition det_is_ub {X : Type} (e : Det_OW_E X) : bool :=
    match e with
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 (ThrowUB _))))))))) => true
    | _ => false
    end.

  Definition det_vis_both {R1 R2 : Type}
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    {X1 X2 : Type}
    (e1 : Det_OW_E X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : Det_OW_E X2) (k2 : X2 -> itree Det_OW_E R2) : Prop :=
    match e1, e2 with
    | inl1 c1, inl1 c2 => sync_call r c1 k1 c2 k2
    | inr1 (inl1 ec1), inr1 (inl1 ec2) => sync_extcall r ec1 k1 ec2 k2
    | inr1 (inr1 (inl1 ic1)), inr1 (inr1 (inl1 ic2)) => sync_intrinsic r ic1 k1 ic2 k2
    | inr1 (inr1 (inr1 (inl1 g1))), inr1 (inr1 (inr1 (inl1 g2))) => sync_global r g1 k1 g2 k2
    | inr1 (inr1 (inr1 (inr1 (inl1 s1)))), inr1 (inr1 (inr1 (inr1 (inl1 s2)))) =>
        sync_stack r s1 k1 s2 k2
    | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 m1))))),
      inr1 (inr1 (inr1 (inr1 (inr1 (inl1 m2))))) =>
        sync_memory r m1 k1 m2 k2
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 o1)))))),
      inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 o2)))))) =>
        sync_oom r o1 k1 o2 k2
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 x1))))))),
      inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 x2))))))) =>
        sync_llvmexc r x1 k1 x2 k2
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 u1)))))))),
      inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 u2)))))))) =>
        sync_ub r u1 k1 u2 k2
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 d1))))))))),
      inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 d2))))))))) =>
        sync_debug r d1 k1 d2 k2
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 f1))))))))),
      inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 f2))))))))) =>
        sync_failure r f1 k1 f2 k2
    | _, _ => False
    end.

  Lemma det_vis_both_mon {R1 R2 : Type}
    (r r' : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    (Hle : forall a b, r a b -> r' a b)
    {X1 X2 : Type}
    (e1 : Det_OW_E X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : Det_OW_E X2) (k2 : X2 -> itree Det_OW_E R2) :
    det_vis_both r e1 k1 e2 k2 ->
    det_vis_both r' e1 k1 e2 k2.
  Proof using Type.
    unfold Det_OW_E in e1, e2.
    repeat match type of e1 with
           | (_ +' _) _ =>
               destruct e1 as [x1 | e1]; destruct e2 as [x2 | e2];
               try (cbn; intros; contradiction)
           end;
      cbn;
      try (destruct x1, x2; cbn; try (intros; contradiction); intros H; intuition auto);
      destruct e1, e2; cbn; intros H; intuition auto.
  Qed.

  Lemma det_vis_both_refl {R : Type}
    (r : itree Det_OW_E R -> itree Det_OW_E R -> Prop)
    {X : Type} (e : Det_OW_E X)
    (k1 k2 : X -> itree Det_OW_E R)
    (Hk : forall x, r (k1 x) (k2 x)) :
    det_vis_both r e k1 e k2.
  Proof using Type.
    unfold Det_OW_E in e.
    repeat match type of e with
           | (_ +' _) _ =>
               destruct e as [ev | e];
               [destruct ev; cbn; repeat split; intros; apply Hk |]
           end.
    destruct e; cbn; repeat split; intros; apply Hk.
  Qed.

  Lemma det_vis_both_ub_inv {R1 R2 : Type}
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    {X1 X2 : Type}
    (e1 : Det_OW_E X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : Det_OW_E X2) (k2 : X2 -> itree Det_OW_E R2) :
    det_vis_both r e1 k1 e2 k2 ->
    det_is_ub e1 = det_is_ub e2.
  Proof using Type.
    unfold Det_OW_E in e1, e2.
    repeat match type of e1 with
           | (_ +' _) _ =>
               destruct e1 as [x1 | e1]; destruct e2 as [x2 | e2];
               try (cbn; intros; contradiction)
           end;
      try (intros _; reflexivity);
      try (destruct x1, x2; intros _; reflexivity);
      destruct e1, e2; intros _; reflexivity.
  Qed.

  Lemma det_vis_both_trans {R1 R2 R3 : Type}
    (r12 : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    (r23 : itree Det_OW_E R2 -> itree Det_OW_E R3 -> Prop)
    (r13 : itree Det_OW_E R1 -> itree Det_OW_E R3 -> Prop)
    (Htr : forall a b c, r12 a b -> r23 b c -> r13 a c)
    {X1 X2 X3 : Type}
    (e1 : Det_OW_E X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : Det_OW_E X2) (k2 : X2 -> itree Det_OW_E R2)
    (e3 : Det_OW_E X3) (k3 : X3 -> itree Det_OW_E R3) :
    det_vis_both r12 e1 k1 e2 k2 ->
    det_vis_both r23 e2 k2 e3 k3 ->
    det_vis_both r13 e1 k1 e3 k3.
  Proof using Type.
    unfold Det_OW_E in e1, e2, e3.
    repeat match type of e1 with
           | (_ +' _) _ =>
               destruct e1 as [x1 | e1];
               destruct e2 as [x2 | e2];
               destruct e3 as [x3 | e3];
               try (cbn; intros; contradiction)
           end;
      cbn;
      try (destruct x1, x2, x3; cbn; try (intros; contradiction);
           intros H1 H2; intuition (try congruence; eauto));
      destruct e1, e2, e3; cbn; intros H1 H2; intuition (try congruence; eauto).
  Qed.

  Lemma det_vis_both_bind {R1 R2 S1 S2 : Type}
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    (s : itree Det_OW_E S1 -> itree Det_OW_E S2 -> Prop)
    (f1 : R1 -> itree Det_OW_E S1) (f2 : R2 -> itree Det_OW_E S2)
    (Hb : forall a b, r a b -> s (ITree.bind a f1) (ITree.bind b f2))
    {X1 X2 : Type}
    (e1 : Det_OW_E X1) (k1 : X1 -> itree Det_OW_E R1)
    (e2 : Det_OW_E X2) (k2 : X2 -> itree Det_OW_E R2) :
    det_vis_both r e1 k1 e2 k2 ->
    det_vis_both s e1 (fun x => ITree.bind (k1 x) f1)
                   e2 (fun y => ITree.bind (k2 y) f2).
  Proof using Type.
    unfold Det_OW_E in e1, e2.
    repeat match type of e1 with
           | (_ +' _) _ =>
               destruct e1 as [x1 | e1]; destruct e2 as [x2 | e2];
               try (cbn; intros; contradiction)
           end;
      cbn;
      try (destruct x1, x2; cbn; try (intros; contradiction); intros H; intuition auto);
      destruct e1, e2; cbn; intros H; intuition auto.
  Qed.


  (** *** 2.1 Coinductive [det_ref] Refinement (Stutter-Insensitive, UB-Asymmetric) *)

  Definition det_step_body {R1 R2 : Type} (RR : R1 -> R2 -> Prop)
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    (t1 : itree Det_OW_E R1) (t2 : itree Det_OW_E R2) : Prop :=
    match observe t1 with
    | RetF x1 =>
        match observe t2 with
        | RetF x2 => RR x1 x2
        | _ => False
        end
    | TauF m1 =>
        match observe t2 with
        | TauF m2 => r m1 m2
        | _ => False
        end
    | VisF e1 k1 =>
        det_is_ub e1 = true \/
        match observe t2 with
        | VisF e2 k2 => det_vis_both r e1 k1 e2 k2
        | _ => False
        end
    end.

  Inductive det_ref_ {R1 R2 : Type} (RR : R1 -> R2 -> Prop)
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop :=
  | DR_Step (t1 : itree Det_OW_E R1) (t2 : itree Det_OW_E R2) :
      det_step_body RR r t1 t2 ->
      det_ref_ RR r t1 t2
  | DR_TauL (t1 m1 : itree Det_OW_E R1) (t2 : itree Det_OW_E R2) :
      observe t1 = TauF m1 ->
      det_ref_ RR r m1 t2 ->
      det_ref_ RR r t1 t2
  | DR_TauR (t1 : itree Det_OW_E R1) (t2 m2 : itree Det_OW_E R2) :
      observe t2 = TauF m2 ->
      det_ref_ RR r t1 m2 ->
      det_ref_ RR r t1 t2.

  Lemma det_ref__mon {R1 R2 : Type} (RR : R1 -> R2 -> Prop) :
    monotone2 (det_ref_ RR).
  Proof using Type.
    intros t1 t2 r r' H Hle.
    induction H as [t1 t2 Hs | t1 m1 t2 Ho1 _ IH | t1 t2 m2 Ho2 _ IH].
    - apply DR_Step; unfold det_step_body in *.
      destruct (observe t1) as [x1 | m1 | X1 e1 k1].
      + exact Hs.
      + destruct (observe t2); [contradiction | exact (Hle _ _ Hs) | contradiction].
      + destruct Hs as [Hub | Hvis]; [left; exact Hub | right].
        destruct (observe t2); try contradiction.
        eapply det_vis_both_mon; [exact Hle | exact Hvis].
    - eapply DR_TauL; [exact Ho1 | exact IH].
    - eapply DR_TauR; [exact Ho2 | exact IH].
  Qed.
  #[local] Hint Resolve det_ref__mon : paco.

  Definition det_ref {R1 R2 : Type} (RR : R1 -> R2 -> Prop)
    (t1 : itree Det_OW_E R1) (t2 : itree Det_OW_E R2) : Prop :=
    paco2 (det_ref_ RR) bot2 t1 t2.

  Lemma det_ref__obs_eq {R1 R2 : Type} (RR : R1 -> R2 -> Prop)
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop) :
    forall t1 t2 t1' t2',
      observe t1 = observe t1' ->
      observe t2 = observe t2' ->
      det_ref_ RR r t1 t2 ->
      det_ref_ RR r t1' t2'.
  Proof using Type.
    intros t1 t2 t1' t2' Ho1 Ho2 H.
    revert t1' t2' Ho1 Ho2.
    induction H as [t1 t2 Hs | t1 m1 t2 Hm1 _ IH | t1 t2 m2 Hm2 _ IH];
      intros t1' t2' Ho1 Ho2.
    - apply DR_Step; unfold det_step_body in *; rewrite <- Ho1, <- Ho2; exact Hs.
    - eapply DR_TauL; [rewrite <- Ho1; exact Hm1 | exact (IH m1 t2' eq_refl Ho2)].
    - eapply DR_TauR; [rewrite <- Ho2; exact Hm2 | exact (IH t1' m2 Ho1 eq_refl)].
  Qed.

  Lemma det_ref_obs_eq {R1 R2 : Type} (RR : R1 -> R2 -> Prop) :
    forall t1 t2 t1' t2',
      observe t1 = observe t1' ->
      observe t2 = observe t2' ->
      det_ref RR t1 t2 ->
      det_ref RR t1' t2'.
  Proof using Type.
    intros t1 t2 t1' t2' Ho1 Ho2 H.
    punfold H; pstep; eapply det_ref__obs_eq; eassumption.
  Qed.

  Lemma det_ref_tau_l {R1 R2 : Type} (RR : R1 -> R2 -> Prop) :
    forall t1 m1 t2,
      observe t1 = TauF m1 ->
      det_ref RR m1 t2 ->
      det_ref RR t1 t2.
  Proof using Type.
    intros t1 m1 t2 Ho H; punfold H; pstep; eapply DR_TauL; [exact Ho | exact H].
  Qed.

  Lemma det_ref_tau_r {R1 R2 : Type} (RR : R1 -> R2 -> Prop) :
    forall t1 t2 m2,
      observe t2 = TauF m2 ->
      det_ref RR t1 m2 ->
      det_ref RR t1 t2.
  Proof using Type.
    intros t1 t2 m2 Ho H; punfold H; pstep; eapply DR_TauR; [exact Ho | exact H].
  Qed.

  Lemma det_ref_inv_tau_l {R1 R2 : Type} (RR : R1 -> R2 -> Prop) :
    forall t1 m1 t2,
      observe t1 = TauF m1 ->
      det_ref RR t1 t2 ->
      det_ref RR m1 t2.
  Proof using Type.
    intros t1 m1 t2 Ho H; punfold H.
    revert m1 Ho.
    induction H as [t1 t2 Hs | t1 m1' t2 Ho1' Hsub _ | t1 t2 m2 Ho2 _ IH];
      intros m1 Ho.
    - unfold det_step_body in Hs; rewrite Ho in Hs.
      destruct (observe t2) as [| m2 |] eqn:Ho2; try contradiction.
      pclearbot; eapply det_ref_tau_r; [exact Ho2 | exact Hs].
    - rewrite Ho in Ho1'; injection Ho1' as <-; pstep; exact Hsub.
    - eapply det_ref_tau_r; [exact Ho2 | exact (IH m1 Ho)].
  Qed.

  Lemma det_ref_inv_tau_r {R1 R2 : Type} (RR : R1 -> R2 -> Prop) :
    forall t1 t2 m2,
      observe t2 = TauF m2 ->
      det_ref RR t1 t2 ->
      det_ref RR t1 m2.
  Proof using Type.
    intros t1 t2 m2 Ho H; punfold H.
    revert m2 Ho.
    induction H as [t1 t2 Hs | t1 m1 t2 Ho1 _ IH | t1 t2 m2' Ho2' Hsub _];
      intros m2 Ho.
    - unfold det_step_body in Hs; rewrite Ho in Hs.
      destruct (observe t1) as [| m1 | X1 e1 k1] eqn:Ho1; try contradiction.
      + pclearbot; eapply det_ref_tau_l; [exact Ho1 | exact Hs].
      + destruct Hs as [Hub | []].
        pstep; apply DR_Step; unfold det_step_body; rewrite Ho1; left; exact Hub.
    - eapply det_ref_tau_l; [exact Ho1 | exact (IH m2 Ho)].
    - rewrite Ho in Ho2'; injection Ho2' as <-; pstep; exact Hsub.
  Qed.

  Lemma det_ref_refl {R : Type} (RR : R -> R -> Prop)
    (HRR : forall x, RR x x) :
    forall (t : itree Det_OW_E R), det_ref RR t t.
  Proof using Type.
    pcofix CIH; intros t; pstep; apply DR_Step; unfold det_step_body.
    destruct (observe t) as [x | m | X e k].
    - exact (HRR x).
    - right; exact (CIH m).
    - right; apply det_vis_both_refl; intros x; right; exact (CIH (k x)).
  Qed.

  Lemma det_ref_trans {R1 R2 R3 : Type}
    (R12 : R1 -> R2 -> Prop) (R23 : R2 -> R3 -> Prop) (R13 : R1 -> R3 -> Prop)
    (HRR : forall a b c, R12 a b -> R23 b c -> R13 a c) :
    forall t1 t2 t3,
      det_ref R12 t1 t2 ->
      det_ref R23 t2 t3 ->
      det_ref R13 t1 t3.
  Proof using Type.
    pcofix CIH.
    assert (Hnon_tau_r :
      forall m2 t3,
        (forall m3, observe t3 <> TauF m3) ->
        det_ref_ R23 (upaco2 (det_ref_ R23) bot2) m2 t3 ->
        forall m1,
          det_ref R12 m1 m2 ->
          det_ref_ R13 (upaco2 (det_ref_ R13) r) m1 t3).
    { intros m2 t3 Hnt3 Hm23.
      induction Hm23 as [m2 t3 Hs23 | m2 m2' t3 Hm2 _ IH23 | m2 t3 m3 Ht3 _ _].
      - intros m1 Hm12; punfold Hm12.
        destruct (observe m2) as [x2 | mm2 | X2 e2 k2] eqn:Hom2.
        + unfold det_step_body in Hs23; rewrite Hom2 in Hs23.
          destruct (observe t3) as [x3 | | ] eqn:Hot3; try contradiction.
          revert Hom2 Hs23.
          induction Hm12 as [m1_ m2_ Hs12 | m1_ m1' m2_ Hm1_ _ IH12 | m1_ m2_ mm2 Hm2_ _ _];
            intros Hom2 Hs23.
          * unfold det_step_body in Hs12; rewrite Hom2 in Hs12.
            destruct (observe m1_) as [x1 | | X1 e1 k1] eqn:Hom1; try contradiction.
            -- apply DR_Step; unfold det_step_body; rewrite Hom1, Hot3; exact (HRR _ _ _ Hs12 Hs23).
            -- destruct Hs12 as [Hub1 | []].
               apply DR_Step; unfold det_step_body; rewrite Hom1; left; exact Hub1.
          * eapply DR_TauL; [exact Hm1_ | exact (IH12 Hom2 Hs23)].
          * congruence.
        + unfold det_step_body in Hs23; rewrite Hom2 in Hs23.
          destruct (observe t3) eqn:Hot3; try contradiction.
          exfalso; exact (Hnt3 _ Hot3).
        + unfold det_step_body in Hs23; rewrite Hom2 in Hs23.
          revert Hom2 Hs23.
          induction Hm12 as [m1_ m2_ Hs12 | m1_ m1' m2_ Hm1_ _ IH12 | m1_ m2_ mm2 Hm2_ _ _];
            intros Hom2 Hs23.
          * unfold det_step_body in Hs12; rewrite Hom2 in Hs12.
            destruct (observe m1_) as [| | X1 e1 k1] eqn:Hom1; try contradiction.
            destruct Hs12 as [Hub1 | Hb12].
            -- apply DR_Step; unfold det_step_body; rewrite Hom1; left; exact Hub1.
            -- destruct Hs23 as [Hub2 | Hb23].
               ++ apply DR_Step; unfold det_step_body; rewrite Hom1; left.
                  erewrite det_vis_both_ub_inv; [exact Hub2 | exact Hb12].
               ++ destruct (observe t3) as [| | X3 e3 k3] eqn:Hot3; try contradiction.
                  apply DR_Step; unfold det_step_body; rewrite Hom1, Hot3; right.
                  eapply det_vis_both_trans; [| exact Hb12 | exact Hb23].
                  intros a b c [Hab | []] [Hbc | []]; right; exact (CIH a b c Hab Hbc).
          * eapply DR_TauL; [exact Hm1_ | exact (IH12 Hom2 Hs23)].
          * congruence.
      - intros m1 Hm12; apply (IH23 Hnt3 m1); eapply det_ref_inv_tau_r; [exact Hm2 | exact Hm12].
      - exfalso; exact (Hnt3 m3 Ht3). }
    intros t1 t2 t3 H12 H23; pstep.
    destruct (observe t1) as [x1 | m1 | X1 e1 k1] eqn:Hot1.
    - assert (Hnt1 : forall m, observe t1 <> TauF m) by (rewrite Hot1; discriminate).
      punfold H12; revert t3 H23 Hnt1.
      induction H12 as [t1_ t2_ Hs12 | t1_ m t2_ Ho1 _ _ | t1_ t2_ m2 Ho2 _ IH12];
        intros t3 H23 Hnt1.
      + destruct (observe t1_) as [y1 | m | Y1 ev kv] eqn:Ho1_;
          [| exfalso; exact (Hnt1 m Ho1_) |].
        * unfold det_step_body in Hs12; rewrite Ho1_ in Hs12.
          destruct (observe t2_) as [x2 | | ] eqn:Ho2_; try contradiction.
          punfold H23; revert Ho2_ Hs12.
          induction H23 as [t2__ t3_ Hs23 | t2__ m t3_ Hm _ _ | t2__ t3_ m3 Ht3 _ IH23];
            intros Ho2_ Hs12.
          -- unfold det_step_body in Hs23; rewrite Ho2_ in Hs23.
             destruct (observe t3_) as [x3 | | ] eqn:Ho3_; try contradiction.
             apply DR_Step; unfold det_step_body; rewrite Ho1_, Ho3_; exact (HRR _ _ _ Hs12 Hs23).
          -- congruence.
          -- eapply DR_TauR; [exact Ht3 | exact (IH23 Ho2_ Hs12)].
        * unfold det_step_body in Hs12; rewrite Ho1_ in Hs12.
          destruct Hs12 as [Hub | Hb12];
            [apply DR_Step; unfold det_step_body; rewrite Ho1_; left; exact Hub |].
          destruct (observe t2_) as [| | X2 e2 k2] eqn:Ho2_; try contradiction.
          punfold H23; revert Ho2_ Hb12.
          induction H23 as [t2__ t3_ Hs23 | t2__ m t3_ Hm _ _ | t2__ t3_ m3 Ht3 _ IH23];
            intros Ho2_ Hb12.
          -- unfold det_step_body in Hs23; rewrite Ho2_ in Hs23.
             destruct Hs23 as [Hub2 | Hb23].
             ++ apply DR_Step; unfold det_step_body; rewrite Ho1_; left.
                erewrite det_vis_both_ub_inv; [exact Hub2 | exact Hb12].
             ++ destruct (observe t3_) as [| | X3 e3 k3] eqn:Ho3_; try contradiction.
                apply DR_Step; unfold det_step_body; rewrite Ho1_, Ho3_; right.
                eapply det_vis_both_trans; [| exact Hb12 | exact Hb23].
                intros a b c [Hab | []] [Hbc | []]; right; exact (CIH a b c Hab Hbc).
          -- congruence.
          -- eapply DR_TauR; [exact Ht3 | exact (IH23 Ho2_ Hb12)].
      + exfalso; exact (Hnt1 m Ho1).
      + apply (IH12 t3); [eapply det_ref_inv_tau_l; [exact Ho2 | exact H23] | exact Hnt1].
    - assert (Hm12 : det_ref R12 m1 t2) by (eapply det_ref_inv_tau_l; [exact Hot1 | exact H12]).
      destruct (observe t3) as [x3 | m3 | X3 e3 k3] eqn:Hot3.
      + eapply DR_TauL; [exact Hot1 |].
        punfold H23; apply (Hnon_tau_r t2 t3); [rewrite Hot3; discriminate | exact H23 | exact Hm12].
      + apply DR_Step; unfold det_step_body; rewrite Hot1, Hot3; right.
        apply (CIH m1 t2 m3 Hm12); eapply det_ref_inv_tau_r; [exact Hot3 | exact H23].
      + eapply DR_TauL; [exact Hot1 |].
        punfold H23; apply (Hnon_tau_r t2 t3); [rewrite Hot3; discriminate | exact H23 | exact Hm12].
    - assert (Hnt1 : forall m, observe t1 <> TauF m) by (rewrite Hot1; discriminate).
      punfold H12; revert t3 H23 Hnt1.
      induction H12 as [t1_ t2_ Hs12 | t1_ m t2_ Ho1 _ _ | t1_ t2_ m2 Ho2 _ IH12];
        intros t3 H23 Hnt1.
      + destruct (observe t1_) as [y1 | m | Y1 ev kv] eqn:Ho1_;
          [| exfalso; exact (Hnt1 m Ho1_) |].
        * unfold det_step_body in Hs12; rewrite Ho1_ in Hs12.
          destruct (observe t2_) as [x2 | | ] eqn:Ho2_; try contradiction.
          punfold H23; revert Ho2_ Hs12.
          induction H23 as [t2__ t3_ Hs23 | t2__ m t3_ Hm _ _ | t2__ t3_ m3 Ht3 _ IH23];
            intros Ho2_ Hs12.
          -- unfold det_step_body in Hs23; rewrite Ho2_ in Hs23.
             destruct (observe t3_) as [x3 | | ] eqn:Ho3_; try contradiction.
             apply DR_Step; unfold det_step_body; rewrite Ho1_, Ho3_; exact (HRR _ _ _ Hs12 Hs23).
          -- congruence.
          -- eapply DR_TauR; [exact Ht3 | exact (IH23 Ho2_ Hs12)].
        * unfold det_step_body in Hs12; rewrite Ho1_ in Hs12.
          destruct Hs12 as [Hub | Hb12];
            [apply DR_Step; unfold det_step_body; rewrite Ho1_; left; exact Hub |].
          destruct (observe t2_) as [| | X2 e2 k2] eqn:Ho2_; try contradiction.
          punfold H23; revert Ho2_ Hb12.
          induction H23 as [t2__ t3_ Hs23 | t2__ m t3_ Hm _ _ | t2__ t3_ m3 Ht3 _ IH23];
            intros Ho2_ Hb12.
          -- unfold det_step_body in Hs23; rewrite Ho2_ in Hs23.
             destruct Hs23 as [Hub2 | Hb23].
             ++ apply DR_Step; unfold det_step_body; rewrite Ho1_; left.
                erewrite det_vis_both_ub_inv; [exact Hub2 | exact Hb12].
             ++ destruct (observe t3_) as [| | X3 e3 k3] eqn:Ho3_; try contradiction.
                apply DR_Step; unfold det_step_body; rewrite Ho1_, Ho3_; right.
                eapply det_vis_both_trans; [| exact Hb12 | exact Hb23].
                intros a b c [Hab | []] [Hbc | []]; right; exact (CIH a b c Hab Hbc).
          -- congruence.
          -- eapply DR_TauR; [exact Ht3 | exact (IH23 Ho2_ Hb12)].
      + exfalso; exact (Hnt1 m Ho1).
      + apply (IH12 t3); [eapply det_ref_inv_tau_l; [exact Ho2 | exact H23] | exact Hnt1].
  Qed.

  Lemma det_ref_bind {R1 R2 S1 S2 : Type}
    (RR : R1 -> R2 -> Prop) (SS : S1 -> S2 -> Prop)
    (t1 : itree Det_OW_E R1) (t2 : itree Det_OW_E R2)
    (k1 : R1 -> itree Det_OW_E S1) (k2 : R2 -> itree Det_OW_E S2) :
    det_ref RR t1 t2 ->
    (forall x1 x2, RR x1 x2 -> det_ref SS (k1 x1) (k2 x2)) ->
    det_ref SS (ITree.bind t1 k1) (ITree.bind t2 k2).
  Proof using Type.
    intros H12 Hk; revert t1 t2 H12.
    pcofix CIH; intros t1 t2 H12; punfold H12; pstep.
    induction H12 as [t1 t2 Hs | t1 m1 t2 Ho1 _ IH | t1 t2 m2 Ho2 _ IH].
    - destruct (observe t1) as [x1 | m1 | X1 e1 ke1] eqn:Hot1.
      + unfold det_step_body in Hs; rewrite Hot1 in Hs.
        destruct (observe t2) as [x2 | | ] eqn:Hot2; try contradiction.
        pose proof (Hk x1 x2 Hs) as Hkx; punfold Hkx.
        eapply det_ref__obs_eq.
        * symmetry; rewrite observe_bind, Hot1; reflexivity.
        * symmetry; rewrite observe_bind, Hot2; reflexivity.
        * eapply det_ref__mon; [exact Hkx |].
          intros a b [Hab | []]; left; eapply paco2_mon; [exact Hab | intros ? ? []].
      + unfold det_step_body in Hs; rewrite Hot1 in Hs.
        destruct (observe t2) as [| m2 |] eqn:Hot2; try contradiction.
        pclearbot; apply DR_Step; unfold det_step_body.
        rewrite !observe_bind, Hot1, Hot2; right; exact (CIH m1 m2 Hs).
      + unfold det_step_body in Hs; rewrite Hot1 in Hs.
        destruct Hs as [Hub | Hvis].
        * apply DR_Step; unfold det_step_body; rewrite observe_bind, Hot1; left; exact Hub.
        * destruct (observe t2) as [| | X2 e2 ke2] eqn:Hot2; try contradiction.
          apply DR_Step; unfold det_step_body; rewrite !observe_bind, Hot1, Hot2; right.
          eapply det_vis_both_bind; [| exact Hvis].
          intros a b [Hab | []]; right; exact (CIH a b Hab).
    - eapply DR_TauL; [rewrite observe_bind, Ho1; reflexivity | exact IH].
    - eapply DR_TauR; [rewrite observe_bind, Ho2; reflexivity | exact IH].
  Qed.

  Lemma run_draws_ext_det_ref {R : Type}
    (RR : R -> R -> Prop) (HRR : forall x, RR x x) :
    forall (s1 s2 : draw_strat) (t : itree OW_E R),
      (forall n dt, s1 n dt = s2 n dt) ->
      det_ref RR (run_draws s1 t) (run_draws s2 t).
  Proof using Type.
    pcofix CIH; intros s1 s2 t Heq; pstep; apply DR_Step; unfold det_step_body.
    rewrite !observe_run_draws.
    destruct (observe t) as [x | m | X e k].
    - exact (HRR x).
    - right; exact (CIH s1 s2 m Heq).
    - destruct (classify_ow_event e) as [de | de'].
      + destruct de as [dt]; right.
        rewrite (Heq 0%nat dt).
        apply CIH; intros n d; exact (Heq (S n) d).
      + right; apply det_vis_both_refl; intros x; right; exact (CIH s1 s2 (k x) Heq).
  Qed.

  (** *** 2.2 Relational [DrawE] Refinement [ow_itree_refines] ([F-44]) *)

  Definition ow_itree_refines {R1 R2 : Type} (RR : R1 -> R2 -> Prop)
    (t_src : itree OW_E R1) (t_tgt : itree OW_E R2) : Prop :=
    forall sigma_tgt : draw_strat,
      wf_draw_strat sigma_tgt ->
      exists sigma_src : draw_strat,
        wf_draw_strat sigma_src /\
        det_ref RR (run_draws sigma_src t_src) (run_draws sigma_tgt t_tgt).

  Theorem ow_itree_refines_refl {R : Type} (RR : R -> R -> Prop)
    (HRR : forall x, RR x x) :
    forall (t : itree OW_E R), ow_itree_refines RR t t.
  Proof using Type.
    intros t sigma_tgt Hwf.
    exists sigma_tgt; split; [exact Hwf | exact (det_ref_refl RR HRR (run_draws sigma_tgt t))].
  Qed.

  Theorem ow_itree_refines_trans {R1 R2 R3 : Type}
    (R12 : R1 -> R2 -> Prop) (R23 : R2 -> R3 -> Prop) (R13 : R1 -> R3 -> Prop)
    (HRR : forall a b c, R12 a b -> R23 b c -> R13 a c) :
    forall t1 t2 t3,
      ow_itree_refines R12 t1 t2 ->
      ow_itree_refines R23 t2 t3 ->
      ow_itree_refines R13 t1 t3.
  Proof using Type.
    intros t1 t2 t3 H12 H23 sigma3 Hwf3.
    destruct (H23 sigma3 Hwf3) as [sigma2 [Hwf2 Hdet23]].
    destruct (H12 sigma2 Hwf2) as [sigma1 [Hwf1 Hdet12]].
    exists sigma1; split; [exact Hwf1 |].
    eapply det_ref_trans; [exact HRR | exact Hdet12 | exact Hdet23].
  Qed.

  Lemma observe_run_draws_bind_ret {R S : Type}
    (sigma : draw_strat) (x : R) (k : R -> itree OW_E S) :
    observe (run_draws sigma (ITree.bind (Ret x) k)) =
    observe (run_draws sigma (k x)).
  Proof using Type.
    rewrite !observe_run_draws, observe_bind; reflexivity.
  Qed.

  Definition ow_draw (dt : dtyp) : itree OW_E dvalue :=
    trigger (@subevent DrawE OW_E _ dvalue (Draw dt)).

  Definition ow_freeze (dt : dtyp) (dv : dvalue) : itree OW_E dvalue :=
    @freeze Pa OW_E _ _ _ _ dt dv.

  Lemma observe_freeze_poison {E : Type -> Type}
    `{DrawE -< E} `{FailureE -< E} `{OOME -< E} `{UBE -< E}
    (dt : dtyp) :
    observe (@freeze Pa E _ _ _ _ dt (DVALUE_Base DVALUE_Poison)) =
    VisF (@subevent DrawE E _ dvalue (Draw dt)) (fun x => Ret x).
  Proof using Type.
    reflexivity.
  Qed.

  Lemma observe_freeze_i_defined {E : Type -> Type}
    `{DrawE -< E} `{FailureE -< E} `{OOME -< E} `{UBE -< E}
    (dt : dtyp) (w : positive) (i : @Integers.bit_int w) :
    observe (@freeze Pa E _ _ _ _ dt (DVALUE_Base (@DVALUE_I Pa w i))) =
    RetF (DVALUE_Base (@DVALUE_I Pa w i)).
  Proof using Type.
    reflexivity.
  Qed.

  (** Source [Draw] existential rule: picking a single valid [Draw] witness
      [v] refines into [t_tgt]. *)
  Theorem ow_itree_refines_draw_src_exists {R1 R2 : Type}
    (RR : R1 -> R2 -> Prop) (dt : dtyp) (v : dvalue)
    (k_src : dvalue -> itree OW_E R1) (t_tgt : itree OW_E R2) :
    valid_draw_value dt v ->
    ow_itree_refines RR (k_src v) t_tgt ->
    ow_itree_refines RR (ITree.bind (ow_draw dt) k_src) t_tgt.
  Proof using Type.
    intros Hv Href sigma_tgt Hwft.
    destruct (Href sigma_tgt Hwft) as [sigma0 [Hwf0 Hdet0]].
    set (sigma_src := prepend_draws [(dt, v)] sigma0).
    exists sigma_src; split.
    - apply prepend_draws_wf; [constructor; [exact Hv | constructor] | exact Hwf0].
    - eapply det_ref_tau_l.
      + rewrite observe_run_draws; unfold ow_draw, ITree.trigger; rewrite observe_bind; reflexivity.
      + unfold sigma_src; cbn [prepend_draws].
        destruct (dtyp_eq_dec dt dt) as [_ | Hneq]; [| exfalso; exact (Hneq eq_refl)].
        eapply det_ref_obs_eq; [symmetry; apply observe_run_draws_bind_ret | reflexivity | exact Hdet0].
  Qed.

  (** Source [Draw] universal (demonic) corollary: if ALL valid [Draw] values
      refine into [t_tgt], then [Draw dt >>= k_src] refines into [t_tgt]. *)
  Theorem ow_itree_refines_draw_src_forall {R1 R2 : Type}
    (RR : R1 -> R2 -> Prop) (dt : dtyp)
    (k_src : dvalue -> itree OW_E R1) (t_tgt : itree OW_E R2) :
    inhabited_draw_dtyp dt ->
    (forall v, valid_draw_value dt v -> ow_itree_refines RR (k_src v) t_tgt) ->
    ow_itree_refines RR (ITree.bind (ow_draw dt) k_src) t_tgt.
  Proof using Type.
    intros Hinh Hall.
    pose proof (default_draw_val_wf dt Hinh) as Hdef.
    eapply ow_itree_refines_draw_src_exists;
      [exact Hdef | exact (Hall (default_draw_val dt) Hdef)].
  Qed.

  (** Target [Draw] introduction: [t_src] refines [Draw dt >>= k_tgt] when
      [t_src] refines [k_tgt v] for EVERY valid [v]. *)
  Theorem ow_itree_refines_draw_tgt_intro {R1 R2 : Type}
    (RR : R1 -> R2 -> Prop) (dt : dtyp)
    (t_src : itree OW_E R1) (k_tgt : dvalue -> itree OW_E R2) :
    inhabited_draw_dtyp dt ->
    (forall v, valid_draw_value dt v -> ow_itree_refines RR t_src (k_tgt v)) ->
    ow_itree_refines RR t_src (ITree.bind (ow_draw dt) k_tgt).
  Proof using Type.
    intros Hinh Hall sigma_tgt Hwft.
    pose proof (Hwft 0%nat dt Hinh) as Hv0.
    destruct (Hall (sigma_tgt 0%nat dt) Hv0 (shift_draw_strat sigma_tgt)
                (shift_draw_strat_wf sigma_tgt Hwft))
      as [sigma_src [Hwfs Hdet]].
    exists sigma_src; split; [exact Hwfs |].
    eapply det_ref_tau_r.
    - rewrite observe_run_draws; unfold ow_draw, ITree.trigger; rewrite observe_bind; reflexivity.
    - eapply det_ref_obs_eq; [reflexivity | symmetry; apply observe_run_draws_bind_ret | exact Hdet].
  Qed.

  (** Target [Draw] universal inversion: if [t_src] refines [Draw dt >>= k_tgt],
      then [t_src] MUST refine [k_tgt v] for EVERY valid [v]. *)
  Theorem ow_itree_refines_draw_tgt_inv {R1 R2 : Type}
    (RR : R1 -> R2 -> Prop) (dt : dtyp)
    (t_src : itree OW_E R1) (k_tgt : dvalue -> itree OW_E R2) :
    ow_itree_refines RR t_src (ITree.bind (ow_draw dt) k_tgt) ->
    forall v, valid_draw_value dt v -> ow_itree_refines RR t_src (k_tgt v).
  Proof using Type.
    intros Href v Hv sigma_tgt Hwft.
    set (sigma_tgt' := prepend_draws [(dt, v)] sigma_tgt).
    assert (Hwft' : wf_draw_strat sigma_tgt')
      by (apply prepend_draws_wf; [constructor; [exact Hv | constructor] | exact Hwft]).
    destruct (Href sigma_tgt' Hwft') as [sigma_src [Hwfs Hdet]].
    exists sigma_src; split; [exact Hwfs |].
    assert (Ho_tgt :
      observe (run_draws sigma_tgt' (ITree.bind (ow_draw dt) k_tgt)) =
      TauF (run_draws sigma_tgt (ITree.bind (Ret v) k_tgt))).
    { rewrite observe_run_draws; unfold ow_draw, ITree.trigger;
        rewrite observe_bind; cbn [observe classify_ow_event].
      unfold sigma_tgt'; cbn [prepend_draws].
      destruct (dtyp_eq_dec dt dt) as [_ | Hneq]; [reflexivity | exfalso; exact (Hneq eq_refl)]. }
    eapply det_ref_obs_eq; [reflexivity | apply observe_run_draws_bind_ret |].
    eapply det_ref_inv_tau_r; [exact Ho_tgt | exact Hdet].
  Qed.

  (** *** 2.3 Explicit [F-44] Separation & Soundness Proofs *)

  Lemma det_ref_ret_ret_inv {R1 R2 : Type} (RR : R1 -> R2 -> Prop) :
    forall (x1 : R1) (x2 : R2),
      det_ref RR (Ret x1) (Ret x2) -> RR x1 x2.
  Proof using Type.
    intros x1 x2 H; punfold H.
    remember (Ret x1 : itree Det_OW_E R1) as t1 eqn:Et1.
    remember (Ret x2 : itree Det_OW_E R2) as t2 eqn:Et2.
    assert (Ho1 : observe t1 = RetF x1) by (subst; reflexivity).
    assert (Ho2 : observe t2 = RetF x2) by (subst; reflexivity).
    clear Et1 Et2; induction H as [t1 t2 Hs | t1 m1 t2 Hm1 _ _ | t1 t2 m2 Hm2 _ _];
      [unfold det_step_body in Hs; rewrite Ho1, Ho2 in Hs; exact Hs | congruence | congruence].
  Qed.

  (** [F-44] Negative Separation Theorem: target-invented [freeze poison] does
      NOT refine constant [0] at any integer width [w : positive]. *)
  Theorem target_invented_freeze_poison_not_refines_zero :
    forall (w : positive),
      ~ ow_itree_refines dvalue_refines
          (Ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w 0))))
          (ow_freeze (DTYPE_Base (DTYPE_I w)) (DVALUE_Base DVALUE_Poison)).
  Proof using Type.
    intros w Href.
    set (v1 := DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w 1))).
    assert (Hv1 : valid_draw_value (DTYPE_Base (DTYPE_I w)) v1)
      by (apply valid_draw_i_iff; exists (@Integers.repr w 1); reflexivity).
    set (sigma1 := prepend_draws [(DTYPE_Base (DTYPE_I w), v1)] default_draw_strat).
    assert (Hwf1 : wf_draw_strat sigma1)
      by (apply prepend_draws_wf; [constructor; [exact Hv1 | constructor] | exact default_draw_strat_wf]).
    destruct (Href sigma1 Hwf1) as [sigma_src [_ Hdet]].
    assert (Ho_src : observe (run_draws sigma_src
                       (Ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w 0))))) =
                     RetF (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w 0))))
      by reflexivity.
    assert (Ho_tgt : observe (run_draws sigma1
                       (ow_freeze (DTYPE_Base (DTYPE_I w)) (DVALUE_Base DVALUE_Poison))) =
                     TauF (run_draws default_draw_strat (Ret v1))).
    { rewrite observe_run_draws; unfold ow_freeze; rewrite observe_freeze_poison;
        cbn [classify_ow_event]; unfold sigma1; cbn [prepend_draws].
      destruct (dtyp_eq_dec (DTYPE_Base (DTYPE_I w)) (DTYPE_Base (DTYPE_I w))) as [_ | Hneq];
        [reflexivity | exfalso; exact (Hneq eq_refl)]. }
    assert (Hdet' : det_ref dvalue_refines
                      (run_draws sigma_src (Ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w 0)))))
                      (run_draws default_draw_strat (Ret v1)))
      by (eapply det_ref_inv_tau_r; [exact Ho_tgt | exact Hdet]).
    assert (Hdet'' : det_ref dvalue_refines
                       (Ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w 0))))
                       (Ret v1))
      by (eapply det_ref_obs_eq; [exact Ho_src | reflexivity | exact Hdet']).
    pose proof (det_ref_ret_ret_inv dvalue_refines _ _ Hdet'') as Hdv.
    destruct Hdv as [Hpsn | Heq]; [discriminate Hpsn |].
    unfold v1 in Heq; inversion Heq as [Hi].
    assert (Hu0 : @Integers.unsigned w (@Integers.repr w 0) = 0%Z)
      by (apply @Integers.unsigned_repr; unfold Integers.max_unsigned, Integers.modulus, Integers.wordsize, Wordsize_pos.wordsize;
          assert (Hp : (2 <= two_power_nat (Pos.to_nat w))%Z) by
            (rewrite two_power_nat_equiv;
             assert (Hge1 : (1 <= Z.of_nat (Pos.to_nat w))%Z) by lia;
             pose proof (Z.pow_le_mono_r 2 1 (Z.of_nat (Pos.to_nat w)) ltac:(lia) Hge1); lia);
          lia).
    assert (Hu1 : @Integers.unsigned w (@Integers.repr w 1) = 1%Z)
      by (apply @Integers.unsigned_repr; unfold Integers.max_unsigned, Integers.modulus, Integers.wordsize, Wordsize_pos.wordsize;
          assert (Hp : (2 <= two_power_nat (Pos.to_nat w))%Z) by
            (rewrite two_power_nat_equiv;
             assert (Hge1 : (1 <= Z.of_nat (Pos.to_nat w))%Z) by lia;
             pose proof (Z.pow_le_mono_r 2 1 (Z.of_nat (Pos.to_nat w)) ltac:(lia) Hge1); lia);
          lia).
    rewrite Hi in Hu1; lia.
  Qed.

  (** [F-44] Positive Soundness Theorem (width-generic):
      [or(freeze x, -1) -> -1] refines for EVERY scalar [x] (poison or defined). *)
  Theorem or_freeze_all_ones_refines_mone :
    forall (sz : positive) (x : dvalue),
      wf_scalar_dvalue sz x ->
      ow_itree_refines dvalue_refines
        (ITree.bind (ow_freeze (DTYPE_Base (DTYPE_I sz)) x) (fun v =>
           EOU_to_itree (E := OW_E)
             (@eval_iop Pa (LLVMAst.Or false) v
                (DVALUE_Base (@DVALUE_I Pa sz (@Integers.mone sz))))))
        (Ret (DVALUE_Base (@DVALUE_I Pa sz (@Integers.mone sz)))).
  Proof using Type.
    intros sz x [-> | [ix ->]] sigma_tgt Hwft.
    - set (v0 := DVALUE_Base (@DVALUE_I Pa sz (@Integers.zero sz))).
      assert (Hv0 : valid_draw_value (DTYPE_Base (DTYPE_I sz)) v0)
        by (apply valid_draw_i_iff; exists (@Integers.zero sz); reflexivity).
      set (sigma_src := prepend_draws [(DTYPE_Base (DTYPE_I sz), v0)] sigma_tgt).
      exists sigma_src; split.
      + apply prepend_draws_wf; [constructor; [exact Hv0 | constructor] | exact Hwft].
      + eapply det_ref_tau_l.
        * rewrite observe_run_draws, observe_bind; unfold ow_freeze; rewrite observe_freeze_poison; reflexivity.
        * unfold sigma_src; cbn [prepend_draws].
          destruct (dtyp_eq_dec (DTYPE_Base (DTYPE_I sz)) (DTYPE_Base (DTYPE_I sz))) as [_ | Hneq];
            [| exfalso; exact (Hneq eq_refl)].
          pstep; apply DR_Step; unfold det_step_body.
          rewrite !observe_run_draws, observe_bind; cbn [observe].
          unfold v0, eval_iop; rewrite eval_iop_integer_base_same_width; cbn.
          rewrite @Integers.or_commut, @Integers.or_mone; right; reflexivity.
    - exists sigma_tgt; split; [exact Hwft |].
      pstep; apply DR_Step; unfold det_step_body.
      rewrite !observe_run_draws, observe_bind; unfold ow_freeze; rewrite observe_freeze_i_defined.
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn.
      rewrite @Integers.or_mone; right; reflexivity.
  Qed.

  (** [F-44] Positive Soundness Theorem on [i1]:
      [or(freeze x, 1) -> -1] refines for EVERY [i1] scalar [x]. *)
  Theorem or_freeze_i1_one_refines_mone :
    forall (x : dvalue),
      wf_scalar_dvalue 1%positive x ->
      ow_itree_refines dvalue_refines
        (ITree.bind (ow_freeze (DTYPE_Base (DTYPE_I 1%positive)) x) (fun v =>
           EOU_to_itree (E := OW_E)
             (@eval_iop Pa (LLVMAst.Or false) v
                (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.repr 1%positive 1))))))
        (Ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.repr 1%positive (-1))))).
  Proof using Type.
    intros x Hx.
    assert (H1m : @Integers.repr 1%positive 1 = @Integers.mone 1%positive)
      by (apply @Integers.same_bits_eq; intros i Hi;
          unfold Integers.zwordsize in Hi; assert (i = 0%Z) by lia; subst i; vm_compute; reflexivity).
    assert (Hm1 : @Integers.repr 1%positive (-1) = @Integers.mone 1%positive)
      by reflexivity.
    rewrite H1m, Hm1; exact (or_freeze_all_ones_refines_mone 1%positive x Hx).
  Qed.

(** ** 3. Operational Stepping on [MCFGtop] & [CFGtop] (Zero Dependent-Equality Axioms) *)

  Inductive mcfg_steps_to_ret {R : Type}
    : draw_strat -> rmap dvalue -> MCFGtop R -> draw_strat -> rmap dvalue -> R -> Prop :=
  | MSR_Ret sigma env (t : MCFGtop R) (r : R) :
      observe t = RetF r ->
      mcfg_steps_to_ret sigma env t sigma env r
  | MSR_Tau sigma env (t t' : MCFGtop R) sigma' env' r :
      observe t = TauF t' ->
      mcfg_steps_to_ret sigma env t' sigma' env' r ->
      mcfg_steps_to_ret sigma env t sigma' env' r
  | MSR_LocalRead sigma env (t : MCFGtop R) id dv (k : dvalue -> MCFGtop R) sigma' env' r :
      observe t = VisF (@subevent LocalE MCFGEtop _ dvalue (LocalRead id)) k ->
      RM.find id env = Some dv ->
      mcfg_steps_to_ret sigma env (k dv) sigma' env' r ->
      mcfg_steps_to_ret sigma env t sigma' env' r
  | MSR_LocalWrite sigma env (t : MCFGtop R) id dv (k : unit -> MCFGtop R) sigma' env' r :
      observe t = VisF (@subevent LocalE MCFGEtop _ unit (LocalWrite id dv)) k ->
      mcfg_steps_to_ret sigma (RM.add id dv env) (k tt) sigma' env' r ->
      mcfg_steps_to_ret sigma env t sigma' env' r
  | MSR_Draw sigma env (t : MCFGtop R) dt (k : dvalue -> MCFGtop R) sigma1 sigma' env' r :
      observe t = VisF (@subevent DrawE MCFGEtop _ dvalue (Draw dt)) k ->
      (forall n d, sigma1 n d = shift_draw_strat sigma n d) ->
      mcfg_steps_to_ret sigma1 env (k (sigma 0%nat dt)) sigma' env' r ->
      mcfg_steps_to_ret sigma env t sigma' env' r.

  Inductive mcfg_steps_to_ub {R : Type}
    : draw_strat -> rmap dvalue -> MCFGtop R -> Prop :=
  | MSU_UB sigma env (t : MCFGtop R) (k : void -> MCFGtop R) :
      observe t = VisF (@subevent UBE MCFGEtop _ void (ThrowUB tt)) k ->
      mcfg_steps_to_ub sigma env t
  | MSU_Tau sigma env (t t' : MCFGtop R) :
      observe t = TauF t' ->
      mcfg_steps_to_ub sigma env t' ->
      mcfg_steps_to_ub sigma env t
  | MSU_LocalRead sigma env (t : MCFGtop R) id dv (k : dvalue -> MCFGtop R) :
      observe t = VisF (@subevent LocalE MCFGEtop _ dvalue (LocalRead id)) k ->
      RM.find id env = Some dv ->
      mcfg_steps_to_ub sigma env (k dv) ->
      mcfg_steps_to_ub sigma env t
  | MSU_LocalWrite sigma env (t : MCFGtop R) id dv (k : unit -> MCFGtop R) :
      observe t = VisF (@subevent LocalE MCFGEtop _ unit (LocalWrite id dv)) k ->
      mcfg_steps_to_ub sigma (RM.add id dv env) (k tt) ->
      mcfg_steps_to_ub sigma env t
  | MSU_Draw sigma env (t : MCFGtop R) dt (k : dvalue -> MCFGtop R) sigma1 :
      observe t = VisF (@subevent DrawE MCFGEtop _ dvalue (Draw dt)) k ->
      (forall n d, sigma1 n d = shift_draw_strat sigma n d) ->
      mcfg_steps_to_ub sigma1 env (k (sigma 0%nat dt)) ->
      mcfg_steps_to_ub sigma env t.

  Inductive cfg_steps_to_ret {R : Type}
    : draw_strat -> rmap dvalue -> CFGtop R -> draw_strat -> rmap dvalue -> R -> Prop :=
  | CSR_Ret sigma env (t : CFGtop R) (r : R) :
      observe t = RetF r ->
      cfg_steps_to_ret sigma env t sigma env r
  | CSR_Tau sigma env (t t' : CFGtop R) sigma' env' r :
      observe t = TauF t' ->
      cfg_steps_to_ret sigma env t' sigma' env' r ->
      cfg_steps_to_ret sigma env t sigma' env' r
  | CSR_LocalRead sigma env (t : CFGtop R) id dv (k : dvalue -> CFGtop R) sigma' env' r :
      observe t = VisF (@subevent LocalE CFGEtop _ dvalue (LocalRead id)) k ->
      RM.find id env = Some dv ->
      cfg_steps_to_ret sigma env (k dv) sigma' env' r ->
      cfg_steps_to_ret sigma env t sigma' env' r
  | CSR_LocalWrite sigma env (t : CFGtop R) id dv (k : unit -> CFGtop R) sigma' env' r :
      observe t = VisF (@subevent LocalE CFGEtop _ unit (LocalWrite id dv)) k ->
      cfg_steps_to_ret sigma (RM.add id dv env) (k tt) sigma' env' r ->
      cfg_steps_to_ret sigma env t sigma' env' r
  | CSR_Draw sigma env (t : CFGtop R) dt (k : dvalue -> CFGtop R) sigma1 sigma' env' r :
      observe t = VisF (@subevent DrawE CFGEtop _ dvalue (Draw dt)) k ->
      (forall n d, sigma1 n d = shift_draw_strat sigma n d) ->
      cfg_steps_to_ret sigma1 env (k (sigma 0%nat dt)) sigma' env' r ->
      cfg_steps_to_ret sigma env t sigma' env' r.

  Inductive cfg_steps_to_ub {R : Type}
    : draw_strat -> rmap dvalue -> CFGtop R -> Prop :=
  | CSU_UB sigma env (t : CFGtop R) (k : void -> CFGtop R) :
      observe t = VisF (@subevent UBE CFGEtop _ void (ThrowUB tt)) k ->
      cfg_steps_to_ub sigma env t
  | CSU_Tau sigma env (t t' : CFGtop R) :
      observe t = TauF t' ->
      cfg_steps_to_ub sigma env t' ->
      cfg_steps_to_ub sigma env t
  | CSU_LocalRead sigma env (t : CFGtop R) id dv (k : dvalue -> CFGtop R) :
      observe t = VisF (@subevent LocalE CFGEtop _ dvalue (LocalRead id)) k ->
      RM.find id env = Some dv ->
      cfg_steps_to_ub sigma env (k dv) ->
      cfg_steps_to_ub sigma env t
  | CSU_LocalWrite sigma env (t : CFGtop R) id dv (k : unit -> CFGtop R) :
      observe t = VisF (@subevent LocalE CFGEtop _ unit (LocalWrite id dv)) k ->
      cfg_steps_to_ub sigma (RM.add id dv env) (k tt) ->
      cfg_steps_to_ub sigma env t
  | CSU_Draw sigma env (t : CFGtop R) dt (k : dvalue -> CFGtop R) sigma1 :
      observe t = VisF (@subevent DrawE CFGEtop _ dvalue (Draw dt)) k ->
      (forall n d, sigma1 n d = shift_draw_strat sigma n d) ->
      cfg_steps_to_ub sigma1 env (k (sigma 0%nat dt)) ->
      cfg_steps_to_ub sigma env t.

  Lemma mcfg_steps_to_ret_obs {R : Type} :
    forall sigma env (t1 t2 : MCFGtop R) sigma' env' r,
      observe t1 = observe t2 ->
      mcfg_steps_to_ret sigma env t1 sigma' env' r ->
      mcfg_steps_to_ret sigma env t2 sigma' env' r.
  Proof using Type.
    intros sigma env t1 t2 sigma' env' r Ho H.
    inversion H; subst;
      [apply MSR_Ret | eapply MSR_Tau | eapply MSR_LocalRead | eapply MSR_LocalWrite | eapply MSR_Draw];
      try (rewrite <- Ho; eassumption); eassumption.
  Qed.

  Lemma mcfg_steps_to_ub_obs {R : Type} :
    forall sigma env (t1 t2 : MCFGtop R),
      observe t1 = observe t2 ->
      mcfg_steps_to_ub sigma env t1 ->
      mcfg_steps_to_ub sigma env t2.
  Proof using Type.
    intros sigma env t1 t2 Ho H.
    inversion H; subst;
      [eapply MSU_UB | eapply MSU_Tau | eapply MSU_LocalRead | eapply MSU_LocalWrite | eapply MSU_Draw];
      try (rewrite <- Ho; eassumption); eassumption.
  Qed.

  Lemma cfg_steps_to_ret_obs {R : Type} :
    forall sigma env (t1 t2 : CFGtop R) sigma' env' r,
      observe t1 = observe t2 ->
      cfg_steps_to_ret sigma env t1 sigma' env' r ->
      cfg_steps_to_ret sigma env t2 sigma' env' r.
  Proof using Type.
    intros sigma env t1 t2 sigma' env' r Ho H.
    inversion H; subst;
      [apply CSR_Ret | eapply CSR_Tau | eapply CSR_LocalRead | eapply CSR_LocalWrite | eapply CSR_Draw];
      try (rewrite <- Ho; eassumption); eassumption.
  Qed.

  Lemma cfg_steps_to_ub_obs {R : Type} :
    forall sigma env (t1 t2 : CFGtop R),
      observe t1 = observe t2 ->
      cfg_steps_to_ub sigma env t1 ->
      cfg_steps_to_ub sigma env t2.
  Proof using Type.
    intros sigma env t1 t2 Ho H.
    inversion H; subst;
      [eapply CSU_UB | eapply CSU_Tau | eapply CSU_LocalRead | eapply CSU_LocalWrite | eapply CSU_Draw];
      try (rewrite <- Ho; eassumption); eassumption.
  Qed.

  Lemma mcfg_steps_to_ret_bind {R S : Type} :
    forall s0 env0 (t : MCFGtop R) s1 env1 x (k : R -> MCFGtop S) s2 env2 y,
      mcfg_steps_to_ret s0 env0 t s1 env1 x ->
      mcfg_steps_to_ret s1 env1 (k x) s2 env2 y ->
      mcfg_steps_to_ret s0 env0 (ITree.bind t k) s2 env2 y.
  Proof using Type.
    intros s0 env0 t s1 env1 x k s2 env2 y H1 H2.
    induction H1 as
      [ s env t r Ho
      | s env t t' s' env' r Ho _ IH
      | s env t id dv ke s' env' r Ho Hf _ IH
      | s env t id dv ke s' env' r Ho _ IH
      | s env t dt ke s_sh s' env' r Ho Hsh _ IH ].
    - eapply mcfg_steps_to_ret_obs; [symmetry; rewrite observe_bind, Ho; reflexivity | exact H2].
    - eapply MSR_Tau; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply MSR_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact (IH H2)].
    - eapply MSR_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply MSR_Draw; [rewrite observe_bind, Ho; reflexivity | exact Hsh | exact (IH H2)].
  Qed.

  Lemma mcfg_steps_to_ub_bind_l {R S : Type} :
    forall s0 env0 (t : MCFGtop R) (k : R -> MCFGtop S),
      mcfg_steps_to_ub s0 env0 t ->
      mcfg_steps_to_ub s0 env0 (ITree.bind t k).
  Proof using Type.
    intros s0 env0 t k H.
    induction H as
      [ s env t ke Ho
      | s env t t' Ho _ IH
      | s env t id dv ke Ho Hf _ IH
      | s env t id dv ke Ho _ IH
      | s env t dt ke s_sh Ho Hsh _ IH ].
    - eapply MSU_UB; rewrite observe_bind, Ho; reflexivity.
    - eapply MSU_Tau; [rewrite observe_bind, Ho; reflexivity | exact IH].
    - eapply MSU_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact IH].
    - eapply MSU_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact IH].
    - eapply MSU_Draw; [rewrite observe_bind, Ho; reflexivity | exact Hsh | exact IH].
  Qed.

  Lemma mcfg_steps_to_ub_bind_r {R S : Type} :
    forall s0 env0 (t : MCFGtop R) s1 env1 x (k : R -> MCFGtop S),
      mcfg_steps_to_ret s0 env0 t s1 env1 x ->
      mcfg_steps_to_ub s1 env1 (k x) ->
      mcfg_steps_to_ub s0 env0 (ITree.bind t k).
  Proof using Type.
    intros s0 env0 t s1 env1 x k H1 H2.
    induction H1 as
      [ s env t r Ho
      | s env t t' s' env' r Ho _ IH
      | s env t id dv ke s' env' r Ho Hf _ IH
      | s env t id dv ke s' env' r Ho _ IH
      | s env t dt ke s_sh s' env' r Ho Hsh _ IH ].
    - eapply mcfg_steps_to_ub_obs; [symmetry; rewrite observe_bind, Ho; reflexivity | exact H2].
    - eapply MSU_Tau; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply MSU_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact (IH H2)].
    - eapply MSU_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply MSU_Draw; [rewrite observe_bind, Ho; reflexivity | exact Hsh | exact (IH H2)].
  Qed.

  Lemma cfg_steps_to_ret_bind {R S : Type} :
    forall s0 env0 (t : CFGtop R) s1 env1 x (k : R -> CFGtop S) s2 env2 y,
      cfg_steps_to_ret s0 env0 t s1 env1 x ->
      cfg_steps_to_ret s1 env1 (k x) s2 env2 y ->
      cfg_steps_to_ret s0 env0 (ITree.bind t k) s2 env2 y.
  Proof using Type.
    intros s0 env0 t s1 env1 x k s2 env2 y H1 H2.
    induction H1 as
      [ s env t r Ho
      | s env t t' s' env' r Ho _ IH
      | s env t id dv ke s' env' r Ho Hf _ IH
      | s env t id dv ke s' env' r Ho _ IH
      | s env t dt ke s_sh s' env' r Ho Hsh _ IH ].
    - eapply cfg_steps_to_ret_obs; [symmetry; rewrite observe_bind, Ho; reflexivity | exact H2].
    - eapply CSR_Tau; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply CSR_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact (IH H2)].
    - eapply CSR_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply CSR_Draw; [rewrite observe_bind, Ho; reflexivity | exact Hsh | exact (IH H2)].
  Qed.

  Lemma cfg_steps_to_ub_bind_l {R S : Type} :
    forall s0 env0 (t : CFGtop R) (k : R -> CFGtop S),
      cfg_steps_to_ub s0 env0 t ->
      cfg_steps_to_ub s0 env0 (ITree.bind t k).
  Proof using Type.
    intros s0 env0 t k H.
    induction H as
      [ s env t ke Ho
      | s env t t' Ho _ IH
      | s env t id dv ke Ho Hf _ IH
      | s env t id dv ke Ho _ IH
      | s env t dt ke s_sh Ho Hsh _ IH ].
    - eapply CSU_UB; rewrite observe_bind, Ho; reflexivity.
    - eapply CSU_Tau; [rewrite observe_bind, Ho; reflexivity | exact IH].
    - eapply CSU_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact IH].
    - eapply CSU_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact IH].
    - eapply CSU_Draw; [rewrite observe_bind, Ho; reflexivity | exact Hsh | exact IH].
  Qed.

  Lemma cfg_steps_to_ub_bind_r {R S : Type} :
    forall s0 env0 (t : CFGtop R) s1 env1 x (k : R -> CFGtop S),
      cfg_steps_to_ret s0 env0 t s1 env1 x ->
      cfg_steps_to_ub s1 env1 (k x) ->
      cfg_steps_to_ub s0 env0 (ITree.bind t k).
  Proof using Type.
    intros s0 env0 t s1 env1 x k H1 H2.
    induction H1 as
      [ s env t r Ho
      | s env t t' s' env' r Ho _ IH
      | s env t id dv ke s' env' r Ho Hf _ IH
      | s env t id dv ke s' env' r Ho _ IH
      | s env t dt ke s_sh s' env' r Ho Hsh _ IH ].
    - eapply cfg_steps_to_ub_obs; [symmetry; rewrite observe_bind, Ho; reflexivity | exact H2].
    - eapply CSU_Tau; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply CSU_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact (IH H2)].
    - eapply CSU_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply CSU_Draw; [rewrite observe_bind, Ho; reflexivity | exact Hsh | exact (IH H2)].
  Qed.

  Lemma mcfg_to_cfg_steps_ret {R : Type} :
    forall s0 env0 (t : MCFGtop R) s1 env1 r,
      mcfg_steps_to_ret s0 env0 t s1 env1 r ->
      cfg_steps_to_ret s0 env0 (withCall t) s1 env1 r.
  Proof using Type.
    intros s0 env0 t s1 env1 r H.
    induction H as
      [ s env t r Ho
      | s env t t' s' env' r Ho _ IH
      | s env t id dv ke s' env' r Ho Hf _ IH
      | s env t id dv ke s' env' r Ho _ IH
      | s env t dt ke s_sh s' env' r Ho Hsh _ IH ];
      unfold withCall in *.
    - apply CSR_Ret; rewrite observe_translate, Ho; reflexivity.
    - eapply CSR_Tau; [rewrite observe_translate, Ho; reflexivity | exact IH].
    - eapply CSR_LocalRead; [rewrite observe_translate, Ho; reflexivity | exact Hf | exact IH].
    - eapply CSR_LocalWrite; [rewrite observe_translate, Ho; reflexivity | exact IH].
    - eapply CSR_Draw; [rewrite observe_translate, Ho; reflexivity | exact Hsh | exact IH].
  Qed.

  Lemma mcfg_to_cfg_steps_ub {R : Type} :
    forall s0 env0 (t : MCFGtop R),
      mcfg_steps_to_ub s0 env0 t ->
      cfg_steps_to_ub s0 env0 (withCall t).
  Proof using Type.
    intros s0 env0 t H.
    induction H as
      [ s env t ke Ho
      | s env t t' Ho _ IH
      | s env t id dv ke Ho Hf _ IH
      | s env t id dv ke Ho _ IH
      | s env t dt ke s_sh Ho Hsh _ IH ];
      unfold withCall in *.
    - eapply CSU_UB; rewrite observe_translate, Ho; reflexivity.
    - eapply CSU_Tau; [rewrite observe_translate, Ho; reflexivity | exact IH].
    - eapply CSU_LocalRead; [rewrite observe_translate, Ho; reflexivity | exact Hf | exact IH].
    - eapply CSU_LocalWrite; [rewrite observe_translate, Ho; reflexivity | exact IH].
    - eapply CSU_Draw; [rewrite observe_translate, Ho; reflexivity | exact Hsh | exact IH].
  Qed.

  Lemma mcfg_steps_to_ub_sigma_ext {R : Type} :
    forall s1 s2 env (t : MCFGtop R),
      (forall n d, s1 n d = s2 n d) ->
      mcfg_steps_to_ub s1 env t ->
      mcfg_steps_to_ub s2 env t.
  Proof using Type.
    intros s1 s2 env t Heq H; revert s2 Heq.
    induction H as
      [ s env t ke Ho
      | s env t t' Ho _ IH
      | s env t id dv ke Ho Hf _ IH
      | s env t id dv ke Ho _ IH
      | s env t dt ke s_sh Ho Hsh Hsub _ ];
      intros s2 Heq.
    - eapply MSU_UB; exact Ho.
    - eapply MSU_Tau; [exact Ho | exact (IH s2 Heq)].
    - eapply MSU_LocalRead; [exact Ho | exact Hf | exact (IH s2 Heq)].
    - eapply MSU_LocalWrite; [exact Ho | exact (IH s2 Heq)].
    - eapply MSU_Draw.
      + exact Ho.
      + intros n d; unfold shift_draw_strat in *; rewrite <- (Heq (S n) d); exact (Hsh n d).
      + rewrite <- (Heq 0%nat dt); exact Hsub.
  Qed.

  Lemma cfg_steps_to_ub_sigma_ext {R : Type} :
    forall s1 s2 env (t : CFGtop R),
      (forall n d, s1 n d = s2 n d) ->
      cfg_steps_to_ub s1 env t ->
      cfg_steps_to_ub s2 env t.
  Proof using Type.
    intros s1 s2 env t Heq H; revert s2 Heq.
    induction H as
      [ s env t ke Ho
      | s env t t' Ho _ IH
      | s env t id dv ke Ho Hf _ IH
      | s env t id dv ke Ho _ IH
      | s env t dt ke s_sh Ho Hsh Hsub _ ];
      intros s2 Heq.
    - eapply CSU_UB; exact Ho.
    - eapply CSU_Tau; [exact Ho | exact (IH s2 Heq)].
    - eapply CSU_LocalRead; [exact Ho | exact Hf | exact (IH s2 Heq)].
    - eapply CSU_LocalWrite; [exact Ho | exact (IH s2 Heq)].
    - eapply CSU_Draw.
      + exact Ho.
      + intros n d; unfold shift_draw_strat in *; rewrite <- (Heq (S n) d); exact (Hsh n d).
      + rewrite <- (Heq 0%nat dt); exact Hsub.
  Qed.

  Lemma cfg_steps_ub_det_ref {R1 R2 : Type} (RR : R1 -> R2 -> Prop) :
    forall sigma env (t1 : CFGtop R1) (t2 : itree Det_OW_E R2),
      cfg_steps_to_ub sigma env t1 ->
      det_ref RR (run_draws sigma (run_cfg_locals env t1)) t2.
  Proof using Type.
    intros sigma env t1 t2 H; revert t2.
    induction H as
      [ s env t ke Ho
      | s env t t' Ho _ IH
      | s env t id dv ke Ho Hf _ IH
      | s env t id dv ke Ho _ IH
      | s env t dt ke s_sh Ho Hsh _ IH ];
      intros t2.
    - pstep; apply DR_Step; unfold det_step_body.
      rewrite observe_run_draws, observe_run_cfg_locals, Ho; cbn; left; reflexivity.
    - eapply det_ref_tau_l; [| exact (IH t2)].
      rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity.
    - eapply det_ref_tau_l; [| exact (IH t2)].
      rewrite observe_run_draws, observe_run_cfg_locals, Ho; cbn; rewrite Hf; reflexivity.
    - eapply det_ref_tau_l; [| exact (IH t2)].
      rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity.
    - eapply det_ref_tau_l.
      + rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity.
      + eapply det_ref_trans with (R12 := @eq R1) (R23 := RR);
          [intros ? ? ? -> Hx; exact Hx | | exact (IH t2)].
        eapply (run_draws_ext_det_ref (@eq R1) (fun x => eq_refl)).
        intros n d; symmetry; exact (Hsh n d).
  Qed.

  Lemma cfg_steps_ret_det_ref {R1 R2 : Type} (RR : R1 -> R2 -> Prop) :
    forall s1 env1 (t1 : CFGtop R1) s1' env1' v1
           s2 env2 (t2 : CFGtop R2) s2' env2' v2,
      cfg_steps_to_ret s1 env1 t1 s1' env1' v1 ->
      cfg_steps_to_ret s2 env2 t2 s2' env2' v2 ->
      RR v1 v2 ->
      det_ref RR
        (run_draws s1 (run_cfg_locals env1 t1))
        (run_draws s2 (run_cfg_locals env2 t2)).
  Proof using Type.
    intros s1 env1 t1 s1' env1' v1 s2 env2 t2 s2' env2' v2 H1 H2 Hrr.
    induction H1 as
      [ s env t r Ho1
      | s env t t' s' env' r Ho1 _ IH1
      | s env t id dv ke s' env' r Ho1 Hf _ IH1
      | s env t id dv ke s' env' r Ho1 _ IH1
      | s env t dt ke s_sh s' env' r Ho1 Hsh _ IH1 ].
    - induction H2 as
        [ sb eb tb rb Ho2
        | sb eb tb tb' sb' eb' rb Ho2 _ IH2
        | sb eb tb id dv ke sb' eb' rb Ho2 Hf _ IH2
        | sb eb tb id dv ke sb' eb' rb Ho2 _ IH2
        | sb eb tb dt ke s_sh sb' eb' rb Ho2 Hsh _ IH2 ].
      + pstep; apply DR_Step; unfold det_step_body.
        rewrite !observe_run_draws, !observe_run_cfg_locals, Ho1, Ho2; exact Hrr.
      + eapply det_ref_tau_r; [| exact (IH2 Hrr)].
        rewrite observe_run_draws, observe_run_cfg_locals, Ho2; reflexivity.
      + eapply det_ref_tau_r; [| exact (IH2 Hrr)].
        rewrite observe_run_draws, observe_run_cfg_locals, Ho2; cbn; rewrite Hf; reflexivity.
      + eapply det_ref_tau_r; [| exact (IH2 Hrr)].
        rewrite observe_run_draws, observe_run_cfg_locals, Ho2; reflexivity.
      + eapply det_ref_tau_r.
        * rewrite observe_run_draws, observe_run_cfg_locals, Ho2; reflexivity.
        * eapply det_ref_trans with (R12 := RR) (R23 := @eq R2);
            [intros ? ? ? Hx <-; exact Hx | exact (IH2 Hrr) |].
          eapply (run_draws_ext_det_ref (@eq R2) (fun x => eq_refl)).
          intros n d; exact (Hsh n d).
    - eapply det_ref_tau_l; [| exact (IH1 Hrr)].
      rewrite observe_run_draws, observe_run_cfg_locals, Ho1; reflexivity.
    - eapply det_ref_tau_l; [| exact (IH1 Hrr)].
      rewrite observe_run_draws, observe_run_cfg_locals, Ho1; cbn; rewrite Hf; reflexivity.
    - eapply det_ref_tau_l; [| exact (IH1 Hrr)].
      rewrite observe_run_draws, observe_run_cfg_locals, Ho1; reflexivity.
    - eapply det_ref_tau_l.
      + rewrite observe_run_draws, observe_run_cfg_locals, Ho1; reflexivity.
      + eapply det_ref_trans with (R12 := @eq R1) (R23 := RR);
          [intros ? ? ? -> Hx; exact Hx | | exact (IH1 Hrr)].
        eapply (run_draws_ext_det_ref (@eq R1) (fun x => eq_refl)).
        intros n d; symmetry; exact (Hsh n d).
  Qed.

End OpenWorldEvents.

(** ** 4. Open-World Per-Function CFG Refinement [validator_cfg_refines] *)

Fixpoint raw_id_in_list (r : raw_id) (xs : list raw_id) : bool :=
  match xs with
  | [] => false
  | x :: rx => raw_id_eqb r x || raw_id_in_list r rx
  end.

Lemma raw_id_in_list_spec : forall r xs,
  raw_id_in_list r xs = true <-> In r xs.
Proof.
  intros r xs; induction xs as [| x rx IH]; cbn; [split; [discriminate | contradiction] |].
  destruct (raw_id_eqb r x) eqn:E.
  - apply raw_id_eqb_eq in E; subst; split; [intros _; left; reflexivity | intros _; reflexivity].
  - rewrite IH; split; [intros H; right; exact H | intros [-> | H]; [rewrite raw_id_eqb_refl in E; discriminate | exact H]].
Qed.

Fixpoint find_raw_id_index_from (r : raw_id) (xs : list raw_id) (idx : nat) : option nat :=
  match xs with
  | [] => None
  | x :: rx =>
      if raw_id_eqb r x then Some idx else find_raw_id_index_from r rx (S idx)
  end.

Definition find_raw_id_index (r : raw_id) (xs : list raw_id) : option nat :=
  find_raw_id_index_from r xs 0%nat.

Lemma find_raw_id_index_from_nth_error :
  forall xs r base idx,
    find_raw_id_index_from r xs base = Some idx ->
    (base <= idx)%nat /\ nth_error xs (idx - base) = Some r.
Proof.
  induction xs as [| x rx IH]; intros r base idx H; cbn in H; [discriminate |].
  destruct (raw_id_eqb r x) eqn:E.
  - apply raw_id_eqb_eq in E; subst x; inversion H; subst idx.
    split; [lia | rewrite Nat.sub_diag; reflexivity].
  - destruct (IH r (S base) idx H) as [Hle Hnth].
    split; [lia |].
    destruct (idx - base)%nat as [| k] eqn:Ed; [lia |].
    cbn; replace k with (idx - S base)%nat by lia; exact Hnth.
Qed.

Lemma find_raw_id_index_nth_error :
  forall xs r idx,
    find_raw_id_index r xs = Some idx ->
    nth_error xs idx = Some r.
Proof.
  intros xs r idx H.
  destruct (find_raw_id_index_from_nth_error xs r 0%nat idx H) as [_ Hnth].
  rewrite Nat.sub_0_r in Hnth; exact Hnth.
Qed.

Definition defined_ids_of_block (b : block dtyp) : list raw_id :=
  List.map (fun '(id, _, _) => id) (blk_phis b) ++
  List.flat_map (fun '(iid, _, _) =>
    match iid with
    | IId id => [id]
    | IVoid _ => []
    end) (blk_code b).

Definition defined_ids_of_cfg (G : CFG.cfg dtyp) : list raw_id :=
  List.flat_map defined_ids_of_block (blks G).

Fixpoint exp_param_uses (params defs : list raw_id) (top : option dtyp) (o : exp dtyp)
  {struct o} : list (nat * dtyp) :=
  let fix texp_list_uses (xs : list (dtyp * exp dtyp)) : list (nat * dtyp) :=
      match xs with
      | [] => []
      | (dt, sub) :: rx => exp_param_uses params defs (Some dt) sub ++ texp_list_uses rx
      end in
  match o with
  | EXP_Ident (ID_Local r) =>
      if raw_id_in_list r defs then []
      else match find_raw_id_index r params, top with
           | Some idx, Some dt => [(idx, dt)]
           | _, _ => []
           end
  | EXP_Ident (ID_Global _) | EXP_Integer _ | EXP_Float _ | EXP_Bool _
  | EXP_Null | EXP_Zero_initializer | EXP_Undef | EXP_Poison
  | EXP_BlockAddress _ _ | EXP_Asm _ _ _ _ _ _ | EXP_Metadata _ => []
  | EXP_Cstring l | EXP_Struct l | EXP_Packed_struct l
  | EXP_Array l | EXP_Vector l => texp_list_uses l
  | OP_IBinop _ dt e1 e2 | OP_ICmp _ _ dt e1 e2
  | OP_FBinop _ _ dt e1 e2 | OP_FCmp _ _ dt e1 e2 =>
      exp_param_uses params defs (Some dt) e1 ++
      exp_param_uses params defs (Some dt) e2
  | OP_Conversion _ dtf sub _ =>
      exp_param_uses params defs (Some dtf) sub
  | OP_GetElementPtr _ _ (dtp, pe) idxs =>
      exp_param_uses params defs (Some dtp) pe ++ texp_list_uses idxs
  | OP_ExtractElement (dt1, e1) (dt2, e2)
  | OP_InsertValue (dt1, e1) (dt2, e2) _ =>
      exp_param_uses params defs (Some dt1) e1 ++
      exp_param_uses params defs (Some dt2) e2
  | OP_InsertElement (dt1, e1) (dt2, e2) (dt3, e3)
  | OP_ShuffleVector (dt1, e1) (dt2, e2) (dt3, e3)
  | OP_Select _ (dt1, e1) (dt2, e2) (dt3, e3) =>
      exp_param_uses params defs (Some dt1) e1 ++
      exp_param_uses params defs (Some dt2) e2 ++
      exp_param_uses params defs (Some dt3) e3
  | OP_ExtractValue (dt, sub) _ | OP_Freeze (dt, sub)
  | OP_Fneg _ (dt, sub) | EXP_Splat (dt, sub) =>
      exp_param_uses params defs (Some dt) sub
  end.

Definition block_param_uses (params defs : list raw_id) (b : block dtyp)
  : list (nat * dtyp) :=
  List.flat_map (fun '(_, Phi _ dt pargs, _) =>
    List.flat_map (fun '(_, e) => exp_param_uses params defs (Some dt) e) pargs)
    (blk_phis b) ++
  List.flat_map (fun '(_, ins, _) =>
    match ins with
    | INSTR_Op e => exp_param_uses params defs None e
    | _ => []
    end) (blk_code b) ++
  match blk_term b with
  | (_, TERM_Ret (dt, e), _)
  | (_, TERM_Br (dt, e) _ _, _)
  | (_, TERM_Switch (dt, e) _ _, _)
  | (_, TERM_IndirectBr (dt, e) _ _, _)
  | (_, TERM_Resume (dt, e), _) => exp_param_uses params defs (Some dt) e
  | _ => []
  end.

Definition param_idx_uses_cfg (G : CFG.cfg dtyp) : list (nat * dtyp) :=
  let defs := defined_ids_of_cfg G in
  List.flat_map (block_param_uses (args G) defs) (blks G).

Definition dtyp_eqb_dec (t1 t2 : dtyp) : bool :=
  if dtyp_eq_dec t1 t2 then true else false.

Lemma dtyp_eqb_dec_eq : forall t1 t2, dtyp_eqb_dec t1 t2 = true <-> t1 = t2.
Proof.
  intros t1 t2; unfold dtyp_eqb_dec; destruct (dtyp_eq_dec t1 t2);
    split; intros H; try reflexivity; try assumption; discriminate.
Qed.

Definition param_use_eqb (u1 u2 : nat * dtyp) : bool :=
  Nat.eqb (fst u1) (fst u2) && dtyp_eqb_dec (snd u1) (snd u2).

Lemma param_use_eqb_eq : forall u1 u2, param_use_eqb u1 u2 = true <-> u1 = u2.
Proof.
  intros [i1 t1] [i2 t2]; unfold param_use_eqb; cbn.
  rewrite andb_true_iff, Nat.eqb_eq, dtyp_eqb_dec_eq.
  split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

Fixpoint param_use_in (u : nat * dtyp) (us : list (nat * dtyp)) : bool :=
  match us with
  | [] => false
  | x :: rx => param_use_eqb u x || param_use_in u rx
  end.

Lemma param_use_in_spec : forall u us, param_use_in u us = true <-> In u us.
Proof.
  intros u us; induction us as [| x rx IH]; cbn; [split; [discriminate | contradiction] |].
  destruct (param_use_eqb u x) eqn:E.
  - apply param_use_eqb_eq in E; subst; split; [intros _; left; reflexivity | intros _; reflexivity].
  - rewrite IH; split; [intros H; right; exact H | intros [-> | H]; [
      assert (Hr : param_use_eqb x x = true) by (apply param_use_eqb_eq; reflexivity);
      rewrite Hr in E; discriminate | exact H]].
Qed.

Definition cfg_param_dtyp_compatible (G : CFG.cfg dtyp) (arg_dtys : list dtyp) : bool :=
  forallb (fun '(idx, dt) =>
    match nth_error arg_dtys idx with
    | Some dt_arg => dtyp_eqb_dec dt dt_arg
    | None => false
    end) (param_idx_uses_cfg G).

(** Top-level open-world per-function semantic refinement ([F-33] & [F-44]). *)
Definition validator_cfg_refines {Pa : Params} (src_cfg tgt_cfg : CFG.cfg dtyp) : Prop :=
  List.length (args src_cfg) = List.length (args tgt_cfg) /\
  forall (arg_dtys : list dtyp),
    List.length arg_dtys = List.length (args src_cfg) ->
    cfg_param_dtyp_compatible src_cfg arg_dtys = true ->
    cfg_param_dtyp_compatible tgt_cfg arg_dtys = true /\
    forall (vs : list (@dvalue Pa)),
      Forall2 dvalue_has_dtyp vs arg_dtys ->
      ow_itree_refines dvalue_refines
        (eval_cfg_open src_cfg vs)
        (eval_cfg_open tgt_cfg vs).

Theorem validator_cfg_refines_refl :
  forall {Pa : Params} (G : CFG.cfg dtyp),
    @validator_cfg_refines Pa G G.
Proof.
  intros Pa G; split; [reflexivity |].
  intros arg_dtys _ Hcomp; split; [exact Hcomp |].
  intros vs _; exact (ow_itree_refines_refl (@dvalue_refines Pa) (@dvalue_refines_refl Pa) (eval_cfg_open G vs)).
Qed.

Theorem validator_cfg_refines_trans :
  forall {Pa : Params} (G1 G2 G3 : CFG.cfg dtyp),
    @validator_cfg_refines Pa G1 G2 ->
    @validator_cfg_refines Pa G2 G3 ->
    @validator_cfg_refines Pa G1 G3.
Proof.
  intros Pa G1 G2 G3 [Hlen12 Href12] [Hlen23 Href23].
  split; [lia |].
  intros arg_dtys Hlen1 Hcomp1.
  destruct (Href12 arg_dtys Hlen1 Hcomp1) as [Hcomp2 Hsim12].
  assert (Hlen2 : List.length arg_dtys = List.length (args G2)) by lia.
  destruct (Href23 arg_dtys Hlen2 Hcomp2) as [Hcomp3 Hsim23].
  split; [exact Hcomp3 |].
  intros vs Hvs.
  eapply ow_itree_refines_trans;
    [exact (@dvalue_refines_trans Pa) | exact (Hsim12 vs Hvs) | exact (Hsim23 vs Hvs)].
Qed.


(** ** 5. Bounded-DAG SSA Reification, [cert-v1] Checker & Soundness ([0 Admitted]) *)

(** *** 5.1 Canonical Register Naming, Distinctness & [ocfg_map] Membership *)

Definition show_Z_dec (z : Z) : string :=
  NilEmpty.string_of_int (Z.to_int z).

Definition cert_raw_id_bare (id : raw_id) : string :=
  match id with
  | Name s => s
  | Anon z => show_Z_dec z
  | Raw z => "_RAW_" ++ show_Z_dec z
  end.

Definition cert_reg_name (id : raw_id) : string :=
  "%" ++ cert_raw_id_bare id.

Lemma cert_reg_name_not_dollar : forall id,
  starts_with_dollar (cert_reg_name id) = false.
Proof.
  intros id; reflexivity.
Qed.

Fixpoint no_dup_strings (xs : list string) : bool :=
  match xs with
  | [] => true
  | x :: rx => negb (string_in_list x rx) && no_dup_strings rx
  end.

Lemma no_dup_strings_spec : forall xs,
  no_dup_strings xs = true <-> NoDup xs.
Proof.
  induction xs as [| x rx IH]; cbn.
  - split; [intros _; constructor | intros _; reflexivity].
  - rewrite andb_true_iff, negb_true_iff, IH.
    split.
    + intros [Hni Hnd]; constructor; [| exact Hnd].
      intros Hin; apply string_in_list_spec in Hin; congruence.
    + intros Hnd; inversion Hnd as [| ? ? Hni Hndr]; subst; split; [| exact Hndr].
      destruct (string_in_list x rx) eqn:E; [| reflexivity].
      apply string_in_list_spec in E; contradiction.
Qed.

Fixpoint no_dup_raw_ids (xs : list raw_id) : bool :=
  match xs with
  | [] => true
  | x :: rx => negb (raw_id_in_list x rx) && no_dup_raw_ids rx
  end.

Lemma no_dup_raw_ids_spec : forall xs,
  no_dup_raw_ids xs = true <-> NoDup xs.
Proof.
  induction xs as [| x rx IH]; cbn.
  - split; [intros _; constructor | intros _; reflexivity].
  - rewrite andb_true_iff, negb_true_iff, IH.
    split.
    + intros [Hni Hnd]; constructor; [| exact Hnd].
      intros Hin; apply raw_id_in_list_spec in Hin; congruence.
    + intros Hnd; inversion Hnd as [| ? ? Hni Hndr]; subst; split; [| exact Hndr].
      destruct (raw_id_in_list x rx) eqn:E; [| reflexivity].
      apply raw_id_in_list_spec in E; contradiction.
Qed.

Lemma ocfg_map_in {T : Set} :
  forall (bs : list (block T)) bid b,
    RM.find bid (ocfg_map bs) = Some b ->
    In b bs.
Proof.
  induction bs as [| b0 rest IH]; intros bid b H; cbn in H.
  - rewrite RMF.F.empty_o in H; discriminate.
  - destruct (RawIDOrd.eq_dec (blk_id b0) bid) as [Heq | Hneq].
    + rewrite RMF.F.add_eq_o in H by exact Heq; injection H as ->; left; reflexivity.
    + rewrite RMF.F.add_neq_o in H by exact Hneq; right; exact (IH bid b H).
Qed.

Fixpoint chain_draws {Pa : Params} (draws : list (dtyp * @dvalue Pa))
  (tail_s : @draw_strat Pa) : @draw_strat Pa :=
  match draws with
  | [] => tail_s
  | (dt0, v0) :: rest => prepend_draws [(dt0, v0)] (chain_draws rest tail_s)
  end.

Lemma chain_draws_app {Pa : Params} :
  forall (d1 d2 : list (dtyp * @dvalue Pa)) (tail_s : @draw_strat Pa),
    chain_draws (d1 ++ d2) tail_s = chain_draws d1 (chain_draws d2 tail_s).
Proof.
  induction d1 as [| [dt0 v0] rest IH]; intros d2 tail_s; cbn; [reflexivity |].
  rewrite IH; reflexivity.
Qed.

Lemma chain_draws_wf {Pa : Params} :
  forall (draws : list (dtyp * @dvalue Pa)) (tail_s : @draw_strat Pa),
    Forall (fun '(dt, v) => valid_draw_value dt v) draws ->
    wf_draw_strat tail_s ->
    wf_draw_strat (chain_draws draws tail_s).
Proof.
  intros draws tail_s Hfa Htail.
  induction Hfa as [| [dt0 v0] rest Hv0 _ IH]; cbn; [exact Htail |].
  apply prepend_draws_wf; [constructor; [exact Hv0 | constructor] | exact IH].
Qed.


(** *** 5.2 Freeze-Key Tracking & Oracle Agreement on Let-Free Expressions *)

Definition freeze_key : Set := (positive * cert_expr)%type.

Definition freeze_key_eqb (k1 k2 : freeze_key) : bool :=
  Pos.eqb (fst k1) (fst k2) && cert_expr_eqb (snd k1) (snd k2).

Lemma freeze_key_eqb_refl : forall k, freeze_key_eqb k k = true.
Proof.
  intros [w e]; unfold freeze_key_eqb; cbn.
  rewrite Pos.eqb_refl, cert_expr_eqb_refl; reflexivity.
Qed.

Lemma freeze_key_eqb_eq : forall k1 k2,
  freeze_key_eqb k1 k2 = true <-> k1 = k2.
Proof.
  intros [w1 e1] [w2 e2]; unfold freeze_key_eqb; cbn.
  rewrite andb_true_iff, Pos.eqb_eq, cert_expr_eqb_eq.
  split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

Fixpoint freeze_key_in (k : freeze_key) (ks : list freeze_key) : bool :=
  match ks with
  | [] => false
  | x :: rx => freeze_key_eqb k x || freeze_key_in k rx
  end.

Lemma freeze_key_in_spec : forall k ks,
  freeze_key_in k ks = true <-> In k ks.
Proof.
  intros k ks; induction ks as [| x rx IH]; cbn; [split; [discriminate | contradiction] |].
  destruct (freeze_key_eqb k x) eqn:E.
  - apply freeze_key_eqb_eq in E; subst; split; [intros _; left; reflexivity | intros _; reflexivity].
  - rewrite IH; split; [intros H; right; exact H | intros [-> | H];
      [rewrite freeze_key_eqb_refl in E; discriminate | exact H]].
Qed.

Fixpoint collect_freeze_keys (e : cert_expr) : list freeze_key :=
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ | CE_Let _ _ => []
  | CE_BinOp _ _ _ l r | CE_ICmp _ _ _ l r =>
      collect_freeze_keys l ++ collect_freeze_keys r
  | CE_Cast _ _ _ _ o => collect_freeze_keys o
  | CE_Select _ c t f =>
      collect_freeze_keys c ++ collect_freeze_keys t ++ collect_freeze_keys f
  | CE_Freeze w o => (w, o) :: collect_freeze_keys o
  end.

Fixpoint oracle_of_fmap (fmap : list (freeze_key * Z)) : freeze_oracle :=
  fun w e =>
    match fmap with
    | [] => 0%Z
    | (k, z) :: rest =>
        if freeze_key_eqb (w, e) k then z else oracle_of_fmap rest w e
    end.

Lemma oracle_of_fmap_prepend_agree :
  forall added fmap seen,
    (forall k z, In (k, z) added -> ~ In k seen) ->
    forall w e,
      In (w, e) seen ->
      oracle_of_fmap (added ++ fmap) w e = oracle_of_fmap fmap w e.
Proof.
  induction added as [| [k0 z0] rest IH]; intros fmap seen Hdisj w e Hin; cbn; [reflexivity |].
  destruct (freeze_key_eqb (w, e) k0) eqn:Eqk.
  - apply freeze_key_eqb_eq in Eqk; subst k0.
    exfalso; exact (Hdisj (w, e) z0 (or_introl eq_refl) Hin).
  - apply (IH fmap seen); [intros k z H; exact (Hdisj k z (or_intror H)) | exact Hin].
Qed.

Lemma expand_lets_let_free : forall e,
  is_let_free_expr e = true ->
  expand_lets_with [] e = e.
Proof.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hlf; cbn in Hlf |- *; try reflexivity; try discriminate.
  - apply andb_true_iff in Hlf as [Hl Hr]; rewrite (IHl Hl), (IHr Hr); reflexivity.
  - apply andb_true_iff in Hlf as [Hl Hr]; rewrite (IHl Hl), (IHr Hr); reflexivity.
  - rewrite (IHo Hlf); reflexivity.
  - rewrite !andb_true_iff in Hlf; destruct Hlf as ([Hc Ht] & Hf).
    rewrite (IHc Hc), (IHt Ht), (IHf Hf); reflexivity.
  - rewrite (IHo Hlf); reflexivity.
Qed.

Lemma eval_let_free_oracle_agree {Pa : Params} :
  forall (e : cert_expr) (penv : param_env Pa) (fo1 fo2 : freeze_oracle),
    is_let_free_expr e = true ->
    (forall w o, In (w, o) (collect_freeze_keys e) -> fo1 w o = fo2 w o) ->
    eval_cert_expr penv [] fo1 e = eval_cert_expr penv [] fo2 e.
Proof.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros penv fo1 fo2 Hlf Hag; cbn in Hlf |- *; try reflexivity; try discriminate.
  - apply andb_true_iff in Hlf as [Hl Hr].
    rewrite (IHl penv fo1 fo2 Hl (fun kw ko H => Hag kw ko (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHr penv fo1 fo2 Hr (fun kw ko H => Hag kw ko (proj2 (in_app_iff _ _ _) (or_intror H)))).
    reflexivity.
  - apply andb_true_iff in Hlf as [Hl Hr].
    rewrite (IHl penv fo1 fo2 Hl (fun kw ko H => Hag kw ko (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHr penv fo1 fo2 Hr (fun kw ko H => Hag kw ko (proj2 (in_app_iff _ _ _) (or_intror H)))).
    reflexivity.
  - rewrite (IHo penv fo1 fo2 Hlf Hag); reflexivity.
  - rewrite !andb_true_iff in Hlf; destruct Hlf as ([Hc Ht] & Hf).
    rewrite (IHc penv fo1 fo2 Hc (fun kw ko H => Hag kw ko (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHt penv fo1 fo2 Ht (fun kw ko H => Hag kw ko (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl H)))))).
    rewrite (IHf penv fo1 fo2 Hf (fun kw ko H => Hag kw ko (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_intror H)))))).
    reflexivity.
  - rewrite (IHo penv fo1 fo2 Hlf (fun kw ko H => Hag kw ko (or_intror H))).
    cbn [let_val_exprs List.map]; rewrite (expand_lets_let_free o Hlf).
    rewrite (Hag w o (or_introl eq_refl)); reflexivity.
Qed.

(** *** 5.3 Parameter Environments & Initial Frame Locals *)

Fixpoint build_param_env {Pa : Params}
  (pnames : list string) (vs : list (@dvalue Pa)) : param_env Pa :=
  fun nm =>
    match pnames, vs with
    | p :: pr, v :: vr =>
        if String.eqb p nm then Some v else build_param_env pr vr nm
    | _, _ => None
    end.

Lemma build_param_env_nth {Pa : Params} :
  forall (pnames : list string) (vs : list (@dvalue Pa)) (idx : nat) (nm : string),
    NoDup pnames ->
    List.length pnames = List.length vs ->
    nth_error pnames idx = Some nm ->
    exists dv,
      nth_error vs idx = Some dv /\
      build_param_env pnames vs nm = Some dv.
Proof.
  induction pnames as [| p pr IH]; intros [| v vr] idx nm Hnd Hlen Hnth;
    try discriminate Hlen; [destruct idx; discriminate Hnth |].
  inversion Hnd as [| ? ? Hni Hndr]; subst.
  destruct idx as [| idx']; cbn in Hnth |- *.
  - inversion Hnth; subst p; rewrite String.eqb_refl; exists v; auto.
  - injection Hlen as Hlen'.
    destruct (IH vr idx' nm Hndr Hlen' Hnth) as [dv [Hv Hb]].
    destruct (String.eqb p nm) eqn:Ep.
    + apply String.eqb_eq in Ep; subst p.
      exfalso; apply Hni; eapply nth_error_In; exact Hnth.
    + exists dv; split; [exact Hv | exact Hb].
Qed.

Lemma init_cfg_locals_nth {Pa : Params} :
  forall (params : list raw_id) (vs : list (@dvalue Pa)) (idx : nat) (r : raw_id),
    NoDup params ->
    List.length params = List.length vs ->
    nth_error params idx = Some r ->
    exists dv,
      nth_error vs idx = Some dv /\
      RM.find r (init_cfg_locals params vs) = Some dv.
Proof.
  induction params as [| p pr IH]; intros [| v vr] idx r Hnd Hlen Hnth;
    try discriminate Hlen; [destruct idx; discriminate Hnth |].
  inversion Hnd as [| ? ? Hni Hndr]; subst.
  destruct idx as [| idx']; cbn in Hnth |- *.
  - inversion Hnth; subst p.
    exists v; split; [reflexivity | apply RMF.F.add_eq_o; reflexivity].
  - injection Hlen as Hlen'.
    destruct (IH vr idx' r Hndr Hlen' Hnth) as [dv [Hv Hf]].
    assert (Hneq : p <> r)
      by (intros ->; apply Hni; eapply nth_error_In; exact Hnth).
    exists dv; split; [exact Hv | rewrite RMF.F.add_neq_o by exact Hneq; exact Hf].
Qed.

Lemma Forall2_nth_error_l {A B : Type} (R : A -> B -> Prop) :
  forall (xs : list A) (ys : list B),
    Forall2 R xs ys ->
    forall idx x y,
      nth_error xs idx = Some x ->
      nth_error ys idx = Some y ->
      R x y.
Proof.
  intros xs ys Hfa; induction Hfa as [| x0 y0 rx ry Hr _ IH];
    intros [| idx'] x y Hx Hy; cbn in Hx, Hy; try discriminate.
  - inversion Hx; inversion Hy; subst; exact Hr.
  - exact (IH idx' x y Hx Hy).
Qed.

Definition var_pair_eqb (u1 u2 : string * positive) : bool :=
  String.eqb (fst u1) (fst u2) && Pos.eqb (snd u1) (snd u2).

Lemma var_pair_eqb_eq : forall u1 u2,
  var_pair_eqb u1 u2 = true <-> u1 = u2.
Proof.
  intros [s1 w1] [s2 w2]; unfold var_pair_eqb; cbn.
  rewrite andb_true_iff, String.eqb_eq, Pos.eqb_eq.
  split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

Fixpoint var_pair_in (u : string * positive) (us : list (string * positive)) : bool :=
  match us with
  | [] => false
  | x :: rx => var_pair_eqb u x || var_pair_in u rx
  end.

Lemma var_pair_in_spec : forall u us,
  var_pair_in u us = true <-> In u us.
Proof.
  intros u us; induction us as [| x rx IH]; cbn; [split; [discriminate | contradiction] |].
  destruct (var_pair_eqb u x) eqn:E.
  - apply var_pair_eqb_eq in E; subst; split; [intros _; left; reflexivity | intros _; reflexivity].
  - rewrite IH; split; [intros H; right; exact H | intros [-> | H]; [
      assert (Hr : var_pair_eqb x x = true) by (apply var_pair_eqb_eq; reflexivity);
      rewrite Hr in E; discriminate | exact H]].
Qed.

Definition vars_subset_b (vs allowed : list (string * positive)) : bool :=
  forallb (fun u => var_pair_in u allowed) vs.

Lemma vars_subset_b_wf_param {Pa : Params} :
  forall vs allowed (penv : param_env Pa),
    vars_subset_b vs allowed = true ->
    wf_param_env_for allowed penv ->
    wf_param_env_for vs penv.
Proof.
  intros vs allowed penv Hsub Hwf nm w Hin.
  unfold vars_subset_b in Hsub; rewrite forallb_forall in Hsub.
  pose proof (Hsub (nm, w) Hin) as Hin'.
  apply var_pair_in_spec in Hin'; exact (Hwf nm w Hin').
Qed.

Definition used_src_param_vars (src_cfg : CFG.cfg dtyp) : list (string * positive) :=
  let pnames := List.map cert_reg_name (args src_cfg) in
  List.flat_map (fun '(idx, dt) =>
    match dt, nth_error pnames idx with
    | DTYPE_Base (DTYPE_I w), Some nm => [(nm, w)]
    | _, _ => []
    end) (param_idx_uses_cfg src_cfg).

Lemma used_src_param_vars_wf {Pa : Params} :
  forall (src_cfg : CFG.cfg dtyp) (arg_dtys : list dtyp) (vs : list (@dvalue Pa)),
    NoDup (List.map cert_reg_name (args src_cfg)) ->
    List.length arg_dtys = List.length (args src_cfg) ->
    cfg_param_dtyp_compatible src_cfg arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    wf_param_env_for (used_src_param_vars src_cfg)
      (build_param_env (List.map cert_reg_name (args src_cfg)) vs).
Proof.
  intros src_cfg arg_dtys vs Hnd Hlen_dt Hcomp Hvs nm w Hin.
  unfold used_src_param_vars in Hin.
  apply in_flat_map in Hin as [[idx dt] [Hin_use Hin_here]].
  destruct dt as [tb | |]; try contradiction.
  destruct tb as [w' | | | | | | | | | | ]; try contradiction.
  destruct (nth_error (List.map cert_reg_name (args src_cfg)) idx) as [nm' |] eqn:Hnth_nm;
    [| contradiction].
  destruct Hin_here as [Heq | []]; inversion Heq; subst w' nm'.
  unfold cfg_param_dtyp_compatible in Hcomp; rewrite forallb_forall in Hcomp.
  pose proof (Hcomp (idx, DTYPE_Base (DTYPE_I w)) Hin_use) as Hdt_idx.
  destruct (nth_error arg_dtys idx) as [dt_arg |] eqn:Hnth_dt; [| discriminate Hdt_idx].
  apply dtyp_eqb_dec_eq in Hdt_idx; subst dt_arg.
  assert (Hlen_vs : List.length vs = List.length arg_dtys) by (exact (Forall2_length Hvs)).
  assert (Hlen_pn : List.length (List.map cert_reg_name (args src_cfg)) = List.length vs)
    by (rewrite List.length_map; lia).
  destruct (build_param_env_nth (List.map cert_reg_name (args src_cfg)) vs idx nm Hnd Hlen_pn Hnth_nm)
    as [dv [Hnth_v Hpenv]].
  pose proof (Forall2_nth_error_l dvalue_has_dtyp vs arg_dtys Hvs idx dv (DTYPE_Base (DTYPE_I w)) Hnth_v Hnth_dt)
    as Hty.
  apply dvalue_has_dtyp_i_iff_wf_scalar in Hty.
  exists dv; split; [exact Hpenv | exact Hty].
Qed.

(** *** 5.4 Bounded-DAG SSA Expression Reifier & Operational Soundness *)

Lemma scalar_exp_ind (P : exp dtyp -> Prop)
  (HBin : forall iop dt e1 e2, P e1 -> P e2 -> P (OP_IBinop iop dt e1 e2))
  (HCmp : forall ss cmp dt e1 e2, P e1 -> P e2 -> P (OP_ICmp ss cmp dt e1 e2))
  (HConv : forall ct dtf e1 dtt, P e1 -> P (OP_Conversion ct dtf e1 dtt))
  (HSel : forall fm dtc ec dt1 e1 dt2 e2,
            P ec -> P e1 -> P e2 -> P (OP_Select fm (dtc, ec) (dt1, e1) (dt2, e2)))
  (HFrz : forall dt e1, P e1 -> P (OP_Freeze (dt, e1)))
  (HOther : forall o,
    match o with
    | OP_IBinop _ _ _ _ | OP_ICmp _ _ _ _ _ | OP_Conversion _ _ _ _
    | OP_Select _ _ _ _ | OP_Freeze _ => True
    | _ => P o
    end) :
  forall o : exp dtyp, P o.
Proof.
  fix IH 1; intros o; pose proof (HOther o) as Ho.
  destruct o; try exact Ho.
  - apply HBin; apply IH.
  - apply HCmp; apply IH.
  - apply HConv; apply IH.
  - match goal with |- P (OP_Select _ ?c ?x ?y) => destruct c, x, y end;
      apply HSel; apply IH.
  - match goal with |- P (OP_Freeze ?x) => destruct x end;
      apply HFrz; apply IH.
Qed.

Definition reify_int_const (w : positive) (z : Z) : N :=
  Z.to_N (Z.land z (Z.ones (Z.pos w))).

Lemma repr_reify_int_const : forall (w : positive) (z : Z),
  @Integers.repr w (Z.of_N (reify_int_const w z)) = @Integers.repr w z.
Proof.
  intros w z; unfold reify_int_const.
  assert (Hones : (0 <= Z.ones (Z.pos w))%Z).
  { rewrite Z.ones_equiv;
      assert (Hp : (0 < 2 ^ Z.pos w)%Z) by (apply Z.pow_pos_nonneg; lia); lia. }
  assert (Hnn : (0 <= Z.land z (Z.ones (Z.pos w)))%Z)
    by (apply Z.land_nonneg; right; exact Hones).
  rewrite (Z2N.id _ Hnn).
  apply @Integers.same_bits_eq; intros i Hi.
  rewrite !@Integers.testbit_repr by exact Hi.
  unfold Integers.zwordsize in Hi.
  rewrite Z.land_spec, (Z.ones_spec_low (Z.pos w) i Hi), Bool.andb_true_r.
  reflexivity.
Qed.

Definition check_opt_int_width (top : option dtyp) (w : positive) : bool :=
  match top with
  | None => true
  | Some (DTYPE_Base (DTYPE_I w')) => Pos.eqb w w'
  | Some _ => false
  end.

Lemma check_opt_int_width_some_inv : forall w' w,
  check_opt_int_width (Some (DTYPE_Base (DTYPE_I w'))) w = true -> w = w'.
Proof.
  intros w' w H; cbn in H; apply Pos.eqb_eq in H; exact H.
Qed.

Fixpoint reify_exp
  (unique_freezes : bool)
  (params : list raw_id)
  (src_pnames : list string)
  (defs : list raw_id)
  (smap : rmap (positive * cert_expr))
  (seen : list freeze_key)
  (top : option dtyp)
  (o : exp dtyp)
  {struct o} : option (positive * cert_expr * list freeze_key) :=
  match o with
  | EXP_Ident (ID_Local r) =>
      match RM.find r smap with
      | Some (w, ce) =>
          if check_opt_int_width top w then Some (w, ce, seen) else None
      | None =>
          if raw_id_in_list r defs then None
          else
            match top, find_raw_id_index r params with
            | Some (DTYPE_Base (DTYPE_I w)), Some idx =>
                match nth_error src_pnames idx with
                | Some pnm =>
                    if starts_with_dollar pnm then None
                    else Some (w, CE_Var pnm w, seen)
                | None => None
                end
            | _, _ => None
            end
      end
  | EXP_Integer x =>
      match top with
      | Some (DTYPE_Base (DTYPE_I w)) =>
          Some (w, CE_BvConst w (reify_int_const w (denote_int_syntax x)), seen)
      | _ => None
      end
  | EXP_Bool b =>
      if check_opt_int_width top 1%positive
      then Some (1%positive, CE_BvConst 1%positive (if b then 1%N else 0%N), seen)
      else None
  | EXP_Undef | EXP_Poison =>
      match top with
      | Some (DTYPE_Base (DTYPE_I w)) => Some (w, CE_Poison w, seen)
      | _ => None
      end
  | OP_IBinop iop (DTYPE_Base (DTYPE_I w)) e1 e2 =>
      if check_opt_int_width top w then
        match reify_exp unique_freezes params src_pnames defs smap seen
                (Some (DTYPE_Base (DTYPE_I w))) e1 with
        | Some (_, ce1, seen1) =>
            match reify_exp unique_freezes params src_pnames defs smap seen1
                    (Some (DTYPE_Base (DTYPE_I w))) e2 with
            | Some (_, ce2, seen2) =>
                let '(cop, cfl) := ibinop_to_cert iop in
                Some (w, CE_BinOp cop w cfl ce1 ce2, seen2)
            | None => None
            end
        | None => None
        end
      else None
  | OP_ICmp ss cmp (DTYPE_Base (DTYPE_I w)) e1 e2 =>
      if check_opt_int_width top 1%positive then
        match reify_exp unique_freezes params src_pnames defs smap seen
                (Some (DTYPE_Base (DTYPE_I w))) e1 with
        | Some (_, ce1, seen1) =>
            match reify_exp unique_freezes params src_pnames defs smap seen1
                    (Some (DTYPE_Base (DTYPE_I w))) e2 with
            | Some (_, ce2, seen2) =>
                Some (1%positive, CE_ICmp (icmp_to_cert cmp) ss w ce1 ce2, seen2)
            | None => None
            end
        | None => None
        end
      else None
  | OP_Conversion (CONV_Pure pc) (DTYPE_Base (DTYPE_I fw)) e1 (DTYPE_Base (DTYPE_I tw)) =>
      if check_opt_int_width top tw then
        match pure_conv_to_cert pc with
        | Some (ck, cfl) =>
            let w_ok :=
              match ck with
              | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
              | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg cfl) && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
              | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg cfl)
              end in
            if w_ok then
              match reify_exp unique_freezes params src_pnames defs smap seen
                      (Some (DTYPE_Base (DTYPE_I fw))) e1 with
              | Some (_, ce1, seen1) =>
                  Some (tw, CE_Cast ck fw tw cfl ce1, seen1)
              | None => None
              end
            else None
        | None => None
        end
      else None
  | OP_Select _ (DTYPE_Base (DTYPE_I 1%positive), ec)
                (DTYPE_Base (DTYPE_I w1), e1)
                (DTYPE_Base (DTYPE_I w2), e2) =>
      if Pos.eqb w1 w2 && check_opt_int_width top w1 then
        match reify_exp unique_freezes params src_pnames defs smap seen
                (Some (DTYPE_Base (DTYPE_I 1%positive))) ec with
        | Some (_, cec, seen1) =>
            match reify_exp unique_freezes params src_pnames defs smap seen1
                    (Some (DTYPE_Base (DTYPE_I w1))) e1 with
            | Some (_, ce1, seen2) =>
                match reify_exp unique_freezes params src_pnames defs smap seen2
                        (Some (DTYPE_Base (DTYPE_I w1))) e2 with
                | Some (_, ce2, seen3) =>
                    Some (w1, CE_Select w1 cec ce1 ce2, seen3)
                | None => None
                end
            | None => None
            end
        | None => None
        end
      else None
  | OP_Freeze (DTYPE_Base (DTYPE_I w), e1) =>
      if check_opt_int_width top w then
        match reify_exp unique_freezes params src_pnames defs smap seen
                (Some (DTYPE_Base (DTYPE_I w))) e1 with
        | Some (_, ce1, seen1) =>
            if unique_freezes then
              if freeze_key_in (w, ce1) seen1 then None
              else Some (w, CE_Freeze w ce1, (w, ce1) :: seen1)
            else Some (w, CE_Freeze w ce1, seen1)
        | None => None
        end
      else None
  | _ => None
  end.

Definition wf_smap_entries
  (allowed_vars : list (string * positive))
  (defs : list raw_id)
  (seen : list freeze_key)
  (unique_freezes : bool)
  (smap : rmap (positive * cert_expr)) : Prop :=
  forall r w ce,
    RM.find r smap = Some (w, ce) ->
    In r defs /\
    wt_cert_expr [] ce = true /\
    cert_expr_bit_width ce = w /\
    is_let_free_expr ce = true /\
    incl (collect_free_vars [] ce) allowed_vars /\
    (unique_freezes = true -> incl (collect_freeze_keys ce) seen).

Lemma wf_smap_entries_seen_mono :
  forall allowed defs seen1 seen2 uf smap,
    incl seen1 seen2 ->
    wf_smap_entries allowed defs seen1 uf smap ->
    wf_smap_entries allowed defs seen2 uf smap.
Proof.
  intros allowed defs seen1 seen2 uf smap Hinc Hsmap r w ce Hf.
  destruct (Hsmap r w ce Hf) as (Hr & Hwt & Hbw & Hlf & Hfv & Hfk).
  repeat split; try assumption.
  intros Huf x Hx; exact (Hinc x (Hfk Huf x Hx)).
Qed.

Lemma reify_exp_typing :
  forall (o : exp dtyp) uf params src_pnames defs allowed smap seen0 top w ce seen1,
    wf_smap_entries allowed defs seen0 uf smap ->
    (forall idx w0 pnm,
      In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs top o) ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w0) allowed) ->
    reify_exp uf params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
    check_opt_int_width top w = true /\
    wt_cert_expr [] ce = true /\
    cert_expr_bit_width ce = w /\
    is_let_free_expr ce = true /\
    incl (collect_free_vars [] ce) allowed /\
    incl seen0 seen1 /\
    (uf = true -> incl (collect_freeze_keys ce) seen1).
Proof.
  apply (scalar_exp_ind (fun o =>
    forall uf params src_pnames defs allowed smap seen0 top w ce seen1,
      wf_smap_entries allowed defs seen0 uf smap ->
      (forall idx w0 pnm,
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs top o) ->
        nth_error src_pnames idx = Some pnm ->
        In (pnm, w0) allowed) ->
      reify_exp uf params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
      check_opt_int_width top w = true /\
      wt_cert_expr [] ce = true /\
      cert_expr_bit_width ce = w /\
      is_let_free_expr ce = true /\
      incl (collect_free_vars [] ce) allowed /\
      incl seen0 seen1 /\
      (uf = true -> incl (collect_freeze_keys ce) seen1))).
  - (* OP_IBinop *)
    intros iop dt e1 e2 IH1 IH2 uf params src_pnames defs allowed smap seen0 top w ce seen2 Hsmap Hpu Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen1] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I wb))) e2)
      as [[[w2 ce2] seen2'] |] eqn:Hr2; [| discriminate].
    destruct (ibinop_to_cert iop) as [cop cfl] eqn:Hiop.
    inversion Hr; subst wb ce seen2'; clear Hr.
    destruct (ibinop_to_cert_roundtrip iop cop cfl Hiop) as [_ Hfl].
    destruct (IH1 uf params src_pnames defs allowed smap seen0 (Some (DTYPE_Base (DTYPE_I w))) w1 ce1 seen1
                Hsmap
                (fun idx w0 pnm Hin => Hpu idx w0 pnm (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hr1)
      as (Hcw1 & Hwt1 & Hbw1 & Hlf1 & Hfv1 & Hinc01 & Hfk1).
    apply check_opt_int_width_some_inv in Hcw1; subst w1.
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 uf smap Hinc01 Hsmap) as Hsmap1.
    destruct (IH2 uf params src_pnames defs allowed smap seen1 (Some (DTYPE_Base (DTYPE_I w))) w2 ce2 seen2
                Hsmap1
                (fun idx w0 pnm Hin => Hpu idx w0 pnm (proj2 (in_app_iff _ _ _) (or_intror Hin)))
                Hr2)
      as (Hcw2 & Hwt2 & Hbw2 & Hlf2 & Hfv2 & Hinc12 & Hfk2).
    apply check_opt_int_width_some_inv in Hcw2; subst w2.
    repeat split; try assumption.
    + cbn; rewrite Hfl, Hwt1, Hwt2, Hbw1, Hbw2, !Pos.eqb_refl; reflexivity.
    + cbn; rewrite Hlf1, Hlf2; reflexivity.
    + cbn; apply incl_app; assumption.
    + intros x Hx; exact (Hinc12 x (Hinc01 x Hx)).
    + intros Huf; cbn; apply incl_app;
        [intros x Hx; exact (Hinc12 x (Hfk1 Huf x Hx)) | exact (Hfk2 Huf)].
  - (* OP_ICmp *)
    intros ss cmp dt e1 e2 IH1 IH2 uf params src_pnames defs allowed smap seen0 top w ce seen2 Hsmap Hpu Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen1] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I wb))) e2)
      as [[[w2 ce2] seen2'] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w ce seen2'; clear Hr.
    destruct (IH1 uf params src_pnames defs allowed smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) w1 ce1 seen1
                Hsmap
                (fun idx w0 pnm Hin => Hpu idx w0 pnm (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hr1)
      as (Hcw1 & Hwt1 & Hbw1 & Hlf1 & Hfv1 & Hinc01 & Hfk1).
    apply check_opt_int_width_some_inv in Hcw1; subst w1.
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 uf smap Hinc01 Hsmap) as Hsmap1.
    destruct (IH2 uf params src_pnames defs allowed smap seen1 (Some (DTYPE_Base (DTYPE_I wb))) w2 ce2 seen2
                Hsmap1
                (fun idx w0 pnm Hin => Hpu idx w0 pnm (proj2 (in_app_iff _ _ _) (or_intror Hin)))
                Hr2)
      as (Hcw2 & Hwt2 & Hbw2 & Hlf2 & Hfv2 & Hinc12 & Hfk2).
    apply check_opt_int_width_some_inv in Hcw2; subst w2.
    repeat split; try assumption.
    + cbn; rewrite Hwt1, Hwt2, Hbw1, Hbw2, !Pos.eqb_refl; reflexivity.
    + cbn; rewrite Hlf1, Hlf2; reflexivity.
    + cbn; apply incl_app; assumption.
    + intros x Hx; exact (Hinc12 x (Hinc01 x Hx)).
    + intros Huf; cbn; apply incl_app;
        [intros x Hx; exact (Hinc12 x (Hfk1 Huf x Hx)) | exact (Hfk2 Huf)].
  - (* OP_Conversion *)
    intros ct dtf e1 dtt IH1 uf params src_pnames defs allowed smap seen0 top w ce seen1 Hsmap Hpu Hr.
    cbn [reify_exp] in Hr.
    destruct ct as [pc | |]; try discriminate.
    destruct dtf as [tbf | |]; try discriminate; destruct tbf as [fw | | | | | | | | | |]; try discriminate.
    destruct dtt as [tbt | |]; try discriminate; destruct tbt as [tw | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top tw) eqn:Hcw; [| discriminate].
    destruct (pure_conv_to_cert pc) as [[ck cfl] |] eqn:Hpc; [| discriminate].
    set (w_ok :=
      match ck with
      | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg cfl) && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg cfl)
      end) in *.
    destruct w_ok eqn:Hwok; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I fw))) e1)
      as [[[w1 ce1] seen1'] |] eqn:Hr1; [| discriminate].
    inversion Hr; subst w ce seen1'; clear Hr.
    destruct (IH1 uf params src_pnames defs allowed smap seen0 (Some (DTYPE_Base (DTYPE_I fw))) w1 ce1 seen1
                Hsmap Hpu Hr1)
      as (Hcw1 & Hwt1 & Hbw1 & Hlf1 & Hfv1 & Hinc01 & Hfk1).
    apply check_opt_int_width_some_inv in Hcw1; subst w1.
    repeat split; try assumption.
    + cbn; unfold w_ok in Hwok; rewrite Hwok, Hwt1, Hbw1, Pos.eqb_refl; reflexivity.
  - (* OP_Select *)
    intros fm dtc ec dt1 e1 dt2 e2 IHc IH1 IH2 uf params src_pnames defs allowed smap seen0 top w ce seen3 Hsmap Hpu Hr.
    cbn [reify_exp] in Hr.
    destruct dtc as [tbc | |]; try discriminate; destruct tbc as [wc | | | | | | | | | |]; try discriminate.
    destruct wc as [| |]; try discriminate.
    destruct dt1 as [tb1 | |]; try discriminate; destruct tb1 as [w1 | | | | | | | | | |]; try discriminate.
    destruct dt2 as [tb2 | |]; try discriminate; destruct tb2 as [w2 | | | | | | | | | |]; try discriminate.
    destruct (Pos.eqb w1 w2 && check_opt_int_width top w1) eqn:Hcw; [| discriminate].
    apply andb_true_iff in Hcw as [Hw12 Hcw]; apply Pos.eqb_eq in Hw12; subst w2.
    destruct (reify_exp uf params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I 1%positive))) ec)
      as [[[wc' cec] seen1] |] eqn:Hrc; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I w1))) e1)
      as [[[wa ce1] seen2] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen2 (Some (DTYPE_Base (DTYPE_I w1))) e2)
      as [[[wb ce2] seen3'] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w1 ce seen3'; clear Hr.
    destruct (IHc uf params src_pnames defs allowed smap seen0 (Some (DTYPE_Base (DTYPE_I 1%positive))) wc' cec seen1
                Hsmap
                (fun idx w0 pnm Hin => Hpu idx w0 pnm (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hrc)
      as (Hcwc & Hwtc & Hbwc & Hlfc & Hfvc & Hinc01 & Hfkc).
    apply check_opt_int_width_some_inv in Hcwc; subst wc'.
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 uf smap Hinc01 Hsmap) as Hsmap1.
    destruct (IH1 uf params src_pnames defs allowed smap seen1 (Some (DTYPE_Base (DTYPE_I w))) wa ce1 seen2
                Hsmap1
                (fun idx w0 pnm Hin => Hpu idx w0 pnm (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl Hin)))))
                Hr1)
      as (Hcwa & Hwt1 & Hbw1 & Hlf1 & Hfv1 & Hinc12 & Hfk1).
    apply check_opt_int_width_some_inv in Hcwa; subst wa.
    pose proof (wf_smap_entries_seen_mono allowed defs seen1 seen2 uf smap Hinc12 Hsmap1) as Hsmap2.
    destruct (IH2 uf params src_pnames defs allowed smap seen2 (Some (DTYPE_Base (DTYPE_I w))) wb ce2 seen3
                Hsmap2
                (fun idx w0 pnm Hin => Hpu idx w0 pnm (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_intror Hin)))))
                Hr2)
      as (Hcwb & Hwt2 & Hbw2 & Hlf2 & Hfv2 & Hinc23 & Hfk2).
    apply check_opt_int_width_some_inv in Hcwb; subst wb.
    repeat split; try assumption.
    + cbn; rewrite Hwtc, Hwt1, Hwt2, Hbwc, Hbw1, Hbw2, !Pos.eqb_refl; reflexivity.
    + cbn; rewrite Hlfc, Hlf1, Hlf2; reflexivity.
    + cbn; apply incl_app; [exact Hfvc | apply incl_app; assumption].
    + intros x Hx; exact (Hinc23 x (Hinc12 x (Hinc01 x Hx))).
    + intros Huf; cbn; apply incl_app; [| apply incl_app].
      * intros x Hx; exact (Hinc23 x (Hinc12 x (Hfkc Huf x Hx))).
      * intros x Hx; exact (Hinc23 x (Hfk1 Huf x Hx)).
      * exact (Hfk2 Huf).
  - (* OP_Freeze *)
    intros dt e1 IH1 uf params src_pnames defs allowed smap seen0 top w ce seen1 Hsmap Hpu Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; try discriminate; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_exp uf params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen_mid] |] eqn:Hr1; [| discriminate].
    destruct (IH1 uf params src_pnames defs allowed smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) w1 ce1 seen_mid
                Hsmap Hpu Hr1)
      as (Hcw1 & Hwt1 & Hbw1 & Hlf1 & Hfv1 & Hinc0m & Hfk1).
    apply check_opt_int_width_some_inv in Hcw1; subst w1.
    destruct uf.
    + destruct (freeze_key_in (wb, ce1) seen_mid); [discriminate |].
      inversion Hr; subst wb ce seen1; clear Hr.
      repeat split; try assumption.
      * cbn; rewrite Hwt1, Hbw1, Pos.eqb_refl; reflexivity.
      * intros x Hx; right; exact (Hinc0m x Hx).
      * intros _; cbn; intros x [<- | Hx];
          [left; reflexivity | right; exact (Hfk1 eq_refl x Hx)].
    + inversion Hr; subst wb ce seen1; clear Hr.
      repeat split; try assumption.
      * cbn; rewrite Hwt1, Hbw1, Pos.eqb_refl; reflexivity.
      * intros Huf; discriminate Huf.
  - (* Non-recursive base cases *)
    intros o; destruct o; try exact I;
      intros uf params src_pnames defs allowed smap seen0 top w ce seen1 Hsmap Hpu Hr;
      cbn [reify_exp] in Hr; try discriminate.
    + (* EXP_Ident *)
      destruct id as [| r]; [discriminate |].
      destruct (RM.find r smap) as [[wr cer] |] eqn:Hfind.
      * destruct (check_opt_int_width top wr) eqn:Hcw; [| discriminate].
        inversion Hr; subst wr ce seen1; clear Hr.
        destruct (Hsmap r w cer Hfind) as (_ & Hwt & Hbw & Hlf & Hfv & Hfk).
        repeat split; try assumption; intros x Hx; exact Hx.
      * destruct (raw_id_in_list r defs) eqn:Hrd; [discriminate |].
        destruct top as [dt |]; [| discriminate].
        destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
        destruct (find_raw_id_index r params) as [idx |] eqn:Hidx; [| discriminate].
        destruct (nth_error src_pnames idx) as [pnm |] eqn:Hpnm; [| discriminate].
        destruct (starts_with_dollar pnm) eqn:Hdl; [discriminate |].
        inversion Hr; subst wt ce seen1; clear Hr.
        repeat split; try reflexivity.
        -- cbn; apply Pos.eqb_refl.
        -- cbn; rewrite Hdl; reflexivity.
        -- cbn; intros u [<- | []].
           apply (Hpu idx w pnm); [| exact Hpnm].
           cbn [exp_param_uses]; rewrite Hrd, Hidx; left; reflexivity.
        -- intros x Hx; exact Hx.
        -- intros _ x [].
    + (* EXP_Integer *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      repeat split; try reflexivity.
      * cbn; apply Pos.eqb_refl.
      * intros u [].
      * intros u Hu; exact Hu.
      * intros _ u [].
    + (* EXP_Bool *)
      destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
      inversion Hr; subst w ce seen1; clear Hr.
      repeat split; try assumption; try reflexivity;
        [intros u [] | intros u Hu; exact Hu | intros _ u []].
    + (* EXP_Undef *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      repeat split; try reflexivity;
        [cbn; apply Pos.eqb_refl | intros u [] | intros u Hu; exact Hu | intros _ u []].
    + (* EXP_Poison *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      repeat split; try reflexivity;
        [cbn; apply Pos.eqb_refl | intros u [] | intros u Hu; exact Hu | intros _ u []].
Qed.

Lemma wf_smap_entries_false_seen :
  forall allowed defs seen0 seen1 smap,
    wf_smap_entries allowed defs seen0 false smap ->
    wf_smap_entries allowed defs seen1 false smap.
Proof.
  intros allowed defs seen0 seen1 smap Hsmap r w ce Hf.
  destruct (Hsmap r w ce Hf) as (Hr & Hwt & Hbw & Hlf & Hfv & _).
  repeat split; try assumption; intros Huf; discriminate Huf.
Qed.

Lemma reify_exp_top_width :
  forall uf params src_pnames defs smap seen0 top o w ce seen1,
    reify_exp uf params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
    check_opt_int_width top w = true.
Proof.
  intros uf params src_pnames defs smap seen0 top o w ce seen1 Hr.
  destruct o; cbn [reify_exp] in Hr; try discriminate.
  - destruct id as [| r]; [discriminate |].
    destruct (RM.find r smap) as [[wr cer] |].
    + destruct (check_opt_int_width top wr) eqn:E; [inversion Hr; subst; exact E | discriminate].
    + destruct (raw_id_in_list r defs); [discriminate |].
      destruct top as [[tb | |] |]; try discriminate; destruct tb; try discriminate.
      destruct (find_raw_id_index r params); [| discriminate].
      destruct (nth_error src_pnames n); [| discriminate].
      destruct (starts_with_dollar s); [discriminate |].
      inversion Hr; subst; cbn; apply Pos.eqb_refl.
  - destruct top as [[tb | |] |]; try discriminate; destruct tb; try discriminate.
    inversion Hr; subst; cbn; apply Pos.eqb_refl.
  - destruct (check_opt_int_width top 1%positive) eqn:E; [inversion Hr; subst; exact E | discriminate].
  - destruct top as [[tb | |] |]; try discriminate; destruct tb; try discriminate.
    inversion Hr; subst; cbn; apply Pos.eqb_refl.
  - destruct top as [[tb | |] |]; try discriminate; destruct tb; try discriminate.
    inversion Hr; subst; cbn; apply Pos.eqb_refl.
  - destruct t as [[wb | | | | | | | | | |] | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:E; [| discriminate].
    destruct (reify_exp _ _ _ _ _ _ _ o1) as [[[_ _] _] |]; [| discriminate].
    destruct (reify_exp _ _ _ _ _ _ _ o2) as [[[_ _] _] |]; [| discriminate].
    destruct (ibinop_to_cert iop); inversion Hr; subst; exact E.
  - destruct t as [[wb | | | | | | | | | |] | |]; try discriminate.
    destruct (check_opt_int_width top 1%positive) eqn:E; [| discriminate].
    destruct (reify_exp _ _ _ _ _ _ _ o1) as [[[_ _] _] |]; [| discriminate].
    destruct (reify_exp _ _ _ _ _ _ _ o2) as [[[_ _] _] |]; [| discriminate].
    inversion Hr; subst; exact E.
  - destruct conv as [pc | |]; try discriminate.
    destruct t_from as [[fw | | | | | | | | | |] | |]; try discriminate.
    destruct t_to as [[tw | | | | | | | | | |] | |]; try discriminate.
    destruct (check_opt_int_width top tw) eqn:E; [| discriminate].
    destruct (pure_conv_to_cert pc) as [[ck cfl] |]; [| discriminate].
    destruct (match ck with CCK_ZExt => _ | CCK_SExt => _ | CCK_Trunc => _ end); [| discriminate].
    destruct (reify_exp _ _ _ _ _ _ _ v) as [[[_ _] _] |]; [| discriminate].
    inversion Hr; subst; exact E.
  - destruct cnd as [dtc ec], v1 as [dt1 e1], v2 as [dt2 e2].
    destruct dtc as [[[| | ] | | | | | | | | | |] | |]; try discriminate.
    destruct dt1 as [[w1 | | | | | | | | | |] | |]; try discriminate.
    destruct dt2 as [[w2 | | | | | | | | | |] | |]; try discriminate.
    destruct (Pos.eqb w1 w2 && check_opt_int_width top w1) eqn:E; [| discriminate].
    apply andb_true_iff in E as [_ E].
    destruct (reify_exp _ _ _ _ _ _ _ ec) as [[[_ _] _] |]; [| discriminate].
    destruct (reify_exp _ _ _ _ _ _ _ e1) as [[[_ _] _] |]; [| discriminate].
    destruct (reify_exp _ _ _ _ _ _ _ e2) as [[[_ _] _] |]; [| discriminate].
    inversion Hr; subst; exact E.
  - destruct v as [dt e1].
    destruct dt as [[wb | | | | | | | | | |] | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:E; [| discriminate].
    destruct (reify_exp _ _ _ _ _ _ _ e1) as [[[_ ce1] seen_m] |]; [| discriminate].
    destruct uf;
      [destruct (freeze_key_in (wb, ce1) seen_m); [discriminate | inversion Hr; subst; exact E]
      | inversion Hr; subst; exact E].
Qed.

Lemma reify_exp_freeze_props :
  forall (o : exp dtyp) uf params src_pnames defs allowed smap seen0 top w ce seen1,
    wf_smap_entries allowed defs seen0 uf smap ->
    reify_exp uf params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
    is_let_free_expr ce = true /\
    incl seen0 seen1 /\
    (uf = true -> incl (collect_freeze_keys ce) seen1).
Proof.
  intros o uf params src_pnames defs allowed smap seen0 top w ce seen1 Hsmap Hr.
  set (ext_vars :=
    allowed ++
    List.flat_map (fun '(idx, dt) =>
      match dt, nth_error src_pnames idx with
      | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
      | _, _ => []
      end) (exp_param_uses params defs top o)).
  assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 uf smap).
  { intros r wr cer Hf.
    destruct (Hsmap r wr cer Hf) as (Hr_in & Hwt & Hbw & Hlf & Hfv & Hfk).
    repeat split; try assumption.
    intros u Hu; apply in_app_iff; left; exact (Hfv u Hu). }
  assert (Hpu_ext : forall idx w0 pnm,
    In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs top o) ->
    nth_error src_pnames idx = Some pnm ->
    In (pnm, w0) ext_vars).
  { intros idx w0 pnm Hin Hpnm; apply in_app_iff; right; apply in_flat_map.
    exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin | rewrite Hpnm; left; reflexivity]. }
  destruct (reify_exp_typing o uf params src_pnames defs ext_vars smap seen0 top w ce seen1
              Hsmap_ext Hpu_ext Hr)
    as (_ & _ & _ & Hlf & _ & Hinc & Hfk).
  exact (conj Hlf (conj Hinc Hfk)).
Qed.

Lemma eval_let_free_prepend_fmap {Pa : Params} :
  forall (ce : cert_expr) (penv : param_env Pa) added fmap seen,
    is_let_free_expr ce = true ->
    incl (collect_freeze_keys ce) seen ->
    (forall k z, In (k, z) added -> ~ In k seen) ->
    eval_closed_cert_expr penv (oracle_of_fmap (added ++ fmap)) ce =
    eval_closed_cert_expr penv (oracle_of_fmap fmap) ce.
Proof.
  intros ce penv added fmap seen Hlf Hfk Hdisj.
  unfold eval_closed_cert_expr.
  apply eval_let_free_oracle_agree; [exact Hlf |].
  intros kw ko Hin.
  exact (oracle_of_fmap_prepend_agree added fmap seen Hdisj kw ko (Hfk (kw, ko) Hin)).
Qed.

Definition env_matches_smap {Pa : Params}
  (defs : list raw_id)
  (penv : param_env Pa)
  (foracle : freeze_oracle)
  (smap : rmap (positive * cert_expr))
  (env : rmap (@dvalue Pa)) : Prop :=
  forall r w ce,
    RM.find r smap = Some (w, ce) ->
    In r defs /\
    exists dv,
      RM.find r env = Some dv /\
      eval_closed_cert_expr penv foracle ce = raise_ret dv /\
      wf_scalar_dvalue w dv.

Lemma env_matches_smap_oracle_prepend {Pa : Params} :
  forall allowed defs seen added fmap (penv : param_env Pa) smap env,
    wf_smap_entries allowed defs seen true smap ->
    (forall k z, In (k, z) added -> ~ In k seen) ->
    env_matches_smap defs penv (oracle_of_fmap fmap) smap env ->
    env_matches_smap defs penv (oracle_of_fmap (added ++ fmap)) smap env.
Proof.
  intros allowed defs seen added fmap penv smap env Hwfs Hdisj Henv r w ce Hf.
  destruct (Henv r w ce Hf) as [Hr [dv [Hfe [Hev Hsc]]]].
  destruct (Hwfs r w ce Hf) as (_ & _ & _ & Hlf & _ & Hfk).
  split; [exact Hr | exists dv; repeat split; try assumption].
  exact (eq_trans
           (eval_let_free_prepend_fmap ce penv added fmap seen Hlf (Hfk eq_refl) Hdisj)
           Hev).
Qed.

Lemma mcfg_steps_eou_ret {Pa : Params} {R : Type} :
  forall (sigma : @draw_strat Pa) (env : rmap (@dvalue Pa)) (r : R),
    mcfg_steps_to_ret sigma env (EOU_to_itree (E := MCFGEtop) (raise_ret r)) sigma env r.
Proof.
  intros sigma env r; apply MSR_Ret; reflexivity.
Qed.

Lemma mcfg_steps_eou_ub {Pa : Params} {R : Type} :
  forall (sigma : @draw_strat Pa) (env : rmap (@dvalue Pa)) (msg : string),
    mcfg_steps_to_ub sigma env (EOU_to_itree (E := MCFGEtop) (@raise_ub R msg)).
Proof.
  intros sigma env msg; eapply MSU_UB; reflexivity.
Qed.

Lemma cfg_steps_lwrite {Pa : Params} :
  forall (sigma : @draw_strat Pa) (env : rmap (@dvalue Pa)) (id : raw_id) (dv : @dvalue Pa),
    cfg_steps_to_ret sigma env (lwrite (E := CFGEtop) id dv) sigma (RM.add id dv env) tt.
Proof.
  intros sigma env id dv; eapply CSR_LocalWrite; [reflexivity | apply CSR_Ret; reflexivity].
Qed.

Lemma eval_reified_exp_src {Pa : Params} :
  forall (o : exp dtyp) params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
         (foracle : freeze_oracle) smap (env : rmap (@dvalue Pa)) seen0 top w ce seen1,
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length params ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx dt, In (idx, dt) (exp_param_uses params defs top o) -> nth_error arg_dtys idx = Some dt) ->
    (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env = Some dv) ->
    wf_smap_entries allowed defs seen0 false smap ->
    env_matches_smap defs (build_param_env src_pnames vs) foracle smap env ->
    reify_exp false params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
    exists draws : list (dtyp * @dvalue Pa),
      Forall (fun '(dt, v) => valid_draw_value dt v) draws /\
      (((forall tail_s, mcfg_steps_to_ub (chain_draws draws tail_s) env (denote_exp top o)) /\
        (exists msg, eval_closed_cert_expr (build_param_env src_pnames vs) foracle ce = raise_ub msg)) \/
       (exists dv,
          eval_closed_cert_expr (build_param_env src_pnames vs) foracle ce = raise_ret dv /\
          wf_scalar_dvalue w dv /\
          (forall tail_s, mcfg_steps_to_ret (chain_draws draws tail_s) env (denote_exp top o) tail_s env dv))).
Proof.
  apply (scalar_exp_ind (fun o =>
    forall params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
           (foracle : freeze_oracle) smap (env : rmap (@dvalue Pa)) seen0 top w ce seen1,
      NoDup src_pnames ->
      List.length params = List.length vs ->
      List.length src_pnames = List.length vs ->
      List.length arg_dtys = List.length params ->
      Forall2 dvalue_has_dtyp vs arg_dtys ->
      (forall idx dt, In (idx, dt) (exp_param_uses params defs top o) -> nth_error arg_dtys idx = Some dt) ->
      (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
        exists dv, nth_error vs idx = Some dv /\ RM.find r env = Some dv) ->
      wf_smap_entries allowed defs seen0 false smap ->
      env_matches_smap defs (build_param_env src_pnames vs) foracle smap env ->
      reify_exp false params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
      exists draws : list (dtyp * @dvalue Pa),
        Forall (fun '(dt, v) => valid_draw_value dt v) draws /\
        (((forall tail_s, mcfg_steps_to_ub (chain_draws draws tail_s) env (denote_exp top o)) /\
          (exists msg, eval_closed_cert_expr (build_param_env src_pnames vs) foracle ce = raise_ub msg)) \/
         (exists dv,
            eval_closed_cert_expr (build_param_env src_pnames vs) foracle ce = raise_ret dv /\
            wf_scalar_dvalue w dv /\
            (forall tail_s, mcfg_steps_to_ret (chain_draws draws tail_s) env (denote_exp top o) tail_s env dv))))).
  - (* OP_IBinop *)
    intros iop dt e1 e2 IH1 IH2 params src_pnames defs allowed arg_dtys vs foracle smap env seen0 top w ce seen2
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen1] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I wb))) e2)
      as [[[w2 ce2] seen2'] |] eqn:Hr2; [| discriminate].
    destruct (ibinop_to_cert iop) as [cop cfl] eqn:Hiop.
    inversion Hr; subst wb ce seen2'; clear Hr.
    destruct (ibinop_to_cert_roundtrip iop cop cfl Hiop) as [Heq_iop _].
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr2)) as ->.
    destruct (IH1 params src_pnames defs allowed arg_dtys vs foracle smap env seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hpe Hwfs Henv Hr1)
      as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
    + exists draws1; split; [exact Hfa1 | left; split].
      * intros tail_s; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hub1 tail_s).
      * exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + pose proof (wf_smap_entries_false_seen allowed defs seen0 seen1 smap Hwfs) as Hwfs1.
      destruct (IH2 params src_pnames defs allowed arg_dtys vs foracle smap env seen1
                  (Some (DTYPE_Base (DTYPE_I w))) w ce2 seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror Hin)))
                  Hpe Hwfs1 Henv Hr2)
        as (draws2 & Hfa2 & [[Hub2 [msg2 Hev2]] | [dv2 [Hev2 [Hsc2 Hst2]]]]).
      * exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | left; split].
        -- intros tail_s; rewrite chain_draws_app; cbn [denote_exp].
           eapply mcfg_steps_to_ub_bind_r;
             [exact (Hst1 (chain_draws draws2 tail_s))
             | apply mcfg_steps_to_ub_bind_l; exact (Hub2 tail_s)].
        -- exists msg2; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hev1, Hev2; reflexivity.
      * destruct (eval_iop_wf_scalar cop cfl w dv1 dv2 Hsc1 Hsc2)
          as [[msg_op Hev_op] | [vout [Hev_op Hsc_out]]].
        -- exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | left; split].
           ++ intros tail_s; rewrite chain_draws_app; cbn [denote_exp].
              eapply mcfg_steps_to_ub_bind_r; [exact (Hst1 (chain_draws draws2 tail_s)) |].
              eapply mcfg_steps_to_ub_bind_r; [exact (Hst2 tail_s) |].
              rewrite <- Heq_iop, Hev_op; apply mcfg_steps_eou_ub.
           ++ exists msg_op; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hev1, Hev2; cbn [eou_bind]; exact Hev_op.
        -- exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | right].
           exists vout; split; [| split; [exact Hsc_out |]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hev1, Hev2; cbn [eou_bind]; exact Hev_op.
           ++ intros tail_s; rewrite chain_draws_app; cbn [denote_exp].
              eapply mcfg_steps_to_ret_bind; [exact (Hst1 (chain_draws draws2 tail_s)) |].
              eapply mcfg_steps_to_ret_bind; [exact (Hst2 tail_s) |].
              rewrite <- Heq_iop, Hev_op; apply mcfg_steps_eou_ret.
  - (* OP_ICmp *)
    intros ss cmp dt e1 e2 IH1 IH2 params src_pnames defs allowed arg_dtys vs foracle smap env seen0 top w ce seen2
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen1] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I wb))) e2)
      as [[[w2 ce2] seen2'] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w ce seen2'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr2)) as ->.
    destruct (IH1 params src_pnames defs allowed arg_dtys vs foracle smap env seen0
                (Some (DTYPE_Base (DTYPE_I wb))) wb ce1 seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hpe Hwfs Henv Hr1)
      as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
    + exists draws1; split; [exact Hfa1 | left; split].
      * intros tail_s; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hub1 tail_s).
      * exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + pose proof (wf_smap_entries_false_seen allowed defs seen0 seen1 smap Hwfs) as Hwfs1.
      destruct (IH2 params src_pnames defs allowed arg_dtys vs foracle smap env seen1
                  (Some (DTYPE_Base (DTYPE_I wb))) wb ce2 seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror Hin)))
                  Hpe Hwfs1 Henv Hr2)
        as (draws2 & Hfa2 & [[Hub2 [msg2 Hev2]] | [dv2 [Hev2 [Hsc2 Hst2]]]]).
      * exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | left; split].
        -- intros tail_s; rewrite chain_draws_app; cbn [denote_exp].
           eapply mcfg_steps_to_ub_bind_r;
             [exact (Hst1 (chain_draws draws2 tail_s))
             | apply mcfg_steps_to_ub_bind_l; exact (Hub2 tail_s)].
        -- exists msg2; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hev1, Hev2; reflexivity.
      * destruct (eval_icmp_wf_scalar ss (icmp_to_cert cmp) wb dv1 dv2 Hsc1 Hsc2)
          as [vout [Hev_cmp Hsc_out]].
        exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | right].
        exists vout; split; [| split; [exact Hsc_out |]].
        -- unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hev1, Hev2; cbn [eou_bind]; exact Hev_cmp.
        -- intros tail_s; rewrite chain_draws_app; cbn [denote_exp].
           eapply mcfg_steps_to_ret_bind; [exact (Hst1 (chain_draws draws2 tail_s)) |].
           eapply mcfg_steps_to_ret_bind; [exact (Hst2 tail_s) |].
           rewrite <- (icmp_to_cert_roundtrip cmp), Hev_cmp; apply mcfg_steps_eou_ret.
  - (* OP_Conversion *)
    intros ct dtf e1 dtt IH1 params src_pnames defs allowed arg_dtys vs foracle smap env seen0 top w ce seen1
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr.
    cbn [reify_exp] in Hr.
    destruct ct as [pc | |]; try discriminate.
    destruct dtf as [tbf | |]; try discriminate; destruct tbf as [fw | | | | | | | | | |]; try discriminate.
    destruct dtt as [tbt | |]; try discriminate; destruct tbt as [tw | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top tw) eqn:Hcw; [| discriminate].
    destruct (pure_conv_to_cert pc) as [[ck cfl] |] eqn:Hpc; [| discriminate].
    set (w_ok :=
      match ck with
      | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg cfl) && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg cfl)
      end) in *.
    destruct w_ok eqn:Hwok; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I fw))) e1)
      as [[[w1 ce1] seen1'] |] eqn:Hr1; [| discriminate].
    inversion Hr; subst w ce seen1'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (pure_conv_to_cert_roundtrip pc ck cfl Hpc) as Heq_pc.
    destruct (IH1 params src_pnames defs allowed arg_dtys vs foracle smap env seen0
                (Some (DTYPE_Base (DTYPE_I fw))) fw ce1 seen1
                Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr1)
      as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
    + exists draws1; split; [exact Hfa1 | left; split].
      * intros tail_s; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hub1 tail_s).
      * exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + unfold w_ok in Hwok.
      destruct (eval_cast_wf_scalar ck fw tw cfl dv1 Hwok Hsc1) as [vout [Hev_cast Hsc_out]].
      exists draws1; split; [exact Hfa1 | right].
      exists vout; split; [| split; [exact Hsc_out |]].
      * unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; cbn [eou_bind]; exact Hev_cast.
      * intros tail_s; cbn [denote_exp convert].
        eapply mcfg_steps_to_ret_bind; [exact (Hst1 tail_s) |].
        rewrite <- Heq_pc, Hev_cast; apply mcfg_steps_eou_ret.
  - (* OP_Select *)
    intros fm dtc ec dt1 e1 dt2 e2 IHc IH1 IH2 params src_pnames defs allowed arg_dtys vs foracle smap env seen0 top w ce seen3
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr.
    cbn [reify_exp] in Hr.
    destruct dtc as [tbc | |]; try discriminate; destruct tbc as [wc | | | | | | | | | |]; try discriminate.
    destruct wc as [| |]; try discriminate.
    destruct dt1 as [tb1 | |]; try discriminate; destruct tb1 as [w1 | | | | | | | | | |]; try discriminate.
    destruct dt2 as [tb2 | |]; try discriminate; destruct tb2 as [w2 | | | | | | | | | |]; try discriminate.
    destruct (Pos.eqb w1 w2 && check_opt_int_width top w1) eqn:Hcw; [| discriminate].
    apply andb_true_iff in Hcw as [Hw12 Hcw]; apply Pos.eqb_eq in Hw12; subst w2.
    destruct (reify_exp false params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I 1%positive))) ec)
      as [[[wc' cec] seen1] |] eqn:Hrc; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I w1))) e1)
      as [[[wa ce1] seen2] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen2 (Some (DTYPE_Base (DTYPE_I w1))) e2)
      as [[[wb ce2] seen3'] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w1 ce seen3'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hrc)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr2)) as ->.
    destruct (IHc params src_pnames defs allowed arg_dtys vs foracle smap env seen0
                (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive cec seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hpe Hwfs Henv Hrc)
      as (drawsc & Hfac & [[Hubc [msgc Hevc]] | [dvc [Hevc [Hscc Hstc]]]]).
    + exists drawsc; split; [exact Hfac | left; split].
      * intros tail_s; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hubc tail_s).
      * exists msgc; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hevc; reflexivity.
    + pose proof (wf_smap_entries_false_seen allowed defs seen0 seen1 smap Hwfs) as Hwfs1.
      destruct (IH1 params src_pnames defs allowed arg_dtys vs foracle smap env seen1
                  (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl Hin)))))
                  Hpe Hwfs1 Henv Hr1)
        as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
      * exists (drawsc ++ draws1); split; [apply Forall_app; split; assumption | left; split].
        -- intros tail_s; rewrite chain_draws_app; cbn [denote_exp].
           eapply mcfg_steps_to_ub_bind_r;
             [exact (Hstc (chain_draws draws1 tail_s))
             | apply mcfg_steps_to_ub_bind_l; exact (Hub1 tail_s)].
        -- exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hevc, Hev1; reflexivity.
      * pose proof (wf_smap_entries_false_seen allowed defs seen0 seen2 smap Hwfs) as Hwfs2.
        destruct (IH2 params src_pnames defs allowed arg_dtys vs foracle smap env seen2
                    (Some (DTYPE_Base (DTYPE_I w))) w ce2 seen3
                    Hnd Hlp Hls Hla Hvs
                    (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_intror Hin)))))
                    Hpe Hwfs2 Henv Hr2)
          as (draws2 & Hfa2 & [[Hub2 [msg2 Hev2]] | [dv2 [Hev2 [Hsc2 Hst2]]]]).
        -- exists (drawsc ++ draws1 ++ draws2); split;
             [apply Forall_app; split; [exact Hfac | apply Forall_app; split; assumption] | left; split].
           ++ intros tail_s; rewrite !chain_draws_app; cbn [denote_exp].
              eapply mcfg_steps_to_ub_bind_r; [exact (Hstc (chain_draws draws1 (chain_draws draws2 tail_s))) |].
              eapply mcfg_steps_to_ub_bind_r; [exact (Hst1 (chain_draws draws2 tail_s)) |].
              apply mcfg_steps_to_ub_bind_l; exact (Hub2 tail_s).
           ++ exists msg2; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hevc, Hev1, Hev2; reflexivity.
        -- destruct (eval_select_wf_scalar w dvc dv1 dv2 Hscc Hsc1 Hsc2)
             as [vout [Hev_sel Hsc_out]].
           exists (drawsc ++ draws1 ++ draws2); split;
             [apply Forall_app; split; [exact Hfac | apply Forall_app; split; assumption] | right].
           exists vout; split; [| split; [exact Hsc_out |]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hevc, Hev1, Hev2; cbn [eou_bind]; exact Hev_sel.
           ++ intros tail_s; rewrite !chain_draws_app; cbn [denote_exp].
              eapply mcfg_steps_to_ret_bind; [exact (Hstc (chain_draws draws1 (chain_draws draws2 tail_s))) |].
              eapply mcfg_steps_to_ret_bind; [exact (Hst1 (chain_draws draws2 tail_s)) |].
              eapply mcfg_steps_to_ret_bind; [exact (Hst2 tail_s) |].
              rewrite Hev_sel; apply mcfg_steps_eou_ret.
  - (* OP_Freeze *)
    intros dt e1 IH1 params src_pnames defs allowed arg_dtys vs foracle smap env seen0 top w ce seen1
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; try discriminate; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_exp false params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen_mid] |] eqn:Hr1; [| discriminate].
    inversion Hr; subst wb ce seen1; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    destruct (reify_exp_freeze_props e1 false params src_pnames defs allowed smap seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen_mid Hwfs Hr1)
      as (Hlf1 & _ & _).
    destruct (IH1 params src_pnames defs allowed arg_dtys vs foracle smap env seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen_mid
                Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr1)
      as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
    + exists draws1; split; [exact Hfa1 | left; split].
      * intros tail_s; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hub1 tail_s).
      * exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + destruct Hsc1 as [-> | [iv ->]].
      * set (fv := DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (foracle w ce1)))).
        exists (draws1 ++ [(DTYPE_Base (DTYPE_I w), fv)]).
        split.
        -- apply Forall_app; split; [exact Hfa1 |].
           constructor; [apply valid_draw_i_iff; eexists; reflexivity | constructor].
        -- right; exists fv; split; [| split; [right; eexists; reflexivity |]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr let_val_exprs List.map].
              rewrite Hev1, (expand_lets_let_free ce1 Hlf1); reflexivity.
           ++ intros tail_s; rewrite chain_draws_app; cbn [chain_draws denote_exp].
              eapply mcfg_steps_to_ret_bind;
                [exact (Hst1 (prepend_draws [(DTYPE_Base (DTYPE_I w), fv)] tail_s)) |].
              eapply MSR_Draw; [reflexivity | intros n d; reflexivity |].
              cbn [prepend_draws].
              destruct (dtyp_eq_dec (DTYPE_Base (DTYPE_I w)) (DTYPE_Base (DTYPE_I w))) as [_ | Hneq];
                [apply MSR_Ret; reflexivity | exfalso; exact (Hneq eq_refl)].
      * exists draws1; split; [exact Hfa1 | right].
        exists (DVALUE_Base (@DVALUE_I Pa w iv)).
        split; [| split; [right; exists iv; reflexivity |]].
        -- unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
        -- intros tail_s; cbn [denote_exp].
           eapply mcfg_steps_to_ret_bind; [exact (Hst1 tail_s) | apply MSR_Ret; reflexivity].
  - (* Non-recursive base cases *)
    intros o; destruct o; try exact I;
      intros params src_pnames defs allowed arg_dtys vs foracle smap env seen0 top w ce seen1
             Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr;
      cbn [reify_exp] in Hr; try discriminate.
    + (* EXP_Ident *)
      destruct id as [| r]; [discriminate |].
      destruct (RM.find r smap) as [[wr cer] |] eqn:Hfind.
      * destruct (check_opt_int_width top wr) eqn:Hcw; [| discriminate].
        inversion Hr; subst wr ce seen1; clear Hr.
        destruct (Henv r w cer Hfind) as [_ [dv [Hfe [Hev Hsc]]]].
        exists []; split; [constructor | right; exists dv; split; [exact Hev | split; [exact Hsc |]]].
        intros tail_s; cbn [chain_draws denote_exp lookup_id].
        eapply MSR_LocalRead; [reflexivity | exact Hfe | apply MSR_Ret; reflexivity].
      * destruct (raw_id_in_list r defs) eqn:Hrd; [discriminate |].
        destruct top as [dt |]; [| discriminate].
        destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
        destruct (find_raw_id_index r params) as [idx |] eqn:Hidx; [| discriminate].
        destruct (nth_error src_pnames idx) as [pnm |] eqn:Hpnm; [| discriminate].
        destruct (starts_with_dollar pnm) eqn:Hdl; [discriminate |].
        inversion Hr; subst wt ce seen1; clear Hr.
        assert (Hnin : ~ In r defs)
          by (intros Hin; apply raw_id_in_list_spec in Hin; congruence).
        pose proof (find_raw_id_index_nth_error params r idx Hidx) as Hnth_p.
        destruct (Hpe idx r Hnth_p Hnin) as [dv [Hnth_v Hfe]].
        assert (Hnth_dt : nth_error arg_dtys idx = Some (DTYPE_Base (DTYPE_I w))).
        { apply Hpu; cbn [exp_param_uses]; rewrite Hrd, Hidx; left; reflexivity. }
        pose proof (Forall2_nth_error_l dvalue_has_dtyp vs arg_dtys Hvs idx dv
                      (DTYPE_Base (DTYPE_I w)) Hnth_v Hnth_dt) as Hsc.
        apply dvalue_has_dtyp_i_iff_wf_scalar in Hsc.
        destruct (build_param_env_nth src_pnames vs idx pnm Hnd Hls Hpnm) as [dv' [Hnth_v' Hbp]].
        assert (Heq_dv : dv' = dv) by congruence; subst dv'.
        exists []; split; [constructor | right; exists dv; split; [| split; [exact Hsc |]]].
        -- unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val].
           rewrite Hbp; exact (check_scalar_width_ok w dv Hsc).
        -- intros tail_s; cbn [chain_draws denote_exp lookup_id].
           eapply MSR_LocalRead; [reflexivity | exact Hfe | apply MSR_Ret; reflexivity].
    + (* EXP_Integer *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      exists []; split; [constructor | right].
      exists (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N (reify_int_const w (denote_int_syntax x)))))).
      split; [reflexivity | split; [right; eexists; reflexivity |]].
      intros tail_s; cbn [chain_draws denote_exp]; rewrite repr_reify_int_const.
      apply MSR_Ret; reflexivity.
    + (* EXP_Bool *)
      destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
      inversion Hr; subst w ce seen1; clear Hr.
      exists []; split; [constructor | right].
      destruct b.
      * exists (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.repr 1%positive (Z.of_N 1%N)))).
        split; [reflexivity | split; [right; eexists; reflexivity |]].
        intros tail_s; cbn [chain_draws denote_exp]; rewrite repr_one_N.
        apply MSR_Ret; reflexivity.
      * exists (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.repr 1%positive (Z.of_N 0%N)))).
        split; [reflexivity | split; [right; eexists; reflexivity |]].
        intros tail_s; cbn [chain_draws denote_exp]; rewrite repr_zero_N.
        apply MSR_Ret; reflexivity.
    + (* EXP_Undef *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      exists []; split; [constructor | right].
      exists (DVALUE_Base DVALUE_Poison).
      split; [reflexivity | split; [left; reflexivity | intros tail_s; apply MSR_Ret; reflexivity]].
    + (* EXP_Poison *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      exists []; split; [constructor | right].
      exists (DVALUE_Base DVALUE_Poison).
      split; [reflexivity | split; [left; reflexivity | intros tail_s; apply MSR_Ret; reflexivity]].
Qed.

Lemma eval_reified_exp_tgt {Pa : Params} :
  forall (o : exp dtyp) params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
         (sigma0 : @draw_strat Pa) (fmap0 : list (freeze_key * Z))
         smap (env : rmap (@dvalue Pa)) seen0 top w ce seen1,
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length params ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx dt, In (idx, dt) (exp_param_uses params defs top o) -> nth_error arg_dtys idx = Some dt) ->
    (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env = Some dv) ->
    wf_draw_strat sigma0 ->
    wf_smap_entries allowed defs seen0 true smap ->
    env_matches_smap defs (build_param_env src_pnames vs) (oracle_of_fmap fmap0) smap env ->
    reify_exp true params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
    exists added : list (freeze_key * Z),
      (forall k z, In (k, z) added -> In k seen1 /\ ~ In k seen0) /\
      ((exists msg,
          eval_closed_cert_expr (build_param_env src_pnames vs)
            (oracle_of_fmap (added ++ fmap0)) ce = raise_ub msg) \/
       (exists sigma1 dv,
          wf_draw_strat sigma1 /\
          eval_closed_cert_expr (build_param_env src_pnames vs)
            (oracle_of_fmap (added ++ fmap0)) ce = raise_ret dv /\
          wf_scalar_dvalue w dv /\
          mcfg_steps_to_ret sigma0 env (denote_exp top o) sigma1 env dv)).
Proof.
  apply (scalar_exp_ind (fun o =>
    forall params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
           (sigma0 : @draw_strat Pa) (fmap0 : list (freeze_key * Z))
           smap (env : rmap (@dvalue Pa)) seen0 top w ce seen1,
      NoDup src_pnames ->
      List.length params = List.length vs ->
      List.length src_pnames = List.length vs ->
      List.length arg_dtys = List.length params ->
      Forall2 dvalue_has_dtyp vs arg_dtys ->
      (forall idx dt, In (idx, dt) (exp_param_uses params defs top o) -> nth_error arg_dtys idx = Some dt) ->
      (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
        exists dv, nth_error vs idx = Some dv /\ RM.find r env = Some dv) ->
      wf_draw_strat sigma0 ->
      wf_smap_entries allowed defs seen0 true smap ->
      env_matches_smap defs (build_param_env src_pnames vs) (oracle_of_fmap fmap0) smap env ->
      reify_exp true params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
      exists added : list (freeze_key * Z),
        (forall k z, In (k, z) added -> In k seen1 /\ ~ In k seen0) /\
        ((exists msg,
            eval_closed_cert_expr (build_param_env src_pnames vs)
              (oracle_of_fmap (added ++ fmap0)) ce = raise_ub msg) \/
         (exists sigma1 dv,
            wf_draw_strat sigma1 /\
            eval_closed_cert_expr (build_param_env src_pnames vs)
              (oracle_of_fmap (added ++ fmap0)) ce = raise_ret dv /\
            wf_scalar_dvalue w dv /\
            mcfg_steps_to_ret sigma0 env (denote_exp top o) sigma1 env dv)))).
  - (* OP_IBinop *)
    intros iop dt e1 e2 IH1 IH2 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0 top w ce seen2
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen1] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I wb))) e2)
      as [[[w2 ce2] seen2'] |] eqn:Hr2; [| discriminate].
    destruct (ibinop_to_cert iop) as [cop cfl] eqn:Hiop.
    inversion Hr; subst wb ce seen2'; clear Hr.
    destruct (ibinop_to_cert_roundtrip iop cop cfl Hiop) as [Heq_iop _].
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr2)) as ->.
    destruct (reify_exp_freeze_props e1 true params src_pnames defs allowed smap seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen1 Hwfs0 Hr1)
      as (Hlf1 & Hinc01 & Hfk1).
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 true smap Hinc01 Hwfs0) as Hwfs1.
    destruct (reify_exp_freeze_props e2 true params src_pnames defs allowed smap seen1
                (Some (DTYPE_Base (DTYPE_I w))) w ce2 seen2 Hwfs1 Hr2)
      as (_ & Hinc12 & _).
    destruct (IH1 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hpe Hwfd0 Hwfs0 Henv0 Hr1)
      as (added1 & Had1 & [[msg1 Hev1] | (sigma1 & dv1 & Hwfd1 & Hev1 & Hsc1 & Hst1)]).
    + exists added1; split.
      * intros k z Hkz; destruct (Had1 k z Hkz) as [Hm Hn0]; split; [exact (Hinc12 k Hm) | exact Hn0].
      * left; exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + pose proof (env_matches_smap_oracle_prepend allowed defs seen0 added1 fmap0
                    (build_param_env src_pnames vs) smap env Hwfs0
                    (fun k z H => proj2 (Had1 k z H)) Henv0) as Henv1.
      destruct (IH2 params src_pnames defs allowed arg_dtys vs sigma1 (added1 ++ fmap0) smap env seen1
                  (Some (DTYPE_Base (DTYPE_I w))) w ce2 seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror Hin)))
                  Hpe Hwfd1 Hwfs1 Henv1 Hr2)
        as (added2 & Had2 & [[msg2 Hev2] | (sigma2 & dv2 & Hwfd2 & Hev2 & Hsc2 & Hst2)]).
      * exists (added2 ++ added1).
        assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
          - destruct (Had2 k z Hk2) as [Hs2 Hns1]; split; [exact Hs2 | intros Hs0; exact (Hns1 (Hinc01 k Hs0))].
          - destruct (Had1 k z Hk1) as [Hs1 Hns0]; split; [exact (Hinc12 k Hs1) | exact Hns0]. }
        split; [exact Had12 | left; exists msg2].
        rewrite <- app_assoc.
        pose proof (eval_let_free_prepend_fmap ce1 (build_param_env src_pnames vs)
                      added2 (added1 ++ fmap0) seen1 Hlf1 (Hfk1 eq_refl)
                      (fun k z H => proj2 (Had2 k z H))) as Hev1'.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1', Hev1, Hev2; reflexivity.
      * exists (added2 ++ added1).
        assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
          - destruct (Had2 k z Hk2) as [Hs2 Hns1]; split; [exact Hs2 | intros Hs0; exact (Hns1 (Hinc01 k Hs0))].
          - destruct (Had1 k z Hk1) as [Hs1 Hns0]; split; [exact (Hinc12 k Hs1) | exact Hns0]. }
        split; [exact Had12 |].
        rewrite <- app_assoc.
        pose proof (eval_let_free_prepend_fmap ce1 (build_param_env src_pnames vs)
                      added2 (added1 ++ fmap0) seen1 Hlf1 (Hfk1 eq_refl)
                      (fun k z H => proj2 (Had2 k z H))) as Hev1'.
        destruct (eval_iop_wf_scalar cop cfl w dv1 dv2 Hsc1 Hsc2)
          as [[msg_op Hev_op] | [vout [Hev_op Hsc_out]]].
        -- left; exists msg_op; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hev1', Hev1, Hev2; cbn [eou_bind]; exact Hev_op.
        -- right; exists sigma2, vout; split; [exact Hwfd2 | split; [| split; [exact Hsc_out |]]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hev1', Hev1, Hev2; cbn [eou_bind]; exact Hev_op.
           ++ cbn [denote_exp]; eapply mcfg_steps_to_ret_bind; [exact Hst1 |].
              eapply mcfg_steps_to_ret_bind; [exact Hst2 |].
              rewrite <- Heq_iop, Hev_op; apply mcfg_steps_eou_ret.
  - (* OP_ICmp *)
    intros ss cmp dt e1 e2 IH1 IH2 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0 top w ce seen2
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen1] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I wb))) e2)
      as [[[w2 ce2] seen2'] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w ce seen2'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr2)) as ->.
    destruct (reify_exp_freeze_props e1 true params src_pnames defs allowed smap seen0
                (Some (DTYPE_Base (DTYPE_I wb))) wb ce1 seen1 Hwfs0 Hr1)
      as (Hlf1 & Hinc01 & Hfk1).
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 true smap Hinc01 Hwfs0) as Hwfs1.
    destruct (reify_exp_freeze_props e2 true params src_pnames defs allowed smap seen1
                (Some (DTYPE_Base (DTYPE_I wb))) wb ce2 seen2 Hwfs1 Hr2)
      as (_ & Hinc12 & _).
    destruct (IH1 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0
                (Some (DTYPE_Base (DTYPE_I wb))) wb ce1 seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hpe Hwfd0 Hwfs0 Henv0 Hr1)
      as (added1 & Had1 & [[msg1 Hev1] | (sigma1 & dv1 & Hwfd1 & Hev1 & Hsc1 & Hst1)]).
    + exists added1; split.
      * intros k z Hkz; destruct (Had1 k z Hkz) as [Hm Hn0]; split; [exact (Hinc12 k Hm) | exact Hn0].
      * left; exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + pose proof (env_matches_smap_oracle_prepend allowed defs seen0 added1 fmap0
                    (build_param_env src_pnames vs) smap env Hwfs0
                    (fun k z H => proj2 (Had1 k z H)) Henv0) as Henv1.
      destruct (IH2 params src_pnames defs allowed arg_dtys vs sigma1 (added1 ++ fmap0) smap env seen1
                  (Some (DTYPE_Base (DTYPE_I wb))) wb ce2 seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror Hin)))
                  Hpe Hwfd1 Hwfs1 Henv1 Hr2)
        as (added2 & Had2 & [[msg2 Hev2] | (sigma2 & dv2 & Hwfd2 & Hev2 & Hsc2 & Hst2)]).
      * exists (added2 ++ added1).
        assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
          - destruct (Had2 k z Hk2) as [Hs2 Hns1]; split; [exact Hs2 | intros Hs0; exact (Hns1 (Hinc01 k Hs0))].
          - destruct (Had1 k z Hk1) as [Hs1 Hns0]; split; [exact (Hinc12 k Hs1) | exact Hns0]. }
        split; [exact Had12 | left; exists msg2].
        rewrite <- app_assoc.
        pose proof (eval_let_free_prepend_fmap ce1 (build_param_env src_pnames vs)
                      added2 (added1 ++ fmap0) seen1 Hlf1 (Hfk1 eq_refl)
                      (fun k z H => proj2 (Had2 k z H))) as Hev1'.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1', Hev1, Hev2; reflexivity.
      * exists (added2 ++ added1).
        assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
          - destruct (Had2 k z Hk2) as [Hs2 Hns1]; split; [exact Hs2 | intros Hs0; exact (Hns1 (Hinc01 k Hs0))].
          - destruct (Had1 k z Hk1) as [Hs1 Hns0]; split; [exact (Hinc12 k Hs1) | exact Hns0]. }
        split; [exact Had12 | right].
        rewrite <- app_assoc.
        pose proof (eval_let_free_prepend_fmap ce1 (build_param_env src_pnames vs)
                      added2 (added1 ++ fmap0) seen1 Hlf1 (Hfk1 eq_refl)
                      (fun k z H => proj2 (Had2 k z H))) as Hev1'.
        destruct (eval_icmp_wf_scalar ss (icmp_to_cert cmp) wb dv1 dv2 Hsc1 Hsc2)
          as [vout [Hev_cmp Hsc_out]].
        exists sigma2, vout; split; [exact Hwfd2 | split; [| split; [exact Hsc_out |]]].
        -- unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hev1', Hev1, Hev2; cbn [eou_bind]; exact Hev_cmp.
        -- cbn [denote_exp]; eapply mcfg_steps_to_ret_bind; [exact Hst1 |].
           eapply mcfg_steps_to_ret_bind; [exact Hst2 |].
           rewrite <- (icmp_to_cert_roundtrip cmp), Hev_cmp; apply mcfg_steps_eou_ret.
  - (* OP_Conversion *)
    intros ct dtf e1 dtt IH1 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0 top w ce seen1
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr.
    cbn [reify_exp] in Hr.
    destruct ct as [pc | |]; try discriminate.
    destruct dtf as [tbf | |]; try discriminate; destruct tbf as [fw | | | | | | | | | |]; try discriminate.
    destruct dtt as [tbt | |]; try discriminate; destruct tbt as [tw | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top tw) eqn:Hcw; [| discriminate].
    destruct (pure_conv_to_cert pc) as [[ck cfl] |] eqn:Hpc; [| discriminate].
    set (w_ok :=
      match ck with
      | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg cfl) && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg cfl)
      end) in *.
    destruct w_ok eqn:Hwok; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I fw))) e1)
      as [[[w1 ce1] seen1'] |] eqn:Hr1; [| discriminate].
    inversion Hr; subst w ce seen1'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (pure_conv_to_cert_roundtrip pc ck cfl Hpc) as Heq_pc.
    destruct (IH1 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0
                (Some (DTYPE_Base (DTYPE_I fw))) fw ce1 seen1
                Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr1)
      as (added1 & Had1 & [[msg1 Hev1] | (sigma1 & dv1 & Hwfd1 & Hev1 & Hsc1 & Hst1)]).
    + exists added1; split; [exact Had1 | left; exists msg1].
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + unfold w_ok in Hwok.
      destruct (eval_cast_wf_scalar ck fw tw cfl dv1 Hwok Hsc1) as [vout [Hev_cast Hsc_out]].
      exists added1; split; [exact Had1 | right].
      exists sigma1, vout; split; [exact Hwfd1 | split; [| split; [exact Hsc_out |]]].
      * unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; cbn [eou_bind]; exact Hev_cast.
      * cbn [denote_exp convert]; eapply mcfg_steps_to_ret_bind; [exact Hst1 |].
        rewrite <- Heq_pc, Hev_cast; apply mcfg_steps_eou_ret.
  - (* OP_Select *)
    intros fm dtc ec dt1 e1 dt2 e2 IHc IH1 IH2 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0 top w ce seen3
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr.
    cbn [reify_exp] in Hr.
    destruct dtc as [tbc | |]; try discriminate; destruct tbc as [wc | | | | | | | | | |]; try discriminate.
    destruct wc as [| |]; try discriminate.
    destruct dt1 as [tb1 | |]; try discriminate; destruct tb1 as [w1 | | | | | | | | | |]; try discriminate.
    destruct dt2 as [tb2 | |]; try discriminate; destruct tb2 as [w2 | | | | | | | | | |]; try discriminate.
    destruct (Pos.eqb w1 w2 && check_opt_int_width top w1) eqn:Hcw; [| discriminate].
    apply andb_true_iff in Hcw as [Hw12 Hcw]; apply Pos.eqb_eq in Hw12; subst w2.
    destruct (reify_exp true params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I 1%positive))) ec)
      as [[[wc' cec] seen1] |] eqn:Hrc; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen1 (Some (DTYPE_Base (DTYPE_I w1))) e1)
      as [[[wa ce1] seen2] |] eqn:Hr1; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen2 (Some (DTYPE_Base (DTYPE_I w1))) e2)
      as [[[wb ce2] seen3'] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w1 ce seen3'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hrc)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr2)) as ->.
    destruct (reify_exp_freeze_props ec true params src_pnames defs allowed smap seen0
                (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive cec seen1 Hwfs0 Hrc)
      as (Hlfc & Hinc01 & Hfkc).
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 true smap Hinc01 Hwfs0) as Hwfs1.
    destruct (reify_exp_freeze_props e1 true params src_pnames defs allowed smap seen1
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen2 Hwfs1 Hr1)
      as (Hlf1 & Hinc12 & Hfk1).
    pose proof (wf_smap_entries_seen_mono allowed defs seen1 seen2 true smap Hinc12 Hwfs1) as Hwfs2.
    destruct (reify_exp_freeze_props e2 true params src_pnames defs allowed smap seen2
                (Some (DTYPE_Base (DTYPE_I w))) w ce2 seen3 Hwfs2 Hr2)
      as (_ & Hinc23 & _).
    destruct (IHc params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0
                (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive cec seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_introl Hin)))
                Hpe Hwfd0 Hwfs0 Henv0 Hrc)
      as (addedc & Hadc & [[msgc Hevc] | (sigmac & dvc & Hwfdc & Hevc & Hscc & Hstc)]).
    + exists addedc; split.
      * intros k z Hkz; destruct (Hadc k z Hkz) as [Hm Hn0]; split; [exact (Hinc23 k (Hinc12 k Hm)) | exact Hn0].
      * left; exists msgc; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hevc; reflexivity.
    + pose proof (env_matches_smap_oracle_prepend allowed defs seen0 addedc fmap0
                    (build_param_env src_pnames vs) smap env Hwfs0
                    (fun k z H => proj2 (Hadc k z H)) Henv0) as Henv1.
      destruct (IH1 params src_pnames defs allowed arg_dtys vs sigmac (addedc ++ fmap0) smap env seen1
                  (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl Hin)))))
                  Hpe Hwfdc Hwfs1 Henv1 Hr1)
        as (added1 & Had1 & [[msg1 Hev1] | (sigma1 & dv1 & Hwfd1 & Hev1 & Hsc1 & Hst1)]).
      * exists (added1 ++ addedc).
        assert (Had_c1 : forall k z, In (k, z) (added1 ++ addedc) -> In k seen3 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk1 | Hkc].
          - destruct (Had1 k z Hk1) as [Hs2 Hns1]; split; [exact (Hinc23 k Hs2) | intros Hs0; exact (Hns1 (Hinc01 k Hs0))].
          - destruct (Hadc k z Hkc) as [Hs1 Hns0]; split; [exact (Hinc23 k (Hinc12 k Hs1)) | exact Hns0]. }
        split; [exact Had_c1 | left; exists msg1].
        rewrite <- app_assoc.
        pose proof (eval_let_free_prepend_fmap cec (build_param_env src_pnames vs)
                      added1 (addedc ++ fmap0) seen1 Hlfc (Hfkc eq_refl)
                      (fun k z H => proj2 (Had1 k z H))) as Hevc'.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hevc', Hevc, Hev1; reflexivity.
      * pose proof (env_matches_smap_oracle_prepend allowed defs seen1 added1 (addedc ++ fmap0)
                      (build_param_env src_pnames vs) smap env Hwfs1
                      (fun k z H => proj2 (Had1 k z H)) Henv1) as Henv2.
        destruct (IH2 params src_pnames defs allowed arg_dtys vs sigma1 (added1 ++ (addedc ++ fmap0)) smap env seen2
                    (Some (DTYPE_Base (DTYPE_I w))) w ce2 seen3
                    Hnd Hlp Hls Hla Hvs
                    (fun idx d Hin => Hpu idx d (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_intror Hin)))))
                    Hpe Hwfd1 Hwfs2 Henv2 Hr2)
          as (added2 & Had2 & [[msg2 Hev2] | (sigma2 & dv2 & Hwfd2 & Hev2 & Hsc2 & Hst2)]).
        -- exists (added2 ++ added1 ++ addedc).
           assert (Had_all : forall k z, In (k, z) (added2 ++ added1 ++ addedc) -> In k seen3 /\ ~ In k seen0).
           { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1c].
             - destruct (Had2 k z Hk2) as [Hs3 Hns2]; split; [exact Hs3 | intros Hs0; exact (Hns2 (Hinc12 k (Hinc01 k Hs0)))].
             - apply in_app_iff in Hk1c as [Hk1 | Hkc].
               + destruct (Had1 k z Hk1) as [Hs2 Hns1]; split; [exact (Hinc23 k Hs2) | intros Hs0; exact (Hns1 (Hinc01 k Hs0))].
               + destruct (Hadc k z Hkc) as [Hs1 Hns0]; split; [exact (Hinc23 k (Hinc12 k Hs1)) | exact Hns0]. }
           split; [exact Had_all | left; exists msg2].
           replace ((added2 ++ added1 ++ addedc) ++ fmap0) with (added2 ++ (added1 ++ (addedc ++ fmap0)))
             by (rewrite !app_assoc; reflexivity).
           pose proof (eval_let_free_prepend_fmap cec (build_param_env src_pnames vs)
                         added1 (addedc ++ fmap0) seen1 Hlfc (Hfkc eq_refl)
                         (fun k z H => proj2 (Had1 k z H))) as Hevc1.
           pose proof (eval_let_free_prepend_fmap cec (build_param_env src_pnames vs)
                         added2 (added1 ++ (addedc ++ fmap0)) seen2 Hlfc
                         (fun u Hu => Hinc12 u (Hfkc eq_refl u Hu))
                         (fun k z H => proj2 (Had2 k z H))) as Hevc2.
           pose proof (eval_let_free_prepend_fmap ce1 (build_param_env src_pnames vs)
                         added2 (added1 ++ (addedc ++ fmap0)) seen2 Hlf1 (Hfk1 eq_refl)
                         (fun k z H => proj2 (Had2 k z H))) as Hev12.
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hevc2, Hevc1, Hevc, Hev12, Hev1, Hev2; reflexivity.
        -- exists (added2 ++ added1 ++ addedc).
           assert (Had_all : forall k z, In (k, z) (added2 ++ added1 ++ addedc) -> In k seen3 /\ ~ In k seen0).
           { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1c].
             - destruct (Had2 k z Hk2) as [Hs3 Hns2]; split; [exact Hs3 | intros Hs0; exact (Hns2 (Hinc12 k (Hinc01 k Hs0)))].
             - apply in_app_iff in Hk1c as [Hk1 | Hkc].
               + destruct (Had1 k z Hk1) as [Hs2 Hns1]; split; [exact (Hinc23 k Hs2) | intros Hs0; exact (Hns1 (Hinc01 k Hs0))].
               + destruct (Hadc k z Hkc) as [Hs1 Hns0]; split; [exact (Hinc23 k (Hinc12 k Hs1)) | exact Hns0]. }
           split; [exact Had_all | right].
           replace ((added2 ++ added1 ++ addedc) ++ fmap0) with (added2 ++ (added1 ++ (addedc ++ fmap0)))
             by (rewrite !app_assoc; reflexivity).
           pose proof (eval_let_free_prepend_fmap cec (build_param_env src_pnames vs)
                         added1 (addedc ++ fmap0) seen1 Hlfc (Hfkc eq_refl)
                         (fun k z H => proj2 (Had1 k z H))) as Hevc1.
           pose proof (eval_let_free_prepend_fmap cec (build_param_env src_pnames vs)
                         added2 (added1 ++ (addedc ++ fmap0)) seen2 Hlfc
                         (fun u Hu => Hinc12 u (Hfkc eq_refl u Hu))
                         (fun k z H => proj2 (Had2 k z H))) as Hevc2.
           pose proof (eval_let_free_prepend_fmap ce1 (build_param_env src_pnames vs)
                         added2 (added1 ++ (addedc ++ fmap0)) seen2 Hlf1 (Hfk1 eq_refl)
                         (fun k z H => proj2 (Had2 k z H))) as Hev12.
           destruct (eval_select_wf_scalar w dvc dv1 dv2 Hscc Hsc1 Hsc2)
             as [vout [Hev_sel Hsc_out]].
           exists sigma2, vout; split; [exact Hwfd2 | split; [| split; [exact Hsc_out |]]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hevc2, Hevc1, Hevc, Hev12, Hev1, Hev2; cbn [eou_bind]; exact Hev_sel.
           ++ cbn [denote_exp]; eapply mcfg_steps_to_ret_bind; [exact Hstc |].
              eapply mcfg_steps_to_ret_bind; [exact Hst1 |].
              eapply mcfg_steps_to_ret_bind; [exact Hst2 |].
              rewrite Hev_sel; apply mcfg_steps_eou_ret.
  - (* OP_Freeze *)
    intros dt e1 IH1 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0 top w ce seen1
      Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr.
    cbn [reify_exp] in Hr.
    destruct dt as [tb | |]; try discriminate; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_exp true params src_pnames defs smap seen0 (Some (DTYPE_Base (DTYPE_I wb))) e1)
      as [[[w1 ce1] seen_mid] |] eqn:Hr1; [| discriminate].
    destruct (freeze_key_in (wb, ce1) seen_mid) eqn:Hfk_in; [discriminate |].
    inversion Hr; subst wb ce seen1; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr1)) as ->.
    assert (Hfnin : ~ In (w, ce1) seen_mid)
      by (intros Hin; apply freeze_key_in_spec in Hin; congruence).
    destruct (reify_exp_freeze_props e1 true params src_pnames defs allowed smap seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen_mid Hwfs0 Hr1)
      as (Hlf1 & Hinc0m & Hfk1).
    destruct (IH1 params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce1 seen_mid
                Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr1)
      as (added1 & Had1 & [[msg1 Hev1] | (sigma_m & dv1 & Hwfd_m & Hev1 & Hsc1 & Hst1)]).
    + exists added1; split.
      * intros k z Hkz; destruct (Had1 k z Hkz) as [Hm Hn0]; split; [right; exact Hm | exact Hn0].
      * left; exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + destruct Hsc1 as [-> | [iv ->]].
      * pose proof (Hwfd_m 0%nat (DTYPE_Base (DTYPE_I w)) (inhabited_draw_dtyp_i w)) as Hvd.
        apply valid_draw_i_iff in Hvd as [idraw Hidraw].
        set (z_draw := @Integers.unsigned w idraw).
        exists ([((w, ce1), z_draw)] ++ added1).
        split.
        -- intros k z [Heq | Hkz].
           ++ inversion Heq; subst k z; split;
                [left; reflexivity | intros Hs0; exact (Hfnin (Hinc0m _ Hs0))].
           ++ destruct (Had1 k z Hkz) as [Hm Hn0]; split; [right; exact Hm | exact Hn0].
        -- right; exists (shift_draw_strat sigma_m), (DVALUE_Base (@DVALUE_I Pa w idraw)).
           split; [exact (shift_draw_strat_wf sigma_m Hwfd_m) | split; [| split; [right; exists idraw; reflexivity |]]].
           ++ rewrite <- app_assoc.
              pose proof (eval_let_free_prepend_fmap ce1 (build_param_env src_pnames vs)
                            [((w, ce1), z_draw)] (added1 ++ fmap0) seen_mid Hlf1 (Hfk1 eq_refl)
                            (fun k z H => match H with
                                          | or_introl Heq => eq_ind_r (fun u => ~ In u seen_mid) Hfnin (f_equal fst Heq)
                                          | or_intror Hfalse => False_ind _ Hfalse
                                          end)) as Hev1'.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr let_val_exprs List.map].
              rewrite Hev1', Hev1, (expand_lets_let_free ce1 Hlf1); cbn [app oracle_of_fmap].
              rewrite freeze_key_eqb_refl; unfold z_draw; rewrite (@Integers.repr_unsigned w idraw); reflexivity.
           ++ cbn [denote_exp]; eapply mcfg_steps_to_ret_bind; [exact Hst1 |].
              eapply MSR_Draw; [reflexivity | intros n d; reflexivity | rewrite Hidraw; apply MSR_Ret; reflexivity].
      * exists added1; split.
        -- intros k z Hkz; destruct (Had1 k z Hkz) as [Hm Hn0]; split; [right; exact Hm | exact Hn0].
        -- right; exists sigma_m, (DVALUE_Base (@DVALUE_I Pa w iv)).
           split; [exact Hwfd_m | split; [| split; [right; exists iv; reflexivity |]]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
           ++ cbn [denote_exp]; eapply mcfg_steps_to_ret_bind; [exact Hst1 | apply MSR_Ret; reflexivity].
  - (* Non-recursive base cases *)
    intros o; destruct o; try exact I;
      intros params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap env seen0 top w ce seen1
             Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr;
      cbn [reify_exp] in Hr; try discriminate.
    + (* EXP_Ident *)
      destruct id as [| r]; [discriminate |].
      destruct (RM.find r smap) as [[wr cer] |] eqn:Hfind.
      * destruct (check_opt_int_width top wr) eqn:Hcw; [| discriminate].
        inversion Hr; subst wr ce seen1; clear Hr.
        destruct (Henv0 r w cer Hfind) as [_ [dv [Hfe [Hev Hsc]]]].
        exists []; split; [intros _ _ [] | right; exists sigma0, dv].
        split; [exact Hwfd0 | split; [exact Hev | split; [exact Hsc |]]].
        cbn [denote_exp lookup_id]; eapply MSR_LocalRead; [reflexivity | exact Hfe | apply MSR_Ret; reflexivity].
      * destruct (raw_id_in_list r defs) eqn:Hrd; [discriminate |].
        destruct top as [dt |]; [| discriminate].
        destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
        destruct (find_raw_id_index r params) as [idx |] eqn:Hidx; [| discriminate].
        destruct (nth_error src_pnames idx) as [pnm |] eqn:Hpnm; [| discriminate].
        destruct (starts_with_dollar pnm) eqn:Hdl; [discriminate |].
        inversion Hr; subst wt ce seen1; clear Hr.
        assert (Hnin : ~ In r defs)
          by (intros Hin; apply raw_id_in_list_spec in Hin; congruence).
        pose proof (find_raw_id_index_nth_error params r idx Hidx) as Hnth_p.
        destruct (Hpe idx r Hnth_p Hnin) as [dv [Hnth_v Hfe]].
        assert (Hnth_dt : nth_error arg_dtys idx = Some (DTYPE_Base (DTYPE_I w))).
        { apply Hpu; cbn [exp_param_uses]; rewrite Hrd, Hidx; left; reflexivity. }
        pose proof (Forall2_nth_error_l dvalue_has_dtyp vs arg_dtys Hvs idx dv
                      (DTYPE_Base (DTYPE_I w)) Hnth_v Hnth_dt) as Hsc.
        apply dvalue_has_dtyp_i_iff_wf_scalar in Hsc.
        destruct (build_param_env_nth src_pnames vs idx pnm Hnd Hls Hpnm) as [dv' [Hnth_v' Hbp]].
        assert (Heq_dv : dv' = dv) by congruence; subst dv'.
        exists []; split; [intros _ _ [] | right; exists sigma0, dv].
        split; [exact Hwfd0 | split; [| split; [exact Hsc |]]].
        -- unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val].
           rewrite Hbp; exact (check_scalar_width_ok w dv Hsc).
        -- cbn [denote_exp lookup_id]; eapply MSR_LocalRead; [reflexivity | exact Hfe | apply MSR_Ret; reflexivity].
    + (* EXP_Integer *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      exists []; split; [intros _ _ [] | right].
      exists sigma0,
        (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N (reify_int_const w (denote_int_syntax x)))))).
      split; [exact Hwfd0 | split; [reflexivity | split; [right; eexists; reflexivity |]]].
      cbn [denote_exp]; rewrite repr_reify_int_const; apply MSR_Ret; reflexivity.
    + (* EXP_Bool *)
      destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
      inversion Hr; subst w ce seen1; clear Hr.
      exists []; split; [intros _ _ [] | right].
      destruct b.
      * exists sigma0, (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.repr 1%positive (Z.of_N 1%N)))).
        split; [exact Hwfd0 | split; [reflexivity | split; [right; eexists; reflexivity |]]].
        cbn [denote_exp]; rewrite repr_one_N; apply MSR_Ret; reflexivity.
      * exists sigma0, (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.repr 1%positive (Z.of_N 0%N)))).
        split; [exact Hwfd0 | split; [reflexivity | split; [right; eexists; reflexivity |]]].
        cbn [denote_exp]; rewrite repr_zero_N; apply MSR_Ret; reflexivity.
    + (* EXP_Undef *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      exists []; split; [intros _ _ [] | right].
      exists sigma0, (DVALUE_Base DVALUE_Poison).
      split; [exact Hwfd0 | split; [reflexivity | split; [left; reflexivity | apply MSR_Ret; reflexivity]]].
    + (* EXP_Poison *)
      destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce seen1; clear Hr.
      exists []; split; [intros _ _ [] | right].
      exists sigma0, (DVALUE_Base DVALUE_Poison).
      split; [exact Hwfd0 | split; [reflexivity | split; [left; reflexivity | apply MSR_Ret; reflexivity]]].
Qed.


(** *** 5.5 Bounded-DAG Control-Flow Reifier ([cfg_dag]) & Operational Soundness *)

Lemma NoDup_app_inv_l {A : Type} :
  forall (xs ys : list A), NoDup (xs ++ ys) -> NoDup xs.
Proof.
  induction xs as [| x rx IH]; intros ys Hnd; [constructor |].
  cbn in Hnd; inversion Hnd as [| ? ? Hni Hndr]; subst.
  constructor; [intros Hin; apply Hni, in_app_iff; left; exact Hin | exact (IH ys Hndr)].
Qed.

Lemma bit_int_1_equ_one_eq_unsigned :
  forall (cbit : @Integers.bit_int 1),
    equ cbit one = (@Integers.unsigned 1 cbit =? 1)%Z.
Proof.
  intros cbit; cbn [equ one VInt_Bounded]; unfold Integers.eq.
  rewrite (@Integers.unsigned_one 1).
  match goal with
  | |- (if ?c then _ else _) = _ => destruct c as [Heq | Hneq]
  end.
  - symmetry; apply Z.eqb_eq; exact Heq.
  - symmetry; apply Z.eqb_neq; exact Hneq.
Qed.

Lemma assoc_in_pargs :
  forall (bid : block_id) (pargs : list (block_id * exp dtyp)) (op : exp dtyp),
    assoc bid pargs = Some op -> In (bid, op) pargs.
Proof.
  intros bid pargs op; induction pargs as [| [b' e'] rest IH]; intros H.
  - inversion H.
  - destruct (RawIDOrd.eq_dec bid b') as [<- | Hneq].
    + rewrite (assoc_hd bid e' rest) in H; inversion H; subst; left; reflexivity.
    + rewrite (assoc_tl bid b' e' rest Hneq) in H; right; exact (IH H).
Qed.

Inductive cfg_dag : Set :=
| CD_Unreachable
| CD_RetVoid
| CD_RetScalar (w : positive) (ret_e : cert_expr)
| CD_Eval (w : positive) (step_e : cert_expr) (next : cfg_dag)
| CD_Branch (cond : cert_expr) (on_true on_false : cfg_dag).

Variant dag_outcome {Pa : Params} : Type :=
| DO_UB
| DO_Ret (dv : @dvalue Pa).

Fixpoint eval_cfg_dag {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle) (d : cfg_dag)
  : @dag_outcome Pa :=
  match d with
  | CD_Unreachable => DO_UB
  | CD_RetVoid => DO_Ret NONE
  | CD_RetScalar _ ret_e =>
      match eval_closed_cert_expr penv foracle ret_e with
      | raise_ret dv => DO_Ret dv
      | _ => DO_UB
      end
  | CD_Eval _ step_e next =>
      match eval_closed_cert_expr penv foracle step_e with
      | raise_ret _ => eval_cfg_dag penv foracle next
      | _ => DO_UB
      end
  | CD_Branch cond on_true on_false =>
      match eval_closed_cert_expr penv foracle cond with
      | raise_ret (DVALUE_Base (@DVALUE_I _ 1%positive cbit)) =>
          if (@Integers.unsigned 1 cbit =? 1)%Z
          then eval_cfg_dag penv foracle on_true
          else eval_cfg_dag penv foracle on_false
      | _ => DO_UB
      end
  end.

Fixpoint wf_cfg_dag (allowed : list (string * positive)) (d : cfg_dag) : bool :=
  match d with
  | CD_Unreachable | CD_RetVoid => true
  | CD_RetScalar w ret_e =>
      wt_cert_expr [] ret_e &&
      Pos.eqb (cert_expr_bit_width ret_e) w &&
      is_let_free_expr ret_e &&
      vars_subset_b (collect_free_vars [] ret_e) allowed
  | CD_Eval w step_e next =>
      wt_cert_expr [] step_e &&
      Pos.eqb (cert_expr_bit_width step_e) w &&
      is_let_free_expr step_e &&
      vars_subset_b (collect_free_vars [] step_e) allowed &&
      wf_cfg_dag allowed next
  | CD_Branch cond on_true on_false =>
      wt_cert_expr [] cond &&
      Pos.eqb (cert_expr_bit_width cond) 1%positive &&
      is_let_free_expr cond &&
      vars_subset_b (collect_free_vars [] cond) allowed &&
      wf_cfg_dag allowed on_true &&
      wf_cfg_dag allowed on_false
  end.

Lemma incl_vars_subset_b :
  forall vs allowed,
    incl vs allowed -> vars_subset_b vs allowed = true.
Proof.
  intros vs allowed Hinc; unfold vars_subset_b; apply forallb_forall.
  intros u Hu; apply var_pair_in_spec; exact (Hinc u Hu).
Qed.

Lemma wf_smap_entries_empty :
  forall allowed defs seen uf,
    wf_smap_entries allowed defs seen uf (RM.empty _).
Proof.
  intros allowed defs seen uf r w ce Hf.
  rewrite RMF.F.empty_o in Hf; discriminate Hf.
Qed.

Lemma wf_smap_entries_add :
  forall allowed defs seen uf smap id w ce,
    wf_smap_entries allowed defs seen uf smap ->
    In id defs ->
    wt_cert_expr [] ce = true ->
    cert_expr_bit_width ce = w ->
    is_let_free_expr ce = true ->
    incl (collect_free_vars [] ce) allowed ->
    (uf = true -> incl (collect_freeze_keys ce) seen) ->
    wf_smap_entries allowed defs seen uf (RM.add id (w, ce) smap).
Proof.
  intros allowed defs seen uf smap id w ce Hsmap Hid Hwt Hbw Hlf Hfv Hfk r wr cer Hf.
  destruct (RawIDOrd.eq_dec id r) as [Heq | Hneq].
  - rewrite RMF.F.add_eq_o in Hf by exact Heq; inversion Hf; subst r wr cer.
    repeat split; assumption.
  - rewrite RMF.F.add_neq_o in Hf by exact Hneq; exact (Hsmap r wr cer Hf).
Qed.

Lemma env_matches_smap_empty {Pa : Params} :
  forall defs (penv : param_env Pa) foracle env,
    env_matches_smap defs penv foracle (RM.empty _) env.
Proof.
  intros defs penv foracle env r w ce Hf.
  rewrite RMF.F.empty_o in Hf; discriminate Hf.
Qed.

Lemma env_matches_smap_add {Pa : Params} :
  forall defs (penv : param_env Pa) foracle smap (env : rmap (@dvalue Pa)) id w ce dv,
    env_matches_smap defs penv foracle smap env ->
    In id defs ->
    eval_closed_cert_expr penv foracle ce = raise_ret dv ->
    wf_scalar_dvalue w dv ->
    env_matches_smap defs penv foracle (RM.add id (w, ce) smap) (RM.add id dv env).
Proof.
  intros defs penv foracle smap env id w ce dv Henv Hid Hev Hsc r wr cer Hf.
  destruct (RawIDOrd.eq_dec id r) as [Heq | Hneq].
  - rewrite RMF.F.add_eq_o in Hf by exact Heq; inversion Hf; subst r wr cer.
    split; [exact Hid | exists dv; split; [apply RMF.F.add_eq_o; reflexivity | split; assumption]].
  - rewrite RMF.F.add_neq_o in Hf by exact Hneq.
    destruct (Henv r wr cer Hf) as [Hr [dv' [Hfe [Hev' Hsc']]]].
    split; [exact Hr | exists dv'; split; [rewrite RMF.F.add_neq_o by exact Hneq; exact Hfe | split; assumption]].
Qed.

Fixpoint wrap_evals (evals : list (positive * cert_expr)) (k : cfg_dag) : cfg_dag :=
  match evals with
  | [] => k
  | (w, ce) :: rest => CD_Eval w ce (wrap_evals rest k)
  end.

Fixpoint wrap_phi_evals
  (pevals : list (raw_id * positive * cert_expr)) (k : cfg_dag) : cfg_dag :=
  match pevals with
  | [] => k
  | (_, w, ce) :: rest => CD_Eval w ce (wrap_phi_evals rest k)
  end.

Fixpoint apply_phi_smap
  (smap : rmap (positive * cert_expr))
  (pevals : list (raw_id * positive * cert_expr))
  : rmap (positive * cert_expr) :=
  match pevals with
  | [] => smap
  | (id, w, ce) :: rest => apply_phi_smap (RM.add id (w, ce) smap) rest
  end.

Fixpoint apply_phi_env {Pa : Params}
  (env : rmap (@dvalue Pa)) (dvs : list (raw_id * @dvalue Pa)) : rmap (@dvalue Pa) :=
  match dvs with
  | [] => env
  | (id, dv) :: rest => apply_phi_env (RM.add id dv env) rest
  end.

Lemma cfg_steps_lwrite_list {Pa : Params} :
  forall (dvs : list (raw_id * @dvalue Pa))
         (sigma : @draw_strat Pa) (env : rmap (@dvalue Pa)),
    cfg_steps_to_ret sigma env
      (map_monad (m := CFGtop) (fun '(id, dv) => lwrite id dv) dvs)
      sigma (apply_phi_env env dvs) (List.map (fun _ => tt) dvs).
Proof.
  induction dvs as [| [id dv] rest IH]; intros sigma env; cbn [map_monad apply_phi_env List.map].
  - apply CSR_Ret; reflexivity.
  - eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite |].
    eapply cfg_steps_to_ret_bind; [apply IH | apply CSR_Ret; reflexivity].
Qed.

Definition phi_eval_wf_entry
  (allowed : list (string * positive))
  (defs : list raw_id)
  (seen : list freeze_key)
  (uf : bool)
  (p : raw_id * positive * cert_expr) : Prop :=
  let '(id, w, ce) := p in
  In id defs /\
  wt_cert_expr [] ce = true /\
  cert_expr_bit_width ce = w /\
  is_let_free_expr ce = true /\
  incl (collect_free_vars [] ce) allowed /\
  (uf = true -> incl (collect_freeze_keys ce) seen).

Lemma phi_eval_wf_entry_mono :
  forall allowed defs seen1 seen2 uf pevals,
    incl seen1 seen2 ->
    Forall (phi_eval_wf_entry allowed defs seen1 uf) pevals ->
    Forall (phi_eval_wf_entry allowed defs seen2 uf) pevals.
Proof.
  intros allowed defs seen1 seen2 uf pevals Hinc Hfa.
  induction Hfa as [| [[id w] ce] rest (Hid & Hwt & Hbw & Hlf & Hfv & Hfk) _ IH]; [constructor |].
  constructor; [| exact IH].
  repeat split; try assumption.
  intros Huf u Hu; exact (Hinc u (Hfk Huf u Hu)).
Qed.

Lemma apply_phi_smap_wf :
  forall allowed defs seen uf pevals smap,
    wf_smap_entries allowed defs seen uf smap ->
    Forall (phi_eval_wf_entry allowed defs seen uf) pevals ->
    wf_smap_entries allowed defs seen uf (apply_phi_smap smap pevals).
Proof.
  intros allowed defs seen uf pevals smap Hsmap Hfa; revert smap Hsmap.
  induction Hfa as [| [[id w] ce] rest (Hid & Hwt & Hbw & Hlf & Hfv & Hfk) _ IH];
    intros smap Hsmap; cbn [apply_phi_smap]; [exact Hsmap |].
  apply IH; exact (wf_smap_entries_add allowed defs seen uf smap id w ce Hsmap Hid Hwt Hbw Hlf Hfv Hfk).
Qed.

Lemma wrap_phi_evals_wf :
  forall allowed defs seen uf pevals k,
    Forall (phi_eval_wf_entry allowed defs seen uf) pevals ->
    wf_cfg_dag allowed k = true ->
    wf_cfg_dag allowed (wrap_phi_evals pevals k) = true.
Proof.
  intros allowed defs seen uf pevals k Hfa Hk.
  induction Hfa as [| [[id w] ce] rest (_ & Hwt & Hbw & Hlf & Hfv & _) _ IH];
    cbn [wrap_phi_evals wf_cfg_dag]; [exact Hk |].
  rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv), IH; reflexivity.
Qed.

Definition phi_eval_pair_matches {Pa : Params}
  (penv : param_env Pa)
  (foracle : freeze_oracle)
  (p : raw_id * positive * cert_expr)
  (dv_p : raw_id * @dvalue Pa) : Prop :=
  let '(id, w, ce) := p in
  let '(id', dv) := dv_p in
  id' = id /\
  eval_closed_cert_expr penv foracle ce = raise_ret dv /\
  wf_scalar_dvalue w dv.

Lemma phi_eval_pair_matches_prepend {Pa : Params} :
  forall allowed defs seen added fmap (penv : param_env Pa) pevals dvs,
    Forall (phi_eval_wf_entry allowed defs seen true) pevals ->
    (forall k z, In (k, z) added -> ~ In k seen) ->
    Forall2 (phi_eval_pair_matches penv (oracle_of_fmap fmap)) pevals dvs ->
    Forall2 (phi_eval_pair_matches penv (oracle_of_fmap (added ++ fmap))) pevals dvs.
Proof.
  intros allowed defs seen added fmap penv pevals dvs Hwf Hdisj Hfa2.
  revert dvs Hfa2.
  induction Hwf as [| [[id w] ce] rest (_ & _ & _ & Hlf & _ & Hfk) _ IH];
    intros dvs Hfa2; inversion Hfa2 as [| ? [id' dv] ? dvs_r [Heq [Hev Hsc]] Hfa2_r]; subst;
    [constructor |].
  constructor; [| exact (IH dvs_r Hfa2_r)].
  split; [reflexivity | split; [| exact Hsc]].
  exact (eq_trans (eval_let_free_prepend_fmap ce penv added fmap seen Hlf (Hfk eq_refl) Hdisj) Hev).
Qed.

Lemma apply_phi_env_matches {Pa : Params} :
  forall allowed defs seen uf (penv : param_env Pa) foracle smap env pevals dvs,
    env_matches_smap defs penv foracle smap env ->
    Forall (phi_eval_wf_entry allowed defs seen uf) pevals ->
    Forall2 (phi_eval_pair_matches penv foracle) pevals dvs ->
    env_matches_smap defs penv foracle (apply_phi_smap smap pevals) (apply_phi_env env dvs).
Proof.
  intros allowed defs seen uf penv foracle smap env pevals dvs Henv Hwf Hfa2.
  revert smap env Henv dvs Hfa2.
  induction Hwf as [| [[id w] ce] rest (Hid & _) _ IH];
    intros smap env Henv dvs Hfa2;
    inversion Hfa2 as [| ? [id' dv] ? dvs_r [-> [Hev Hsc]] Hfa2_r]; subst;
    cbn [apply_phi_smap apply_phi_env]; [exact Henv |].
  apply IH; [exact (env_matches_smap_add defs penv foracle smap env id w ce dv Henv Hid Hev Hsc) | exact Hfa2_r].
Qed.

Lemma apply_phi_env_preserves_nondefs {Pa : Params} :
  forall allowed defs seen uf (penv : param_env Pa) foracle (env : rmap (@dvalue Pa)) pevals dvs r,
    Forall (phi_eval_wf_entry allowed defs seen uf) pevals ->
    Forall2 (phi_eval_pair_matches penv foracle) pevals dvs ->
    ~ In r defs ->
    RM.find r (apply_phi_env env dvs) = RM.find r env.
Proof.
  intros allowed defs seen uf penv foracle env pevals dvs r Hwf Hfa2 Hnin.
  revert env dvs Hfa2.
  induction Hwf as [| [[id w] ce] rest (Hid & _) _ IH];
    intros env dvs Hfa2;
    inversion Hfa2 as [| ? [id' dv] ? dvs_r [-> _] Hfa2_r]; subst;
    cbn [apply_phi_env]; [reflexivity |].
  rewrite (IH (RM.add id dv env) dvs_r Hfa2_r).
  apply RMF.F.add_neq_o; intros ->; exact (Hnin Hid).
Qed.

Fixpoint reify_phi_evals
  (uf : bool)
  (params : list raw_id)
  (src_pnames : list string)
  (defs : list raw_id)
  (smap0 : rmap (positive * cert_expr))
  (bid_from : block_id)
  (seen : list freeze_key)
  (phis : list (local_id * phi dtyp * list (metadata dtyp)))
  : option (list (raw_id * positive * cert_expr) * list freeze_key) :=
  match phis with
  | [] => Some ([], seen)
  | (id, Phi _ dt pargs, _) :: rest =>
      if raw_id_in_list id defs then
        match dt, assoc bid_from pargs with
        | DTYPE_Base (DTYPE_I w), Some op =>
            match reify_exp uf params src_pnames defs smap0 seen
                    (Some (DTYPE_Base (DTYPE_I w))) op with
            | Some (_, ce, seen1) =>
                match reify_phi_evals uf params src_pnames defs smap0 bid_from seen1 rest with
                | Some (pevals, seen2) => Some ((id, w, ce) :: pevals, seen2)
                | None => None
                end
            | None => None
            end
        | _, _ => None
        end
      else None
  end.

Lemma reify_phi_evals_typing :
  forall phis uf params src_pnames defs allowed smap0 bid_from seen0 pevals seen2,
    wf_smap_entries allowed defs seen0 uf smap0 ->
    (forall id fm dt pargs md op idx w0 pnm,
      In (id, Phi fm dt pargs, md) phis ->
      In (bid_from, op) pargs ->
      In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some dt) op) ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w0) allowed) ->
    reify_phi_evals uf params src_pnames defs smap0 bid_from seen0 phis = Some (pevals, seen2) ->
    incl seen0 seen2 /\
    Forall (phi_eval_wf_entry allowed defs seen2 uf) pevals.
Proof.
  induction phis as [| [[id [fm dt pargs]] md] rest IH];
    intros uf params src_pnames defs allowed smap0 bid_from seen0 pevals seen2 Hsmap0 Hpu Hr;
    cbn [reify_phi_evals] in Hr.
  - inversion Hr; subst; split; [intros x Hx; exact Hx | constructor].
  - destruct (raw_id_in_list id defs) eqn:Hid; [| discriminate].
    apply raw_id_in_list_spec in Hid.
    destruct dt as [tb | |]; try discriminate; destruct tb as [w | | | | | | | | | |]; try discriminate.
    destruct (assoc bid_from pargs) as [op |] eqn:Hassoc; [| discriminate].
    pose proof (assoc_in_pargs bid_from pargs op Hassoc) as Hin_op.
    destruct (reify_exp uf params src_pnames defs smap0 seen0 (Some (DTYPE_Base (DTYPE_I w))) op)
      as [[[w1 ce] seen1] |] eqn:Hre; [| discriminate].
    destruct (reify_phi_evals uf params src_pnames defs smap0 bid_from seen1 rest)
      as [[pevals_r seen2'] |] eqn:Hrr; [| discriminate].
    inversion Hr; subst pevals seen2'; clear Hr.
    destruct (reify_exp_typing op uf params src_pnames defs allowed smap0 seen0
                (Some (DTYPE_Base (DTYPE_I w))) w1 ce seen1 Hsmap0
                (fun idx w0 pnm Hin => Hpu id fm (DTYPE_Base (DTYPE_I w)) pargs md op idx w0 pnm
                                         (or_introl eq_refl) Hin_op Hin) Hre)
      as (Hcw & Hwt & Hbw & Hlf & Hfv & Hinc01 & Hfk).
    apply check_opt_int_width_some_inv in Hcw; subst w1.
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 uf smap0 Hinc01 Hsmap0) as Hsmap1.
    destruct (IH uf params src_pnames defs allowed smap0 bid_from seen1 pevals_r seen2 Hsmap1
                (fun id' fm' dt' pargs' md' op' idx w0 pnm Hin_p =>
                   Hpu id' fm' dt' pargs' md' op' idx w0 pnm (or_intror Hin_p)) Hrr)
      as [Hinc12 Hfa_r].
    split; [intros x Hx; exact (Hinc12 x (Hinc01 x Hx)) |].
    constructor; [| exact Hfa_r].
    repeat split; try assumption.
    intros Huf u Hu; exact (Hinc12 u (Hfk Huf u Hu)).
Qed.

Lemma eval_reified_phi_map_src {Pa : Params} :
  forall phis params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
         (foracle : freeze_oracle) smap0 (env0 : rmap (@dvalue Pa))
         bid_from seen0 pevals seen2,
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length params ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall id fm dt pargs md op idx dt_u,
      In (id, Phi fm dt pargs, md) phis ->
      In (bid_from, op) pargs ->
      In (idx, dt_u) (exp_param_uses params defs (Some dt) op) ->
      nth_error arg_dtys idx = Some dt_u) ->
    (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env0 = Some dv) ->
    wf_smap_entries allowed defs seen0 false smap0 ->
    env_matches_smap defs (build_param_env src_pnames vs) foracle smap0 env0 ->
    reify_phi_evals false params src_pnames defs smap0 bid_from seen0 phis = Some (pevals, seen2) ->
    exists draws : list (dtyp * @dvalue Pa),
      Forall (fun '(dt, v) => valid_draw_value dt v) draws /\
      (((forall tail_s,
           cfg_steps_to_ub (chain_draws draws tail_s) env0
             (map_monad (m := CFGtop) (denote_phi bid_from) phis)) /\
        (forall k, eval_cfg_dag (build_param_env src_pnames vs) foracle (wrap_phi_evals pevals k) = DO_UB)) \/
       (exists dvs,
          Forall2 (phi_eval_pair_matches (build_param_env src_pnames vs) foracle) pevals dvs /\
          (forall k,
             eval_cfg_dag (build_param_env src_pnames vs) foracle (wrap_phi_evals pevals k) =
             eval_cfg_dag (build_param_env src_pnames vs) foracle k) /\
          (forall tail_s,
             cfg_steps_to_ret (chain_draws draws tail_s) env0
               (map_monad (m := CFGtop) (denote_phi bid_from) phis)
               tail_s env0 dvs))).
Proof.
  induction phis as [| [[id [fm dt pargs]] md] rest IH];
    intros params src_pnames defs allowed arg_dtys vs foracle smap0 env0 bid_from seen0 pevals seen2
           Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr;
    cbn [reify_phi_evals] in Hr.
  - inversion Hr; subst pevals seen2.
    exists []; split; [constructor | right; exists []].
    split; [constructor | split; [intros k; reflexivity | intros tail_s; apply CSR_Ret; reflexivity]].
  - destruct (raw_id_in_list id defs) eqn:Hid; [| discriminate].
    destruct dt as [tb | |]; try discriminate; destruct tb as [w | | | | | | | | | |]; try discriminate.
    destruct (assoc bid_from pargs) as [op |] eqn:Hassoc; [| discriminate].
    pose proof (assoc_in_pargs bid_from pargs op Hassoc) as Hin_op.
    destruct (reify_exp false params src_pnames defs smap0 seen0 (Some (DTYPE_Base (DTYPE_I w))) op)
      as [[[w1 ce] seen1] |] eqn:Hre; [| discriminate].
    destruct (reify_phi_evals false params src_pnames defs smap0 bid_from seen1 rest)
      as [[pevals_r seen2'] |] eqn:Hrr; [| discriminate].
    inversion Hr; subst pevals seen2'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hre)) as ->.
    destruct (eval_reified_exp_src op params src_pnames defs allowed arg_dtys vs foracle smap0 env0 seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu id fm (DTYPE_Base (DTYPE_I w)) pargs md op idx d
                                    (or_introl eq_refl) Hin_op Hin)
                Hpe Hwfs Henv Hre)
      as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
    + exists draws1; split; [exact Hfa1 | left; split].
      * intros tail_s; cbn [map_monad denote_phi]; rewrite Hassoc; unfold denote_exp'.
        apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub1 tail_s).
      * intros k; cbn [wrap_phi_evals eval_cfg_dag]; rewrite Hev1; reflexivity.
    + pose proof (wf_smap_entries_false_seen allowed defs seen0 seen1 smap0 Hwfs) as Hwfs1.
      destruct (IH params src_pnames defs allowed arg_dtys vs foracle smap0 env0 bid_from seen1 pevals_r seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun id' fm' dt' pargs' md' op' idx d Hin_p =>
                     Hpu id' fm' dt' pargs' md' op' idx d (or_intror Hin_p))
                  Hpe Hwfs1 Henv Hrr)
        as (draws2 & Hfa2 & [[Hub2 Hev_ub2] | [dvs_r [Hfa2_m [Hev_k Hst2]]]]).
      * exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | left; split].
        -- intros tail_s; rewrite chain_draws_app; cbn [map_monad denote_phi]; rewrite Hassoc; unfold denote_exp'.
           eapply cfg_steps_to_ub_bind_r.
           ++ eapply cfg_steps_to_ret_bind;
                [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst1 (chain_draws draws2 tail_s)))
                | apply CSR_Ret; reflexivity].
           ++ apply cfg_steps_to_ub_bind_l; exact (Hub2 tail_s).
        -- intros k; cbn [wrap_phi_evals eval_cfg_dag]; rewrite Hev1; exact (Hev_ub2 k).
      * exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | right].
        exists ((id, dv1) :: dvs_r); split; [| split].
        -- constructor; [split; [reflexivity | split; assumption] | exact Hfa2_m].
        -- intros k; cbn [wrap_phi_evals eval_cfg_dag]; rewrite Hev1; exact (Hev_k k).
        -- intros tail_s; rewrite chain_draws_app; cbn [map_monad denote_phi]; rewrite Hassoc; unfold denote_exp'.
           eapply cfg_steps_to_ret_bind.
           ++ eapply cfg_steps_to_ret_bind;
                [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst1 (chain_draws draws2 tail_s)))
                | apply CSR_Ret; reflexivity].
           ++ eapply cfg_steps_to_ret_bind; [exact (Hst2 tail_s) | apply CSR_Ret; reflexivity].
Qed.

Lemma eval_reified_phi_map_tgt {Pa : Params} :
  forall phis params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
         (sigma0 : @draw_strat Pa) (fmap0 : list (freeze_key * Z))
         smap0 (env0 : rmap (@dvalue Pa)) bid_from seen0 pevals seen2,
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length params ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall id fm dt pargs md op idx dt_u,
      In (id, Phi fm dt pargs, md) phis ->
      In (bid_from, op) pargs ->
      In (idx, dt_u) (exp_param_uses params defs (Some dt) op) ->
      nth_error arg_dtys idx = Some dt_u) ->
    (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env0 = Some dv) ->
    wf_draw_strat sigma0 ->
    wf_smap_entries allowed defs seen0 true smap0 ->
    env_matches_smap defs (build_param_env src_pnames vs) (oracle_of_fmap fmap0) smap0 env0 ->
    reify_phi_evals true params src_pnames defs smap0 bid_from seen0 phis = Some (pevals, seen2) ->
    exists added : list (freeze_key * Z),
      (forall key z, In (key, z) added -> In key seen2 /\ ~ In key seen0) /\
      ((forall k,
          eval_cfg_dag (build_param_env src_pnames vs)
            (oracle_of_fmap (added ++ fmap0)) (wrap_phi_evals pevals k) = DO_UB) \/
       (exists sigma1 dvs,
          wf_draw_strat sigma1 /\
          Forall2 (phi_eval_pair_matches (build_param_env src_pnames vs)
                     (oracle_of_fmap (added ++ fmap0))) pevals dvs /\
          (forall fmap_later k,
             (forall key z, In (key, z) fmap_later -> ~ In key seen2) ->
             eval_cfg_dag (build_param_env src_pnames vs)
               (oracle_of_fmap (fmap_later ++ added ++ fmap0)) (wrap_phi_evals pevals k) =
             eval_cfg_dag (build_param_env src_pnames vs)
               (oracle_of_fmap (fmap_later ++ added ++ fmap0)) k) /\
          cfg_steps_to_ret sigma0 env0
            (map_monad (m := CFGtop) (denote_phi bid_from) phis)
            sigma1 env0 dvs)).
Proof.
  induction phis as [| [[id [fm dt pargs]] md] rest IH];
    intros params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap0 env0 bid_from seen0 pevals seen2
           Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr;
    cbn [reify_phi_evals] in Hr.
  - inversion Hr; subst pevals seen2.
    exists []; split; [intros _ _ [] | right; exists sigma0, []].
    split; [exact Hwfd0 | split; [constructor | split; [intros _ k _; reflexivity | apply CSR_Ret; reflexivity]]].
  - destruct (raw_id_in_list id defs) eqn:Hid; [| discriminate].
    destruct dt as [tb | |]; try discriminate; destruct tb as [w | | | | | | | | | |]; try discriminate.
    destruct (assoc bid_from pargs) as [op |] eqn:Hassoc; [| discriminate].
    pose proof (assoc_in_pargs bid_from pargs op Hassoc) as Hin_op.
    destruct (reify_exp true params src_pnames defs smap0 seen0 (Some (DTYPE_Base (DTYPE_I w))) op)
      as [[[w1 ce] seen1] |] eqn:Hre; [| discriminate].
    destruct (reify_phi_evals true params src_pnames defs smap0 bid_from seen1 rest)
      as [[pevals_r seen2'] |] eqn:Hrr; [| discriminate].
    inversion Hr; subst pevals seen2'; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hre)) as ->.
    destruct (reify_exp_freeze_props op true params src_pnames defs allowed smap0 seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce seen1 Hwfs0 Hre)
      as (Hlf1 & Hinc01 & Hfk1).
    pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 true smap0 Hinc01 Hwfs0) as Hwfs1.
    assert (Hinc12 : incl seen1 seen2).
    { set (ext_vars :=
        allowed ++
        List.flat_map (fun '(_, Phi _ dt_p pargs_p, _) =>
          List.flat_map (fun '(_, e_p) =>
            List.flat_map (fun '(idx, dt_u) =>
              match dt_u, nth_error src_pnames idx with
              | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
              | _, _ => []
              end) (exp_param_uses params defs (Some dt_p) e_p)) pargs_p) rest).
      assert (Hsmap_ext : wf_smap_entries ext_vars defs seen1 true smap0).
      { intros r0 wr0 cer0 Hf0; destruct (Hwfs1 r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
        repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
      assert (Hpu_ext : forall id' fm' dt' pargs' md' op' idx w0 pnm,
        In (id', Phi fm' dt' pargs', md') rest ->
        In (bid_from, op') pargs' ->
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some dt') op') ->
        nth_error src_pnames idx = Some pnm ->
        In (pnm, w0) ext_vars).
      { intros id' fm' dt' pargs' md' op' idx w0 pnm Hin1 Hin2 Hin3 Hpnm.
        apply in_app_iff; right; apply in_flat_map; exists (id', Phi fm' dt' pargs', md'); split; [exact Hin1 |].
        apply in_flat_map; exists (bid_from, op'); split; [exact Hin2 |].
        apply in_flat_map; exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin3 | rewrite Hpnm; left; reflexivity]. }
      exact (proj1 (reify_phi_evals_typing rest true params src_pnames defs ext_vars smap0 bid_from
                      seen1 pevals_r seen2 Hsmap_ext Hpu_ext Hrr)). }
    destruct (eval_reified_exp_tgt op params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap0 env0 seen0
                (Some (DTYPE_Base (DTYPE_I w))) w ce seen1
                Hnd Hlp Hls Hla Hvs
                (fun idx d Hin => Hpu id fm (DTYPE_Base (DTYPE_I w)) pargs md op idx d
                                    (or_introl eq_refl) Hin_op Hin)
                Hpe Hwfd0 Hwfs0 Henv0 Hre)
      as (added1 & Had1 & [[msg1 Hev1] | (sigma_m & dv1 & Hwfd_m & Hev1 & Hsc1 & Hst1)]).
    + exists added1; split.
      * intros k z Hkz; destruct (Had1 k z Hkz) as [Hs1 Hn0]; split; [exact (Hinc12 k Hs1) | exact Hn0].
      * left; intros k; cbn [wrap_phi_evals eval_cfg_dag]; rewrite Hev1; reflexivity.
    + pose proof (env_matches_smap_oracle_prepend allowed defs seen0 added1 fmap0
                    (build_param_env src_pnames vs) smap0 env0 Hwfs0
                    (fun k z H => proj2 (Had1 k z H)) Henv0) as Henv1.
      destruct (IH params src_pnames defs allowed arg_dtys vs sigma_m (added1 ++ fmap0) smap0 env0 bid_from
                  seen1 pevals_r seen2 Hnd Hlp Hls Hla Hvs
                  (fun id' fm' dt' pargs' md' op' idx d Hin_p =>
                     Hpu id' fm' dt' pargs' md' op' idx d (or_intror Hin_p))
                  Hpe Hwfd_m Hwfs1 Henv1 Hrr)
        as (added2 & Had2 & [Hev_ub2 | (sigma2 & dvs_r & Hwfd2 & Hfa2_m & Hev_k & Hst2)]).
      * exists (added2 ++ added1).
        assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
          - destruct (Had2 k z Hk2) as [Hs2 Hn1]; split; [exact Hs2 | intros Hs0; exact (Hn1 (Hinc01 k Hs0))].
          - destruct (Had1 k z Hk1) as [Hs1 Hn0]; split; [exact (Hinc12 k Hs1) | exact Hn0]. }
        split; [exact Had12 | left; intros k].
        rewrite <- app_assoc.
        pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                      added2 (added1 ++ fmap0) seen1 Hlf1 (Hfk1 eq_refl)
                      (fun q z H => proj2 (Had2 q z H))) as Hev1'.
        cbn [wrap_phi_evals eval_cfg_dag]; rewrite Hev1', Hev1; exact (Hev_ub2 k).
      * exists (added2 ++ added1).
        assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
        { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
          - destruct (Had2 k z Hk2) as [Hs2 Hn1]; split; [exact Hs2 | intros Hs0; exact (Hn1 (Hinc01 k Hs0))].
          - destruct (Had1 k z Hk1) as [Hs1 Hn0]; split; [exact (Hinc12 k Hs1) | exact Hn0]. }
        split; [exact Had12 | right; exists sigma2, ((id, dv1) :: dvs_r)].
        pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                      added2 (added1 ++ fmap0) seen1 Hlf1 (Hfk1 eq_refl)
                      (fun q z H => proj2 (Had2 q z H))) as Hev1'.
        split; [exact Hwfd2 | split; [| split]].
        -- rewrite <- app_assoc; constructor;
             [split; [reflexivity | split; [rewrite Hev1'; exact Hev1 | exact Hsc1]] | exact Hfa2_m].
        -- intros fmap_later k Hdisj_lat.
           assert (Hdisj_lat1 : forall key z, In (key, z) (fmap_later ++ added2) -> ~ In key seen1).
           { intros key z Hkz; apply in_app_iff in Hkz as [Hl | Ha2].
             - intros Hs1; exact (Hdisj_lat key z Hl (Hinc12 key Hs1)).
             - exact (proj2 (Had2 key z Ha2)). }
           replace (fmap_later ++ (added2 ++ added1) ++ fmap0)
             with ((fmap_later ++ added2) ++ (added1 ++ fmap0))
             by (rewrite !app_assoc; reflexivity).
           pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                         (fmap_later ++ added2) (added1 ++ fmap0) seen1 Hlf1 (Hfk1 eq_refl) Hdisj_lat1)
             as Hev_lat1.
           cbn [wrap_phi_evals eval_cfg_dag]; rewrite Hev_lat1, Hev1.
           replace ((fmap_later ++ added2) ++ added1 ++ fmap0)
             with (fmap_later ++ (added2 ++ (added1 ++ fmap0)))
             by (rewrite !app_assoc; reflexivity).
           exact (Hev_k fmap_later k Hdisj_lat).
        -- cbn [map_monad denote_phi]; rewrite Hassoc; unfold denote_exp'.
           eapply cfg_steps_to_ret_bind.
           ++ eapply cfg_steps_to_ret_bind;
                [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ Hst1) | apply CSR_Ret; reflexivity].
           ++ eapply cfg_steps_to_ret_bind; [exact Hst2 | apply CSR_Ret; reflexivity].
Qed.

Fixpoint reify_code
  (uf : bool)
  (params : list raw_id)
  (src_pnames : list string)
  (defs : list raw_id)
  (smap : rmap (positive * cert_expr))
  (seen : list freeze_key)
  (c : code dtyp)
  : option (list (positive * cert_expr) * rmap (positive * cert_expr) * list freeze_key) :=
  match c with
  | [] => Some ([], smap, seen)
  | (IId id, INSTR_Op op, _) :: rest =>
      if raw_id_in_list id defs then
        match reify_exp uf params src_pnames defs smap seen None op with
        | Some (w, ce, seen1) =>
            let smap1 := RM.add id (w, ce) smap in
            match reify_code uf params src_pnames defs smap1 seen1 rest with
            | Some (cevals, smap2, seen2) =>
                Some ((w, ce) :: cevals, smap2, seen2)
            | None => None
            end
        | None => None
        end
      else None
  | (IVoid _, INSTR_Comment _, _) :: rest =>
      reify_code uf params src_pnames defs smap seen rest
  | _ :: _ => None
  end.

Lemma reify_code_typing :
  forall c uf params src_pnames defs allowed smap0 seen0 cevals smap2 seen2,
    wf_smap_entries allowed defs seen0 uf smap0 ->
    (forall iid op md idx w0 pnm,
      In (iid, INSTR_Op op, md) c ->
      In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs None op) ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w0) allowed) ->
    reify_code uf params src_pnames defs smap0 seen0 c = Some (cevals, smap2, seen2) ->
    incl seen0 seen2 /\
    wf_smap_entries allowed defs seen2 uf smap2 /\
    (forall k, wf_cfg_dag allowed k = true -> wf_cfg_dag allowed (wrap_evals cevals k) = true).
Proof.
  induction c as [| [[iid ins] md] rest IH];
    intros uf params src_pnames defs allowed smap0 seen0 cevals smap2 seen2 Hsmap0 Hpu Hr;
    cbn [reify_code] in Hr.
  - inversion Hr; subst; repeat split; [intros x Hx; exact Hx | exact Hsmap0 | intros k Hk; exact Hk].
  - destruct iid as [id | vid].
    + destruct ins; try discriminate.
      destruct (raw_id_in_list id defs) eqn:Hid; [| discriminate].
      apply raw_id_in_list_spec in Hid.
      destruct (reify_exp uf params src_pnames defs smap0 seen0 None op)
        as [[[w ce] seen1] |] eqn:Hre; [| discriminate].
      destruct (reify_code uf params src_pnames defs (RM.add id (w, ce) smap0) seen1 rest)
        as [[[cevals_r smap2'] seen2'] |] eqn:Hrr; [| discriminate].
      inversion Hr; subst cevals smap2' seen2'; clear Hr.
      destruct (reify_exp_typing op uf params src_pnames defs allowed smap0 seen0 None w ce seen1
                  Hsmap0
                  (fun idx w0 pnm Hin => Hpu (IId id) op md idx w0 pnm (or_introl eq_refl) Hin)
                  Hre)
        as (_ & Hwt & Hbw & Hlf & Hfv & Hinc01 & Hfk).
      pose proof (wf_smap_entries_seen_mono allowed defs seen0 seen1 uf smap0 Hinc01 Hsmap0) as Hsmap0'.
      pose proof (wf_smap_entries_add allowed defs seen1 uf smap0 id w ce Hsmap0'
                    Hid Hwt Hbw Hlf Hfv Hfk) as Hsmap1.
      destruct (IH uf params src_pnames defs allowed (RM.add id (w, ce) smap0) seen1
                  cevals_r smap2 seen2 Hsmap1
                  (fun iid' op' md' idx w0 pnm Hin_i => Hpu iid' op' md' idx w0 pnm (or_intror Hin_i))
                  Hrr)
        as (Hinc12 & Hsmap2 & Hwk).
      split; [intros x Hx; exact (Hinc12 x (Hinc01 x Hx)) | split; [exact Hsmap2 |]].
      intros k Hk; cbn [wrap_evals wf_cfg_dag].
      rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv), (Hwk k Hk); reflexivity.
    + destruct ins; try discriminate.
      exact (IH uf params src_pnames defs allowed smap0 seen0 cevals smap2 seen2 Hsmap0
               (fun iid' op' md' idx w0 pnm Hin_i => Hpu iid' op' md' idx w0 pnm (or_intror Hin_i)) Hr).
Qed.

Lemma eval_reified_code_src {Pa : Params} :
  forall c params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
         (foracle : freeze_oracle) smap0 (env0 : rmap (@dvalue Pa))
         seen0 cevals smap2 seen2,
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length params ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall iid op md idx dt_u,
      In (iid, INSTR_Op op, md) c ->
      In (idx, dt_u) (exp_param_uses params defs None op) ->
      nth_error arg_dtys idx = Some dt_u) ->
    (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env0 = Some dv) ->
    wf_smap_entries allowed defs seen0 false smap0 ->
    env_matches_smap defs (build_param_env src_pnames vs) foracle smap0 env0 ->
    reify_code false params src_pnames defs smap0 seen0 c = Some (cevals, smap2, seen2) ->
    exists draws : list (dtyp * @dvalue Pa),
      Forall (fun '(dt, v) => valid_draw_value dt v) draws /\
      (((forall tail_s,
           cfg_steps_to_ub (chain_draws draws tail_s) env0 (denote_code c None)) /\
        (forall k, eval_cfg_dag (build_param_env src_pnames vs) foracle (wrap_evals cevals k) = DO_UB)) \/
       (exists env2,
          (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
             exists dv, nth_error vs idx = Some dv /\ RM.find r env2 = Some dv) /\
          env_matches_smap defs (build_param_env src_pnames vs) foracle smap2 env2 /\
          (forall k,
             eval_cfg_dag (build_param_env src_pnames vs) foracle (wrap_evals cevals k) =
             eval_cfg_dag (build_param_env src_pnames vs) foracle k) /\
          (forall tail_s,
             cfg_steps_to_ret (chain_draws draws tail_s) env0 (denote_code c None) tail_s env2 tt))).
Proof.
  induction c as [| [[iid ins] md] rest IH];
    intros params src_pnames defs allowed arg_dtys vs foracle smap0 env0 seen0 cevals smap2 seen2
           Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfs Henv Hr;
    cbn [reify_code] in Hr.
  - inversion Hr; subst cevals smap2 seen2.
    exists []; split; [constructor | right; exists env0].
    split; [exact Hpe | split; [exact Henv | split; [intros k; reflexivity | intros tail_s; apply CSR_Ret; reflexivity]]].
  - destruct iid as [id | vid].
    + destruct ins; try discriminate.
      destruct (raw_id_in_list id defs) eqn:Hid; [| discriminate].
      apply raw_id_in_list_spec in Hid.
      destruct (reify_exp false params src_pnames defs smap0 seen0 None op)
        as [[[w ce] seen1] |] eqn:Hre; [| discriminate].
      destruct (reify_code false params src_pnames defs (RM.add id (w, ce) smap0) seen1 rest)
        as [[[cevals_r smap2'] seen2'] |] eqn:Hrr; [| discriminate].
      inversion Hr; subst cevals smap2' seen2'; clear Hr.
      destruct (eval_reified_exp_src op params src_pnames defs allowed arg_dtys vs foracle smap0 env0 seen0
                  None w ce seen1 Hnd Hlp Hls Hla Hvs
                  (fun idx d Hin => Hpu (IId id) op md idx d (or_introl eq_refl) Hin)
                  Hpe Hwfs Henv Hre)
        as (draws1 & Hfa1 & [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]]).
      * exists draws1; split; [exact Hfa1 | left; split].
        -- intros tail_s; unfold denote_code; cbn [loop_monad denote_instr]; unfold denote_exp'.
           apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub1 tail_s).
        -- intros k; cbn [wrap_evals eval_cfg_dag]; rewrite Hev1; reflexivity.
      * set (ext_vars :=
          allowed ++
          List.flat_map (fun '(idx, dt_u) =>
            match dt_u, nth_error src_pnames idx with
            | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
            | _, _ => []
            end) (exp_param_uses params defs None op)).
        assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 false smap0).
        { intros r0 wr0 cer0 Hf0; destruct (Hwfs r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
          repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
        assert (Hpu_ext : forall idx w0 pnm,
          In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs None op) ->
          nth_error src_pnames idx = Some pnm -> In (pnm, w0) ext_vars).
        { intros idx w0 pnm Hin Hpnm; apply in_app_iff; right; apply in_flat_map.
          exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin | rewrite Hpnm; left; reflexivity]. }
        destruct (reify_exp_typing op false params src_pnames defs ext_vars smap0 seen0 None w ce seen1
                    Hsmap_ext Hpu_ext Hre)
          as (_ & Hwt_ce & Hbw_ce & Hlf_ce & Hfv_ce & Hinc01 & Hfk_ce).
        pose proof (wf_smap_entries_seen_mono ext_vars defs seen0 seen1 false smap0 Hinc01 Hsmap_ext) as Hsmap_ext1.
        pose proof (wf_smap_entries_add ext_vars defs seen1 false smap0 id w ce Hsmap_ext1
                      Hid Hwt_ce Hbw_ce Hlf_ce Hfv_ce Hfk_ce) as Hwfs1.
        assert (Hpe1 : forall idx r, nth_error params idx = Some r -> ~ In r defs ->
          exists dv, nth_error vs idx = Some dv /\ RM.find r (RM.add id dv1 env0) = Some dv).
        { intros idx r Hnth Hnin; destruct (Hpe idx r Hnth Hnin) as [dv [Hv Hfe]].
          exists dv; split; [exact Hv | rewrite RMF.F.add_neq_o; [exact Hfe | intros ->; exact (Hnin Hid)]]. }
        pose proof (env_matches_smap_add defs (build_param_env src_pnames vs) foracle smap0 env0
                      id w ce dv1 Henv Hid Hev1 Hsc1) as Henv1.
        destruct (IH params src_pnames defs ext_vars arg_dtys vs foracle
                    (RM.add id (w, ce) smap0) (RM.add id dv1 env0) seen1 cevals_r smap2 seen2
                    Hnd Hlp Hls Hla Hvs
                    (fun iid' op' md' idx d Hin_i => Hpu iid' op' md' idx d (or_intror Hin_i))
                    Hpe1 Hwfs1 Henv1 Hrr)
          as (draws2 & Hfa2 & [[Hub2 Hev_ub2] | (env2 & Hpe2 & Henv2 & Hev_k & Hst2)]).
        -- exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | left; split].
           ++ intros tail_s; rewrite chain_draws_app; unfold denote_code; cbn [loop_monad denote_instr]; unfold denote_exp'.
              eapply cfg_steps_to_ub_bind_r.
              ** eapply cfg_steps_to_ret_bind;
                   [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst1 (chain_draws draws2 tail_s))) |].
                 eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite | apply CSR_Ret; reflexivity].
              ** exact (Hub2 tail_s).
           ++ intros k; cbn [wrap_evals eval_cfg_dag]; rewrite Hev1; exact (Hev_ub2 k).
        -- exists (draws1 ++ draws2); split; [apply Forall_app; split; assumption | right; exists env2].
           split; [exact Hpe2 | split; [exact Henv2 | split]].
           ++ intros k; cbn [wrap_evals eval_cfg_dag]; rewrite Hev1; exact (Hev_k k).
           ++ intros tail_s; rewrite chain_draws_app; unfold denote_code; cbn [loop_monad denote_instr]; unfold denote_exp'.
              eapply cfg_steps_to_ret_bind.
              ** eapply cfg_steps_to_ret_bind;
                   [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst1 (chain_draws draws2 tail_s))) |].
                 eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite | apply CSR_Ret; reflexivity].
              ** exact (Hst2 tail_s).
    + destruct ins; try discriminate.
      destruct (IH params src_pnames defs allowed arg_dtys vs foracle smap0 env0 seen0 cevals smap2 seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun iid' op' md' idx d Hin_i => Hpu iid' op' md' idx d (or_intror Hin_i))
                  Hpe Hwfs Henv Hr)
        as (draws2 & Hfa2 & [[Hub2 Hev_ub2] | (env2 & Hpe2 & Henv2 & Hev_k & Hst2)]).
      * exists draws2; split; [exact Hfa2 | left; split].
        -- intros tail_s; unfold denote_code; cbn [loop_monad denote_instr].
           eapply cfg_steps_to_ub_bind_r; [apply CSR_Ret; reflexivity | exact (Hub2 tail_s)].
        -- exact Hev_ub2.
      * exists draws2; split; [exact Hfa2 | right; exists env2].
        split; [exact Hpe2 | split; [exact Henv2 | split; [exact Hev_k |]]].
        intros tail_s; unfold denote_code; cbn [loop_monad denote_instr].
        eapply cfg_steps_to_ret_bind; [apply CSR_Ret; reflexivity | exact (Hst2 tail_s)].
Qed.

Lemma reify_code_wf_smap :
  forall c uf params src_pnames defs allowed smap0 seen0 cevals smap2 seen2,
    wf_smap_entries allowed defs seen0 uf smap0 ->
    reify_code uf params src_pnames defs smap0 seen0 c = Some (cevals, smap2, seen2) ->
    exists ext_vars,
      incl seen0 seen2 /\
      wf_smap_entries ext_vars defs seen2 uf smap2.
Proof.
  intros c uf params src_pnames defs allowed smap0 seen0 cevals smap2 seen2 Hsmap0 Hr.
  set (ext_vars :=
    allowed ++
    List.flat_map (fun '(_, ins, _) =>
      match ins with
      | INSTR_Op op =>
          List.flat_map (fun '(idx, dt_u) =>
            match dt_u, nth_error src_pnames idx with
            | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
            | _, _ => []
            end) (exp_param_uses params defs None op)
      | _ => []
      end) c).
  assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 uf smap0).
  { intros r0 wr0 cer0 Hf0; destruct (Hsmap0 r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
    repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
  assert (Hpu_ext : forall iid op md idx w0 pnm,
    In (iid, INSTR_Op op, md) c ->
    In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs None op) ->
    nth_error src_pnames idx = Some pnm ->
    In (pnm, w0) ext_vars).
  { intros iid op md idx w0 pnm Hin1 Hin2 Hpnm.
    apply in_app_iff; right; apply in_flat_map; exists (iid, INSTR_Op op, md); split; [exact Hin1 |].
    apply in_flat_map; exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin2 | rewrite Hpnm; left; reflexivity]. }
  destruct (reify_code_typing c uf params src_pnames defs ext_vars smap0 seen0 cevals smap2 seen2
              Hsmap_ext Hpu_ext Hr)
    as (Hinc & Hsmap2 & _).
  exists ext_vars; split; assumption.
Qed.

Lemma reify_phi_evals_wf_smap :
  forall phis uf params src_pnames defs allowed smap0 bid_from seen0 pevals seen2,
    wf_smap_entries allowed defs seen0 uf smap0 ->
    reify_phi_evals uf params src_pnames defs smap0 bid_from seen0 phis = Some (pevals, seen2) ->
    exists ext_vars,
      incl seen0 seen2 /\
      Forall (phi_eval_wf_entry ext_vars defs seen2 uf) pevals /\
      wf_smap_entries ext_vars defs seen2 uf (apply_phi_smap smap0 pevals).
Proof.
  intros phis uf params src_pnames defs allowed smap0 bid_from seen0 pevals seen2 Hsmap0 Hr.
  set (ext_vars :=
    allowed ++
    List.flat_map (fun '(_, Phi _ dt_p pargs_p, _) =>
      List.flat_map (fun '(_, e_p) =>
        List.flat_map (fun '(idx, dt_u) =>
          match dt_u, nth_error src_pnames idx with
          | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
          | _, _ => []
          end) (exp_param_uses params defs (Some dt_p) e_p)) pargs_p) phis).
  assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 uf smap0).
  { intros r0 wr0 cer0 Hf0; destruct (Hsmap0 r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
    repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
  assert (Hpu_ext : forall id' fm' dt' pargs' md' op' idx w0 pnm,
    In (id', Phi fm' dt' pargs', md') phis ->
    In (bid_from, op') pargs' ->
    In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs (Some dt') op') ->
    nth_error src_pnames idx = Some pnm ->
    In (pnm, w0) ext_vars).
  { intros id' fm' dt' pargs' md' op' idx w0 pnm Hin1 Hin2 Hin3 Hpnm.
    apply in_app_iff; right; apply in_flat_map; exists (id', Phi fm' dt' pargs', md'); split; [exact Hin1 |].
    apply in_flat_map; exists (bid_from, op'); split; [exact Hin2 |].
    apply in_flat_map; exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin3 | rewrite Hpnm; left; reflexivity]. }
  destruct (reify_phi_evals_typing phis uf params src_pnames defs ext_vars smap0 bid_from
              seen0 pevals seen2 Hsmap_ext Hpu_ext Hr)
    as [Hinc Hfa].
  pose proof (wf_smap_entries_seen_mono ext_vars defs seen0 seen2 uf smap0 Hinc Hsmap_ext) as Hsmap2.
  exists ext_vars; split; [exact Hinc | split; [exact Hfa | exact (apply_phi_smap_wf _ _ _ _ _ _ Hsmap2 Hfa)]].
Qed.

Lemma eval_reified_code_tgt {Pa : Params} :
  forall c params src_pnames defs allowed arg_dtys (vs : list (@dvalue Pa))
         (sigma0 : @draw_strat Pa) (fmap0 : list (freeze_key * Z))
         smap0 (env0 : rmap (@dvalue Pa)) seen0 cevals smap2 seen2,
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length params ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall iid op md idx dt_u,
      In (iid, INSTR_Op op, md) c ->
      In (idx, dt_u) (exp_param_uses params defs None op) ->
      nth_error arg_dtys idx = Some dt_u) ->
    (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env0 = Some dv) ->
    wf_draw_strat sigma0 ->
    wf_smap_entries allowed defs seen0 true smap0 ->
    env_matches_smap defs (build_param_env src_pnames vs) (oracle_of_fmap fmap0) smap0 env0 ->
    reify_code true params src_pnames defs smap0 seen0 c = Some (cevals, smap2, seen2) ->
    exists added : list (freeze_key * Z),
      (forall key z, In (key, z) added -> In key seen2 /\ ~ In key seen0) /\
      ((forall k,
          eval_cfg_dag (build_param_env src_pnames vs)
            (oracle_of_fmap (added ++ fmap0)) (wrap_evals cevals k) = DO_UB) \/
       (exists sigma2 env2,
          wf_draw_strat sigma2 /\
          (forall idx r, nth_error params idx = Some r -> ~ In r defs ->
             exists dv, nth_error vs idx = Some dv /\ RM.find r env2 = Some dv) /\
          env_matches_smap defs (build_param_env src_pnames vs)
            (oracle_of_fmap (added ++ fmap0)) smap2 env2 /\
          (forall fmap_later k,
             (forall key z, In (key, z) fmap_later -> ~ In key seen2) ->
             eval_cfg_dag (build_param_env src_pnames vs)
               (oracle_of_fmap (fmap_later ++ added ++ fmap0)) (wrap_evals cevals k) =
             eval_cfg_dag (build_param_env src_pnames vs)
               (oracle_of_fmap (fmap_later ++ added ++ fmap0)) k) /\
          cfg_steps_to_ret sigma0 env0 (denote_code c None) sigma2 env2 tt)).
Proof.
  induction c as [| [[iid ins] md] rest IH];
    intros params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap0 env0 seen0 cevals smap2 seen2
           Hnd Hlp Hls Hla Hvs Hpu Hpe Hwfd0 Hwfs0 Henv0 Hr;
    cbn [reify_code] in Hr.
  - inversion Hr; subst cevals smap2 seen2.
    exists []; split; [intros _ _ [] | right; exists sigma0, env0].
    split; [exact Hwfd0 | split; [exact Hpe | split; [exact Henv0 |
      split; [intros _ k _; reflexivity | apply CSR_Ret; reflexivity]]]].
  - destruct iid as [id | vid].
    + destruct ins; try discriminate.
      destruct (raw_id_in_list id defs) eqn:Hid; [| discriminate].
      apply raw_id_in_list_spec in Hid.
      destruct (reify_exp true params src_pnames defs smap0 seen0 None op)
        as [[[w ce] seen1] |] eqn:Hre; [| discriminate].
      destruct (reify_code true params src_pnames defs (RM.add id (w, ce) smap0) seen1 rest)
        as [[[cevals_r smap2'] seen2'] |] eqn:Hrr; [| discriminate].
      inversion Hr; subst cevals smap2' seen2'; clear Hr.
      set (ext_vars :=
        allowed ++
        List.flat_map (fun '(idx, dt_u) =>
          match dt_u, nth_error src_pnames idx with
          | DTYPE_Base (DTYPE_I w0), Some pnm => [(pnm, w0)]
          | _, _ => []
          end) (exp_param_uses params defs None op)).
      assert (Hsmap_ext : wf_smap_entries ext_vars defs seen0 true smap0).
      { intros r0 wr0 cer0 Hf0; destruct (Hwfs0 r0 wr0 cer0 Hf0) as (H1 & H2 & H3 & H4 & H5 & H6).
        repeat split; try assumption; intros u Hu; apply in_app_iff; left; exact (H5 u Hu). }
      assert (Hpu_ext : forall idx w0 pnm,
        In (idx, DTYPE_Base (DTYPE_I w0)) (exp_param_uses params defs None op) ->
        nth_error src_pnames idx = Some pnm -> In (pnm, w0) ext_vars).
      { intros idx w0 pnm Hin Hpnm; apply in_app_iff; right; apply in_flat_map.
        exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin | rewrite Hpnm; left; reflexivity]. }
      destruct (reify_exp_typing op true params src_pnames defs ext_vars smap0 seen0 None w ce seen1
                  Hsmap_ext Hpu_ext Hre)
        as (_ & Hwt_ce & Hbw_ce & Hlf_ce & Hfv_ce & Hinc01 & Hfk_ce).
      pose proof (wf_smap_entries_seen_mono ext_vars defs seen0 seen1 true smap0 Hinc01 Hsmap_ext) as Hsmap_ext1.
      pose proof (wf_smap_entries_add ext_vars defs seen1 true smap0 id w ce Hsmap_ext1
                    Hid Hwt_ce Hbw_ce Hlf_ce Hfv_ce Hfk_ce) as Hwfs1.
      destruct (reify_code_wf_smap rest true params src_pnames defs ext_vars
                  (RM.add id (w, ce) smap0) seen1 cevals_r smap2 seen2 Hwfs1 Hrr)
        as (_ & Hinc12 & _).
      destruct (eval_reified_exp_tgt op params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap0 env0 seen0
                  None w ce seen1 Hnd Hlp Hls Hla Hvs
                  (fun idx d Hin => Hpu (IId id) op md idx d (or_introl eq_refl) Hin)
                  Hpe Hwfd0 Hwfs0 Henv0 Hre)
        as (added1 & Had1 & [[msg1 Hev1] | (sigma1 & dv1 & Hwfd1 & Hev1 & Hsc1 & Hst1)]).
      * exists added1; split.
        -- intros k z Hkz; destruct (Had1 k z Hkz) as [Hs1 Hn0]; split; [exact (Hinc12 k Hs1) | exact Hn0].
        -- left; intros k; cbn [wrap_evals eval_cfg_dag]; rewrite Hev1; reflexivity.
      * pose proof (env_matches_smap_oracle_prepend allowed defs seen0 added1 fmap0
                      (build_param_env src_pnames vs) smap0 env0 Hwfs0
                      (fun k z H => proj2 (Had1 k z H)) Henv0) as Henv0'.
        pose proof (env_matches_smap_add defs (build_param_env src_pnames vs) (oracle_of_fmap (added1 ++ fmap0))
                      smap0 env0 id w ce dv1 Henv0' Hid Hev1 Hsc1) as Henv1.
        assert (Hpe1 : forall idx r, nth_error params idx = Some r -> ~ In r defs ->
          exists dv, nth_error vs idx = Some dv /\ RM.find r (RM.add id dv1 env0) = Some dv).
        { intros idx r Hnth Hnin; destruct (Hpe idx r Hnth Hnin) as [dv [Hv Hfe]].
          exists dv; split; [exact Hv | rewrite RMF.F.add_neq_o; [exact Hfe | intros ->; exact (Hnin Hid)]]. }
        destruct (IH params src_pnames defs ext_vars arg_dtys vs sigma1 (added1 ++ fmap0)
                    (RM.add id (w, ce) smap0) (RM.add id dv1 env0) seen1 cevals_r smap2 seen2
                    Hnd Hlp Hls Hla Hvs
                    (fun iid' op' md' idx d Hin_i => Hpu iid' op' md' idx d (or_intror Hin_i))
                    Hpe1 Hwfd1 Hwfs1 Henv1 Hrr)
          as (added2 & Had2 & [Hev_ub2 | (sigma2 & env2 & Hwfd2 & Hpe2 & Henv2 & Hev_k & Hst2)]).
        -- exists (added2 ++ added1).
           assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
           { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
             - destruct (Had2 k z Hk2) as [Hs2 Hn1]; split; [exact Hs2 | intros Hs0; exact (Hn1 (Hinc01 k Hs0))].
             - destruct (Had1 k z Hk1) as [Hs1 Hn0]; split; [exact (Hinc12 k Hs1) | exact Hn0]. }
           split; [exact Had12 | left; intros k].
           rewrite <- app_assoc.
           pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                         added2 (added1 ++ fmap0) seen1 Hlf_ce (Hfk_ce eq_refl)
                         (fun q z H => proj2 (Had2 q z H))) as Hev1'.
           cbn [wrap_evals eval_cfg_dag]; rewrite Hev1', Hev1; exact (Hev_ub2 k).
        -- exists (added2 ++ added1).
           assert (Had12 : forall k z, In (k, z) (added2 ++ added1) -> In k seen2 /\ ~ In k seen0).
           { intros k z Hkz; apply in_app_iff in Hkz as [Hk2 | Hk1].
             - destruct (Had2 k z Hk2) as [Hs2 Hn1]; split; [exact Hs2 | intros Hs0; exact (Hn1 (Hinc01 k Hs0))].
             - destruct (Had1 k z Hk1) as [Hs1 Hn0]; split; [exact (Hinc12 k Hs1) | exact Hn0]. }
           split; [exact Had12 | right; exists sigma2, env2].
           split; [exact Hwfd2 | split; [exact Hpe2 | split; [rewrite <- app_assoc; exact Henv2 | split]]].
           ++ intros fmap_later k Hdisj_lat.
              assert (Hdisj_lat1 : forall key z, In (key, z) (fmap_later ++ added2) -> ~ In key seen1).
              { intros key z Hkz; apply in_app_iff in Hkz as [Hl | Ha2].
                - intros Hs1; exact (Hdisj_lat key z Hl (Hinc12 key Hs1)).
                - exact (proj2 (Had2 key z Ha2)). }
              replace (fmap_later ++ (added2 ++ added1) ++ fmap0)
                with ((fmap_later ++ added2) ++ (added1 ++ fmap0))
                by (rewrite !app_assoc; reflexivity).
              pose proof (eval_let_free_prepend_fmap ce (build_param_env src_pnames vs)
                            (fmap_later ++ added2) (added1 ++ fmap0) seen1 Hlf_ce (Hfk_ce eq_refl) Hdisj_lat1)
                as Hev_lat1.
              cbn [wrap_evals eval_cfg_dag]; rewrite Hev_lat1, Hev1.
              replace ((fmap_later ++ added2) ++ added1 ++ fmap0)
                with (fmap_later ++ (added2 ++ (added1 ++ fmap0)))
                by (rewrite !app_assoc; reflexivity).
              exact (Hev_k fmap_later k Hdisj_lat).
           ++ unfold denote_code; cbn [loop_monad denote_instr]; unfold denote_exp'.
              eapply cfg_steps_to_ret_bind.
              ** eapply cfg_steps_to_ret_bind;
                   [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ Hst1) |].
                 eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite | apply CSR_Ret; reflexivity].
              ** exact Hst2.
    + destruct ins; try discriminate.
      destruct (IH params src_pnames defs allowed arg_dtys vs sigma0 fmap0 smap0 env0 seen0 cevals smap2 seen2
                  Hnd Hlp Hls Hla Hvs
                  (fun iid' op' md' idx d Hin_i => Hpu iid' op' md' idx d (or_intror Hin_i))
                  Hpe Hwfd0 Hwfs0 Henv0 Hr)
        as (added2 & Had2 & [Hev_ub2 | (sigma2 & env2 & Hwfd2 & Hpe2 & Henv2 & Hev_k & Hst2)]).
      * exists added2; split; [exact Had2 | left; exact Hev_ub2].
      * exists added2; split; [exact Had2 | right; exists sigma2, env2].
        split; [exact Hwfd2 | split; [exact Hpe2 | split; [exact Henv2 | split; [exact Hev_k |]]]].
        unfold denote_code; cbn [loop_monad denote_instr].
        eapply cfg_steps_to_ret_bind; [apply CSR_Ret; reflexivity | exact Hst2].
Qed.

Fixpoint summarize_ocfg_dag
  (fuel : nat)
  (uf : bool)
  (params : list raw_id)
  (src_pnames : list string)
  (defs : list raw_id)
  (bmap : rmap (block dtyp))
  (is_entry : bool)
  (bid_from bid_cur : block_id)
  (smap : rmap (positive * cert_expr))
  (seen : list freeze_key)
  {struct fuel} : option cfg_dag :=
  match fuel with
  | O => None
  | S fuel' =>
      match RM.find bid_cur bmap with
      | None => None
      | Some b =>
          if is_entry && negb (list_empty_b (blk_phis b)) then None
          else
            match reify_phi_evals uf params src_pnames defs smap bid_from seen (blk_phis b) with
            | None => None
            | Some (pevals, seen_p) =>
                let smap_p := apply_phi_smap smap pevals in
                match reify_code uf params src_pnames defs smap_p seen_p (blk_code b) with
                | None => None
                | Some (cevals, smap_c, seen_c) =>
                    let wrap_blk := fun d_term =>
                      wrap_phi_evals pevals (wrap_evals cevals d_term) in
                    match blk_term b with
                    | (_, TERM_Unreachable, _) =>
                        Some (wrap_blk CD_Unreachable)
                    | (_, TERM_Ret_void, _) =>
                        Some (wrap_blk CD_RetVoid)
                    | (_, TERM_Ret (DTYPE_Base (DTYPE_I w), op), _) =>
                        match reify_exp uf params src_pnames defs smap_c seen_c
                                (Some (DTYPE_Base (DTYPE_I w))) op with
                        | Some (_, ce_ret, _) =>
                            Some (wrap_blk (CD_RetScalar w ce_ret))
                        | None => None
                        end
                    | (_, TERM_Br_1 br, _) =>
                        match summarize_ocfg_dag fuel' uf params src_pnames defs bmap
                                false bid_cur br smap_c seen_c with
                        | Some d_next => Some (wrap_blk d_next)
                        | None => None
                        end
                    | (_, TERM_Br (DTYPE_Base (DTYPE_I 1%positive), op) br1 br2, _) =>
                        match reify_exp uf params src_pnames defs smap_c seen_c
                                (Some (DTYPE_Base (DTYPE_I 1%positive))) op with
                        | Some (_, ce_cond, seen_br) =>
                            match summarize_ocfg_dag fuel' uf params src_pnames defs bmap
                                    false bid_cur br1 smap_c seen_br,
                                  summarize_ocfg_dag fuel' uf params src_pnames defs bmap
                                    false bid_cur br2 smap_c seen_br with
                            | Some d_t, Some d_f =>
                                Some (wrap_blk (CD_Branch ce_cond d_t d_f))
                            | _, _ => None
                            end
                        | None => None
                        end
                    | _ => None
                    end
                end
            end
      end
  end.

Definition summarize_cfg_dag
  (uf : bool) (G : CFG.cfg dtyp) (src_pnames : list string) : option cfg_dag :=
  summarize_ocfg_dag
    (S (List.length (blks G)))
    uf
    (args G)
    src_pnames
    (defined_ids_of_cfg G)
    (ocfg_map (blks G))
    true
    (init G)
    (init G)
    (RM.empty _)
    [].

Lemma block_param_uses_phi_in :
  forall params defs b id fm dt pargs md bid_from op u,
    In (id, Phi fm dt pargs, md) (blk_phis b) ->
    In (bid_from, op) pargs ->
    In u (exp_param_uses params defs (Some dt) op) ->
    In u (block_param_uses params defs b).
Proof.
  intros params defs b id fm dt pargs md bid_from op u Hphi Hparg Hu.
  unfold block_param_uses; apply in_app_iff; left.
  apply in_flat_map; exists (id, Phi fm dt pargs, md); split; [exact Hphi |].
  apply in_flat_map; exists (bid_from, op); split; assumption.
Qed.

Lemma block_param_uses_code_in :
  forall params defs b iid op md u,
    In (iid, INSTR_Op op, md) (blk_code b) ->
    In u (exp_param_uses params defs None op) ->
    In u (block_param_uses params defs b).
Proof.
  intros params defs b iid op md u Hc Hu.
  unfold block_param_uses; apply in_app_iff; right; apply in_app_iff; left.
  apply in_flat_map; exists (iid, INSTR_Op op, md); split; assumption.
Qed.

Lemma block_param_uses_ret_in :
  forall params defs b iid dt op md u,
    blk_term b = (iid, TERM_Ret (dt, op), md) ->
    In u (exp_param_uses params defs (Some dt) op) ->
    In u (block_param_uses params defs b).
Proof.
  intros params defs b iid dt op md u Ht Hu.
  unfold block_param_uses; apply in_app_iff; right; apply in_app_iff; right.
  rewrite Ht; exact Hu.
Qed.

Lemma block_param_uses_br_in :
  forall params defs b iid dt op br1 br2 md u,
    blk_term b = (iid, TERM_Br (dt, op) br1 br2, md) ->
    In u (exp_param_uses params defs (Some dt) op) ->
    In u (block_param_uses params defs b).
Proof.
  intros params defs b iid dt op br1 br2 md u Ht Hu.
  unfold block_param_uses; apply in_app_iff; right; apply in_app_iff; right.
  rewrite Ht; exact Hu.
Qed.

Lemma summarize_ocfg_dag_wf :
  forall fuel uf G src_pnames allowed is_entry bid_from bid_cur smap seen d,
    (forall idx w0 pnm,
      In (idx, DTYPE_Base (DTYPE_I w0)) (param_idx_uses_cfg G) ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w0) allowed) ->
    wf_smap_entries allowed (defined_ids_of_cfg G) seen uf smap ->
    summarize_ocfg_dag fuel uf (args G) src_pnames (defined_ids_of_cfg G)
      (ocfg_map (blks G)) is_entry bid_from bid_cur smap seen = Some d ->
    wf_cfg_dag allowed d = true.
Proof.
  induction fuel as [| fuel' IH];
    intros uf G src_pnames allowed is_entry bid_from bid_cur smap seen d Hpu_cfg Hsmap Hr;
    cbn [summarize_ocfg_dag] in Hr; [discriminate |].
  destruct (RM.find bid_cur (ocfg_map (blks G))) as [b |] eqn:Hfb; [| discriminate].
  pose proof (ocfg_map_in (blks G) bid_cur b Hfb) as Hb_in.
  destruct (is_entry && negb (list_empty_b (blk_phis b))); [discriminate |].
  destruct (reify_phi_evals uf (args G) src_pnames (defined_ids_of_cfg G) smap bid_from seen (blk_phis b))
    as [[pevals seen_p] |] eqn:Hr_phis; [| discriminate].
  destruct (reify_phi_evals_typing (blk_phis b) uf (args G) src_pnames (defined_ids_of_cfg G) allowed
              smap bid_from seen pevals seen_p Hsmap
              (fun id fm dt pargs md op idx w0 pnm Hphi Hparg Hu Hpnm =>
                 Hpu_cfg idx w0 pnm
                   (proj2 (in_flat_map _ (blks G) _)
                     (ex_intro _ b (conj Hb_in (block_param_uses_phi_in _ _ b id fm dt pargs md bid_from op _ Hphi Hparg Hu))))
                   Hpnm)
              Hr_phis)
    as [Hinc_sp Hfa_p].
  pose proof (apply_phi_smap_wf allowed (defined_ids_of_cfg G) seen_p uf pevals smap
                (wf_smap_entries_seen_mono _ _ _ _ _ _ Hinc_sp Hsmap) Hfa_p) as Hsmap_p.
  destruct (reify_code uf (args G) src_pnames (defined_ids_of_cfg G) (apply_phi_smap smap pevals) seen_p (blk_code b))
    as [[[cevals smap_c] seen_c] |] eqn:Hr_code; [| discriminate].
  destruct (reify_code_typing (blk_code b) uf (args G) src_pnames (defined_ids_of_cfg G) allowed
              (apply_phi_smap smap pevals) seen_p cevals smap_c seen_c Hsmap_p
              (fun iid op md idx w0 pnm Hc Hu Hpnm =>
                 Hpu_cfg idx w0 pnm
                   (proj2 (in_flat_map _ (blks G) _)
                     (ex_intro _ b (conj Hb_in (block_param_uses_code_in _ _ b iid op md _ Hc Hu))))
                   Hpnm)
              Hr_code)
    as (_ & Hsmap_c & Hwrap_c).
  assert (Hwrap_blk : forall dt_k,
    wf_cfg_dag allowed dt_k = true ->
    wf_cfg_dag allowed (wrap_phi_evals pevals (wrap_evals cevals dt_k)) = true).
  { intros dt_k Hdtk; exact (wrap_phi_evals_wf _ _ _ _ _ _ Hfa_p (Hwrap_c dt_k Hdtk)). }
  destruct (blk_term b) as [[tiid tm] tmd] eqn:Htm.
  destruct tm; try discriminate.
  - (* TERM_Ret *)
    destruct v as [dt op].
    destruct dt as [tb | |]; try discriminate; destruct tb as [w | | | | | | | | | |]; try discriminate.
    destruct (reify_exp uf (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                (Some (DTYPE_Base (DTYPE_I w))) op)
      as [[[w1 ce_ret] seen_ret] |] eqn:Hr_ret; [| discriminate].
    inversion Hr; subst d; clear Hr.
    destruct (reify_exp_typing op uf (args G) src_pnames (defined_ids_of_cfg G) allowed smap_c seen_c
                (Some (DTYPE_Base (DTYPE_I w))) w1 ce_ret seen_ret Hsmap_c
                (fun idx w0 pnm Hu Hpnm =>
                   Hpu_cfg idx w0 pnm
                     (proj2 (in_flat_map _ (blks G) _)
                       (ex_intro _ b (conj Hb_in (block_param_uses_ret_in _ _ b tiid _ op tmd _ Htm Hu))))
                     Hpnm)
                Hr_ret)
      as (Hcw & Hwt & Hbw & Hlf & Hfv & _ & _).
    apply check_opt_int_width_some_inv in Hcw; subst w1.
    apply Hwrap_blk; cbn [wf_cfg_dag].
    rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv); reflexivity.
  - (* TERM_Ret_void *)
    inversion Hr; subst d; apply Hwrap_blk; reflexivity.
  - (* TERM_Br *)
    destruct v as [dt op].
    destruct dt as [tb | |]; try discriminate; destruct tb as [wc | | | | | | | | | |]; try discriminate.
    destruct wc as [| |]; try discriminate.
    destruct (reify_exp uf (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                (Some (DTYPE_Base (DTYPE_I 1%positive))) op)
      as [[[wc' ce_cond] seen_br] |] eqn:Hr_cond; [| discriminate].
    destruct (summarize_ocfg_dag fuel' uf (args G) src_pnames (defined_ids_of_cfg G)
                (ocfg_map (blks G)) false bid_cur br1 smap_c seen_br)
      as [d_t |] eqn:Hr_t; [| discriminate].
    destruct (summarize_ocfg_dag fuel' uf (args G) src_pnames (defined_ids_of_cfg G)
                (ocfg_map (blks G)) false bid_cur br2 smap_c seen_br)
      as [d_f |] eqn:Hr_f; [| discriminate].
    inversion Hr; subst d; clear Hr.
    destruct (reify_exp_typing op uf (args G) src_pnames (defined_ids_of_cfg G) allowed smap_c seen_c
                (Some (DTYPE_Base (DTYPE_I 1%positive))) wc' ce_cond seen_br Hsmap_c
                (fun idx w0 pnm Hu Hpnm =>
                   Hpu_cfg idx w0 pnm
                     (proj2 (in_flat_map _ (blks G) _)
                       (ex_intro _ b (conj Hb_in (block_param_uses_br_in _ _ b tiid _ op br1 br2 tmd _ Htm Hu))))
                     Hpnm)
                Hr_cond)
      as (Hcw & Hwt & Hbw & Hlf & Hfv & Hinc_br & _).
    apply check_opt_int_width_some_inv in Hcw; subst wc'.
    pose proof (wf_smap_entries_seen_mono _ _ _ _ _ _ Hinc_br Hsmap_c) as Hsmap_br.
    pose proof (IH uf G src_pnames allowed false bid_cur br1 smap_c seen_br d_t Hpu_cfg Hsmap_br Hr_t) as Hwft.
    pose proof (IH uf G src_pnames allowed false bid_cur br2 smap_c seen_br d_f Hpu_cfg Hsmap_br Hr_f) as Hwff.
    apply Hwrap_blk; cbn [wf_cfg_dag].
    rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv), Hwft, Hwff; reflexivity.
  - (* TERM_Br_1 *)
    destruct (summarize_ocfg_dag fuel' uf (args G) src_pnames (defined_ids_of_cfg G)
                (ocfg_map (blks G)) false bid_cur br smap_c seen_c)
      as [d_next |] eqn:Hr_n; [| discriminate].
    inversion Hr; subst d.
    apply Hwrap_blk; exact (IH uf G src_pnames allowed false bid_cur br smap_c seen_c d_next Hpu_cfg Hsmap_c Hr_n).
  - (* TERM_Unreachable *)
    inversion Hr; subst d; apply Hwrap_blk; reflexivity.
Qed.

Lemma summarize_cfg_dag_wf :
  forall uf G src_pnames allowed d,
    (forall idx w0 pnm,
      In (idx, DTYPE_Base (DTYPE_I w0)) (param_idx_uses_cfg G) ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w0) allowed) ->
    summarize_cfg_dag uf G src_pnames = Some d ->
    wf_cfg_dag allowed d = true.
Proof.
  intros uf G src_pnames allowed d Hpu Hr.
  exact (summarize_ocfg_dag_wf (S (List.length (blks G))) uf G src_pnames allowed
           true (init G) (init G) (RM.empty _) [] d Hpu
           (wf_smap_entries_empty allowed (defined_ids_of_cfg G) [] uf) Hr).
Qed.

Lemma denote_ocfg_map_step_obs {Pa : Params} :
  forall (bmap : rmap (block dtyp)) (bid_from bid_cur : block_id) (b : block dtyp),
    RM.find bid_cur bmap = Some b ->
    observe (@denote_ocfg_map Pa bmap None (bid_from, bid_cur)) =
    observe (ITree.bind
      (ITree.bind (denote_block b bid_from None)
        (fun bd => match bd with
                   | inr dv => Ret (inr (inr dv))
                   | inl bid_target => Ret (inl (bid_cur, bid_target))
                   end))
      (fun lr => match lr with
                 | inl j => Tau (denote_ocfg_map bmap None j)
                 | inr r => Ret r
                 end)).
Proof.
  intros bmap bid_from bid_cur b Hf.
  unfold denote_ocfg_map; rewrite observe_iter; cbn beta; rewrite Hf; reflexivity.
Qed.

Lemma cfg_param_dtyp_compatible_nth :
  forall G arg_dtys idx dt,
    cfg_param_dtyp_compatible G arg_dtys = true ->
    In (idx, dt) (param_idx_uses_cfg G) ->
    nth_error arg_dtys idx = Some dt.
Proof.
  intros G arg_dtys idx dt Hcomp Hin.
  unfold cfg_param_dtyp_compatible in Hcomp; rewrite forallb_forall in Hcomp.
  pose proof (Hcomp (idx, dt) Hin) as Hidx.
  destruct (nth_error arg_dtys idx) as [dt_a |] eqn:Hnth; [| discriminate Hidx].
  apply dtyp_eqb_dec_eq in Hidx; subst dt_a; reflexivity.
Qed.

Lemma summarize_ocfg_src_sound {Pa : Params} :
  forall fuel G src_pnames allowed arg_dtys (vs : list (@dvalue Pa))
         (foracle : freeze_oracle) is_entry bid_from bid_cur
         smap (env : rmap (@dvalue Pa)) seen d,
    NoDup src_pnames ->
    List.length (args G) = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length (args G) ->
    cfg_param_dtyp_compatible G arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx r, nth_error (args G) idx = Some r -> ~ In r (defined_ids_of_cfg G) ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env = Some dv) ->
    wf_smap_entries allowed (defined_ids_of_cfg G) seen false smap ->
    env_matches_smap (defined_ids_of_cfg G) (build_param_env src_pnames vs) foracle smap env ->
    summarize_ocfg_dag fuel false (args G) src_pnames (defined_ids_of_cfg G)
      (ocfg_map (blks G)) is_entry bid_from bid_cur smap seen = Some d ->
    exists draws : list (dtyp * @dvalue Pa),
      Forall (fun '(dt, v) => valid_draw_value dt v) draws /\
      (((forall tail_s,
           cfg_steps_to_ub (chain_draws draws tail_s) env
             (denote_ocfg_map (ocfg_map (blks G)) None (bid_from, bid_cur))) /\
        eval_cfg_dag (build_param_env src_pnames vs) foracle d = DO_UB) \/
       (exists env_out dv,
          eval_cfg_dag (build_param_env src_pnames vs) foracle d = DO_Ret dv /\
          (forall tail_s,
             cfg_steps_to_ret (chain_draws draws tail_s) env
               (denote_ocfg_map (ocfg_map (blks G)) None (bid_from, bid_cur))
               tail_s env_out (inr dv)))).
Proof.
  induction fuel as [| fuel' IH];
    intros G src_pnames allowed arg_dtys vs foracle is_entry bid_from bid_cur smap env seen d
           Hnd Hlp Hls Hla Hcomp Hvs Hpe Hwfs Henv Hr;
    cbn [summarize_ocfg_dag] in Hr; [discriminate |].
  destruct (RM.find bid_cur (ocfg_map (blks G))) as [b |] eqn:Hfb; [| discriminate].
  pose proof (ocfg_map_in (blks G) bid_cur b Hfb) as Hb_in.
  destruct (is_entry && negb (list_empty_b (blk_phis b))); [discriminate |].
  destruct (reify_phi_evals false (args G) src_pnames (defined_ids_of_cfg G) smap bid_from seen (blk_phis b))
    as [[pevals seen_p] |] eqn:Hr_phis; [| discriminate].
  destruct (reify_code false (args G) src_pnames (defined_ids_of_cfg G)
              (apply_phi_smap smap pevals) seen_p (blk_code b))
    as [[[cevals smap_c] seen_c] |] eqn:Hr_code; [| discriminate].
  destruct (eval_reified_phi_map_src (blk_phis b) (args G) src_pnames (defined_ids_of_cfg G)
              allowed arg_dtys vs foracle smap env bid_from seen pevals seen_p
              Hnd Hlp Hls Hla Hvs
              (fun id fm dt pargs md op idx dt_u Hphi Hparg Hu =>
                 cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                   (proj2 (in_flat_map _ (blks G) _)
                     (ex_intro _ b (conj Hb_in (block_param_uses_phi_in _ _ b id fm dt pargs md bid_from op _ Hphi Hparg Hu)))))
              Hpe Hwfs Henv Hr_phis)
    as (draws_p & Hfa_dp & [[Hub_p Hev_ub_p] | (dvs_p & Hpm_p & Hev_kp & Hst_p)]).
  - exists draws_p; split; [exact Hfa_dp | left; split].
    + intros tail_s.
      eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
      unfold denote_block, denote_phis.
      apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l.
      exact (Hub_p tail_s).
    + destruct (blk_term b) as [[tiid tm] tmd]; destruct tm; try discriminate.
      * destruct v as [[tb | |] op]; try discriminate; destruct tb; try discriminate.
        destruct (reify_exp _ _ _ _ _ _ _ op) as [[[_ _] _] |]; [inversion Hr; subst; apply Hev_ub_p | discriminate].
      * inversion Hr; subst; apply Hev_ub_p.
      * destruct v as [[[| | ] | |] op]; try discriminate.
        destruct (reify_exp _ _ _ _ _ _ _ op) as [[[_ _] _] |]; [| discriminate].
        destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ br1 _ _); [| discriminate].
        destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ br2 _ _); [inversion Hr; subst; apply Hev_ub_p | discriminate].
      * destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ br _ _); [inversion Hr; subst; apply Hev_ub_p | discriminate].
      * inversion Hr; subst; apply Hev_ub_p.
  - destruct (reify_phi_evals_wf_smap (blk_phis b) false (args G) src_pnames (defined_ids_of_cfg G)
                allowed smap bid_from seen pevals seen_p Hwfs Hr_phis)
      as (ext_p & _ & Hfa_wf_p & Hwfs_p).
    pose proof (apply_phi_env_matches ext_p (defined_ids_of_cfg G) seen_p false
                  (build_param_env src_pnames vs) foracle smap env pevals dvs_p
                  Henv Hfa_wf_p Hpm_p) as Henv_p.
    assert (Hpe_p : forall idx r, nth_error (args G) idx = Some r -> ~ In r (defined_ids_of_cfg G) ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r (apply_phi_env env dvs_p) = Some dv).
    { intros idx r Hnth Hnin; destruct (Hpe idx r Hnth Hnin) as [dv [Hv Hfe]].
      exists dv; split; [exact Hv |].
      rewrite (apply_phi_env_preserves_nondefs ext_p (defined_ids_of_cfg G) seen_p false
                 (build_param_env src_pnames vs) foracle env pevals dvs_p r Hfa_wf_p Hpm_p Hnin);
        exact Hfe. }
    assert (Hphis_step : forall tail_s,
      cfg_steps_to_ret (chain_draws draws_p tail_s) env
        (denote_phis bid_from (blk_phis b)) tail_s (apply_phi_env env dvs_p) tt).
    { intros tail_s; unfold denote_phis.
      eapply cfg_steps_to_ret_bind; [exact (Hst_p tail_s) |].
      eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite_list | apply CSR_Ret; reflexivity]. }
    destruct (eval_reified_code_src (blk_code b) (args G) src_pnames (defined_ids_of_cfg G)
                ext_p arg_dtys vs foracle (apply_phi_smap smap pevals) (apply_phi_env env dvs_p)
                seen_p cevals smap_c seen_c Hnd Hlp Hls Hla Hvs
                (fun iid op md idx dt_u Hc Hu =>
                   cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                     (proj2 (in_flat_map _ (blks G) _)
                       (ex_intro _ b (conj Hb_in (block_param_uses_code_in _ _ b iid op md _ Hc Hu)))))
                Hpe_p Hwfs_p Henv_p Hr_code)
      as (draws_c & Hfa_dc & [[Hub_c Hev_ub_c] | (env_c & Hpe_c & Henv_c & Hev_kc & Hst_c)]).
    + exists (draws_p ++ draws_c); split; [apply Forall_app; split; assumption | left; split].
      * intros tail_s; rewrite chain_draws_app.
        eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
        unfold denote_block.
        apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l.
        eapply cfg_steps_to_ub_bind_r; [exact (Hphis_step (chain_draws draws_c tail_s)) |].
        apply cfg_steps_to_ub_bind_l; exact (Hub_c tail_s).
      * destruct (blk_term b) as [[tiid tm] tmd]; destruct tm; try discriminate.
        -- destruct v as [[tb | |] op]; try discriminate; destruct tb; try discriminate.
           destruct (reify_exp _ _ _ _ _ _ _ op) as [[[_ _] _] |]; [| discriminate].
           inversion Hr; subst; rewrite Hev_kp; apply Hev_ub_c.
        -- inversion Hr; subst; rewrite Hev_kp; apply Hev_ub_c.
        -- destruct v as [[[| | ] | |] op]; try discriminate.
           destruct (reify_exp _ _ _ _ _ _ _ op) as [[[_ _] _] |]; [| discriminate].
           destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ br1 _ _); [| discriminate].
           destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ br2 _ _); [| discriminate].
           inversion Hr; subst; rewrite Hev_kp; apply Hev_ub_c.
        -- destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ br _ _); [| discriminate].
           inversion Hr; subst; rewrite Hev_kp; apply Hev_ub_c.
        -- inversion Hr; subst; rewrite Hev_kp; apply Hev_ub_c.
    + destruct (reify_code_wf_smap (blk_code b) false (args G) src_pnames (defined_ids_of_cfg G)
                  ext_p (apply_phi_smap smap pevals) seen_p cevals smap_c seen_c Hwfs_p Hr_code)
        as (ext_c & _ & Hwfs_c).
      destruct (blk_term b) as [[tiid tm] tmd] eqn:Htm.
      destruct tm; try discriminate.
      * (* TERM_Ret *)
        destruct v as [dt op].
        destruct dt as [tb | |]; try discriminate; destruct tb as [w | | | | | | | | | |]; try discriminate.
        destruct (reify_exp false (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                    (Some (DTYPE_Base (DTYPE_I w))) op)
          as [[[w1 ce_ret] seen_ret] |] eqn:Hr_ret; [| discriminate].
        inversion Hr; subst d; clear Hr.
        pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr_ret)) as ->.
        destruct (eval_reified_exp_src op (args G) src_pnames (defined_ids_of_cfg G)
                    ext_c arg_dtys vs foracle smap_c env_c seen_c
                    (Some (DTYPE_Base (DTYPE_I w))) w ce_ret seen_ret
                    Hnd Hlp Hls Hla Hvs
                    (fun idx dt_u Hu =>
                       cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                         (proj2 (in_flat_map _ (blks G) _)
                           (ex_intro _ b (conj Hb_in (block_param_uses_ret_in _ _ b tiid _ op tmd _ Htm Hu)))))
                    Hpe_c Hwfs_c Henv_c Hr_ret)
          as (draws_r & Hfa_dr & [[Hub_r [msg_r Hev_r]] | [dv_r [Hev_r [_ Hst_r]]]]).
        -- exists ((draws_p ++ draws_c) ++ draws_r).
           split; [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dr] | left; split].
           ++ intros tail_s; rewrite !chain_draws_app.
              eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
              unfold denote_block; rewrite Htm.
              apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l.
              eapply cfg_steps_to_ub_bind_r; [exact (Hphis_step (chain_draws draws_c (chain_draws draws_r tail_s))) |].
              eapply cfg_steps_to_ub_bind_r; [exact (Hst_c (chain_draws draws_r tail_s)) |].
              cbn [denote_terminator]; unfold denote_exp'.
              apply cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub_r tail_s).
           ++ rewrite Hev_kp, Hev_kc; cbn [eval_cfg_dag]; rewrite Hev_r; reflexivity.
        -- exists ((draws_p ++ draws_c) ++ draws_r).
           split; [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dr] | right].
           exists env_c, dv_r; split.
           ++ rewrite Hev_kp, Hev_kc; cbn [eval_cfg_dag]; rewrite Hev_r; reflexivity.
           ++ intros tail_s; rewrite !chain_draws_app.
              eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
              unfold denote_block; rewrite Htm.
              eapply cfg_steps_to_ret_bind.
              ** eapply cfg_steps_to_ret_bind.
                 --- eapply cfg_steps_to_ret_bind; [exact (Hphis_step (chain_draws draws_c (chain_draws draws_r tail_s))) |].
                     eapply cfg_steps_to_ret_bind; [exact (Hst_c (chain_draws draws_r tail_s)) |].
                     cbn [denote_terminator]; unfold denote_exp'.
                     eapply cfg_steps_to_ret_bind;
                       [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst_r tail_s)) | apply CSR_Ret; reflexivity].
                 --- apply CSR_Ret; reflexivity.
              ** apply CSR_Ret; reflexivity.
      * (* TERM_Ret_void *)
        inversion Hr; subst d; clear Hr.
        exists (draws_p ++ draws_c); split; [apply Forall_app; split; assumption | right].
        exists env_c, NONE; split; [rewrite Hev_kp, Hev_kc; reflexivity |].
        intros tail_s; rewrite chain_draws_app.
        eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
        unfold denote_block; rewrite Htm.
        eapply cfg_steps_to_ret_bind.
        -- eapply cfg_steps_to_ret_bind.
           ++ eapply cfg_steps_to_ret_bind; [exact (Hphis_step (chain_draws draws_c tail_s)) |].
              eapply cfg_steps_to_ret_bind; [exact (Hst_c tail_s) | apply CSR_Ret; reflexivity].
           ++ apply CSR_Ret; reflexivity.
        -- apply CSR_Ret; reflexivity.
      * (* TERM_Br *)
        destruct v as [dt op].
        destruct dt as [tb | |]; try discriminate; destruct tb as [wc | | | | | | | | | |]; try discriminate.
        destruct wc as [| |]; try discriminate.
        destruct (reify_exp false (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                    (Some (DTYPE_Base (DTYPE_I 1%positive))) op)
          as [[[wc' ce_cond] seen_br] |] eqn:Hr_cond; [| discriminate].
        destruct (summarize_ocfg_dag fuel' false (args G) src_pnames (defined_ids_of_cfg G)
                    (ocfg_map (blks G)) false bid_cur br1 smap_c seen_br)
          as [d_t |] eqn:Hr_t; [| discriminate].
        destruct (summarize_ocfg_dag fuel' false (args G) src_pnames (defined_ids_of_cfg G)
                    (ocfg_map (blks G)) false bid_cur br2 smap_c seen_br)
          as [d_f |] eqn:Hr_f; [| discriminate].
        inversion Hr; subst d; clear Hr.
        pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr_cond)) as ->.
        destruct (eval_reified_exp_src op (args G) src_pnames (defined_ids_of_cfg G)
                    ext_c arg_dtys vs foracle smap_c env_c seen_c
                    (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive ce_cond seen_br
                    Hnd Hlp Hls Hla Hvs
                    (fun idx dt_u Hu =>
                       cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                         (proj2 (in_flat_map _ (blks G) _)
                           (ex_intro _ b (conj Hb_in (block_param_uses_br_in _ _ b tiid _ op br1 br2 tmd _ Htm Hu)))))
                    Hpe_c Hwfs_c Henv_c Hr_cond)
          as (draws_br & Hfa_dbr & [[Hub_br [msg_br Hev_br]] | [dv_br [Hev_br [Hsc_br Hst_br]]]]).
        -- exists ((draws_p ++ draws_c) ++ draws_br).
           split; [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dbr] | left; split].
           ++ intros tail_s; rewrite !chain_draws_app.
              eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
              unfold denote_block; rewrite Htm.
              apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l.
              eapply cfg_steps_to_ub_bind_r; [exact (Hphis_step (chain_draws draws_c (chain_draws draws_br tail_s))) |].
              eapply cfg_steps_to_ub_bind_r; [exact (Hst_c (chain_draws draws_br tail_s)) |].
              cbn [denote_terminator]; unfold denote_exp'.
              apply cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub_br tail_s).
           ++ rewrite Hev_kp, Hev_kc; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
        -- destruct Hsc_br as [-> | [cbit ->]].
           ++ exists ((draws_p ++ draws_c) ++ draws_br).
              split; [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dbr] | left; split].
              ** intros tail_s; rewrite !chain_draws_app.
                 eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
                 unfold denote_block; rewrite Htm.
                 apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l.
                 eapply cfg_steps_to_ub_bind_r; [exact (Hphis_step (chain_draws draws_c (chain_draws draws_br tail_s))) |].
                 eapply cfg_steps_to_ub_bind_r; [exact (Hst_c (chain_draws draws_br tail_s)) |].
                 cbn [denote_terminator]; unfold denote_exp'.
                 eapply cfg_steps_to_ub_bind_r;
                   [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst_br tail_s)) | eapply CSU_UB; reflexivity].
              ** rewrite Hev_kp, Hev_kc; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
           ++ pose proof (wf_smap_entries_false_seen ext_c (defined_ids_of_cfg G) seen_c seen_br smap_c Hwfs_c) as Hwfs_br.
              destruct (@Integers.unsigned 1 cbit =? 1)%Z eqn:Ecbit.
              ** destruct (IH G src_pnames ext_c arg_dtys vs foracle false bid_cur br1 smap_c env_c seen_br d_t
                             Hnd Hlp Hls Hla Hcomp Hvs Hpe_c Hwfs_br Henv_c Hr_t)
                   as (draws_n & Hfa_dn & [[Hub_n Hev_ub_n] | [env_out [dv_out [Hev_out Hst_n]]]]).
                 --- exists (((draws_p ++ draws_c) ++ draws_br) ++ draws_n).
                     split;
                       [apply Forall_app; split;
                          [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dbr] | exact Hfa_dn]
                       | left; split].
                     +++ intros tail_s; rewrite !chain_draws_app.
                         eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
                         unfold denote_block; rewrite Htm.
                         eapply cfg_steps_to_ub_bind_r.
                         *** eapply cfg_steps_to_ret_bind.
                             ---- eapply cfg_steps_to_ret_bind;
                                    [exact (Hphis_step (chain_draws draws_c (chain_draws draws_br (chain_draws draws_n tail_s)))) |].
                                  eapply cfg_steps_to_ret_bind;
                                    [exact (Hst_c (chain_draws draws_br (chain_draws draws_n tail_s))) |].
                                  cbn [denote_terminator]; unfold denote_exp'.
                                  eapply cfg_steps_to_ret_bind;
                                    [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst_br (chain_draws draws_n tail_s))) |].
                                  rewrite bit_int_1_equ_one_eq_unsigned, Ecbit; apply CSR_Ret; reflexivity.
                             ---- apply CSR_Ret; reflexivity.
                         *** eapply CSU_Tau; [reflexivity | exact (Hub_n tail_s)].
                     +++ rewrite Hev_kp, Hev_kc; cbn [eval_cfg_dag]; rewrite Hev_br, Ecbit; exact Hev_ub_n.
                 --- exists (((draws_p ++ draws_c) ++ draws_br) ++ draws_n).
                     split;
                       [apply Forall_app; split;
                          [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dbr] | exact Hfa_dn]
                       | right; exists env_out, dv_out; split].
                     +++ rewrite Hev_kp, Hev_kc; cbn [eval_cfg_dag]; rewrite Hev_br, Ecbit; exact Hev_out.
                     +++ intros tail_s; rewrite !chain_draws_app.
                         eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
                         unfold denote_block; rewrite Htm.
                         eapply cfg_steps_to_ret_bind.
                         *** eapply cfg_steps_to_ret_bind.
                             ---- eapply cfg_steps_to_ret_bind;
                                    [exact (Hphis_step (chain_draws draws_c (chain_draws draws_br (chain_draws draws_n tail_s)))) |].
                                  eapply cfg_steps_to_ret_bind;
                                    [exact (Hst_c (chain_draws draws_br (chain_draws draws_n tail_s))) |].
                                  cbn [denote_terminator]; unfold denote_exp'.
                                  eapply cfg_steps_to_ret_bind;
                                    [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst_br (chain_draws draws_n tail_s))) |].
                                  rewrite bit_int_1_equ_one_eq_unsigned, Ecbit; apply CSR_Ret; reflexivity.
                             ---- apply CSR_Ret; reflexivity.
                         *** eapply CSR_Tau; [reflexivity | exact (Hst_n tail_s)].
              ** destruct (IH G src_pnames ext_c arg_dtys vs foracle false bid_cur br2 smap_c env_c seen_br d_f
                             Hnd Hlp Hls Hla Hcomp Hvs Hpe_c Hwfs_br Henv_c Hr_f)
                   as (draws_n & Hfa_dn & [[Hub_n Hev_ub_n] | [env_out [dv_out [Hev_out Hst_n]]]]).
                 --- exists (((draws_p ++ draws_c) ++ draws_br) ++ draws_n).
                     split;
                       [apply Forall_app; split;
                          [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dbr] | exact Hfa_dn]
                       | left; split].
                     +++ intros tail_s; rewrite !chain_draws_app.
                         eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
                         unfold denote_block; rewrite Htm.
                         eapply cfg_steps_to_ub_bind_r.
                         *** eapply cfg_steps_to_ret_bind.
                             ---- eapply cfg_steps_to_ret_bind;
                                    [exact (Hphis_step (chain_draws draws_c (chain_draws draws_br (chain_draws draws_n tail_s)))) |].
                                  eapply cfg_steps_to_ret_bind;
                                    [exact (Hst_c (chain_draws draws_br (chain_draws draws_n tail_s))) |].
                                  cbn [denote_terminator]; unfold denote_exp'.
                                  eapply cfg_steps_to_ret_bind;
                                    [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst_br (chain_draws draws_n tail_s))) |].
                                  rewrite bit_int_1_equ_one_eq_unsigned, Ecbit; apply CSR_Ret; reflexivity.
                             ---- apply CSR_Ret; reflexivity.
                         *** eapply CSU_Tau; [reflexivity | exact (Hub_n tail_s)].
                     +++ rewrite Hev_kp, Hev_kc; cbn [eval_cfg_dag]; rewrite Hev_br, Ecbit; exact Hev_ub_n.
                 --- exists (((draws_p ++ draws_c) ++ draws_br) ++ draws_n).
                     split;
                       [apply Forall_app; split;
                          [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dbr] | exact Hfa_dn]
                       | right; exists env_out, dv_out; split].
                     +++ rewrite Hev_kp, Hev_kc; cbn [eval_cfg_dag]; rewrite Hev_br, Ecbit; exact Hev_out.
                     +++ intros tail_s; rewrite !chain_draws_app.
                         eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
                         unfold denote_block; rewrite Htm.
                         eapply cfg_steps_to_ret_bind.
                         *** eapply cfg_steps_to_ret_bind.
                             ---- eapply cfg_steps_to_ret_bind;
                                    [exact (Hphis_step (chain_draws draws_c (chain_draws draws_br (chain_draws draws_n tail_s)))) |].
                                  eapply cfg_steps_to_ret_bind;
                                    [exact (Hst_c (chain_draws draws_br (chain_draws draws_n tail_s))) |].
                                  cbn [denote_terminator]; unfold denote_exp'.
                                  eapply cfg_steps_to_ret_bind;
                                    [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst_br (chain_draws draws_n tail_s))) |].
                                  rewrite bit_int_1_equ_one_eq_unsigned, Ecbit; apply CSR_Ret; reflexivity.
                             ---- apply CSR_Ret; reflexivity.
                         *** eapply CSR_Tau; [reflexivity | exact (Hst_n tail_s)].
      * (* TERM_Br_1 *)
        destruct (summarize_ocfg_dag fuel' false (args G) src_pnames (defined_ids_of_cfg G)
                    (ocfg_map (blks G)) false bid_cur br smap_c seen_c)
          as [d_next |] eqn:Hr_n; [| discriminate].
        inversion Hr; subst d; clear Hr.
        destruct (IH G src_pnames ext_c arg_dtys vs foracle false bid_cur br smap_c env_c seen_c d_next
                    Hnd Hlp Hls Hla Hcomp Hvs Hpe_c Hwfs_c Henv_c Hr_n)
          as (draws_n & Hfa_dn & [[Hub_n Hev_ub_n] | [env_out [dv_out [Hev_out Hst_n]]]]).
        -- exists ((draws_p ++ draws_c) ++ draws_n).
           split; [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dn] | left; split].
           ++ intros tail_s; rewrite !chain_draws_app.
              eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
              unfold denote_block; rewrite Htm.
              eapply cfg_steps_to_ub_bind_r.
              ** eapply cfg_steps_to_ret_bind.
                 --- eapply cfg_steps_to_ret_bind; [exact (Hphis_step (chain_draws draws_c (chain_draws draws_n tail_s))) |].
                     eapply cfg_steps_to_ret_bind; [exact (Hst_c (chain_draws draws_n tail_s)) | apply CSR_Ret; reflexivity].
                 --- apply CSR_Ret; reflexivity.
              ** eapply CSU_Tau; [reflexivity | exact (Hub_n tail_s)].
           ++ rewrite Hev_kp, Hev_kc; exact Hev_ub_n.
        -- exists ((draws_p ++ draws_c) ++ draws_n).
           split; [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dn] | right].
           exists env_out, dv_out; split; [rewrite Hev_kp, Hev_kc; exact Hev_out |].
           intros tail_s; rewrite !chain_draws_app.
           eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
           unfold denote_block; rewrite Htm.
           eapply cfg_steps_to_ret_bind.
           ++ eapply cfg_steps_to_ret_bind.
              ** eapply cfg_steps_to_ret_bind; [exact (Hphis_step (chain_draws draws_c (chain_draws draws_n tail_s))) |].
                 eapply cfg_steps_to_ret_bind; [exact (Hst_c (chain_draws draws_n tail_s)) | apply CSR_Ret; reflexivity].
              ** apply CSR_Ret; reflexivity.
           ++ eapply CSR_Tau; [reflexivity | exact (Hst_n tail_s)].
      * (* TERM_Unreachable *)
        inversion Hr; subst d; clear Hr.
        exists (draws_p ++ draws_c); split; [apply Forall_app; split; assumption | left; split].
        -- intros tail_s; rewrite chain_draws_app.
           eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
           unfold denote_block; rewrite Htm.
           apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l.
           eapply cfg_steps_to_ub_bind_r; [exact (Hphis_step (chain_draws draws_c tail_s)) |].
           eapply cfg_steps_to_ub_bind_r; [exact (Hst_c tail_s) | eapply CSU_UB; reflexivity].
        -- rewrite Hev_kp, Hev_kc; reflexivity.
Qed.

Lemma summarize_src_dag_sound {Pa : Params} :
  forall G src_pnames arg_dtys (vs : list (@dvalue Pa)) (foracle : freeze_oracle) d,
    NoDup (args G) ->
    NoDup src_pnames ->
    List.length src_pnames = List.length (args G) ->
    List.length arg_dtys = List.length (args G) ->
    cfg_param_dtyp_compatible G arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    summarize_cfg_dag false G src_pnames = Some d ->
    exists sigma_src : @draw_strat Pa,
      wf_draw_strat sigma_src /\
      ((cfg_steps_to_ub sigma_src (init_cfg_locals (args G) vs) (denote_cfg G None) /\
        eval_cfg_dag (build_param_env src_pnames vs) foracle d = DO_UB) \/
       (exists sigma_src' env_out dv,
          eval_cfg_dag (build_param_env src_pnames vs) foracle d = DO_Ret dv /\
          cfg_steps_to_ret sigma_src (init_cfg_locals (args G) vs) (denote_cfg G None)
            sigma_src' env_out dv)).
Proof.
  intros G src_pnames arg_dtys vs foracle d Hnd_p Hnd_s Hlen_sp Hlen_da Hcomp Hvs Hr.
  assert (Hlen_vs : List.length vs = List.length arg_dtys) by exact (Forall2_length Hvs).
  assert (Hlp : List.length (args G) = List.length vs) by lia.
  assert (Hls : List.length src_pnames = List.length vs) by lia.
  assert (Hpe0 : forall idx r, nth_error (args G) idx = Some r -> ~ In r (defined_ids_of_cfg G) ->
    exists dv, nth_error vs idx = Some dv /\ RM.find r (init_cfg_locals (args G) vs) = Some dv).
  { intros idx r Hnth _; exact (init_cfg_locals_nth (args G) vs idx r Hnd_p Hlp Hnth). }
  destruct (summarize_ocfg_src_sound (S (List.length (blks G))) G src_pnames [] arg_dtys vs foracle
              true (init G) (init G) (RM.empty _) (init_cfg_locals (args G) vs) [] d
              Hnd_s Hlp Hls Hlen_da Hcomp Hvs Hpe0
              (wf_smap_entries_empty [] (defined_ids_of_cfg G) [] false)
              (env_matches_smap_empty (defined_ids_of_cfg G) (build_param_env src_pnames vs)
                 foracle (init_cfg_locals (args G) vs))
              Hr)
    as (draws & Hfa & [[Hub Hev_ub] | [env_out [dv [Hev_ret Hst_ret]]]]).
  - exists (chain_draws draws default_draw_strat).
    split; [exact (chain_draws_wf draws default_draw_strat Hfa default_draw_strat_wf) | left; split; [| exact Hev_ub]].
    unfold denote_cfg, denote_cfg_map; apply cfg_steps_to_ub_bind_l; exact (Hub default_draw_strat).
  - exists (chain_draws draws default_draw_strat).
    split; [exact (chain_draws_wf draws default_draw_strat Hfa default_draw_strat_wf) | right].
    exists default_draw_strat, env_out, dv; split; [exact Hev_ret |].
    unfold denote_cfg, denote_cfg_map.
    eapply cfg_steps_to_ret_bind; [exact (Hst_ret default_draw_strat) | apply CSR_Ret; reflexivity].
Qed.

Lemma summarize_ocfg_tgt_sound {Pa : Params} :
  forall fuel G src_pnames allowed arg_dtys (vs : list (@dvalue Pa))
         (sigma0 : @draw_strat Pa) (fmap0 : list (freeze_key * Z))
         is_entry bid_from bid_cur smap (env : rmap (@dvalue Pa)) seen0 d,
    NoDup src_pnames ->
    List.length (args G) = List.length vs ->
    List.length src_pnames = List.length vs ->
    List.length arg_dtys = List.length (args G) ->
    cfg_param_dtyp_compatible G arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx r, nth_error (args G) idx = Some r -> ~ In r (defined_ids_of_cfg G) ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r env = Some dv) ->
    wf_draw_strat sigma0 ->
    wf_smap_entries allowed (defined_ids_of_cfg G) seen0 true smap ->
    env_matches_smap (defined_ids_of_cfg G) (build_param_env src_pnames vs)
      (oracle_of_fmap fmap0) smap env ->
    summarize_ocfg_dag fuel true (args G) src_pnames (defined_ids_of_cfg G)
      (ocfg_map (blks G)) is_entry bid_from bid_cur smap seen0 = Some d ->
    exists added : list (freeze_key * Z),
      (forall key z, In (key, z) added -> ~ In key seen0) /\
      (eval_cfg_dag (build_param_env src_pnames vs) (oracle_of_fmap (added ++ fmap0)) d = DO_UB \/
       (exists sigma_out env_out dv,
          wf_draw_strat sigma_out /\
          eval_cfg_dag (build_param_env src_pnames vs) (oracle_of_fmap (added ++ fmap0)) d = DO_Ret dv /\
          cfg_steps_to_ret sigma0 env
            (denote_ocfg_map (ocfg_map (blks G)) None (bid_from, bid_cur))
            sigma_out env_out (inr dv))).
Proof.
  induction fuel as [| fuel' IH];
    intros G src_pnames allowed arg_dtys vs sigma0 fmap0 is_entry bid_from bid_cur smap env seen0 d
           Hnd Hlp Hls Hla Hcomp Hvs Hpe Hwfd0 Hwfs0 Henv0 Hr;
    cbn [summarize_ocfg_dag] in Hr; [discriminate |].
  destruct (RM.find bid_cur (ocfg_map (blks G))) as [b |] eqn:Hfb; [| discriminate].
  pose proof (ocfg_map_in (blks G) bid_cur b Hfb) as Hb_in.
  destruct (is_entry && negb (list_empty_b (blk_phis b))); [discriminate |].
  destruct (reify_phi_evals true (args G) src_pnames (defined_ids_of_cfg G) smap bid_from seen0 (blk_phis b))
    as [[pevals seen_p] |] eqn:Hr_phis; [| discriminate].
  destruct (reify_code true (args G) src_pnames (defined_ids_of_cfg G)
              (apply_phi_smap smap pevals) seen_p (blk_code b))
    as [[[cevals smap_c] seen_c] |] eqn:Hr_code; [| discriminate].
  destruct (reify_phi_evals_wf_smap (blk_phis b) true (args G) src_pnames (defined_ids_of_cfg G)
              allowed smap bid_from seen0 pevals seen_p Hwfs0 Hr_phis)
    as (ext_p & Hinc0p & Hfa_wf_p & Hwfs_p).
  destruct (reify_code_wf_smap (blk_code b) true (args G) src_pnames (defined_ids_of_cfg G)
              ext_p (apply_phi_smap smap pevals) seen_p cevals smap_c seen_c Hwfs_p Hr_code)
    as (ext_c & Hinc_pc & Hwfs_c).
  destruct (eval_reified_phi_map_tgt (blk_phis b) (args G) src_pnames (defined_ids_of_cfg G)
              allowed arg_dtys vs sigma0 fmap0 smap env bid_from seen0 pevals seen_p
              Hnd Hlp Hls Hla Hvs
              (fun id fm dt pargs md op idx dt_u Hphi Hparg Hu =>
                 cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                   (proj2 (in_flat_map _ (blks G) _)
                     (ex_intro _ b (conj Hb_in (block_param_uses_phi_in _ _ b id fm dt pargs md bid_from op _ Hphi Hparg Hu)))))
              Hpe Hwfd0 Hwfs0 Henv0 Hr_phis)
    as (added_p & Had_p & [Hev_ub_p | (sigma_p & dvs_p & Hwfd_p & Hpm_p & Hev_kp & Hst_p)]).
  - exists added_p; split; [intros k z H; exact (proj2 (Had_p k z H)) | left].
    destruct (blk_term b) as [[tiid tm] tmd]; destruct tm; try discriminate.
    + destruct v as [[tb | |] op]; try discriminate; destruct tb; try discriminate.
      destruct (reify_exp _ _ _ _ _ _ _ op) as [[[_ _] _] |]; [inversion Hr; subst; apply Hev_ub_p | discriminate].
    + inversion Hr; subst; apply Hev_ub_p.
    + destruct v as [[[| | ] | |] op]; try discriminate.
      destruct (reify_exp _ _ _ _ _ _ _ op) as [[[_ _] _] |]; [| discriminate].
      destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ br1 _ _); [| discriminate].
      destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ br2 _ _); [inversion Hr; subst; apply Hev_ub_p | discriminate].
    + destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ br _ _); [inversion Hr; subst; apply Hev_ub_p | discriminate].
    + inversion Hr; subst; apply Hev_ub_p.
  - pose proof (env_matches_smap_oracle_prepend allowed (defined_ids_of_cfg G) seen0 added_p fmap0
                  (build_param_env src_pnames vs) smap env Hwfs0
                  (fun k z H => proj2 (Had_p k z H)) Henv0) as Henv0'.
    pose proof (apply_phi_env_matches ext_p (defined_ids_of_cfg G) seen_p true
                  (build_param_env src_pnames vs) (oracle_of_fmap (added_p ++ fmap0))
                  smap env pevals dvs_p Henv0' Hfa_wf_p Hpm_p) as Henv_p.
    assert (Hpe_p : forall idx r, nth_error (args G) idx = Some r -> ~ In r (defined_ids_of_cfg G) ->
      exists dv, nth_error vs idx = Some dv /\ RM.find r (apply_phi_env env dvs_p) = Some dv).
    { intros idx r Hnth Hnin; destruct (Hpe idx r Hnth Hnin) as [dv [Hv Hfe]].
      exists dv; split; [exact Hv |].
      rewrite (apply_phi_env_preserves_nondefs ext_p (defined_ids_of_cfg G) seen_p true
                 (build_param_env src_pnames vs) (oracle_of_fmap (added_p ++ fmap0))
                 env pevals dvs_p r Hfa_wf_p Hpm_p Hnin);
        exact Hfe. }
    assert (Hphis_step : cfg_steps_to_ret sigma0 env (denote_phis bid_from (blk_phis b))
                           sigma_p (apply_phi_env env dvs_p) tt).
    { unfold denote_phis.
      eapply cfg_steps_to_ret_bind; [exact Hst_p |].
      eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite_list | apply CSR_Ret; reflexivity]. }
    destruct (eval_reified_code_tgt (blk_code b) (args G) src_pnames (defined_ids_of_cfg G)
                ext_p arg_dtys vs sigma_p (added_p ++ fmap0)
                (apply_phi_smap smap pevals) (apply_phi_env env dvs_p)
                seen_p cevals smap_c seen_c Hnd Hlp Hls Hla Hvs
                (fun iid op md idx dt_u Hc Hu =>
                   cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                     (proj2 (in_flat_map _ (blks G) _)
                       (ex_intro _ b (conj Hb_in (block_param_uses_code_in _ _ b iid op md _ Hc Hu)))))
                Hpe_p Hwfd_p Hwfs_p Henv_p Hr_code)
      as (added_c & Had_c & [Hev_ub_c | (sigma_c & env_c & Hwfd_c & Hpe_c & Henv_c & Hev_kc & Hst_c)]).
    + exists (added_c ++ added_p).
      assert (Hdisj_cp : forall k z, In (k, z) (added_c ++ added_p) -> ~ In k seen0).
      { intros k z Hkz; apply in_app_iff in Hkz as [Hc | Hp].
        - intros Hs0; exact (proj2 (Had_c k z Hc) (Hinc0p k Hs0)).
        - exact (proj2 (Had_p k z Hp)). }
      split; [exact Hdisj_cp | left].
      assert (Hstrip_p : forall dt_k,
        eval_cfg_dag (build_param_env src_pnames vs)
          (oracle_of_fmap ((added_c ++ added_p) ++ fmap0)) (wrap_phi_evals pevals dt_k) =
        eval_cfg_dag (build_param_env src_pnames vs)
          (oracle_of_fmap (added_c ++ added_p ++ fmap0)) dt_k).
      { intros dt_k; rewrite <- app_assoc.
        exact (Hev_kp added_c dt_k (fun q z H => proj2 (Had_c q z H))). }
      destruct (blk_term b) as [[tiid tm] tmd]; destruct tm; try discriminate.
      * destruct v as [[tb | |] op]; try discriminate; destruct tb; try discriminate.
        destruct (reify_exp _ _ _ _ _ _ _ op) as [[[_ _] _] |]; [| discriminate].
        inversion Hr; subst; rewrite Hstrip_p; apply Hev_ub_c.
      * inversion Hr; subst; rewrite Hstrip_p; apply Hev_ub_c.
      * destruct v as [[[| | ] | |] op]; try discriminate.
        destruct (reify_exp _ _ _ _ _ _ _ op) as [[[_ _] _] |]; [| discriminate].
        destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ br1 _ _); [| discriminate].
        destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ br2 _ _); [| discriminate].
        inversion Hr; subst; rewrite Hstrip_p; apply Hev_ub_c.
      * destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ br _ _); [| discriminate].
        inversion Hr; subst; rewrite Hstrip_p; apply Hev_ub_c.
      * inversion Hr; subst; rewrite Hstrip_p; apply Hev_ub_c.
    + assert (Hstrip_blk : forall added_t dt_k,
        (forall k z, In (k, z) added_t -> ~ In k seen_c) ->
        eval_cfg_dag (build_param_env src_pnames vs)
          (oracle_of_fmap ((added_t ++ added_c ++ added_p) ++ fmap0))
          (wrap_phi_evals pevals (wrap_evals cevals dt_k)) =
        eval_cfg_dag (build_param_env src_pnames vs)
          (oracle_of_fmap (added_t ++ added_c ++ added_p ++ fmap0)) dt_k).
      { intros added_t dt_k Hdisj_t.
        assert (Hdisj_tc_p : forall k z, In (k, z) (added_t ++ added_c) -> ~ In k seen_p).
        { intros k z Hkz; apply in_app_iff in Hkz as [Ht | Hc].
          - intros Hsp; exact (Hdisj_t k z Ht (Hinc_pc k Hsp)).
          - exact (proj2 (Had_c k z Hc)). }
        replace ((added_t ++ added_c ++ added_p) ++ fmap0)
          with ((added_t ++ added_c) ++ added_p ++ fmap0)
          by (rewrite !app_assoc; reflexivity).
        rewrite (Hev_kp (added_t ++ added_c) (wrap_evals cevals dt_k) Hdisj_tc_p).
        replace ((added_t ++ added_c) ++ added_p ++ fmap0)
          with (added_t ++ added_c ++ added_p ++ fmap0)
          by (rewrite !app_assoc; reflexivity).
        exact (Hev_kc added_t dt_k Hdisj_t). }
      assert (Hdisj_all : forall added_t,
        (forall k z, In (k, z) added_t -> ~ In k seen_c) ->
        forall k z, In (k, z) (added_t ++ added_c ++ added_p) -> ~ In k seen0).
      { intros added_t Hdt k z Hkz; apply in_app_iff in Hkz as [Ht | Hcp].
        - intros Hs0; exact (Hdt k z Ht (Hinc_pc k (Hinc0p k Hs0))).
        - apply in_app_iff in Hcp as [Hc | Hp].
          + intros Hs0; exact (proj2 (Had_c k z Hc) (Hinc0p k Hs0)).
          + exact (proj2 (Had_p k z Hp)). }
      destruct (blk_term b) as [[tiid tm] tmd] eqn:Htm.
      destruct tm; try discriminate.
      * (* TERM_Ret *)
        destruct v as [dt op].
        destruct dt as [tb | |]; try discriminate; destruct tb as [w | | | | | | | | | |]; try discriminate.
        destruct (reify_exp true (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                    (Some (DTYPE_Base (DTYPE_I w))) op)
          as [[[w1 ce_ret] seen_ret] |] eqn:Hr_ret; [| discriminate].
        inversion Hr; subst d; clear Hr.
        pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr_ret)) as ->.
        destruct (eval_reified_exp_tgt op (args G) src_pnames (defined_ids_of_cfg G)
                    ext_c arg_dtys vs sigma_c (added_c ++ added_p ++ fmap0) smap_c env_c seen_c
                    (Some (DTYPE_Base (DTYPE_I w))) w ce_ret seen_ret
                    Hnd Hlp Hls Hla Hvs
                    (fun idx dt_u Hu =>
                       cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                         (proj2 (in_flat_map _ (blks G) _)
                           (ex_intro _ b (conj Hb_in (block_param_uses_ret_in _ _ b tiid _ op tmd _ Htm Hu)))))
                    Hpe_c Hwfd_c Hwfs_c Henv_c Hr_ret)
          as (added_r & Had_r & [[msg_r Hev_r] | (sigma_r & dv_r & Hwfd_r & Hev_r & _ & Hst_r)]).
        -- exists (added_r ++ added_c ++ added_p).
           split; [exact (Hdisj_all added_r (fun k z H => proj2 (Had_r k z H))) | left].
           rewrite (Hstrip_blk added_r (CD_RetScalar w ce_ret) (fun k z H => proj2 (Had_r k z H))).
           cbn [eval_cfg_dag]; rewrite Hev_r; reflexivity.
        -- exists (added_r ++ added_c ++ added_p).
           split; [exact (Hdisj_all added_r (fun k z H => proj2 (Had_r k z H))) | right].
           exists sigma_r, env_c, dv_r; split; [exact Hwfd_r | split].
           ++ rewrite (Hstrip_blk added_r (CD_RetScalar w ce_ret) (fun k z H => proj2 (Had_r k z H))).
              cbn [eval_cfg_dag]; rewrite Hev_r; reflexivity.
           ++ eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
              unfold denote_block; rewrite Htm.
              eapply cfg_steps_to_ret_bind.
              ** eapply cfg_steps_to_ret_bind.
                 --- eapply cfg_steps_to_ret_bind; [exact Hphis_step |].
                     eapply cfg_steps_to_ret_bind; [exact Hst_c |].
                     cbn [denote_terminator]; unfold denote_exp'.
                     eapply cfg_steps_to_ret_bind;
                       [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ Hst_r) | apply CSR_Ret; reflexivity].
                 --- apply CSR_Ret; reflexivity.
              ** apply CSR_Ret; reflexivity.
      * (* TERM_Ret_void *)
        inversion Hr; subst d; clear Hr.
        exists ([] ++ added_c ++ added_p).
        split; [exact (Hdisj_all [] (fun _ _ H => False_ind _ H)) | right].
        exists sigma_c, env_c, NONE; split; [exact Hwfd_c | split].
        -- rewrite (Hstrip_blk [] CD_RetVoid (fun _ _ H => False_ind _ H)); reflexivity.
        -- eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
           unfold denote_block; rewrite Htm.
           eapply cfg_steps_to_ret_bind.
           ++ eapply cfg_steps_to_ret_bind.
              ** eapply cfg_steps_to_ret_bind; [exact Hphis_step |].
                 eapply cfg_steps_to_ret_bind; [exact Hst_c | apply CSR_Ret; reflexivity].
              ** apply CSR_Ret; reflexivity.
           ++ apply CSR_Ret; reflexivity.
      * (* TERM_Br *)
        destruct v as [dt op].
        destruct dt as [tb | |]; try discriminate; destruct tb as [wc | | | | | | | | | |]; try discriminate.
        destruct wc as [| |]; try discriminate.
        destruct (reify_exp true (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                    (Some (DTYPE_Base (DTYPE_I 1%positive))) op)
          as [[[wc' ce_cond] seen_br] |] eqn:Hr_cond; [| discriminate].
        destruct (summarize_ocfg_dag fuel' true (args G) src_pnames (defined_ids_of_cfg G)
                    (ocfg_map (blks G)) false bid_cur br1 smap_c seen_br)
          as [d_t |] eqn:Hr_t; [| discriminate].
        destruct (summarize_ocfg_dag fuel' true (args G) src_pnames (defined_ids_of_cfg G)
                    (ocfg_map (blks G)) false bid_cur br2 smap_c seen_br)
          as [d_f |] eqn:Hr_f; [| discriminate].
        inversion Hr; subst d; clear Hr.
        pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr_cond)) as ->.
        destruct (reify_exp_freeze_props op true (args G) src_pnames (defined_ids_of_cfg G)
                    ext_c smap_c seen_c (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive ce_cond seen_br
                    Hwfs_c Hr_cond)
          as (Hlf_cond & Hinc_cbr & Hfk_cond).
        pose proof (wf_smap_entries_seen_mono ext_c (defined_ids_of_cfg G) seen_c seen_br true smap_c Hinc_cbr Hwfs_c)
          as Hwfs_br.
        destruct (eval_reified_exp_tgt op (args G) src_pnames (defined_ids_of_cfg G)
                    ext_c arg_dtys vs sigma_c (added_c ++ added_p ++ fmap0) smap_c env_c seen_c
                    (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive ce_cond seen_br
                    Hnd Hlp Hls Hla Hvs
                    (fun idx dt_u Hu =>
                       cfg_param_dtyp_compatible_nth G arg_dtys idx dt_u Hcomp
                         (proj2 (in_flat_map _ (blks G) _)
                           (ex_intro _ b (conj Hb_in (block_param_uses_br_in _ _ b tiid _ op br1 br2 tmd _ Htm Hu)))))
                    Hpe_c Hwfd_c Hwfs_c Henv_c Hr_cond)
          as (added_br & Had_br & [[msg_br Hev_br] | (sigma_br & dv_br & Hwfd_br & Hev_br & Hsc_br & Hst_br)]).
        -- exists (added_br ++ added_c ++ added_p).
           split; [exact (Hdisj_all added_br (fun k z H => proj2 (Had_br k z H))) | left].
           rewrite (Hstrip_blk added_br (CD_Branch ce_cond d_t d_f) (fun k z H => proj2 (Had_br k z H))).
           cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
        -- destruct Hsc_br as [-> | [cbit ->]].
           ++ exists (added_br ++ added_c ++ added_p).
              split; [exact (Hdisj_all added_br (fun k z H => proj2 (Had_br k z H))) | left].
              rewrite (Hstrip_blk added_br (CD_Branch ce_cond d_t d_f) (fun k z H => proj2 (Had_br k z H))).
              cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
           ++ pose proof (env_matches_smap_oracle_prepend ext_c (defined_ids_of_cfg G) seen_c
                            added_br (added_c ++ added_p ++ fmap0)
                            (build_param_env src_pnames vs) smap_c env_c Hwfs_c
                            (fun k z H => proj2 (Had_br k z H)) Henv_c) as Henv_br.
              destruct (@Integers.unsigned 1 cbit =? 1)%Z eqn:Ecbit.
              ** destruct (IH G src_pnames ext_c arg_dtys vs sigma_br (added_br ++ added_c ++ added_p ++ fmap0)
                             false bid_cur br1 smap_c env_c seen_br d_t
                             Hnd Hlp Hls Hla Hcomp Hvs Hpe_c Hwfd_br Hwfs_br Henv_br Hr_t)
                   as (added_n & Had_n & [Hev_ub_n | (sigma_out & env_out & dv_out & Hwfd_out & Hev_out & Hst_n)]).
                 --- assert (Hdisj_nbr : forall k z, In (k, z) (added_n ++ added_br) -> ~ In k seen_c).
                     { intros k z Hkz; apply in_app_iff in Hkz as [Hn | Hb0].
                       - intros Hsc0; exact (Had_n k z Hn (Hinc_cbr k Hsc0)).
                       - exact (proj2 (Had_br k z Hb0)). }
                     exists ((added_n ++ added_br) ++ added_c ++ added_p).
                     split; [exact (Hdisj_all (added_n ++ added_br) Hdisj_nbr) | left].
                     rewrite (Hstrip_blk (added_n ++ added_br) (CD_Branch ce_cond d_t d_f) Hdisj_nbr).
                     replace ((added_n ++ added_br) ++ added_c ++ added_p ++ fmap0)
                       with (added_n ++ added_br ++ added_c ++ added_p ++ fmap0)
                       by (rewrite !app_assoc; reflexivity).
                     pose proof (eval_let_free_prepend_fmap ce_cond (build_param_env src_pnames vs)
                                   added_n (added_br ++ added_c ++ added_p ++ fmap0) seen_br
                                   Hlf_cond (Hfk_cond eq_refl) Had_n) as Hev_br'.
                     cbn [eval_cfg_dag]; rewrite Hev_br', Hev_br, Ecbit; exact Hev_ub_n.
                 --- assert (Hdisj_nbr : forall k z, In (k, z) (added_n ++ added_br) -> ~ In k seen_c).
                     { intros k z Hkz; apply in_app_iff in Hkz as [Hn | Hb0].
                       - intros Hsc0; exact (Had_n k z Hn (Hinc_cbr k Hsc0)).
                       - exact (proj2 (Had_br k z Hb0)). }
                     exists ((added_n ++ added_br) ++ added_c ++ added_p).
                     split; [exact (Hdisj_all (added_n ++ added_br) Hdisj_nbr) | right].
                     exists sigma_out, env_out, dv_out; split; [exact Hwfd_out | split].
                     +++ rewrite (Hstrip_blk (added_n ++ added_br) (CD_Branch ce_cond d_t d_f) Hdisj_nbr).
                         replace ((added_n ++ added_br) ++ added_c ++ added_p ++ fmap0)
                           with (added_n ++ added_br ++ added_c ++ added_p ++ fmap0)
                           by (rewrite !app_assoc; reflexivity).
                         pose proof (eval_let_free_prepend_fmap ce_cond (build_param_env src_pnames vs)
                                       added_n (added_br ++ added_c ++ added_p ++ fmap0) seen_br
                                       Hlf_cond (Hfk_cond eq_refl) Had_n) as Hev_br'.
                         cbn [eval_cfg_dag]; rewrite Hev_br', Hev_br, Ecbit; exact Hev_out.
                     +++ eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
                         unfold denote_block; rewrite Htm.
                         eapply cfg_steps_to_ret_bind.
                         *** eapply cfg_steps_to_ret_bind.
                             ---- eapply cfg_steps_to_ret_bind; [exact Hphis_step |].
                                  eapply cfg_steps_to_ret_bind; [exact Hst_c |].
                                  cbn [denote_terminator]; unfold denote_exp'.
                                  eapply cfg_steps_to_ret_bind;
                                    [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ Hst_br) |].
                                  rewrite bit_int_1_equ_one_eq_unsigned, Ecbit; apply CSR_Ret; reflexivity.
                             ---- apply CSR_Ret; reflexivity.
                         *** eapply CSR_Tau; [reflexivity | exact Hst_n].
              ** destruct (IH G src_pnames ext_c arg_dtys vs sigma_br (added_br ++ added_c ++ added_p ++ fmap0)
                             false bid_cur br2 smap_c env_c seen_br d_f
                             Hnd Hlp Hls Hla Hcomp Hvs Hpe_c Hwfd_br Hwfs_br Henv_br Hr_f)
                   as (added_n & Had_n & [Hev_ub_n | (sigma_out & env_out & dv_out & Hwfd_out & Hev_out & Hst_n)]).
                 --- assert (Hdisj_nbr : forall k z, In (k, z) (added_n ++ added_br) -> ~ In k seen_c).
                     { intros k z Hkz; apply in_app_iff in Hkz as [Hn | Hb0].
                       - intros Hsc0; exact (Had_n k z Hn (Hinc_cbr k Hsc0)).
                       - exact (proj2 (Had_br k z Hb0)). }
                     exists ((added_n ++ added_br) ++ added_c ++ added_p).
                     split; [exact (Hdisj_all (added_n ++ added_br) Hdisj_nbr) | left].
                     rewrite (Hstrip_blk (added_n ++ added_br) (CD_Branch ce_cond d_t d_f) Hdisj_nbr).
                     replace ((added_n ++ added_br) ++ added_c ++ added_p ++ fmap0)
                       with (added_n ++ added_br ++ added_c ++ added_p ++ fmap0)
                       by (rewrite !app_assoc; reflexivity).
                     pose proof (eval_let_free_prepend_fmap ce_cond (build_param_env src_pnames vs)
                                   added_n (added_br ++ added_c ++ added_p ++ fmap0) seen_br
                                   Hlf_cond (Hfk_cond eq_refl) Had_n) as Hev_br'.
                     cbn [eval_cfg_dag]; rewrite Hev_br', Hev_br, Ecbit; exact Hev_ub_n.
                 --- assert (Hdisj_nbr : forall k z, In (k, z) (added_n ++ added_br) -> ~ In k seen_c).
                     { intros k z Hkz; apply in_app_iff in Hkz as [Hn | Hb0].
                       - intros Hsc0; exact (Had_n k z Hn (Hinc_cbr k Hsc0)).
                       - exact (proj2 (Had_br k z Hb0)). }
                     exists ((added_n ++ added_br) ++ added_c ++ added_p).
                     split; [exact (Hdisj_all (added_n ++ added_br) Hdisj_nbr) | right].
                     exists sigma_out, env_out, dv_out; split; [exact Hwfd_out | split].
                     +++ rewrite (Hstrip_blk (added_n ++ added_br) (CD_Branch ce_cond d_t d_f) Hdisj_nbr).
                         replace ((added_n ++ added_br) ++ added_c ++ added_p ++ fmap0)
                           with (added_n ++ added_br ++ added_c ++ added_p ++ fmap0)
                           by (rewrite !app_assoc; reflexivity).
                         pose proof (eval_let_free_prepend_fmap ce_cond (build_param_env src_pnames vs)
                                       added_n (added_br ++ added_c ++ added_p ++ fmap0) seen_br
                                       Hlf_cond (Hfk_cond eq_refl) Had_n) as Hev_br'.
                         cbn [eval_cfg_dag]; rewrite Hev_br', Hev_br, Ecbit; exact Hev_out.
                     +++ eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
                         unfold denote_block; rewrite Htm.
                         eapply cfg_steps_to_ret_bind.
                         *** eapply cfg_steps_to_ret_bind.
                             ---- eapply cfg_steps_to_ret_bind; [exact Hphis_step |].
                                  eapply cfg_steps_to_ret_bind; [exact Hst_c |].
                                  cbn [denote_terminator]; unfold denote_exp'.
                                  eapply cfg_steps_to_ret_bind;
                                    [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ Hst_br) |].
                                  rewrite bit_int_1_equ_one_eq_unsigned, Ecbit; apply CSR_Ret; reflexivity.
                             ---- apply CSR_Ret; reflexivity.
                         *** eapply CSR_Tau; [reflexivity | exact Hst_n].
      * (* TERM_Br_1 *)
        destruct (summarize_ocfg_dag fuel' true (args G) src_pnames (defined_ids_of_cfg G)
                    (ocfg_map (blks G)) false bid_cur br smap_c seen_c)
          as [d_next |] eqn:Hr_n; [| discriminate].
        inversion Hr; subst d; clear Hr.
        destruct (IH G src_pnames ext_c arg_dtys vs sigma_c (added_c ++ added_p ++ fmap0)
                    false bid_cur br smap_c env_c seen_c d_next
                    Hnd Hlp Hls Hla Hcomp Hvs Hpe_c Hwfd_c Hwfs_c Henv_c Hr_n)
          as (added_n & Had_n & [Hev_ub_n | (sigma_out & env_out & dv_out & Hwfd_out & Hev_out & Hst_n)]).
        -- exists (added_n ++ added_c ++ added_p).
           split; [exact (Hdisj_all added_n Had_n) | left].
           rewrite (Hstrip_blk added_n d_next Had_n); exact Hev_ub_n.
        -- exists (added_n ++ added_c ++ added_p).
           split; [exact (Hdisj_all added_n Had_n) | right].
           exists sigma_out, env_out, dv_out; split; [exact Hwfd_out | split].
           ++ rewrite (Hstrip_blk added_n d_next Had_n); exact Hev_out.
           ++ eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
              unfold denote_block; rewrite Htm.
              eapply cfg_steps_to_ret_bind.
              ** eapply cfg_steps_to_ret_bind.
                 --- eapply cfg_steps_to_ret_bind; [exact Hphis_step |].
                     eapply cfg_steps_to_ret_bind; [exact Hst_c | apply CSR_Ret; reflexivity].
                 --- apply CSR_Ret; reflexivity.
              ** eapply CSR_Tau; [reflexivity | exact Hst_n].
      * (* TERM_Unreachable *)
        inversion Hr; subst d; clear Hr.
        exists ([] ++ added_c ++ added_p).
        split; [exact (Hdisj_all [] (fun _ _ H => False_ind _ H)) | left].
        rewrite (Hstrip_blk [] CD_Unreachable (fun _ _ H => False_ind _ H)); reflexivity.
Qed.

Lemma summarize_tgt_dag_sound {Pa : Params} :
  forall G src_pnames arg_dtys (vs : list (@dvalue Pa)) (sigma_tgt : @draw_strat Pa) d,
    NoDup (args G) ->
    NoDup src_pnames ->
    List.length src_pnames = List.length (args G) ->
    List.length arg_dtys = List.length (args G) ->
    cfg_param_dtyp_compatible G arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    wf_draw_strat sigma_tgt ->
    summarize_cfg_dag true G src_pnames = Some d ->
    exists fmap_tgt : list (freeze_key * Z),
      eval_cfg_dag (build_param_env src_pnames vs) (oracle_of_fmap fmap_tgt) d = DO_UB \/
      (exists sigma_tgt' env_out dv,
         eval_cfg_dag (build_param_env src_pnames vs) (oracle_of_fmap fmap_tgt) d = DO_Ret dv /\
         cfg_steps_to_ret sigma_tgt (init_cfg_locals (args G) vs) (denote_cfg G None)
           sigma_tgt' env_out dv).
Proof.
  intros G src_pnames arg_dtys vs sigma_tgt d Hnd_p Hnd_s Hlen_sp Hlen_da Hcomp Hvs Hwfd Hr.
  assert (Hlen_vs : List.length vs = List.length arg_dtys) by exact (Forall2_length Hvs).
  assert (Hlp : List.length (args G) = List.length vs) by lia.
  assert (Hls : List.length src_pnames = List.length vs) by lia.
  assert (Hpe0 : forall idx r, nth_error (args G) idx = Some r -> ~ In r (defined_ids_of_cfg G) ->
    exists dv, nth_error vs idx = Some dv /\ RM.find r (init_cfg_locals (args G) vs) = Some dv).
  { intros idx r Hnth _; exact (init_cfg_locals_nth (args G) vs idx r Hnd_p Hlp Hnth). }
  destruct (summarize_ocfg_tgt_sound (S (List.length (blks G))) G src_pnames [] arg_dtys vs
              sigma_tgt [] true (init G) (init G) (RM.empty _) (init_cfg_locals (args G) vs) [] d
              Hnd_s Hlp Hls Hlen_da Hcomp Hvs Hpe0 Hwfd
              (wf_smap_entries_empty [] (defined_ids_of_cfg G) [] true)
              (env_matches_smap_empty (defined_ids_of_cfg G) (build_param_env src_pnames vs)
                 (oracle_of_fmap []) (init_cfg_locals (args G) vs))
              Hr)
    as (fmap_tgt & _ & [Hev_ub | (sigma_out & env_out & dv & _ & Hev_ret & Hst_ret)]).
  - exists (fmap_tgt ++ []); left; exact Hev_ub.
  - exists (fmap_tgt ++ []); right; exists sigma_out, env_out, dv; split; [exact Hev_ret |].
    unfold denote_cfg, denote_cfg_map.
    eapply cfg_steps_to_ret_bind; [exact Hst_ret | apply CSR_Ret; reflexivity].
Qed.


(** *** 5.6 Source UB Assumption Discharge, Target UB-Safety & Certificate Obligation Checker *)

Lemma vars_subset_b_incl :
  forall vs allowed,
    vars_subset_b vs allowed = true -> incl vs allowed.
Proof.
  intros vs allowed H u Hu; unfold vars_subset_b in H.
  rewrite forallb_forall in H; apply var_pair_in_spec; exact (H u Hu).
Qed.

Fixpoint spine_is_unreachable (d : cfg_dag) : bool :=
  match d with
  | CD_Unreachable => true
  | CD_Eval _ _ next => spine_is_unreachable next
  | CD_Branch _ on_t on_f => spine_is_unreachable on_t && spine_is_unreachable on_f
  | CD_RetVoid | CD_RetScalar _ _ => false
  end.

Lemma spine_is_unreachable_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle d,
    spine_is_unreachable d = true ->
    eval_cfg_dag penv foracle d = DO_UB.
Proof.
  intros penv foracle d; induction d as [| | w ret_e | w step_e next IH | cond on_t IHt on_f IHf];
    intros H; cbn in H |- *; try discriminate; [reflexivity | |].
  - destruct (eval_closed_cert_expr penv foracle step_e) as [| | | dv];
      [reflexivity | reflexivity | reflexivity | exact (IH H)].
  - apply andb_true_iff in H as [Ht Hf].
    destruct (eval_closed_cert_expr penv foracle cond) as [| | | dvc]; try reflexivity.
    destruct dvc as [dbc | |]; try reflexivity.
    destruct dbc as [| wc cbit | | | | | |]; try reflexivity.
    destruct wc as [| |]; try reflexivity.
    destruct (@Integers.unsigned 1 cbit =? 1)%Z; [exact (IHt Ht) | exact (IHf Hf)].
Qed.

Fixpoint spine_src_evals (d : cfg_dag) : list cert_expr :=
  match d with
  | CD_Unreachable | CD_RetVoid => []
  | CD_RetScalar _ ret_e => [ret_e]
  | CD_Eval _ step_e next => step_e :: spine_src_evals next
  | CD_Branch cond on_t on_f =>
      if spine_is_unreachable on_f then cond :: spine_src_evals on_t
      else if spine_is_unreachable on_t then cond :: spine_src_evals on_f
      else [cond]
  end.

Lemma spine_src_evals_ret {Pa : Params} :
  forall (penv : param_env Pa) foracle d v e,
    eval_cfg_dag penv foracle d = DO_Ret v ->
    In e (spine_src_evals d) ->
    exists dv, eval_closed_cert_expr penv foracle e = raise_ret dv.
Proof.
  intros penv foracle d; induction d as [| | w ret_e | w step_e next IH | cond on_t IHt on_f IHf];
    intros v e Hev Hin; cbn [eval_cfg_dag spine_src_evals] in Hev, Hin.
  - discriminate Hev.
  - contradiction.
  - destruct Hin as [<- | []].
    destruct (eval_closed_cert_expr penv foracle ret_e) as [| | | dv]; try discriminate Hev.
    exists dv; reflexivity.
  - destruct (eval_closed_cert_expr penv foracle step_e) as [| | | dv0] eqn:Es; try discriminate Hev.
    destruct Hin as [<- | Hin]; [exists dv0; reflexivity | exact (IH v e Hev Hin)].
  - destruct (eval_closed_cert_expr penv foracle cond) as [| | | dvc] eqn:Ec; try discriminate Hev.
    destruct dvc as [dbc | |]; try discriminate Hev.
    destruct dbc as [| wc cbit | | | | | |]; try discriminate Hev.
    destruct wc as [| |]; try discriminate Hev.
    destruct (spine_is_unreachable on_f) eqn:Euf.
    + destruct (@Integers.unsigned 1 cbit =? 1)%Z.
      * destruct Hin as [<- | Hin]; [eexists; exact Ec | exact (IHt v e Hev Hin)].
      * rewrite (spine_is_unreachable_sound penv foracle on_f Euf) in Hev; discriminate Hev.
    + destruct (spine_is_unreachable on_t) eqn:Eut.
      * destruct (@Integers.unsigned 1 cbit =? 1)%Z.
        -- rewrite (spine_is_unreachable_sound penv foracle on_t Eut) in Hev; discriminate Hev.
        -- destruct Hin as [<- | Hin]; [eexists; exact Ec | exact (IHf v e Hev Hin)].
      * destruct Hin as [<- | []]; eexists; exact Ec.
Qed.

Lemma spine_src_evals_wf :
  forall allowed d e,
    wf_cfg_dag allowed d = true ->
    In e (spine_src_evals d) ->
    wt_cert_expr [] e = true /\
    is_let_free_expr e = true /\
    incl (collect_free_vars [] e) allowed.
Proof.
  intros allowed d; induction d as [| | w ret_e | w step_e next IH | cond on_t IHt on_f IHf];
    intros e Hwf Hin; cbn [wf_cfg_dag spine_src_evals] in Hwf, Hin; try contradiction.
  - destruct Hin as [<- | []].
    rewrite !andb_true_iff in Hwf; destruct Hwf as (((Hwt & _) & Hlf) & Hfv).
    exact (conj Hwt (conj Hlf (vars_subset_b_incl _ _ Hfv))).
  - rewrite !andb_true_iff in Hwf; destruct Hwf as ((((Hwt & _) & Hlf) & Hfv) & Hwfn).
    destruct Hin as [<- | Hin];
      [exact (conj Hwt (conj Hlf (vars_subset_b_incl _ _ Hfv))) | exact (IH e Hwfn Hin)].
  - rewrite !andb_true_iff in Hwf; destruct Hwf as (((((Hwt & _) & Hlf) & Hfv) & Hwft) & Hwff).
    destruct (spine_is_unreachable on_f).
    + destruct Hin as [<- | Hin];
        [exact (conj Hwt (conj Hlf (vars_subset_b_incl _ _ Hfv))) | exact (IHt e Hwft Hin)].
    + destruct (spine_is_unreachable on_t).
      * destruct Hin as [<- | Hin];
          [exact (conj Hwt (conj Hlf (vars_subset_b_incl _ _ Hfv))) | exact (IHf e Hwff Hin)].
      * destruct Hin as [<- | []]; exact (conj Hwt (conj Hlf (vars_subset_b_incl _ _ Hfv))).
Qed.

Fixpoint spine_branch_conds (d : cfg_dag) : list cert_expr :=
  match d with
  | CD_Unreachable | CD_RetVoid | CD_RetScalar _ _ => []
  | CD_Eval _ _ next => spine_branch_conds next
  | CD_Branch cond on_t on_f =>
      if spine_is_unreachable on_f then cond :: spine_branch_conds on_t
      else if spine_is_unreachable on_t then cond :: spine_branch_conds on_f
      else [cond]
  end.

Lemma spine_branch_conds_ret {Pa : Params} :
  forall (penv : param_env Pa) foracle d v c,
    eval_cfg_dag penv foracle d = DO_Ret v ->
    In c (spine_branch_conds d) ->
    exists cbit : @Integers.bit_int 1,
      eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit)).
Proof.
  intros penv foracle d; induction d as [| | w ret_e | w step_e next IH | cond on_t IHt on_f IHf];
    intros v c Hev Hin; cbn [eval_cfg_dag spine_branch_conds] in Hev, Hin; try contradiction.
  - destruct (eval_closed_cert_expr penv foracle step_e) as [| | | _]; try discriminate Hev.
    exact (IH v c Hev Hin).
  - destruct (eval_closed_cert_expr penv foracle cond) as [| | | dvc] eqn:Ec; try discriminate Hev.
    destruct dvc as [dbc | |]; try discriminate Hev.
    destruct dbc as [| wc cbit | | | | | |]; try discriminate Hev.
    destruct wc as [| |]; try discriminate Hev.
    destruct (spine_is_unreachable on_f) eqn:Euf.
    + destruct (@Integers.unsigned 1 cbit =? 1)%Z.
      * destruct Hin as [<- | Hin]; [exists cbit; exact Ec | exact (IHt v c Hev Hin)].
      * rewrite (spine_is_unreachable_sound penv foracle on_f Euf) in Hev; discriminate Hev.
    + destruct (spine_is_unreachable on_t) eqn:Eut.
      * destruct (@Integers.unsigned 1 cbit =? 1)%Z.
        -- rewrite (spine_is_unreachable_sound penv foracle on_t Eut) in Hev; discriminate Hev.
        -- destruct Hin as [<- | Hin]; [exists cbit; exact Ec | exact (IHf v c Hev Hin)].
      * destruct Hin as [<- | []]; exists cbit; exact Ec.
Qed.

Lemma is_syntactic_subexpr_wt_fv :
  forall sub big allowed,
    is_syntactic_subexpr sub big = true ->
    wt_cert_expr [] big = true ->
    is_let_free_expr big = true ->
    incl (collect_free_vars [] big) allowed ->
    wt_cert_expr [] sub = true /\
    is_let_free_expr sub = true /\
    incl (collect_free_vars [] sub) allowed.
Proof.
  intros sub big.
  induction big as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros allowed Hsub Hwt Hlf Hfv;
    cbn [is_syntactic_subexpr] in Hsub;
    destruct (cert_expr_eqb sub _) eqn:Heq;
    try (apply cert_expr_eqb_eq in Heq; subst sub; exact (conj Hwt (conj Hlf Hfv)));
    cbn [orb] in Hsub; try discriminate Hsub.
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf, Hfv.
    rewrite !andb_true_iff in Hwt, Hlf.
    destruct Hwt as ((((_ & Hwtl) & Hwtr) & _) & _); destruct Hlf as [Hlfl Hlfr].
    apply orb_true_iff in Hsub as [Hsl | Hsr].
    + exact (IHl allowed Hsl Hwtl Hlfl (fun u Hu => Hfv u (proj2 (in_app_iff _ _ _) (or_introl Hu)))).
    + exact (IHr allowed Hsr Hwtr Hlfr (fun u Hu => Hfv u (proj2 (in_app_iff _ _ _) (or_intror Hu)))).
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf, Hfv.
    rewrite !andb_true_iff in Hwt, Hlf.
    destruct Hwt as (((Hwtl & Hwtr) & _) & _); destruct Hlf as [Hlfl Hlfr].
    apply orb_true_iff in Hsub as [Hsl | Hsr].
    + exact (IHl allowed Hsl Hwtl Hlfl (fun u Hu => Hfv u (proj2 (in_app_iff _ _ _) (or_introl Hu)))).
    + exact (IHr allowed Hsr Hwtr Hlfr (fun u Hu => Hfv u (proj2 (in_app_iff _ _ _) (or_intror Hu)))).
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf, Hfv.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((_ & Hwto) & _).
    exact (IHo allowed Hsub Hwto Hlf Hfv).
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf, Hfv.
    rewrite !andb_true_iff in Hwt, Hlf.
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & _) & _) & _).
    destruct Hlf as ([Hlfc Hlft] & Hlff).
    rewrite !orb_true_iff in Hsub; destruct Hsub as [[Hsc | Hst] | Hsf].
    + exact (IHc allowed Hsc Hwtc Hlfc (fun u Hu => Hfv u (proj2 (in_app_iff _ _ _) (or_introl Hu)))).
    + exact (IHt allowed Hst Hwtt Hlft
               (fun u Hu => Hfv u (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl Hu)))))).
    + exact (IHf allowed Hsf Hwtf Hlff
               (fun u Hu => Hfv u (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_intror Hu)))))).
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf, Hfv.
    apply andb_true_iff in Hwt as [Hwto _].
    exact (IHo allowed Hsub Hwto Hlf Hfv).
Qed.

Lemma signed_zero_iff_unsigned_zero :
  forall (w : positive) (ir : @Integers.bit_int w),
    @Integers.signed w ir = 0%Z <-> @Integers.unsigned w ir = 0%Z.
Proof.
  intros w ir; split; intros Hz.
  - rewrite <- (@Integers.repr_signed w ir), Hz.
    change (@Integers.repr w 0) with (@Integers.zero w).
    exact (@Integers.unsigned_zero w).
  - rewrite <- (@Integers.repr_unsigned w ir), Hz.
    change (@Integers.repr w 0) with (@Integers.zero w).
    exact (@Integers.signed_zero w).
Qed.

Definition is_nonzero_bv_const (e : cert_expr) : bool :=
  match e with
  | CE_BvConst w val =>
      negb (@Integers.eq w (@Integers.repr w (Z.of_N val)) (@Integers.zero w))
  | _ => false
  end.

Lemma is_nonzero_bv_const_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle e,
    is_nonzero_bv_const e = true ->
    exists w (i : @Integers.bit_int w),
      eval_closed_cert_expr penv foracle e =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w i)) /\
      (@Integers.unsigned w i <> 0)%Z.
Proof.
  intros penv foracle [w val | | | | | | | |] H; try discriminate H.
  cbn [is_nonzero_bv_const] in H; apply negb_true_iff in H.
  unfold Integers.eq in H; rewrite (@Integers.unsigned_zero w) in H.
  match type of H with
  | (if ?c then _ else _) = false => destruct c as [_ | Hneq]; [discriminate H |]
  end.
  exists w, (@Integers.repr w (Z.of_N val)).
  split; [reflexivity | exact Hneq].
Qed.

Definition is_safe_sdiv_bv_const (e : cert_expr) : bool :=
  match e with
  | CE_BvConst w val =>
      let r := @Integers.repr w (Z.of_N val) in
      negb (@Integers.eq w r (@Integers.zero w)) &&
      negb (@Integers.eq w r (@Integers.mone w))
  | _ => false
  end.

Lemma is_safe_sdiv_bv_const_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle e,
    is_safe_sdiv_bv_const e = true ->
    exists w (i : @Integers.bit_int w),
      eval_closed_cert_expr penv foracle e =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w i)) /\
      (@Integers.unsigned w i <> 0)%Z /\
      (@Integers.signed w i <> 0)%Z /\
      (@Integers.signed w i <> (-1))%Z.
Proof.
  intros penv foracle [w val | | | | | | | |] H; try discriminate H.
  cbn [is_safe_sdiv_bv_const] in H; apply andb_true_iff in H as [Hz Hm].
  apply negb_true_iff in Hz; apply negb_true_iff in Hm.
  set (r := @Integers.repr w (Z.of_N val)) in *.
  unfold Integers.eq in Hz; rewrite (@Integers.unsigned_zero w) in Hz.
  match type of Hz with
  | (if ?c then _ else _) = false => destruct c as [_ | Huz]; [discriminate Hz |]
  end.
  unfold Integers.eq in Hm.
  match type of Hm with
  | (if ?c then _ else _) = false => destruct c as [_ | Hum]; [discriminate Hm |]
  end.
  exists w, r; split; [reflexivity | split; [exact Huz | split]].
  - intros Hsz; apply Huz, signed_zero_iff_unsigned_zero; exact Hsz.
  - intros Hsm; apply Hum.
    assert (Hr_eq : r = @Integers.mone w).
    { rewrite <- (@Integers.repr_signed w r), Hsm.
      change (@Integers.repr w (-1)) with (@Integers.mone w); reflexivity. }
    rewrite Hr_eq; reflexivity.
Qed.

Fixpoint expr_has_div_with_rhs (rhs_target : cert_expr) (e : cert_expr) {struct e} : bool :=
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ | CE_Let _ _ => false
  | CE_BinOp op _ _ l r =>
      (is_div_or_rem_op op && cert_expr_eqb r rhs_target) ||
      expr_has_div_with_rhs rhs_target l ||
      expr_has_div_with_rhs rhs_target r
  | CE_ICmp _ _ _ l r =>
      expr_has_div_with_rhs rhs_target l || expr_has_div_with_rhs rhs_target r
  | CE_Cast _ _ _ _ o | CE_Freeze _ o =>
      expr_has_div_with_rhs rhs_target o
  | CE_Select _ c t f =>
      expr_has_div_with_rhs rhs_target c ||
      expr_has_div_with_rhs rhs_target t ||
      expr_has_div_with_rhs rhs_target f
  end.

Lemma expr_has_div_with_rhs_spec :
  forall rhs_target big,
    expr_has_div_with_rhs rhs_target big = true ->
    exists op w fl lhs,
      is_div_or_rem_op op = true /\
      is_syntactic_subexpr (CE_BinOp op w fl lhs rhs_target) big = true.
Proof.
  intros rhs_target big.
  induction big as
    [ w val | w | nm w
    | op0 w0 fl0 l IHl r IHr
    | pr ss w0 l IHl r IHr
    | k fw tw fl0 o IHo
    | w0 c IHc t IHt f IHf
    | w0 o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros H; cbn [expr_has_div_with_rhs] in H; try discriminate H.
  - rewrite !orb_true_iff in H; destruct H as [[Hhere | Hl] | Hr].
    + apply andb_true_iff in Hhere as [Hop Heqr]; apply cert_expr_eqb_eq in Heqr; subst r.
      exists op0, w0, fl0, l; split; [exact Hop |].
      cbn [is_syntactic_subexpr]; rewrite cert_expr_eqb_refl; reflexivity.
    + destruct (IHl Hl) as (op & w & fl & lhs & Hop & Hsub).
      exists op, w, fl, lhs; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
    + destruct (IHr Hr) as (op & w & fl & lhs & Hop & Hsub).
      exists op, w, fl, lhs; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
  - apply orb_true_iff in H as [Hl | Hr].
    + destruct (IHl Hl) as (op & w & fl & lhs & Hop & Hsub).
      exists op, w, fl, lhs; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
    + destruct (IHr Hr) as (op & w & fl & lhs & Hop & Hsub).
      exists op, w, fl, lhs; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
  - destruct (IHo H) as (op & w & fl & lhs & Hop & Hsub).
    exists op, w, fl, lhs; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
  - rewrite !orb_true_iff in H; destruct H as [[Hc | Ht] | Hf].
    + destruct (IHc Hc) as (op & w & fl & lhs & Hop & Hsub).
      exists op, w, fl, lhs; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
    + destruct (IHt Ht) as (op & w & fl & lhs & Hop & Hsub).
      exists op, w, fl, lhs; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
    + destruct (IHf Hf) as (op & w & fl & lhs & Hop & Hsub).
      exists op, w, fl, lhs; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
  - destruct (IHo H) as (op & w & fl & lhs & Hop & Hsub).
    exists op, w, fl, lhs; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
Qed.

Fixpoint expr_has_defined_div_rhs
  (ctx : ub_ctx) (rhs_target : cert_expr) (e : cert_expr) {struct e} : bool :=
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ | CE_Let _ _ => false
  | CE_BinOp op _ _ l r =>
      (is_div_or_rem_op op && cert_expr_eqb r rhs_target && expr_guaranteed_defined ctx l) ||
      expr_has_defined_div_rhs ctx rhs_target l ||
      expr_has_defined_div_rhs ctx rhs_target r
  | CE_ICmp _ _ _ l r =>
      expr_has_defined_div_rhs ctx rhs_target l || expr_has_defined_div_rhs ctx rhs_target r
  | CE_Cast _ _ _ _ o | CE_Freeze _ o =>
      expr_has_defined_div_rhs ctx rhs_target o
  | CE_Select _ c t f =>
      expr_has_defined_div_rhs ctx rhs_target c ||
      expr_has_defined_div_rhs ctx rhs_target t ||
      expr_has_defined_div_rhs ctx rhs_target f
  end.

Lemma expr_has_defined_div_rhs_spec :
  forall ctx rhs_target big,
    expr_has_defined_div_rhs ctx rhs_target big = true ->
    exists op w fl lhs,
      is_div_or_rem_op op = true /\
      expr_guaranteed_defined ctx lhs = true /\
      is_syntactic_subexpr (CE_BinOp op w fl lhs rhs_target) big = true.
Proof.
  intros ctx rhs_target big.
  induction big as
    [ w val | w | nm w
    | op0 w0 fl0 l IHl r IHr
    | pr ss w0 l IHl r IHr
    | k fw tw fl0 o IHo
    | w0 c IHc t IHt f IHf
    | w0 o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros H; cbn [expr_has_defined_div_rhs] in H; try discriminate H.
  - rewrite !orb_true_iff in H; destruct H as [[Hhere | Hl] | Hr].
    + rewrite !andb_true_iff in Hhere; destruct Hhere as ([Hop Heqr] & Hdef).
      apply cert_expr_eqb_eq in Heqr; subst r.
      exists op0, w0, fl0, l; split; [exact Hop | split; [exact Hdef |]].
      cbn [is_syntactic_subexpr]; rewrite cert_expr_eqb_refl; reflexivity.
    + destruct (IHl Hl) as (op & w & fl & lhs & Hop & Hdef & Hsub).
      exists op, w, fl, lhs; split; [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
    + destruct (IHr Hr) as (op & w & fl & lhs & Hop & Hdef & Hsub).
      exists op, w, fl, lhs; split; [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
  - apply orb_true_iff in H as [Hl | Hr].
    + destruct (IHl Hl) as (op & w & fl & lhs & Hop & Hdef & Hsub).
      exists op, w, fl, lhs; split; [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
    + destruct (IHr Hr) as (op & w & fl & lhs & Hop & Hdef & Hsub).
      exists op, w, fl, lhs; split; [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
  - destruct (IHo H) as (op & w & fl & lhs & Hop & Hdef & Hsub).
    exists op, w, fl, lhs; split; [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
  - rewrite !orb_true_iff in H; destruct H as [[Hc | Ht] | Hf].
    + destruct (IHc Hc) as (op & w & fl & lhs & Hop & Hdef & Hsub).
      exists op, w, fl, lhs; split; [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
    + destruct (IHt Ht) as (op & w & fl & lhs & Hop & Hdef & Hsub).
      exists op, w, fl, lhs; split; [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
    + destruct (IHf Hf) as (op & w & fl & lhs & Hop & Hdef & Hsub).
      exists op, w, fl, lhs; split; [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
  - destruct (IHo H) as (op & w & fl & lhs & Hop & Hdef & Hsub).
    exists op, w, fl, lhs; split; [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
Qed.

Fixpoint expr_has_sdiv_pair (el er : cert_expr) (e : cert_expr) {struct e} : bool :=
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ | CE_Let _ _ => false
  | CE_BinOp op _ _ l r =>
      ((cert_binop_eqb op CB_SDiv || cert_binop_eqb op CB_SRem) &&
       cert_expr_eqb l el && cert_expr_eqb r er) ||
      expr_has_sdiv_pair el er l ||
      expr_has_sdiv_pair el er r
  | CE_ICmp _ _ _ l r =>
      expr_has_sdiv_pair el er l || expr_has_sdiv_pair el er r
  | CE_Cast _ _ _ _ o | CE_Freeze _ o =>
      expr_has_sdiv_pair el er o
  | CE_Select _ c t f =>
      expr_has_sdiv_pair el er c ||
      expr_has_sdiv_pair el er t ||
      expr_has_sdiv_pair el er f
  end.

Lemma expr_has_sdiv_pair_spec :
  forall el er big,
    expr_has_sdiv_pair el er big = true ->
    exists op w fl,
      (op = CB_SDiv \/ op = CB_SRem) /\
      is_syntactic_subexpr (CE_BinOp op w fl el er) big = true.
Proof.
  intros el er big.
  induction big as
    [ w val | w | nm w
    | op0 w0 fl0 l IHl r IHr
    | pr ss w0 l IHl r IHr
    | k fw tw fl0 o IHo
    | w0 c IHc t IHt f IHf
    | w0 o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros H; cbn [expr_has_sdiv_pair] in H; try discriminate H.
  - rewrite !orb_true_iff in H; destruct H as [[Hhere | Hl] | Hr].
    + rewrite !andb_true_iff in Hhere; destruct Hhere as ([Hop Heql] & Heqr).
      apply cert_expr_eqb_eq in Heql; apply cert_expr_eqb_eq in Heqr; subst l r.
      assert (Hop' : op0 = CB_SDiv \/ op0 = CB_SRem).
      { apply orb_true_iff in Hop as [Hs | Hr0];
          [left; apply cert_binop_eqb_eq, Hs | right; apply cert_binop_eqb_eq, Hr0]. }
      exists op0, w0, fl0; split; [exact Hop' |].
      cbn [is_syntactic_subexpr]; rewrite cert_expr_eqb_refl; reflexivity.
    + destruct (IHl Hl) as (op & w & fl & Hop & Hsub).
      exists op, w, fl; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
    + destruct (IHr Hr) as (op & w & fl & Hop & Hsub).
      exists op, w, fl; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
  - apply orb_true_iff in H as [Hl | Hr].
    + destruct (IHl Hl) as (op & w & fl & Hop & Hsub).
      exists op, w, fl; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
    + destruct (IHr Hr) as (op & w & fl & Hop & Hsub).
      exists op, w, fl; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
  - destruct (IHo H) as (op & w & fl & Hop & Hsub).
    exists op, w, fl; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
  - rewrite !orb_true_iff in H; destruct H as [[Hc | Ht] | Hf].
    + destruct (IHc Hc) as (op & w & fl & Hop & Hsub).
      exists op, w, fl; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
    + destruct (IHt Ht) as (op & w & fl & Hop & Hsub).
      exists op, w, fl; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
    + destruct (IHf Hf) as (op & w & fl & Hop & Hsub).
      exists op, w, fl; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
  - destruct (IHo H) as (op & w & fl & Hop & Hsub).
    exists op, w, fl; split; [exact Hop | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto].
Qed.

Lemma div_subexpr_rhs_not_poison {Pa : Params} :
  forall (penv : param_env Pa) foracle op w fl lhs rhs vsub,
    is_div_or_rem_op op = true ->
    wt_cert_expr [] (CE_BinOp op w fl lhs rhs) = true ->
    eval_closed_cert_expr penv foracle (CE_BinOp op w fl lhs rhs) = raise_ret vsub ->
    eval_closed_cert_expr penv foracle rhs <> raise_ret (DVALUE_Base DVALUE_Poison).
Proof.
  intros penv foracle op w fl lhs rhs vsub Hop Hwt Hev Er.
  cbn [wt_cert_expr] in Hwt; rewrite !andb_true_iff in Hwt.
  destruct Hwt as ((((_ & Hwtl) & _) & Hwl) & _); apply Pos.eqb_eq in Hwl.
  unfold eval_closed_cert_expr in Hev, Er; cbn [eval_cert_expr] in Hev.
  destruct (eval_cert_expr penv [] foracle lhs) as [| | | vl] eqn:El; try discriminate Hev.
  pose proof (eval_cert_expr_ret_wf_scalar lhs _ _ _ _ _ Hwtl El) as Hwfl.
  rewrite Hwl in Hwfl.
  destruct (eval_cert_div_rem_poison_rhs_ub penv [] foracle op w fl lhs rhs vl Hop Hwfl El Er)
    as [msg Hub].
  cbn [eval_cert_expr] in Hub; congruence.
Qed.

Lemma defined_div_subexpr_rhs_nonzero {Pa : Params} :
  forall (penv : param_env Pa) foracle ctx op w fl lhs rhs vsub,
    is_div_or_rem_op op = true ->
    expr_guaranteed_defined ctx lhs = true ->
    wt_cert_expr [] (CE_BinOp op w fl lhs rhs) = true ->
    wf_param_env_for (collect_free_vars [] (CE_BinOp op w fl lhs rhs)) penv ->
    ub_ctx_holds penv foracle ctx ->
    eval_closed_cert_expr penv foracle (CE_BinOp op w fl lhs rhs) = raise_ret vsub ->
    exists ir : @Integers.bit_int w,
      eval_closed_cert_expr penv foracle rhs =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w ir)) /\
      (@Integers.unsigned w ir <> 0)%Z.
Proof.
  intros penv foracle ctx op w fl lhs rhs vsub Hop Hdefl Hwt Hpenv Hctx Hev.
  pose proof (div_subexpr_rhs_not_poison penv foracle op w fl lhs rhs vsub Hop Hwt Hev) as Hnpsr.
  cbn [wt_cert_expr collect_free_vars] in Hwt, Hpenv; rewrite !andb_true_iff in Hwt.
  destruct Hwt as ((((_ & Hwtl) & Hwtr) & Hwl) & Hwr).
  apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
  assert (Hpl : wf_param_env_for (collect_free_vars [] lhs) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
  destruct (expr_guaranteed_defined_sound ctx lhs penv foracle Hdefl Hwtl Hpl Hctx)
    as [_ [il Hil]].
  revert il Hil; rewrite Hwl; intros il Hil.
  pose proof Hev as Hev0.
  unfold eval_closed_cert_expr in Hev0, Hil; cbn [eval_cert_expr] in Hev0.
  rewrite Hil in Hev0; cbn [eou_bind] in Hev0.
  destruct (eval_cert_expr penv [] foracle rhs) as [| | | vr] eqn:Er; try discriminate Hev0.
  cbn [eou_bind] in Hev0.
  pose proof (eval_cert_expr_ret_wf_scalar rhs _ _ _ _ _ Hwtr Er) as Hwfr.
  rewrite Hwr in Hwfr.
  destruct Hwfr as [-> | [ir ->]]; [exfalso; exact (Hnpsr Er) |].
  unfold eval_iop in Hev0; rewrite eval_iop_integer_base_same_width in Hev0.
  destruct op; cbn in Hop; try discriminate Hop;
    unfold cert_to_ibinop, eval_int_op in Hev0; cbn in Hev0.
  - destruct (@Integers.unsigned w ir =? 0)%Z eqn:Ez; [cbn in Hev0; discriminate Hev0 |].
    apply Z.eqb_neq in Ez; exists ir; split; [exact Er | exact Ez].
  - destruct (@Integers.signed w ir =? 0)%Z eqn:Ez; [cbn in Hev0; discriminate Hev0 |].
    apply Z.eqb_neq in Ez; exists ir; split; [exact Er |].
    intros Hu; apply Ez, signed_zero_iff_unsigned_zero; exact Hu.
  - destruct (@Integers.unsigned w ir =? 0)%Z eqn:Ez; [cbn in Hev0; discriminate Hev0 |].
    apply Z.eqb_neq in Ez; exists ir; split; [exact Er | exact Ez].
  - destruct (@Integers.signed w ir =? 0)%Z eqn:Ez; [cbn in Hev0; discriminate Hev0 |].
    apply Z.eqb_neq in Ez; exists ir; split; [exact Er |].
    intros Hu; apply Ez, signed_zero_iff_unsigned_zero; exact Hu.
Qed.

Lemma sdiv_subexpr_no_ovf {Pa : Params} :
  forall (penv : param_env Pa) foracle op w0 fl el er vsub w
         (il ir : @Integers.bit_int w),
    (op = CB_SDiv \/ op = CB_SRem) ->
    wt_cert_expr [] (CE_BinOp op w0 fl el er) = true ->
    eval_closed_cert_expr penv foracle (CE_BinOp op w0 fl el er) = raise_ret vsub ->
    eval_closed_cert_expr penv foracle el = raise_ret (DVALUE_Base (@DVALUE_I Pa w il)) ->
    eval_closed_cert_expr penv foracle er = raise_ret (DVALUE_Base (@DVALUE_I Pa w ir)) ->
    ~ (@Integers.signed w il = @Integers.min_signed w /\
       @Integers.signed w ir = (-1)%Z).
Proof.
  intros penv foracle op w0 fl el er vsub w il ir Hop Hwt Hev El Er [Hmin Hm1].
  cbn [wt_cert_expr] in Hwt; rewrite !andb_true_iff in Hwt.
  destruct Hwt as ((((_ & Hwtl) & _) & Hwl) & _); apply Pos.eqb_eq in Hwl.
  pose proof (eval_cert_expr_ret_wf_scalar el _ _ _ _ _ Hwtl El) as Hwfl.
  rewrite Hwl in Hwfl.
  destruct Hwfl as [Hps | [il0 Heq0]]; [discriminate Hps |].
  injection Heq0 as Heq_dv.
  pose proof (dvalue_I_width_eq _ _ _ _ Heq_dv) as Hweq; subst w0; clear il0 Heq0 Heq_dv.
  unfold eval_closed_cert_expr in Hev, El, Er; cbn [eval_cert_expr] in Hev.
  rewrite El, Er in Hev; cbn [eou_bind] in Hev.
  unfold eval_iop in Hev; rewrite eval_iop_integer_base_same_width in Hev.
  destruct Hop as [-> | ->];
    unfold cert_to_ibinop, eval_int_op in Hev; cbn in Hev;
    rewrite Hmin, Hm1, Z.eqb_refl in Hev; cbn in Hev; discriminate Hev.
Qed.

Definition check_ub_assumption_justified
  (allowed : list (string * positive))
  (d_src : cfg_dag)
  (ctx : ub_ctx)
  (ua : ub_assumption) : bool :=
  let src_evals := spine_src_evals d_src in
  let src_brs := spine_branch_conds d_src in
  match ua with
  | UBA_UnreachableEliminated =>
      spine_is_unreachable d_src || ctx_has_unreachable ctx
  | UBA_ParamNoUndef param w =>
      negb (starts_with_dollar param) &&
      var_pair_in (param, w) allowed &&
      (spine_is_unreachable d_src ||
       ctx_has_unreachable ctx ||
       ctx_has_param_noundef ctx param w ||
       ctx_has_branch_cond_defined ctx (CE_Var param w) ||
       existsb (cert_expr_eqb (CE_Var param w)) src_brs ||
       existsb (expr_has_div_with_rhs (CE_Var param w)) src_evals)
  | UBA_BranchCondDefined cond_e =>
      wt_cert_expr [] cond_e &&
      wf_let_dag [] cond_e &&
      vars_subset_b (collect_free_vars [] cond_e) allowed &&
      let ec := expand_lets cond_e in
      (spine_is_unreachable d_src ||
       ctx_has_unreachable ctx ||
       ctx_has_branch_cond_defined ctx ec ||
       expr_guaranteed_defined ctx ec ||
       existsb (cert_expr_eqb ec) src_brs ||
       existsb (expr_has_div_with_rhs ec) src_evals)
  | UBA_DivisorNonZero div_e =>
      wt_cert_expr [] div_e &&
      wf_let_dag [] div_e &&
      vars_subset_b (collect_free_vars [] div_e) allowed &&
      let ed := expand_lets div_e in
      (spine_is_unreachable d_src ||
       ctx_has_unreachable ctx ||
       ctx_has_divisor_nonzero ctx ed ||
       is_nonzero_bv_const ed ||
       existsb (expr_has_defined_div_rhs ctx ed) src_evals)
  | UBA_SignedDivNoOverflow lhs_e rhs_e =>
      wt_cert_expr [] lhs_e &&
      wt_cert_expr [] rhs_e &&
      Pos.eqb (cert_expr_bit_width lhs_e) (cert_expr_bit_width rhs_e) &&
      wf_let_dag [] lhs_e &&
      wf_let_dag [] rhs_e &&
      vars_subset_b (collect_free_vars [] lhs_e) allowed &&
      vars_subset_b (collect_free_vars [] rhs_e) allowed &&
      let el := expand_lets lhs_e in
      let er := expand_lets rhs_e in
      (spine_is_unreachable d_src ||
       ctx_has_unreachable ctx ||
       is_safe_sdiv_bv_const er ||
       existsb (expr_has_sdiv_pair el er) src_evals)
  | UBA_PtrNonNull _
  | UBA_PtrAligned _ _
  | UBA_PtrDereferenceable _ _
  | UBA_LoadNoUndef _ _ => true
  end.

Lemma check_ub_assumption_justified_sound {Pa : Params} :
  forall allowed d_src ctx ua (penv : param_env Pa) foracle v_src,
    wf_cfg_dag allowed d_src = true ->
    wf_param_env_for allowed penv ->
    eval_cfg_dag penv foracle d_src = DO_Ret v_src ->
    ub_ctx_holds penv foracle ctx ->
    check_ub_assumption_justified allowed d_src ctx ua = true ->
    ub_assumption_holds penv foracle ua.
Proof.
  intros allowed d_src ctx ua penv foracle v_src Hwfd Hpenv Hevd Hctx Hchk.
  destruct ua as
    [ param w | param | param align | param bytes | slot w
    | div_e | lhs_e rhs_e | cond_e | ];
    cbn [check_ub_assumption_justified ub_assumption_holds] in Hchk |- *; try exact I.
  - (* UBA_ParamNoUndef *)
    rewrite !andb_true_iff in Hchk; destruct Hchk as ([Hnd Hvp] & Hjust).
    intros dv Hpm ->.
    apply var_pair_in_spec in Hvp.
    destruct (Hpenv param w Hvp) as [dv0 [Hpm0 Hwfv]]; rewrite Hpm in Hpm0; injection Hpm0 as <-.
    assert (Hev_var : eval_closed_cert_expr penv foracle (CE_Var param w) =
                      raise_ret (DVALUE_Base DVALUE_Poison)).
    { unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val].
      rewrite Hpm; exact (check_scalar_width_ok w (DVALUE_Base DVALUE_Poison) Hwfv). }
    rewrite !orb_true_iff in Hjust.
    destruct Hjust as [[[[[Hunr | Hcu] | Hnu] | Hbrc] | Hex_br] | Hex_div].
    + rewrite (spine_is_unreachable_sound penv foracle d_src Hunr) in Hevd; discriminate Hevd.
    + exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + exact (ctx_has_param_noundef_sound penv foracle ctx param w _ Hnu Hctx Hpm eq_refl).
    + exact (ctx_has_branch_cond_defined_sound penv foracle ctx _ _ Hbrc Hctx Hev_var eq_refl).
    + apply existsb_exists in Hex_br as [c [Hcin Hceq]]; apply cert_expr_eqb_eq in Hceq; subst c.
      destruct (spine_branch_conds_ret penv foracle d_src v_src _ Hevd Hcin) as [cbit Ec].
      congruence.
    + apply existsb_exists in Hex_div as [big [Hbin Hdiv]].
      destruct (expr_has_div_with_rhs_spec _ big Hdiv) as (op & w0 & fl & lhs & Hop & Hsub).
      destruct (spine_src_evals_wf allowed d_src big Hwfd Hbin) as (Hwtb & Hlfb & Hfvb).
      destruct (is_syntactic_subexpr_wt_fv _ big allowed Hsub Hwtb Hlfb Hfvb) as (Hwts & _ & _).
      destruct (spine_src_evals_ret penv foracle d_src v_src big Hevd Hbin) as [vbig Hvbig].
      destruct (is_syntactic_subexpr_eval_ret _ big penv [] foracle vbig Hsub Hvbig) as [vsub Hvsub].
      exact (div_subexpr_rhs_not_poison penv foracle op w0 fl lhs (CE_Var param w) vsub
               Hop Hwts Hvsub Hev_var).
  - (* UBA_DivisorNonZero *)
    cbn zeta in Hchk; rewrite !andb_true_iff in Hchk.
    destruct Hchk as (((Hwt & _) & Hsub_fv) & Hjust).
    set (ed := expand_lets div_e) in *.
    destruct (expand_lets_with_typing div_e [] [] Hwt wf_let_subst_nil) as (_ & Hwt_ed & _).
    pose proof (vars_subset_b_wf_param _ allowed penv Hsub_fv Hpenv) as Hp_div.
    pose proof (expand_lets_with_wf_param_env div_e [] penv (fun _ _ H => False_ind _ H) Hp_div)
      as Hp_ed.
    rewrite !orb_true_iff in Hjust.
    destruct Hjust as [[[[Hunr | Hcu] | Hcd] | Hc_nz] | Hex_div].
    + rewrite (spine_is_unreachable_sound penv foracle d_src Hunr) in Hevd; discriminate Hevd.
    + exfalso; exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + exact (ctx_has_divisor_nonzero_sound penv foracle ctx ed Hcd Hctx).
    + exact (is_nonzero_bv_const_sound penv foracle ed Hc_nz).
    + apply existsb_exists in Hex_div as [big [Hbin Hdiv]].
      destruct (expr_has_defined_div_rhs_spec ctx ed big Hdiv)
        as (op & w0 & fl & lhs & Hop & Hdefl & Hsub).
      destruct (spine_src_evals_wf allowed d_src big Hwfd Hbin) as (Hwtb & Hlfb & Hfvb).
      destruct (is_syntactic_subexpr_wt_fv _ big allowed Hsub Hwtb Hlfb Hfvb)
        as (Hwts & _ & Hfvs).
      assert (Hps : wf_param_env_for (collect_free_vars [] (CE_BinOp op w0 fl lhs ed)) penv)
        by (intros x wx Hx; exact (Hpenv x wx (Hfvs (x, wx) Hx))).
      destruct (spine_src_evals_ret penv foracle d_src v_src big Hevd Hbin) as [vbig Hvbig].
      destruct (is_syntactic_subexpr_eval_ret _ big penv [] foracle vbig Hsub Hvbig) as [vsub Hvsub].
      destruct (defined_div_subexpr_rhs_nonzero penv foracle ctx op w0 fl lhs ed vsub
                  Hop Hdefl Hwts Hps Hctx Hvsub) as [ir [Eed Hnz]].
      exists w0, ir; split; [exact Eed | exact Hnz].
  - (* UBA_SignedDivNoOverflow *)
    cbn zeta in Hchk; rewrite !andb_true_iff in Hchk.
    destruct Hchk as (((((((_ & _) & _) & _) & _) & _) & _) & Hjust).
    set (el := expand_lets lhs_e) in *; set (er := expand_lets rhs_e) in *.
    intros w il ir El Er.
    rewrite !orb_true_iff in Hjust.
    destruct Hjust as [[[Hunr | Hcu] | Hsafe] | Hex_sdiv].
    + rewrite (spine_is_unreachable_sound penv foracle d_src Hunr) in Hevd; discriminate Hevd.
    + exfalso; exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + destruct (is_safe_sdiv_bv_const_sound penv foracle er Hsafe)
        as (w' & ir' & Eer' & _ & _ & Hnm1).
      rewrite Er in Eer'; injection Eer' as Heq_dv.
      pose proof (dvalue_I_width_eq _ _ _ _ Heq_dv) as Hweq; subst w'.
      pose proof (dvalue_I_same_sz_inj _ _ _ Heq_dv) as <-.
      intros [_ Hm1]; exact (Hnm1 Hm1).
    + apply existsb_exists in Hex_sdiv as [big [Hbin Hsdiv]].
      destruct (expr_has_sdiv_pair_spec el er big Hsdiv) as (op & w0 & fl & Hop & Hsub).
      destruct (spine_src_evals_wf allowed d_src big Hwfd Hbin) as (Hwtb & Hlfb & Hfvb).
      destruct (is_syntactic_subexpr_wt_fv _ big allowed Hsub Hwtb Hlfb Hfvb) as (Hwts & _ & _).
      destruct (spine_src_evals_ret penv foracle d_src v_src big Hevd Hbin) as [vbig Hvbig].
      destruct (is_syntactic_subexpr_eval_ret _ big penv [] foracle vbig Hsub Hvbig) as [vsub Hvsub].
      exact (sdiv_subexpr_no_ovf penv foracle op w0 fl el er vsub w il ir Hop Hwts Hvsub El Er).
  - (* UBA_BranchCondDefined *)
    cbn zeta in Hchk; rewrite !andb_true_iff in Hchk.
    destruct Hchk as (((Hwt & _) & Hsub_fv) & Hjust).
    set (ec := expand_lets cond_e) in *.
    destruct (expand_lets_with_typing cond_e [] [] Hwt wf_let_subst_nil) as (_ & Hwt_ec & _).
    pose proof (vars_subset_b_wf_param _ allowed penv Hsub_fv Hpenv) as Hp_cond.
    pose proof (expand_lets_with_wf_param_env cond_e [] penv (fun _ _ H => False_ind _ H) Hp_cond)
      as Hp_ec.
    intros v Hevc ->.
    rewrite !orb_true_iff in Hjust.
    destruct Hjust as [[[[[Hunr | Hcu] | Hbrc] | Hdef] | Hex_br] | Hex_div].
    + rewrite (spine_is_unreachable_sound penv foracle d_src Hunr) in Hevd; discriminate Hevd.
    + exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + exact (ctx_has_branch_cond_defined_sound penv foracle ctx ec _ Hbrc Hctx Hevc eq_refl).
    + destruct (expr_guaranteed_defined_sound ctx ec penv foracle Hdef Hwt_ec Hp_ec Hctx)
        as [_ [ic Hic]].
      congruence.
    + apply existsb_exists in Hex_br as [c [Hcin Hceq]]; apply cert_expr_eqb_eq in Hceq; subst c.
      destruct (spine_branch_conds_ret penv foracle d_src v_src ec Hevd Hcin) as [cbit Ec].
      congruence.
    + apply existsb_exists in Hex_div as [big [Hbin Hdiv]].
      destruct (expr_has_div_with_rhs_spec ec big Hdiv) as (op & w0 & fl & lhs & Hop & Hsub).
      destruct (spine_src_evals_wf allowed d_src big Hwfd Hbin) as (Hwtb & Hlfb & Hfvb).
      destruct (is_syntactic_subexpr_wt_fv _ big allowed Hsub Hwtb Hlfb Hfvb) as (Hwts & _ & _).
      destruct (spine_src_evals_ret penv foracle d_src v_src big Hevd Hbin) as [vbig Hvbig].
      destruct (is_syntactic_subexpr_eval_ret _ big penv [] foracle vbig Hsub Hvbig) as [vsub Hvsub].
      exact (div_subexpr_rhs_not_poison penv foracle op w0 fl lhs ec vsub Hop Hwts Hvsub Hevc).
  - (* UBA_UnreachableEliminated *)
    apply orb_true_iff in Hchk as [Hunr | Hcu].
    + rewrite (spine_is_unreachable_sound penv foracle d_src Hunr) in Hevd; discriminate Hevd.
    + exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
Qed.

Fixpoint check_ub_assumptions_list
  (allowed : list (string * positive))
  (d_src : cfg_dag)
  (acc_ctx : ub_ctx)
  (uas : list ub_assumption) : option ub_ctx :=
  match uas with
  | [] => Some acc_ctx
  | ua :: rest =>
      if check_ub_assumption_justified allowed d_src acc_ctx ua
      then check_ub_assumptions_list allowed d_src (ua :: acc_ctx) rest
      else None
  end.

Lemma check_ub_assumptions_list_sound {Pa : Params} :
  forall uas allowed d_src acc_ctx final_ctx (penv : param_env Pa) foracle v_src,
    wf_cfg_dag allowed d_src = true ->
    wf_param_env_for allowed penv ->
    eval_cfg_dag penv foracle d_src = DO_Ret v_src ->
    ub_ctx_holds penv foracle acc_ctx ->
    check_ub_assumptions_list allowed d_src acc_ctx uas = Some final_ctx ->
    ub_ctx_holds penv foracle final_ctx.
Proof.
  induction uas as [| ua rest IH];
    intros allowed d_src acc_ctx final_ctx penv foracle v_src Hwfd Hpenv Hevd Hacc Hchk;
    cbn [check_ub_assumptions_list] in Hchk.
  - inversion Hchk; subst; exact Hacc.
  - destruct (check_ub_assumption_justified allowed d_src acc_ctx ua) eqn:Hua; [| discriminate Hchk].
    pose proof (check_ub_assumption_justified_sound allowed d_src acc_ctx ua penv foracle v_src
                  Hwfd Hpenv Hevd Hacc Hua) as Hua_holds.
    exact (IH allowed d_src (ua :: acc_ctx) final_ctx penv foracle v_src
              Hwfd Hpenv Hevd (Forall_cons ua Hua_holds Hacc) Hchk).
Qed.

Fixpoint ctx_has_sdiv_no_ovf (ctx : ub_ctx) (el er : cert_expr) : bool :=
  match ctx with
  | [] => false
  | UBA_SignedDivNoOverflow l r :: rest =>
      (cert_expr_eqb (expand_lets l) el && cert_expr_eqb (expand_lets r) er) ||
      ctx_has_sdiv_no_ovf rest el er
  | _ :: rest => ctx_has_sdiv_no_ovf rest el er
  end.

Lemma ctx_has_sdiv_no_ovf_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle ctx el er w (il ir : @Integers.bit_int w),
    ctx_has_sdiv_no_ovf ctx el er = true ->
    ub_ctx_holds penv foracle ctx ->
    eval_closed_cert_expr penv foracle el = raise_ret (DVALUE_Base (@DVALUE_I Pa w il)) ->
    eval_closed_cert_expr penv foracle er = raise_ret (DVALUE_Base (@DVALUE_I Pa w ir)) ->
    ~ (@Integers.signed w il = @Integers.min_signed w /\
       @Integers.signed w ir = (-1)%Z).
Proof.
  intros penv foracle ctx el er w il ir H Hctx El Er.
  induction Hctx as [| ua rest Hua Hrest IH]; [discriminate H |].
  destruct ua; cbn in H; try exact (IH H).
  apply orb_true_iff in H as [Hhere | Hlater]; [| exact (IH Hlater)].
  apply andb_true_iff in Hhere as [Hl Hr].
  apply cert_expr_eqb_eq in Hl; apply cert_expr_eqb_eq in Hr; subst el er.
  exact (Hua w il ir El Er).
Qed.

Fixpoint expr_safe_under_src
  (ctx : ub_ctx)
  (src_evals : list cert_expr)
  (e : cert_expr) {struct e} : bool :=
  ctx_has_unreachable ctx ||
  ub_free_expr e ||
  existsb (is_syntactic_subexpr e) src_evals ||
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ => true
  | CE_Let _ _ => false
  | CE_ICmp _ _ _ l r =>
      expr_safe_under_src ctx src_evals l &&
      expr_safe_under_src ctx src_evals r
  | CE_Cast _ _ _ _ o | CE_Freeze _ o =>
      expr_safe_under_src ctx src_evals o
  | CE_Select _ c t f =>
      expr_safe_under_src ctx src_evals c &&
      expr_safe_under_src ctx src_evals t &&
      expr_safe_under_src ctx src_evals f
  | CE_BinOp op _ _ l r =>
      expr_safe_under_src ctx src_evals l &&
      expr_safe_under_src ctx src_evals r &&
      match op with
      | CB_UDiv | CB_URem =>
          is_nonzero_bv_const r || ctx_has_divisor_nonzero ctx r
      | CB_SDiv | CB_SRem =>
          is_safe_sdiv_bv_const r ||
          ((is_nonzero_bv_const r || ctx_has_divisor_nonzero ctx r) &&
           expr_guaranteed_defined ctx l &&
           ctx_has_sdiv_no_ovf ctx l r)
      | _ => true
      end
  end.

Lemma expr_safe_under_src_no_ub {Pa : Params} :
  forall e ctx src_evals (penv : param_env Pa) foracle msg,
    expr_safe_under_src ctx src_evals e = true ->
    wt_cert_expr [] e = true ->
    wf_param_env_for (collect_free_vars [] e) penv ->
    ub_ctx_holds penv foracle ctx ->
    (forall big, In big src_evals -> exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv) ->
    eval_closed_cert_expr penv foracle e <> raise_ub msg.
Proof.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros ctx src_evals penv foracle msg Hsafe Hwt Hpenv Hctx Hsrc Hev.
  - discriminate Hev.
  - discriminate Hev.
  - exact (ub_free_expr_no_ub (CE_Var nm w) [] penv [] foracle msg eq_refl Hwt Hev).
  - cbn [expr_safe_under_src] in Hsafe; rewrite !orb_true_iff in Hsafe.
    destruct Hsafe as [[[Hcu | Hubf] | Hex] | Hrec].
    + exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + exact (ub_free_expr_no_ub _ [] penv [] foracle msg Hubf Hwt Hev).
    + apply existsb_exists in Hex as [big [Hbin Hsub]].
      destruct (Hsrc big Hbin) as [vbig Hvbig].
      destruct (is_syntactic_subexpr_eval_ret _ big penv [] foracle vbig Hsub Hvbig) as [ve Hve].
      unfold eval_closed_cert_expr in *; congruence.
    + rewrite !andb_true_iff in Hrec; destruct Hrec as ([Hsl Hsr] & Hop_ok).
      cbn [wt_cert_expr collect_free_vars] in Hwt, Hpenv; rewrite !andb_true_iff in Hwt.
      destruct Hwt as ((((_ & Hwtl) & Hwtr) & Hwl) & Hwr).
      apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
      assert (Hpl : wf_param_env_for (collect_free_vars [] l) penv)
        by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
      assert (Hpr : wf_param_env_for (collect_free_vars [] r) penv)
        by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
      unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev.
      destruct (eval_cert_expr penv [] foracle l) as [| sl | | vl] eqn:El;
        cbn [eou_bind] in Hev; try discriminate Hev.
      * inversion Hev; subst sl; exact (IHl ctx src_evals penv foracle msg Hsl Hwtl Hpl Hctx Hsrc El).
      * destruct (eval_cert_expr penv [] foracle r) as [| sr | | vr] eqn:Er;
          cbn [eou_bind] in Hev; try discriminate Hev.
        -- inversion Hev; subst sr; exact (IHr ctx src_evals penv foracle msg Hsr Hwtr Hpr Hctx Hsrc Er).
        -- pose proof (eval_cert_expr_ret_wf_scalar l _ _ _ _ _ Hwtl El) as Hwfl.
           pose proof (eval_cert_expr_ret_wf_scalar r _ _ _ _ _ Hwtr Er) as Hwfr.
           rewrite Hwl in Hwfl; rewrite Hwr in Hwfr.
           destruct (is_div_or_rem_op op) eqn:Ediv.
           ++ assert (Hextract_nz :
                is_nonzero_bv_const r || ctx_has_divisor_nonzero ctx r = true ->
                exists ir : @Integers.bit_int w,
                  vr = DVALUE_Base (@DVALUE_I Pa w ir) /\ (@Integers.unsigned w ir <> 0)%Z).
              { intros Hnz_or.
                assert (Hex_nz : exists w' (ir' : @Integers.bit_int w'),
                  eval_closed_cert_expr penv foracle r = raise_ret (DVALUE_Base (@DVALUE_I Pa w' ir')) /\
                  (@Integers.unsigned w' ir' <> 0)%Z).
                { apply orb_true_iff in Hnz_or as [Hcn | Hdn];
                    [exact (is_nonzero_bv_const_sound penv foracle r Hcn)
                    | exact (ctx_has_divisor_nonzero_sound penv foracle ctx r Hdn Hctx)]. }
                destruct Hex_nz as (w' & ir' & Er' & Hnz').
                unfold eval_closed_cert_expr in Er'; rewrite Er in Er'; injection Er' as <-.
                destruct Hwfr as [Hps | [ir0 Heq0]]; [discriminate Hps |].
                injection Heq0 as Heq_dv.
                pose proof (dvalue_I_width_eq _ _ _ _ Heq_dv) as Hweq; subst w'.
                exists ir'; split; [reflexivity | exact Hnz']. }
              destruct op; cbn in Ediv; try discriminate Ediv.
              ** (* CB_UDiv *)
                 destruct (Hextract_nz Hop_ok) as [ir [-> Hnz]].
                 destruct Hwfl as [-> | [il ->]]; [cbn in Hev; discriminate Hev |].
                 unfold eval_iop in Hev; rewrite eval_iop_integer_base_same_width in Hev.
                 unfold cert_to_ibinop, eval_int_op in Hev; cbn in Hev.
                 rewrite (proj2 (Z.eqb_neq (@Integers.unsigned w ir) 0%Z) Hnz) in Hev.
                 repeat match type of Hev with context [if ?b then _ else _] => destruct b end;
                   cbn in Hev; discriminate Hev.
              ** (* CB_SDiv *)
                 apply orb_true_iff in Hop_ok as [Hsafe_c | Hguarded].
                 --- destruct (is_safe_sdiv_bv_const_sound penv foracle r Hsafe_c)
                       as (w' & ir' & Er' & _ & Hnsz & Hnsm).
                     unfold eval_closed_cert_expr in Er'; rewrite Er in Er'; injection Er' as <-.
                     destruct Hwfr as [Hps | [ir0 Heq0]]; [discriminate Hps |].
                     injection Heq0 as Heq_dv; pose proof (dvalue_I_width_eq _ _ _ _ Heq_dv) as ->.
                     destruct Hwfl as [-> | [il ->]].
                     +++ cbn in Hev; destruct (Z.eq_dec (@Integers.signed w ir') (-1)%Z) as [Hm1 | _];
                           [exact (Hnsm Hm1) | cbn in Hev; discriminate Hev].
                     +++ unfold eval_iop in Hev; rewrite eval_iop_integer_base_same_width in Hev.
                         unfold cert_to_ibinop, eval_int_op in Hev; cbn in Hev.
                         rewrite (proj2 (Z.eqb_neq (@Integers.signed w ir') 0%Z) Hnsz) in Hev.
                         rewrite (proj2 (Z.eqb_neq (@Integers.signed w ir') (-1)%Z) Hnsm), Bool.andb_false_r in Hev.
                         repeat match type of Hev with context [if ?b then _ else _] => destruct b end;
                           cbn in Hev; discriminate Hev.
                 --- rewrite !andb_true_iff in Hguarded; destruct Hguarded as ([Hnz_or Hdefl] & Hnovf).
                     destruct (Hextract_nz Hnz_or) as [ir [-> Hnz]]; subst vr.
                     assert (Hnsz : (@Integers.signed w ir <> 0)%Z)
                       by (intros Hs; apply Hnz, signed_zero_iff_unsigned_zero; exact Hs).
                     destruct (expr_guaranteed_defined_sound ctx l penv foracle Hdefl Hwtl Hpl Hctx)
                       as [_ [il0 Hil0]].
                     revert il0 Hil0; rewrite Hwl; intros il0 Hil0.
                     unfold eval_closed_cert_expr in Hil0; rewrite El in Hil0; injection Hil0 as ->.
                     pose proof (ctx_has_sdiv_no_ovf_sound penv foracle ctx l r w il0 ir Hnovf Hctx El Er)
                       as Hno_ovf.
                     unfold eval_iop in Hev; rewrite eval_iop_integer_base_same_width in Hev.
                     unfold cert_to_ibinop, eval_int_op in Hev; cbn in Hev.
                     rewrite (proj2 (Z.eqb_neq (@Integers.signed w ir) 0%Z) Hnsz) in Hev.
                     destruct ((@Integers.min_signed w =? @Integers.signed w il0)%Z &&
                               (@Integers.signed w ir =? -1)%Z) eqn:Eovf.
                     +++ apply andb_true_iff in Eovf as [Em1 Em2].
                         apply Z.eqb_eq in Em1; apply Z.eqb_eq in Em2.
                         exact (Hno_ovf (conj (eq_sym Em1) Em2)).
                     +++ repeat match type of Hev with context [if ?b then _ else _] => destruct b end;
                           cbn in Hev; discriminate Hev.
              ** (* CB_URem *)
                 destruct (Hextract_nz Hop_ok) as [ir [-> Hnz]].
                 destruct Hwfl as [-> | [il ->]]; [cbn in Hev; discriminate Hev |].
                 unfold eval_iop in Hev; rewrite eval_iop_integer_base_same_width in Hev.
                 unfold cert_to_ibinop, eval_int_op in Hev; cbn in Hev.
                 rewrite (proj2 (Z.eqb_neq (@Integers.unsigned w ir) 0%Z) Hnz) in Hev.
                 cbn in Hev; discriminate Hev.
              ** (* CB_SRem *)
                 apply orb_true_iff in Hop_ok as [Hsafe_c | Hguarded].
                 --- destruct (is_safe_sdiv_bv_const_sound penv foracle r Hsafe_c)
                       as (w' & ir' & Er' & _ & Hnsz & Hnsm).
                     unfold eval_closed_cert_expr in Er'; rewrite Er in Er'; injection Er' as <-.
                     destruct Hwfr as [Hps | [ir0 Heq0]]; [discriminate Hps |].
                     injection Heq0 as Heq_dv; pose proof (dvalue_I_width_eq _ _ _ _ Heq_dv) as ->.
                     destruct Hwfl as [-> | [il ->]].
                     +++ cbn in Hev; destruct (Z.eq_dec (@Integers.signed w ir') (-1)%Z) as [Hm1 | _];
                           [exact (Hnsm Hm1) | cbn in Hev; discriminate Hev].
                     +++ unfold eval_iop in Hev; rewrite eval_iop_integer_base_same_width in Hev.
                         unfold cert_to_ibinop, eval_int_op in Hev; cbn in Hev.
                         rewrite (proj2 (Z.eqb_neq (@Integers.signed w ir') 0%Z) Hnsz) in Hev.
                         rewrite (proj2 (Z.eqb_neq (@Integers.signed w ir') (-1)%Z) Hnsm), Bool.andb_false_r in Hev.
                         cbn in Hev; discriminate Hev.
                 --- rewrite !andb_true_iff in Hguarded; destruct Hguarded as ([Hnz_or Hdefl] & Hnovf).
                     destruct (Hextract_nz Hnz_or) as [ir [-> Hnz]]; subst vr.
                     assert (Hnsz : (@Integers.signed w ir <> 0)%Z)
                       by (intros Hs; apply Hnz, signed_zero_iff_unsigned_zero; exact Hs).
                     destruct (expr_guaranteed_defined_sound ctx l penv foracle Hdefl Hwtl Hpl Hctx)
                       as [_ [il0 Hil0]].
                     revert il0 Hil0; rewrite Hwl; intros il0 Hil0.
                     unfold eval_closed_cert_expr in Hil0; rewrite El in Hil0; injection Hil0 as ->.
                     pose proof (ctx_has_sdiv_no_ovf_sound penv foracle ctx l r w il0 ir Hnovf Hctx El Er)
                       as Hno_ovf.
                     unfold eval_iop in Hev; rewrite eval_iop_integer_base_same_width in Hev.
                     unfold cert_to_ibinop, eval_int_op in Hev; cbn in Hev.
                     rewrite (proj2 (Z.eqb_neq (@Integers.signed w ir) 0%Z) Hnsz) in Hev.
                     destruct ((@Integers.min_signed w =? @Integers.signed w il0)%Z &&
                               (@Integers.signed w ir =? -1)%Z) eqn:Eovf.
                     +++ apply andb_true_iff in Eovf as [Em1 Em2].
                         apply Z.eqb_eq in Em1; apply Z.eqb_eq in Em2.
                         exact (Hno_ovf (conj (eq_sym Em1) Em2)).
                     +++ cbn in Hev; discriminate Hev.
           ++ destruct (eval_iop_non_div_rem_no_ub op fl w vl vr Ediv Hwfl Hwfr) as [v' [Hv' _]];
                congruence.
  - cbn [expr_safe_under_src] in Hsafe; rewrite !orb_true_iff in Hsafe.
    destruct Hsafe as [[[Hcu | Hubf] | Hex] | Hrec].
    + exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + exact (ub_free_expr_no_ub _ [] penv [] foracle msg Hubf Hwt Hev).
    + apply existsb_exists in Hex as [big [Hbin Hsub]].
      destruct (Hsrc big Hbin) as [vbig Hvbig].
      destruct (is_syntactic_subexpr_eval_ret _ big penv [] foracle vbig Hsub Hvbig) as [ve Hve].
      unfold eval_closed_cert_expr in *; congruence.
    + apply andb_true_iff in Hrec as [Hsl Hsr].
      cbn [wt_cert_expr collect_free_vars] in Hwt, Hpenv; rewrite !andb_true_iff in Hwt.
      destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr).
      apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
      assert (Hpl : wf_param_env_for (collect_free_vars [] l) penv)
        by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
      assert (Hpr : wf_param_env_for (collect_free_vars [] r) penv)
        by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
      unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev.
      destruct (eval_cert_expr penv [] foracle l) as [| sl | | vl] eqn:El;
        cbn [eou_bind] in Hev; try discriminate Hev.
      * inversion Hev; subst sl; exact (IHl ctx src_evals penv foracle msg Hsl Hwtl Hpl Hctx Hsrc El).
      * destruct (eval_cert_expr penv [] foracle r) as [| sr | | vr] eqn:Er;
          cbn [eou_bind] in Hev; try discriminate Hev.
        -- inversion Hev; subst sr; exact (IHr ctx src_evals penv foracle msg Hsr Hwtr Hpr Hctx Hsrc Er).
        -- pose proof (eval_cert_expr_ret_wf_scalar l _ _ _ _ _ Hwtl El) as Hwfl.
           pose proof (eval_cert_expr_ret_wf_scalar r _ _ _ _ _ Hwtr Er) as Hwfr.
           rewrite Hwl in Hwfl; rewrite Hwr in Hwfr.
           destruct (eval_icmp_wf_scalar ss pr w vl vr Hwfl Hwfr) as [v' [Hv' _]]; congruence.
  - cbn [expr_safe_under_src] in Hsafe; rewrite !orb_true_iff in Hsafe.
    destruct Hsafe as [[[Hcu | Hubf] | Hex] | Hso].
    + exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + exact (ub_free_expr_no_ub _ [] penv [] foracle msg Hubf Hwt Hev).
    + apply existsb_exists in Hex as [big [Hbin Hsub]].
      destruct (Hsrc big Hbin) as [vbig Hvbig].
      destruct (is_syntactic_subexpr_eval_ret _ big penv [] foracle vbig Hsub Hvbig) as [ve Hve].
      unfold eval_closed_cert_expr in *; congruence.
    + cbn [wt_cert_expr collect_free_vars] in Hwt, Hpenv; rewrite !andb_true_iff in Hwt.
      destruct Hwt as ((Hk & Hwto) & Hwo); apply Pos.eqb_eq in Hwo.
      unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev.
      destruct (eval_cert_expr penv [] foracle o) as [| so | | vo] eqn:Eo;
        cbn [eou_bind] in Hev; try discriminate Hev.
      * inversion Hev; subst so; exact (IHo ctx src_evals penv foracle msg Hso Hwto Hpenv Hctx Hsrc Eo).
      * pose proof (eval_cert_expr_ret_wf_scalar o _ _ _ _ _ Hwto Eo) as Hwfo.
        rewrite Hwo in Hwfo.
        destruct (eval_cast_wf_scalar k fw tw fl vo Hk Hwfo) as [v' [Hv' _]]; congruence.
  - cbn [expr_safe_under_src] in Hsafe; rewrite !orb_true_iff in Hsafe.
    destruct Hsafe as [[[Hcu | Hubf] | Hex] | Hrec].
    + exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + exact (ub_free_expr_no_ub _ [] penv [] foracle msg Hubf Hwt Hev).
    + apply existsb_exists in Hex as [big [Hbin Hsub]].
      destruct (Hsrc big Hbin) as [vbig Hvbig].
      destruct (is_syntactic_subexpr_eval_ret _ big penv [] foracle vbig Hsub Hvbig) as [ve Hve].
      unfold eval_closed_cert_expr in *; congruence.
    + rewrite !andb_true_iff in Hrec; destruct Hrec as ([Hsc Hst] & Hsf).
      cbn [wt_cert_expr collect_free_vars] in Hwt, Hpenv; rewrite !andb_true_iff in Hwt.
      destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hwc) & Hwt0) & Hwf0).
      apply Pos.eqb_eq in Hwc; apply Pos.eqb_eq in Hwt0; apply Pos.eqb_eq in Hwf0.
      assert (Hpc : wf_param_env_for (collect_free_vars [] c) penv)
        by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
      assert (Hpt : wf_param_env_for (collect_free_vars [] t) penv)
        by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; left; exact Hx).
      assert (Hpf : wf_param_env_for (collect_free_vars [] f) penv)
        by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; right; exact Hx).
      unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev.
      destruct (eval_cert_expr penv [] foracle c) as [| sc | | vc] eqn:Ec;
        cbn [eou_bind] in Hev; try discriminate Hev.
      * inversion Hev; subst sc; exact (IHc ctx src_evals penv foracle msg Hsc Hwtc Hpc Hctx Hsrc Ec).
      * destruct (eval_cert_expr penv [] foracle t) as [| st | | vt] eqn:Et;
          cbn [eou_bind] in Hev; try discriminate Hev.
        -- inversion Hev; subst st; exact (IHt ctx src_evals penv foracle msg Hst Hwtt Hpt Hctx Hsrc Et).
        -- destruct (eval_cert_expr penv [] foracle f) as [| sf | | vf] eqn:Ef;
             cbn [eou_bind] in Hev; try discriminate Hev.
           ++ inversion Hev; subst sf; exact (IHf ctx src_evals penv foracle msg Hsf Hwtf Hpf Hctx Hsrc Ef).
           ++ pose proof (eval_cert_expr_ret_wf_scalar c _ _ _ _ _ Hwtc Ec) as Hwfc.
              pose proof (eval_cert_expr_ret_wf_scalar t _ _ _ _ _ Hwtt Et) as Hwft.
              pose proof (eval_cert_expr_ret_wf_scalar f _ _ _ _ _ Hwtf Ef) as Hwff.
              rewrite Hwc in Hwfc; rewrite Hwt0 in Hwft; rewrite Hwf0 in Hwff.
              destruct (eval_select_wf_scalar w vc vt vf Hwfc Hwft Hwff) as [v' [Hv' _]]; congruence.
  - cbn [expr_safe_under_src] in Hsafe; rewrite !orb_true_iff in Hsafe.
    destruct Hsafe as [[[Hcu | Hubf] | Hex] | Hso].
    + exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + exact (ub_free_expr_no_ub _ [] penv [] foracle msg Hubf Hwt Hev).
    + apply existsb_exists in Hex as [big [Hbin Hsub]].
      destruct (Hsrc big Hbin) as [vbig Hvbig].
      destruct (is_syntactic_subexpr_eval_ret _ big penv [] foracle vbig Hsub Hvbig) as [ve Hve].
      unfold eval_closed_cert_expr in *; congruence.
    + cbn [wt_cert_expr collect_free_vars] in Hwt, Hpenv; apply andb_true_iff in Hwt as [Hwto _].
      unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev.
      destruct (eval_cert_expr penv [] foracle o) as [| so | | vo] eqn:Eo;
        cbn [eou_bind] in Hev; try discriminate Hev.
      * inversion Hev; subst so; exact (IHo ctx src_evals penv foracle msg Hso Hwto Hpenv Hctx Hsrc Eo).
      * destruct vo as [[| | | | | | |] | |]; discriminate Hev.
  - cbn [expr_safe_under_src] in Hsafe; rewrite !orb_true_iff in Hsafe.
    destruct Hsafe as [[[Hcu | Hubf] | Hex] | Hfalse]; [| | | discriminate Hfalse].
    + exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + exact (ub_free_expr_no_ub _ [] penv [] foracle msg Hubf Hwt Hev).
    + apply existsb_exists in Hex as [big [Hbin Hsub]].
      destruct (Hsrc big Hbin) as [vbig Hvbig].
      destruct (is_syntactic_subexpr_eval_ret _ big penv [] foracle vbig Hsub Hvbig) as [ve Hve].
      unfold eval_closed_cert_expr in *; congruence.
Qed.

Lemma expr_safe_under_src_sound {Pa : Params} :
  forall e ctx src_evals (penv : param_env Pa) foracle,
    expr_safe_under_src ctx src_evals e = true ->
    wt_cert_expr [] e = true ->
    wf_param_env_for (collect_free_vars [] e) penv ->
    ub_ctx_holds penv foracle ctx ->
    (forall big, In big src_evals -> exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv) ->
    exists vout,
      eval_closed_cert_expr penv foracle e = raise_ret vout /\
      wf_scalar_dvalue (cert_expr_bit_width e) vout.
Proof.
  intros e ctx src_evals penv foracle Hsafe Hwt Hpenv Hctx Hsrc.
  destruct (eval_cert_expr_totality e [] penv [] foracle Hwt wf_let_val_env_nil Hpenv)
    as [[msg Hub] | Hret].
  - exfalso; exact (expr_safe_under_src_no_ub e ctx src_evals penv foracle msg Hsafe Hwt Hpenv Hctx Hsrc Hub).
  - exact Hret.
Qed.

Fixpoint src_dag_to_expr (w : positive) (d : cfg_dag) : option cert_expr :=
  match d with
  | CD_Unreachable | CD_RetVoid => None
  | CD_RetScalar w' ret_e =>
      if Pos.eqb w' w then Some ret_e else None
  | CD_Eval _ _ next => src_dag_to_expr w next
  | CD_Branch cond on_t on_f =>
      if spine_is_unreachable on_f then src_dag_to_expr w on_t
      else if spine_is_unreachable on_t then src_dag_to_expr w on_f
      else
        match src_dag_to_expr w on_t, src_dag_to_expr w on_f with
        | Some et, Some ef =>
            if ub_free_expr et && ub_free_expr ef
            then Some (CE_Select w cond et ef)
            else None
        | _, _ => None
        end
  end.

Lemma src_dag_to_expr_typing :
  forall allowed w d e,
    wf_cfg_dag allowed d = true ->
    src_dag_to_expr w d = Some e ->
    wt_cert_expr [] e = true /\
    cert_expr_bit_width e = w /\
    is_let_free_expr e = true /\
    incl (collect_free_vars [] e) allowed.
Proof.
  intros allowed w d; induction d as [| | w' ret_e | ws step_e next IH | cond on_t IHt on_f IHf];
    intros e Hwf Hr; cbn [wf_cfg_dag src_dag_to_expr] in Hwf, Hr; try discriminate Hr.
  - destruct (Pos.eqb w' w) eqn:Ebw; [| discriminate Hr]; apply Pos.eqb_eq in Ebw; subst w'.
    inversion Hr; subst e.
    rewrite !andb_true_iff in Hwf; destruct Hwf as (((Hwt & Hbw) & Hlf) & Hfv).
    apply Pos.eqb_eq in Hbw.
    exact (conj Hwt (conj Hbw (conj Hlf (vars_subset_b_incl _ _ Hfv)))).
  - rewrite !andb_true_iff in Hwf; destruct Hwf as (_ & Hwfn); exact (IH e Hwfn Hr).
  - rewrite !andb_true_iff in Hwf; destruct Hwf as (((((Hwtc & Hbwc) & Hlfc) & Hfvc) & Hwft) & Hwff).
    destruct (spine_is_unreachable on_f); [exact (IHt e Hwft Hr) |].
    destruct (spine_is_unreachable on_t); [exact (IHf e Hwff Hr) |].
    destruct (src_dag_to_expr w on_t) as [et |] eqn:Ert; [| discriminate Hr].
    destruct (src_dag_to_expr w on_f) as [ef |] eqn:Erf; [| discriminate Hr].
    destruct (ub_free_expr et && ub_free_expr ef); [| discriminate Hr].
    inversion Hr; subst e; clear Hr.
    destruct (IHt et Hwft Ert) as (Hwtt & Hbwt & Hlft & Hfvt).
    destruct (IHf ef Hwff Erf) as (Hwtf & Hbwf & Hlff & Hfvf).
    cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars].
    rewrite Hwtc, Hwtt, Hwtf, Hbwc, Hbwt, Hbwf, !Pos.eqb_refl, Hlfc, Hlft, Hlff.
    repeat split; try reflexivity.
    intros u Hu; apply in_app_iff in Hu as [Huc | Hutf]; [exact (vars_subset_b_incl _ _ Hfvc u Huc) |].
    apply in_app_iff in Hutf as [Hut | Huf]; [exact (Hfvt u Hut) | exact (Hfvf u Huf)].
Qed.

Lemma src_dag_to_expr_sound {Pa : Params} :
  forall allowed w d e (penv : param_env Pa) foracle dv_src,
    wf_cfg_dag allowed d = true ->
    wf_param_env_for allowed penv ->
    src_dag_to_expr w d = Some e ->
    eval_cfg_dag penv foracle d = DO_Ret dv_src ->
    eval_closed_cert_expr penv foracle e = raise_ret dv_src.
Proof.
  intros allowed w d; induction d as [| | w' ret_e | ws step_e next IH | cond on_t IHt on_f IHf];
    intros e penv foracle dv_src Hwf Hpenv Hr Hevd;
    cbn [wf_cfg_dag src_dag_to_expr eval_cfg_dag] in Hwf, Hr, Hevd; try discriminate Hr; try discriminate Hevd.
  - destruct (Pos.eqb w' w); [| discriminate Hr]; inversion Hr; subst e.
    destruct (eval_closed_cert_expr penv foracle ret_e) as [| | | dv]; try discriminate Hevd.
    inversion Hevd; subst dv; reflexivity.
  - rewrite !andb_true_iff in Hwf; destruct Hwf as (_ & Hwfn).
    destruct (eval_closed_cert_expr penv foracle step_e) as [| | | _]; try discriminate Hevd.
    exact (IH e penv foracle dv_src Hwfn Hpenv Hr Hevd).
  - rewrite !andb_true_iff in Hwf; destruct Hwf as (((((_ & _) & _) & _) & Hwft) & Hwff).
    destruct (eval_closed_cert_expr penv foracle cond) as [| | | dvc] eqn:Ec; try discriminate Hevd.
    destruct dvc as [dbc | |]; try discriminate Hevd.
    destruct dbc as [| wc cbit | | | | | |]; try discriminate Hevd.
    destruct wc as [| |]; try discriminate Hevd.
    destruct (spine_is_unreachable on_f) eqn:Euf.
    + destruct (@Integers.unsigned 1 cbit =? 1)%Z.
      * exact (IHt e penv foracle dv_src Hwft Hpenv Hr Hevd).
      * rewrite (spine_is_unreachable_sound penv foracle on_f Euf) in Hevd; discriminate Hevd.
    + destruct (spine_is_unreachable on_t) eqn:Eut.
      * destruct (@Integers.unsigned 1 cbit =? 1)%Z.
        -- rewrite (spine_is_unreachable_sound penv foracle on_t Eut) in Hevd; discriminate Hevd.
        -- exact (IHf e penv foracle dv_src Hwff Hpenv Hr Hevd).
      * destruct (src_dag_to_expr w on_t) as [et |] eqn:Ert; [| discriminate Hr].
        destruct (src_dag_to_expr w on_f) as [ef |] eqn:Erf; [| discriminate Hr].
        destruct (ub_free_expr et && ub_free_expr ef) eqn:Eubf; [| discriminate Hr].
        apply andb_true_iff in Eubf as [Hubt Hubf].
        inversion Hr; subst e; clear Hr.
        destruct (src_dag_to_expr_typing allowed w on_t et Hwft Ert) as (Hwtt & _ & _ & Hfvt).
        destruct (src_dag_to_expr_typing allowed w on_f ef Hwff Erf) as (Hwtf & _ & _ & Hfvf).
        assert (Hpt : wf_param_env_for (collect_free_vars [] et) penv)
          by (intros x wx Hx; exact (Hpenv x wx (Hfvt (x, wx) Hx))).
        assert (Hpf : wf_param_env_for (collect_free_vars [] ef) penv)
          by (intros x wx Hx; exact (Hpenv x wx (Hfvf (x, wx) Hx))).
        destruct (@Integers.unsigned 1 cbit =? 1)%Z eqn:Ecbit.
        -- pose proof (IHt et penv foracle dv_src Hwft Hpenv Ert Hevd) as Het.
           destruct (ub_free_expr_eval_ret ef [] penv [] foracle Hubf Hwtf wf_let_val_env_nil Hpf)
             as [vf [Hef _]].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ec, Het, Hef; cbn.
           rewrite Ecbit; reflexivity.
        -- pose proof (IHf ef penv foracle dv_src Hwff Hpenv Erf Hevd) as Hef.
           destruct (ub_free_expr_eval_ret et [] penv [] foracle Hubt Hwtt wf_let_val_env_nil Hpt)
             as [vt [Het _]].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ec, Het, Hef; cbn.
           rewrite Ecbit; reflexivity.
Qed.

Definition tgt_cond_guaranteed_defined
  (ctx : ub_ctx) (src_evals src_br_conds : list cert_expr) (cond : cert_expr) : bool :=
  expr_guaranteed_defined ctx cond ||
  existsb (cert_expr_eqb cond) src_br_conds ||
  existsb (expr_has_div_with_rhs cond) src_evals.

Lemma tgt_cond_guaranteed_defined_sound {Pa : Params} :
  forall allowed ctx src_evals src_br_conds cond (penv : param_env Pa) foracle dvc,
    tgt_cond_guaranteed_defined ctx src_evals src_br_conds cond = true ->
    wt_cert_expr [] cond = true ->
    cert_expr_bit_width cond = 1%positive ->
    wf_param_env_for (collect_free_vars [] cond) penv ->
    ub_ctx_holds penv foracle ctx ->
    (forall big, In big src_evals ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed) ->
    (forall big, In big src_evals ->
      exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv) ->
    (forall c, In c src_br_conds ->
      exists cbit : @Integers.bit_int 1,
        eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))) ->
    eval_closed_cert_expr penv foracle cond = raise_ret dvc ->
    wf_scalar_dvalue 1%positive dvc ->
    exists cbit : @Integers.bit_int 1, dvc = DVALUE_Base (@DVALUE_I Pa 1 cbit).
Proof.
  intros allowed ctx src_evals src_br_conds cond penv foracle dvc
         Hdef Hwtc Hbwc Hpc Hctx Hsrc_wf Hsrc_ret Hbr_ret Ec Hwfc.
  destruct Hwfc as [-> | [cbit ->]]; [| exists cbit; reflexivity].
  exfalso; unfold tgt_cond_guaranteed_defined in Hdef; rewrite !orb_true_iff in Hdef.
  destruct Hdef as [[Hgd | Hex_br] | Hex_div].
  - destruct (expr_guaranteed_defined_sound ctx cond penv foracle Hgd Hwtc Hpc Hctx)
      as [_ [ic Hic]].
    revert ic Hic; rewrite Hbwc; intros ic Hic; congruence.
  - apply existsb_exists in Hex_br as [c [Hcin Hceq]]; apply cert_expr_eqb_eq in Hceq; subst c.
    destruct (Hbr_ret cond Hcin) as [cbit Ec']; congruence.
  - apply existsb_exists in Hex_div as [big [Hbin Hdiv]].
    destruct (expr_has_div_with_rhs_spec cond big Hdiv) as (op & w0 & fl & lhs & Hop & Hsub).
    destruct (Hsrc_wf big Hbin) as (Hwtb & Hlfb & Hfvb).
    destruct (is_syntactic_subexpr_wt_fv _ big allowed Hsub Hwtb Hlfb Hfvb) as (Hwts & _ & _).
    destruct (Hsrc_ret big Hbin) as [vbig Hvbig].
    destruct (is_syntactic_subexpr_eval_ret _ big penv [] foracle vbig Hsub Hvbig) as [vsub Hvsub].
    exact (div_subexpr_rhs_not_poison penv foracle op w0 fl lhs cond vsub Hop Hwts Hvsub Ec).
Qed.

Fixpoint tgt_dag_to_expr
  (ctx : ub_ctx)
  (src_evals src_br_conds : list cert_expr)
  (w : positive)
  (d : cfg_dag) : option cert_expr :=
  match d with
  | CD_Unreachable | CD_RetVoid => None
  | CD_RetScalar w' ret_e =>
      if Pos.eqb w' w && expr_safe_under_src ctx src_evals ret_e
      then Some ret_e else None
  | CD_Eval _ step_e next =>
      if expr_safe_under_src ctx src_evals step_e
      then tgt_dag_to_expr ctx src_evals src_br_conds w next
      else None
  | CD_Branch cond on_t on_f =>
      if tgt_cond_guaranteed_defined ctx src_evals src_br_conds cond &&
         expr_safe_under_src ctx src_evals cond then
        match tgt_dag_to_expr ctx src_evals src_br_conds w on_t,
              tgt_dag_to_expr ctx src_evals src_br_conds w on_f with
        | Some et, Some ef => Some (CE_Select w cond et ef)
        | _, _ => None
        end
      else None
  end.

Lemma tgt_dag_to_expr_typing :
  forall allowed ctx src_evals src_br_conds w d e,
    wf_cfg_dag allowed d = true ->
    tgt_dag_to_expr ctx src_evals src_br_conds w d = Some e ->
    wt_cert_expr [] e = true /\
    cert_expr_bit_width e = w /\
    is_let_free_expr e = true /\
    incl (collect_free_vars [] e) allowed.
Proof.
  intros allowed ctx src_evals src_br_conds w d.
  induction d as [| | w' ret_e | ws step_e next IH | cond on_t IHt on_f IHf];
    intros e Hwf Hr; cbn [wf_cfg_dag tgt_dag_to_expr] in Hwf, Hr; try discriminate Hr.
  - destruct (Pos.eqb w' w && expr_safe_under_src ctx src_evals ret_e) eqn:Eok; [| discriminate Hr].
    apply andb_true_iff in Eok as [Ebw _]; apply Pos.eqb_eq in Ebw; subst w'.
    inversion Hr; subst e.
    rewrite !andb_true_iff in Hwf; destruct Hwf as (((Hwt & Hbw) & Hlf) & Hfv).
    apply Pos.eqb_eq in Hbw.
    exact (conj Hwt (conj Hbw (conj Hlf (vars_subset_b_incl _ _ Hfv)))).
  - destruct (expr_safe_under_src ctx src_evals step_e); [| discriminate Hr].
    rewrite !andb_true_iff in Hwf; destruct Hwf as (_ & Hwfn); exact (IH e Hwfn Hr).
  - destruct (tgt_cond_guaranteed_defined ctx src_evals src_br_conds cond &&
              expr_safe_under_src ctx src_evals cond); [| discriminate Hr].
    destruct (tgt_dag_to_expr ctx src_evals src_br_conds w on_t) as [et |] eqn:Ert; [| discriminate Hr].
    destruct (tgt_dag_to_expr ctx src_evals src_br_conds w on_f) as [ef |] eqn:Erf; [| discriminate Hr].
    inversion Hr; subst e; clear Hr.
    rewrite !andb_true_iff in Hwf; destruct Hwf as (((((Hwtc & Hbwc) & Hlfc) & Hfvc) & Hwft) & Hwff).
    destruct (IHt et Hwft Ert) as (Hwtt & Hbwt & Hlft & Hfvt).
    destruct (IHf ef Hwff Erf) as (Hwtf & Hbwf & Hlff & Hfvf).
    cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars].
    rewrite Hwtc, Hwtt, Hwtf, Hbwc, Hbwt, Hbwf, !Pos.eqb_refl, Hlfc, Hlft, Hlff.
    repeat split; try reflexivity.
    intros u Hu; apply in_app_iff in Hu as [Huc | Hutf]; [exact (vars_subset_b_incl _ _ Hfvc u Huc) |].
    apply in_app_iff in Hutf as [Hut | Huf]; [exact (Hfvt u Hut) | exact (Hfvf u Huf)].
Qed.

Lemma tgt_dag_to_expr_sound {Pa : Params} :
  forall allowed ctx src_evals src_br_conds w d e (penv : param_env Pa) foracle,
    wf_cfg_dag allowed d = true ->
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv foracle ctx ->
    (forall big, In big src_evals ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed) ->
    (forall big, In big src_evals ->
      exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv) ->
    (forall c, In c src_br_conds ->
      exists cbit : @Integers.bit_int 1,
        eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))) ->
    tgt_dag_to_expr ctx src_evals src_br_conds w d = Some e ->
    exists dv_tgt,
      eval_closed_cert_expr penv foracle e = raise_ret dv_tgt /\
      eval_cfg_dag penv foracle d = DO_Ret dv_tgt.
Proof.
  intros allowed ctx src_evals src_br_conds w d.
  induction d as [| | w' ret_e | ws step_e next IH | cond on_t IHt on_f IHf];
    intros e penv foracle Hwf Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hr;
    cbn [wf_cfg_dag tgt_dag_to_expr eval_cfg_dag] in Hwf, Hr |- *; try discriminate Hr.
  - destruct (Pos.eqb w' w && expr_safe_under_src ctx src_evals ret_e) eqn:Eok; [| discriminate Hr].
    apply andb_true_iff in Eok as [_ Hsafe]; inversion Hr; subst e.
    rewrite !andb_true_iff in Hwf; destruct Hwf as (((Hwt & _) & _) & Hfv).
    pose proof (vars_subset_b_wf_param _ allowed penv Hfv Hpenv) as Hpr.
    destruct (expr_safe_under_src_sound ret_e ctx src_evals penv foracle Hsafe Hwt Hpr Hctx Hsrc_ret)
      as [dv_tgt [Hev _]].
    exists dv_tgt; rewrite Hev; split; reflexivity.
  - destruct (expr_safe_under_src ctx src_evals step_e) eqn:Esafe; [| discriminate Hr].
    rewrite !andb_true_iff in Hwf; destruct Hwf as ((((Hwt & _) & _) & Hfv) & Hwfn).
    pose proof (vars_subset_b_wf_param _ allowed penv Hfv Hpenv) as Hps.
    destruct (expr_safe_under_src_sound step_e ctx src_evals penv foracle Esafe Hwt Hps Hctx Hsrc_ret)
      as [dvs [Es _]].
    rewrite Es; exact (IH e penv foracle Hwfn Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hr).
  - destruct (tgt_cond_guaranteed_defined ctx src_evals src_br_conds cond &&
              expr_safe_under_src ctx src_evals cond) eqn:Econd; [| discriminate Hr].
    apply andb_true_iff in Econd as [Hcdef Hcsafe].
    destruct (tgt_dag_to_expr ctx src_evals src_br_conds w on_t) as [et |] eqn:Ert; [| discriminate Hr].
    destruct (tgt_dag_to_expr ctx src_evals src_br_conds w on_f) as [ef |] eqn:Erf; [| discriminate Hr].
    inversion Hr; subst e; clear Hr.
    rewrite !andb_true_iff in Hwf; destruct Hwf as (((((Hwtc & Hbwc) & _) & Hfvc) & Hwft) & Hwff).
    apply Pos.eqb_eq in Hbwc.
    pose proof (vars_subset_b_wf_param _ allowed penv Hfvc Hpenv) as Hpc.
    destruct (expr_safe_under_src_sound cond ctx src_evals penv foracle Hcsafe Hwtc Hpc Hctx Hsrc_ret)
      as [dvc [Ec Hwfc]].
    rewrite Hbwc in Hwfc.
    destruct (tgt_cond_guaranteed_defined_sound allowed ctx src_evals src_br_conds cond penv foracle dvc
                Hcdef Hwtc Hbwc Hpc Hctx Hsrc_wf Hsrc_ret Hbr_ret Ec Hwfc)
      as [cbit ->].
    destruct (IHt et penv foracle Hwft Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Ert) as [dvt [Het Hevt]].
    destruct (IHf ef penv foracle Hwff Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Erf) as [dvf [Hef Hevf]].
    rewrite Ec; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ec, Het, Hef; cbn.
    destruct (@Integers.unsigned 1 cbit =? 1)%Z;
      [exists dvt; split; [reflexivity | exact Hevt]
      | exists dvf; split; [reflexivity | exact Hevf]].
Qed.

Fixpoint tgt_dag_void_safe
  (ctx : ub_ctx)
  (src_evals src_br_conds : list cert_expr)
  (d : cfg_dag) : bool :=
  match d with
  | CD_RetVoid => true
  | CD_Unreachable | CD_RetScalar _ _ => false
  | CD_Eval _ step_e next =>
      expr_safe_under_src ctx src_evals step_e &&
      tgt_dag_void_safe ctx src_evals src_br_conds next
  | CD_Branch cond on_t on_f =>
      tgt_cond_guaranteed_defined ctx src_evals src_br_conds cond &&
      expr_safe_under_src ctx src_evals cond &&
      tgt_dag_void_safe ctx src_evals src_br_conds on_t &&
      tgt_dag_void_safe ctx src_evals src_br_conds on_f
  end.

Lemma tgt_dag_void_safe_sound {Pa : Params} :
  forall allowed ctx src_evals src_br_conds d (penv : param_env Pa) foracle,
    wf_cfg_dag allowed d = true ->
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv foracle ctx ->
    (forall big, In big src_evals ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed) ->
    (forall big, In big src_evals ->
      exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv) ->
    (forall c, In c src_br_conds ->
      exists cbit : @Integers.bit_int 1,
        eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))) ->
    tgt_dag_void_safe ctx src_evals src_br_conds d = true ->
    eval_cfg_dag penv foracle d = DO_Ret NONE.
Proof.
  intros allowed ctx src_evals src_br_conds d.
  induction d as [| | w' ret_e | ws step_e next IH | cond on_t IHt on_f IHf];
    intros penv foracle Hwf Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hvs;
    cbn [wf_cfg_dag tgt_dag_void_safe eval_cfg_dag] in Hwf, Hvs |- *; try discriminate Hvs; [reflexivity | |].
  - apply andb_true_iff in Hvs as [Hsafe Hvsn].
    rewrite !andb_true_iff in Hwf; destruct Hwf as ((((Hwt & _) & _) & Hfv) & Hwfn).
    pose proof (vars_subset_b_wf_param _ allowed penv Hfv Hpenv) as Hps.
    destruct (expr_safe_under_src_sound step_e ctx src_evals penv foracle Hsafe Hwt Hps Hctx Hsrc_ret)
      as [dvs [Es _]].
    rewrite Es; exact (IH penv foracle Hwfn Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hvsn).
  - rewrite !andb_true_iff in Hvs; destruct Hvs as (((Hcdef & Hcsafe) & Hvst) & Hvsf).
    rewrite !andb_true_iff in Hwf; destruct Hwf as (((((Hwtc & Hbwc) & _) & Hfvc) & Hwft) & Hwff).
    apply Pos.eqb_eq in Hbwc.
    pose proof (vars_subset_b_wf_param _ allowed penv Hfvc Hpenv) as Hpc.
    destruct (expr_safe_under_src_sound cond ctx src_evals penv foracle Hcsafe Hwtc Hpc Hctx Hsrc_ret)
      as [dvc [Ec Hwfc]].
    rewrite Hbwc in Hwfc.
    destruct (tgt_cond_guaranteed_defined_sound allowed ctx src_evals src_br_conds cond penv foracle dvc
                Hcdef Hwtc Hbwc Hpc Hctx Hsrc_wf Hsrc_ret Hbr_ret Ec Hwfc)
      as [cbit ->].
    rewrite Ec; destruct (@Integers.unsigned 1 cbit =? 1)%Z.
    + exact (IHt penv foracle Hwft Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hvst).
    + exact (IHf penv foracle Hwff Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hvsf).
Qed.

Definition check_scalar_dag_via_ro
  (allowed : list (string * positive))
  (ctx : ub_ctx)
  (ro : return_obligation)
  (opt_pf : option (list lrat_step))
  (src_evals src_br_conds : list cert_expr)
  (d_src d_tgt : cfg_dag) : bool :=
  match ro with
  | RO_VoidEquiv => false
  | RO_ScalarRefines w cert_src cert_tgt _ =>
      vars_subset_b (collect_free_vars [] cert_src) allowed &&
      vars_subset_b (collect_free_vars [] cert_tgt) allowed &&
      match src_dag_to_expr w d_src,
            tgt_dag_to_expr ctx src_evals src_br_conds w d_tgt with
      | Some reified_src, Some reified_tgt =>
          check_expr_refines ctx reified_src cert_src &&
          check_expr_refines_with_lrat ctx cert_src cert_tgt opt_pf &&
          check_expr_refines ctx cert_tgt reified_tgt
      | _, _ => false
      end
  end.

Lemma check_scalar_dag_via_ro_sound {Pa : Params} :
  forall allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt
         (penv : param_env Pa) foracle dv_src,
    wf_cfg_dag allowed d_src = true ->
    wf_cfg_dag allowed d_tgt = true ->
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv foracle ctx ->
    (forall big, In big src_evals ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed) ->
    (forall big, In big src_evals ->
      exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv) ->
    (forall c, In c src_br_conds ->
      exists cbit : @Integers.bit_int 1,
        eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))) ->
    check_scalar_dag_via_ro allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt = true ->
    eval_cfg_dag penv foracle d_src = DO_Ret dv_src ->
    exists dv_tgt,
      eval_cfg_dag penv foracle d_tgt = DO_Ret dv_tgt /\
      dvalue_refines dv_src dv_tgt.
Proof.
  intros allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt penv foracle dv_src
         Hwfs Hwft Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hchk Hevs.
  destruct ro as [| w cert_src cert_tgt smt_v]; [discriminate Hchk |].
  cbn [check_scalar_dag_via_ro] in Hchk; rewrite !andb_true_iff in Hchk.
  destruct Hchk as ([Hfvs_cs Hfvs_ct] & Hmatch).
  destruct (src_dag_to_expr w d_src) as [r_src |] eqn:Ers; [| discriminate Hmatch].
  destruct (tgt_dag_to_expr ctx src_evals src_br_conds w d_tgt) as [r_tgt |] eqn:Ert;
    [| discriminate Hmatch].
  rewrite !andb_true_iff in Hmatch; destruct Hmatch as ([Hr1 Hr2] & Hr3).
  destruct (src_dag_to_expr_typing allowed w d_src r_src Hwfs Ers) as (_ & _ & _ & Hfv_rs).
  destruct (tgt_dag_to_expr_typing allowed ctx src_evals src_br_conds w d_tgt r_tgt Hwft Ert)
    as (_ & _ & _ & Hfv_rt).
  assert (Hp_rs : wf_param_env_for (collect_free_vars [] r_src) penv)
    by (intros x wx Hx; exact (Hpenv x wx (Hfv_rs (x, wx) Hx))).
  assert (Hp_rt : wf_param_env_for (collect_free_vars [] r_tgt) penv)
    by (intros x wx Hx; exact (Hpenv x wx (Hfv_rt (x, wx) Hx))).
  pose proof (vars_subset_b_wf_param _ allowed penv Hfvs_cs Hpenv) as Hp_cs.
  pose proof (vars_subset_b_wf_param _ allowed penv Hfvs_ct Hpenv) as Hp_ct.
  pose proof (src_dag_to_expr_sound allowed w d_src r_src penv foracle dv_src Hwfs Hpenv Ers Hevs)
    as Hev_rs.
  destruct (tgt_dag_to_expr_sound allowed ctx src_evals src_br_conds w d_tgt r_tgt penv foracle
              Hwft Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Ert)
    as [dv_tgt [Hev_rt Hev_dtgt]].
  pose proof (check_expr_refines_sound ctx r_src cert_src penv foracle Hr1 Hp_rs Hp_cs Hctx) as Href1.
  pose proof (check_expr_refines_with_lrat_sound ctx cert_src cert_tgt opt_pf penv foracle
                Hr2 Hp_cs Hp_ct Hctx) as Href2.
  pose proof (check_expr_refines_sound ctx cert_tgt r_tgt penv foracle Hr3 Hp_ct Hp_rt Hctx) as Href3.
  rewrite Hev_rs in Href1; cbn [refine_eou_dvalue] in Href1.
  destruct (eval_closed_cert_expr penv foracle cert_src) as [| | | dv_cs]; try contradiction Href1.
  cbn [refine_eou_dvalue] in Href2.
  destruct (eval_closed_cert_expr penv foracle cert_tgt) as [| | | dv_ct]; try contradiction Href2.
  rewrite Hev_rt in Href3; cbn [refine_eou_dvalue] in Href3.
  exists dv_tgt; split; [exact Hev_dtgt |].
  exact (dvalue_refines_trans _ _ _ Href1 (dvalue_refines_trans _ _ _ Href2 Href3)).
Qed.

Fixpoint dag_node_count (d : cfg_dag) : nat :=
  match d with
  | CD_Unreachable | CD_RetVoid | CD_RetScalar _ _ => 1%nat
  | CD_Eval _ _ next => S (dag_node_count next)
  | CD_Branch _ on_t on_f => S (dag_node_count on_t + dag_node_count on_f)
  end.

Fixpoint check_dag_refines_cert
  (fuel : nat)
  (allowed : list (string * positive))
  (ctx : ub_ctx)
  (ro : return_obligation)
  (opt_pf : option (list lrat_step))
  (src_evals src_br_conds : list cert_expr)
  (d_src d_tgt : cfg_dag) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if spine_is_unreachable d_src || ctx_has_unreachable ctx then true
      else if check_scalar_dag_via_ro allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt
           then true
      else
        match d_src with
        | CD_Unreachable => true
        | CD_Eval _ se next_s =>
            check_dag_refines_cert fuel' allowed ctx ro opt_pf
              (se :: src_evals) src_br_conds next_s d_tgt
        | CD_Branch cs ts fs =>
            if spine_is_unreachable fs then
              check_dag_refines_cert fuel' allowed ctx ro opt_pf
                (cs :: src_evals) (cs :: src_br_conds) ts d_tgt
            else if spine_is_unreachable ts then
              check_dag_refines_cert fuel' allowed ctx ro opt_pf
                (cs :: src_evals) (cs :: src_br_conds) fs d_tgt
            else
              match d_tgt with
              | CD_Eval _ te next_t =>
                  expr_safe_under_src ctx src_evals te &&
                  check_dag_refines_cert fuel' allowed ctx ro opt_pf
                    src_evals src_br_conds d_src next_t
              | CD_Branch ct tt ft =>
                  check_expr_refines ctx cs ct &&
                  check_dag_refines_cert fuel' allowed ctx ro opt_pf
                    (cs :: src_evals) (cs :: src_br_conds) ts tt &&
                  check_dag_refines_cert fuel' allowed ctx ro opt_pf
                    (cs :: src_evals) (cs :: src_br_conds) fs ft
              | _ => false
              end
        | CD_RetVoid =>
            match ro with
            | RO_VoidEquiv => tgt_dag_void_safe ctx src_evals src_br_conds d_tgt
            | _ => false
            end
        | CD_RetScalar ws es =>
            match d_tgt with
            | CD_Eval _ te next_t =>
                expr_safe_under_src ctx src_evals te &&
                check_dag_refines_cert fuel' allowed ctx ro opt_pf
                  src_evals src_br_conds d_src next_t
            | CD_RetScalar wt et =>
                match ro with
                | RO_ScalarRefines w _ _ _ =>
                    Pos.eqb ws w && Pos.eqb wt w &&
                    check_expr_refines_with_lrat ctx es et opt_pf
                | _ => false
                end
            | _ => false
            end
        end
  end.

Lemma check_dag_refines_cert_sound {Pa : Params} :
  forall fuel allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt
         (penv : param_env Pa) foracle dv_src,
    wf_cfg_dag allowed d_src = true ->
    wf_cfg_dag allowed d_tgt = true ->
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv foracle ctx ->
    (forall big, In big src_evals ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed) ->
    (forall big, In big src_evals ->
      exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv) ->
    (forall c, In c src_br_conds ->
      exists cbit : @Integers.bit_int 1,
        eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))) ->
    check_dag_refines_cert fuel allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt = true ->
    eval_cfg_dag penv foracle d_src = DO_Ret dv_src ->
    exists dv_tgt,
      eval_cfg_dag penv foracle d_tgt = DO_Ret dv_tgt /\
      dvalue_refines dv_src dv_tgt.
Proof.
  induction fuel as [| fuel' IH];
    intros allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt penv foracle dv_src
           Hwfs Hwft Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hchk Hevs;
    cbn [check_dag_refines_cert] in Hchk; [discriminate Hchk |].
  destruct (spine_is_unreachable d_src || ctx_has_unreachable ctx) eqn:Eunr.
  { exfalso; apply orb_true_iff in Eunr as [Hs_unr | Hc_unr].
    - rewrite (spine_is_unreachable_sound penv foracle d_src Hs_unr) in Hevs; discriminate Hevs.
    - exact (ctx_has_unreachable_sound penv foracle ctx Hc_unr Hctx). }
  destruct (check_scalar_dag_via_ro allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt) eqn:Ero.
  { exact (check_scalar_dag_via_ro_sound allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt
             penv foracle dv_src Hwfs Hwft Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Ero Hevs). }
  destruct d_src as [| | ws es | ws se next_s | cs ts fs].
  - discriminate Hevs.
  - (* CD_RetVoid *)
    destruct ro as [| ? ? ? ?]; [| discriminate Hchk].
    cbn [eval_cfg_dag] in Hevs; inversion Hevs; subst dv_src.
    exists NONE; split;
      [exact (tgt_dag_void_safe_sound allowed ctx src_evals src_br_conds d_tgt penv foracle
                Hwft Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hchk)
      | apply dvalue_refines_refl].
  - (* CD_RetScalar *)
    destruct d_tgt as [| | wt et | wt te next_t | ct tt ft]; try discriminate Hchk.
    + destruct ro as [| w _ _ _]; [discriminate Hchk |].
      rewrite !andb_true_iff in Hchk; destruct Hchk as ([_ _] & Href).
      cbn [wf_cfg_dag eval_cfg_dag] in Hwfs, Hwft, Hevs.
      rewrite !andb_true_iff in Hwfs, Hwft.
      destruct Hwfs as (((_ & _) & _) & Hfvs); destruct Hwft as (((_ & _) & _) & Hfvt).
      pose proof (vars_subset_b_wf_param _ allowed penv Hfvs Hpenv) as Hpes.
      pose proof (vars_subset_b_wf_param _ allowed penv Hfvt Hpenv) as Hpet.
      destruct (eval_closed_cert_expr penv foracle es) as [| | | dv_s] eqn:Ees; try discriminate Hevs.
      inversion Hevs; subst dv_s.
      pose proof (check_expr_refines_with_lrat_sound ctx es et opt_pf penv foracle Href Hpes Hpet Hctx)
        as Href_eou.
      rewrite Ees in Href_eou; cbn [refine_eou_dvalue] in Href_eou.
      destruct (eval_closed_cert_expr penv foracle et) as [| | | dv_t] eqn:Eet; try contradiction Href_eou.
      exists dv_t; cbn [eval_cfg_dag]; rewrite Eet; split; [reflexivity | exact Href_eou].
    + apply andb_true_iff in Hchk as [Hsafe Hchk'].
      cbn [wf_cfg_dag] in Hwft; rewrite !andb_true_iff in Hwft.
      destruct Hwft as ((((Hwte & _) & _) & Hfve) & Hwfnt).
      pose proof (vars_subset_b_wf_param _ allowed penv Hfve Hpenv) as Hpte.
      destruct (expr_safe_under_src_sound te ctx src_evals penv foracle Hsafe Hwte Hpte Hctx Hsrc_ret)
        as [dve [Ete _]].
      cbn [eval_cfg_dag]; rewrite Ete.
      exact (IH allowed ctx ro opt_pf src_evals src_br_conds (CD_RetScalar ws es) next_t
               penv foracle dv_src Hwfs Hwfnt Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hchk' Hevs).
  - (* CD_Eval on d_src *)
    cbn [wf_cfg_dag eval_cfg_dag] in Hwfs, Hevs; rewrite !andb_true_iff in Hwfs.
    destruct Hwfs as ((((Hwtse & _) & Hlfse) & Hfvse) & Hwfns).
    destruct (eval_closed_cert_expr penv foracle se) as [| | | dvse] eqn:Ese; try discriminate Hevs.
    assert (Hsrc_wf' : forall big, In big (se :: src_evals) ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed).
    { intros big [<- | Hin];
        [exact (conj Hwtse (conj Hlfse (vars_subset_b_incl _ _ Hfvse))) | exact (Hsrc_wf big Hin)]. }
    assert (Hsrc_ret' : forall big, In big (se :: src_evals) ->
      exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv).
    { intros big [<- | Hin]; [exists dvse; exact Ese | exact (Hsrc_ret big Hin)]. }
    exact (IH allowed ctx ro opt_pf (se :: src_evals) src_br_conds next_s d_tgt
             penv foracle dv_src Hwfns Hwft Hpenv Hctx Hsrc_wf' Hsrc_ret' Hbr_ret Hchk Hevs).
  - (* CD_Branch on d_src *)
    cbn [wf_cfg_dag eval_cfg_dag] in Hwfs, Hevs; rewrite !andb_true_iff in Hwfs.
    destruct Hwfs as (((((Hwtcs & Hbwcs) & Hlfcs) & Hfvcs) & Hwfts) & Hwffs).
    destruct (eval_closed_cert_expr penv foracle cs) as [| | | dvcs] eqn:Ecs; try discriminate Hevs.
    destruct dvcs as [dbcs | |]; try discriminate Hevs.
    destruct dbcs as [| wcs cbit | | | | | |]; try discriminate Hevs.
    destruct wcs as [| |]; try discriminate Hevs.
    assert (Hsrc_wf' : forall big, In big (cs :: src_evals) ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed).
    { intros big [<- | Hin];
        [exact (conj Hwtcs (conj Hlfcs (vars_subset_b_incl _ _ Hfvcs))) | exact (Hsrc_wf big Hin)]. }
    assert (Hsrc_ret' : forall big, In big (cs :: src_evals) ->
      exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv).
    { intros big [<- | Hin]; [eexists; exact Ecs | exact (Hsrc_ret big Hin)]. }
    assert (Hbr_ret' : forall c, In c (cs :: src_br_conds) ->
      exists cb0 : @Integers.bit_int 1,
        eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cb0))).
    { intros c [<- | Hin]; [exists cbit; exact Ecs | exact (Hbr_ret c Hin)]. }
    destruct (spine_is_unreachable fs) eqn:Eufs.
    + destruct (@Integers.unsigned 1 cbit =? 1)%Z.
      * exact (IH allowed ctx ro opt_pf (cs :: src_evals) (cs :: src_br_conds) ts d_tgt
                 penv foracle dv_src Hwfts Hwft Hpenv Hctx Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk Hevs).
      * rewrite (spine_is_unreachable_sound penv foracle fs Eufs) in Hevs; discriminate Hevs.
    + destruct (spine_is_unreachable ts) eqn:Euts.
      * destruct (@Integers.unsigned 1 cbit =? 1)%Z.
        -- rewrite (spine_is_unreachable_sound penv foracle ts Euts) in Hevs; discriminate Hevs.
        -- exact (IH allowed ctx ro opt_pf (cs :: src_evals) (cs :: src_br_conds) fs d_tgt
                    penv foracle dv_src Hwffs Hwft Hpenv Hctx Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk Hevs).
      * destruct d_tgt as [| | wt et | wt te next_t | ct tt ft]; try discriminate Hchk.
        -- apply andb_true_iff in Hchk as [Hsafe Hchk'].
           cbn [wf_cfg_dag] in Hwft; rewrite !andb_true_iff in Hwft.
           destruct Hwft as ((((Hwte & _) & _) & Hfve) & Hwfnt).
           pose proof (vars_subset_b_wf_param _ allowed penv Hfve Hpenv) as Hpte.
           destruct (expr_safe_under_src_sound te ctx src_evals penv foracle Hsafe Hwte Hpte Hctx Hsrc_ret)
             as [dve [Ete _]].
           cbn [eval_cfg_dag]; rewrite Ete.
           assert (Hwfs_all : wf_cfg_dag allowed (CD_Branch cs ts fs) = true)
             by (cbn [wf_cfg_dag]; rewrite Hwtcs, Hbwcs, Hlfcs, Hfvcs, Hwfts, Hwffs; reflexivity).
           assert (Hevs_all : eval_cfg_dag penv foracle (CD_Branch cs ts fs) = DO_Ret dv_src)
             by (cbn [eval_cfg_dag]; rewrite Ecs; exact Hevs).
           exact (IH allowed ctx ro opt_pf src_evals src_br_conds (CD_Branch cs ts fs) next_t
                    penv foracle dv_src Hwfs_all Hwfnt Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hchk' Hevs_all).
        -- rewrite !andb_true_iff in Hchk; destruct Hchk as ([Hc_ref Hchk_t] & Hchk_f).
           cbn [wf_cfg_dag] in Hwft; rewrite !andb_true_iff in Hwft.
           destruct Hwft as (((((Hwtct & _) & _) & Hfvct) & Hwftt) & Hwfft).
           pose proof (vars_subset_b_wf_param _ allowed penv Hfvcs Hpenv) as Hpcs.
           pose proof (vars_subset_b_wf_param _ allowed penv Hfvct Hpenv) as Hpct.
           pose proof (check_expr_refines_sound ctx cs ct penv foracle Hc_ref Hpcs Hpct Hctx) as Hcref.
           rewrite Ecs in Hcref; cbn [refine_eou_dvalue] in Hcref.
           destruct (eval_closed_cert_expr penv foracle ct) as [| | | dvct] eqn:Ect; try contradiction Hcref.
           destruct Hcref as [Hps | ->]; [discriminate Hps |].
           cbn [eval_cfg_dag]; rewrite Ect.
           destruct (@Integers.unsigned 1 cbit =? 1)%Z.
           ++ exact (IH allowed ctx ro opt_pf (cs :: src_evals) (cs :: src_br_conds) ts tt
                       penv foracle dv_src Hwfts Hwftt Hpenv Hctx Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_t Hevs).
           ++ exact (IH allowed ctx ro opt_pf (cs :: src_evals) (cs :: src_br_conds) fs ft
                       penv foracle dv_src Hwffs Hwfft Hpenv Hctx Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_f Hevs).
Qed.

Definition check_return_obligation_valid
  (allowed : list (string * positive))
  (ctx : ub_ctx)
  (ro : return_obligation)
  (opt_pf : option (list lrat_step)) : bool :=
  match ro with
  | RO_VoidEquiv => true
  | RO_ScalarRefines _ se te _ =>
      vars_subset_b (collect_free_vars [] se) allowed &&
      vars_subset_b (collect_free_vars [] te) allowed &&
      check_expr_refines_with_lrat ctx se te opt_pf
  end.

Definition check_value_equivalence_refines
  (ctx : ub_ctx) (ve : value_equivalence) : bool :=
  wf_value_equivalence ve &&
  check_expr_refines ctx (ve_src_expr ve) (ve_tgt_expr ve).

Lemma check_value_equivalence_refines_sound {Pa : Params} :
  forall ctx ve (penv : param_env Pa) foracle,
    check_value_equivalence_refines ctx ve = true ->
    wf_param_env_for (collect_free_vars [] (ve_src_expr ve)) penv ->
    wf_param_env_for (collect_free_vars [] (ve_tgt_expr ve)) penv ->
    ub_ctx_holds penv foracle ctx ->
    refine_eou_dvalue
      (eval_closed_cert_expr penv foracle (ve_src_expr ve))
      (eval_closed_cert_expr penv foracle (ve_tgt_expr ve)).
Proof.
  intros ctx ve penv foracle Hchk Hps Hpt Hctx.
  apply andb_true_iff in Hchk as [_ Href].
  exact (check_expr_refines_sound ctx (ve_src_expr ve) (ve_tgt_expr ve) penv foracle Href Hps Hpt Hctx).
Qed.

Definition check_cert_cfg_with_lrat
  (src_cfg tgt_cfg : CFG.cfg dtyp)
  (cert : proof_certificate)
  (opt_pf : option (list lrat_step)) : bool :=
  let src_pnames := List.map cert_reg_name (args src_cfg) in
  let allowed := used_src_param_vars src_cfg in
  let src_uses := param_idx_uses_cfg src_cfg in
  let tgt_uses := param_idx_uses_cfg tgt_cfg in
  let all_ub_assumptions := List.flat_map bc_ub_assumptions (pc_blocks cert) in
  wf_proof_certificate cert &&
  check_validator_syntax_gates src_cfg tgt_cfg &&
  Nat.eqb (List.length (args src_cfg)) (List.length (args tgt_cfg)) &&
  no_dup_raw_ids (args src_cfg) &&
  no_dup_raw_ids (args tgt_cfg) &&
  no_dup_strings src_pnames &&
  forallb (fun u => param_use_in u src_uses) tgt_uses &&
  list_empty_b (pc_loop_invariants cert) &&
  forallb (fun bc => list_empty_b (bc_memory_invariants bc)) (pc_blocks cert) &&
  match summarize_cfg_dag false src_cfg src_pnames,
        summarize_cfg_dag true tgt_cfg src_pnames with
  | Some d_src, Some d_tgt =>
      match check_ub_assumptions_list allowed d_src [] all_ub_assumptions with
      | Some ctx =>
          check_return_obligation_valid allowed ctx (pc_return_obligation cert) opt_pf &&
          let fuel := S (dag_node_count d_src + dag_node_count d_tgt) in
          check_dag_refines_cert fuel allowed ctx (pc_return_obligation cert) opt_pf
            (spine_src_evals d_src) (spine_branch_conds d_src) d_src d_tgt
      | None => false
      end
  | _, _ => false
  end.

Definition check_cert_cfg
  (src_cfg tgt_cfg : CFG.cfg dtyp) (cert : proof_certificate) : bool :=
  check_cert_cfg_with_lrat src_cfg tgt_cfg cert None.

Definition strip_leading_at (s : string) : string :=
  match s with
  | String c rest =>
      if Nat.eqb (nat_of_ascii c) 64%nat then rest else s
  | EmptyString => EmptyString
  end.

Definition cert_fn_matches_raw_id (fn_name : string) (rid : raw_id) : bool :=
  String.eqb (strip_leading_at fn_name) (cert_raw_id_bare rid).

Definition check_cert_defn_with_lrat
  (src_tenv tgt_tenv : list (ident * typ))
  (src_defn tgt_defn : definition typ (CFG.cfg typ))
  (cert : proof_certificate)
  (opt_pf : option (list lrat_step)) : bool :=
  cert_fn_matches_raw_id (pc_function_name cert) (dc_name (df_prototype src_defn)) &&
  check_prototype_contract (df_prototype src_defn) (df_prototype tgt_defn) &&
  check_cert_cfg_with_lrat
    (convert_typ src_tenv (df_instrs src_defn))
    (convert_typ tgt_tenv (df_instrs tgt_defn))
    cert opt_pf.

Definition check_cert_defn
  (src_tenv tgt_tenv : list (ident * typ))
  (src_defn tgt_defn : definition typ (CFG.cfg typ))
  (cert : proof_certificate) : bool :=
  check_cert_defn_with_lrat src_tenv tgt_tenv src_defn tgt_defn cert None.


(** *** 5.7 Top-Level Per-Function Translation Validator Soundness ([0 Admitted]) *)

Theorem check_cert_cfg_with_lrat_sound :
  forall {Pa : Params} (src_cfg tgt_cfg : CFG.cfg dtyp)
         (cert : proof_certificate) (opt_pf : option (list lrat_step)),
    check_cert_cfg_with_lrat src_cfg tgt_cfg cert opt_pf = true ->
    @validator_cfg_refines Pa src_cfg tgt_cfg.
Proof.
  intros Pa src_cfg tgt_cfg cert opt_pf Hchk.
  unfold check_cert_cfg_with_lrat in Hchk; cbn zeta in Hchk.
  set (src_pnames := List.map cert_reg_name (args src_cfg)) in *.
  set (allowed := used_src_param_vars src_cfg) in *.
  set (src_uses := param_idx_uses_cfg src_cfg) in *.
  set (tgt_uses := param_idx_uses_cfg tgt_cfg) in *.
  set (all_ub := List.flat_map bc_ub_assumptions (pc_blocks cert)) in *.
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as (((((((((_ & _) & Hlen_st) & Hnd_sa) & Hnd_ta) & Hnd_sp) & Huses_sub) & _) & _) & Hrest).
  apply Nat.eqb_eq in Hlen_st.
  apply no_dup_raw_ids_spec in Hnd_sa.
  apply no_dup_raw_ids_spec in Hnd_ta.
  apply no_dup_strings_spec in Hnd_sp.
  destruct (summarize_cfg_dag false src_cfg src_pnames) as [d_src |] eqn:Esum_s;
    [| discriminate Hrest].
  destruct (summarize_cfg_dag true tgt_cfg src_pnames) as [d_tgt |] eqn:Esum_t;
    [| discriminate Hrest].
  destruct (check_ub_assumptions_list allowed d_src [] all_ub) as [ctx |] eqn:Ectx;
    [| discriminate Hrest].
  apply andb_true_iff in Hrest as [_ Hdag_ref].
  assert (Hpu_src : forall idx w0 pnm,
    In (idx, DTYPE_Base (DTYPE_I w0)) src_uses ->
    nth_error src_pnames idx = Some pnm ->
    In (pnm, w0) allowed).
  { intros idx w0 pnm Hin Hpnm; unfold allowed, used_src_param_vars.
    apply in_flat_map; exists (idx, DTYPE_Base (DTYPE_I w0)).
    split; [exact Hin | fold src_pnames; rewrite Hpnm; left; reflexivity]. }
  assert (Hpu_tgt : forall idx w0 pnm,
    In (idx, DTYPE_Base (DTYPE_I w0)) tgt_uses ->
    nth_error src_pnames idx = Some pnm ->
    In (pnm, w0) allowed).
  { intros idx w0 pnm Hin Hpnm.
    rewrite forallb_forall in Huses_sub.
    pose proof (Huses_sub (idx, DTYPE_Base (DTYPE_I w0)) Hin) as Hin_s.
    apply param_use_in_spec in Hin_s; exact (Hpu_src idx w0 pnm Hin_s Hpnm). }
  pose proof (summarize_cfg_dag_wf false src_cfg src_pnames allowed d_src Hpu_src Esum_s) as Hwfd_s.
  pose proof (summarize_cfg_dag_wf true tgt_cfg src_pnames allowed d_tgt Hpu_tgt Esum_t) as Hwfd_t.
  split; [exact Hlen_st |].
  intros arg_dtys Hlen_da Hcomp_s.
  assert (Hcomp_t : cfg_param_dtyp_compatible tgt_cfg arg_dtys = true).
  { unfold cfg_param_dtyp_compatible in Hcomp_s |- *.
    rewrite forallb_forall in Hcomp_s, Huses_sub |- *.
    intros u Hu; apply Hcomp_s; apply param_use_in_spec; exact (Huses_sub u Hu). }
  split; [exact Hcomp_t |].
  intros vs Hvs sigma_tgt Hwfsig_t.
  assert (Hlen_sp_s : List.length src_pnames = List.length (args src_cfg))
    by (unfold src_pnames; apply List.length_map).
  assert (Hlen_sp_t : List.length src_pnames = List.length (args tgt_cfg))
    by lia.
  assert (Hlen_da_t : List.length arg_dtys = List.length (args tgt_cfg))
    by lia.
  destruct (summarize_tgt_dag_sound tgt_cfg src_pnames arg_dtys vs sigma_tgt d_tgt
              Hnd_ta Hnd_sp Hlen_sp_t Hlen_da_t Hcomp_t Hvs Hwfsig_t Esum_t)
    as [fmap_tgt Htgt_out].
  set (foracle := oracle_of_fmap fmap_tgt) in *.
  set (penv := build_param_env src_pnames vs) in *.
  destruct (summarize_src_dag_sound src_cfg src_pnames arg_dtys vs foracle d_src
              Hnd_sa Hnd_sp Hlen_sp_s Hlen_da Hcomp_s Hvs Esum_s)
    as [sigma_src [Hwfsig_s Hsrc_out]].
  exists sigma_src; split; [exact Hwfsig_s |].
  destruct Hsrc_out as [[Hst_ub_s _] | (sigma_src' & env_out_s & dv_src & Hev_ds & Hst_ret_s)].
  - exact (cfg_steps_ub_det_ref dvalue_refines sigma_src
             (init_cfg_locals (args src_cfg) vs) (denote_cfg src_cfg None)
             (run_draws sigma_tgt (eval_cfg_open tgt_cfg vs)) Hst_ub_s).
  - pose proof (used_src_param_vars_wf src_cfg arg_dtys vs Hnd_sp Hlen_da Hcomp_s Hvs) as Hpenv_wf.
    fold src_pnames penv allowed in Hpenv_wf.
    pose proof (check_ub_assumptions_list_sound all_ub allowed d_src [] ctx penv foracle dv_src
                  Hwfd_s Hpenv_wf Hev_ds (Forall_nil _) Ectx) as Hctx_holds.
    destruct (check_dag_refines_cert_sound
                (S (dag_node_count d_src + dag_node_count d_tgt))
                allowed ctx (pc_return_obligation cert) opt_pf
                (spine_src_evals d_src) (spine_branch_conds d_src)
                d_src d_tgt penv foracle dv_src
                Hwfd_s Hwfd_t Hpenv_wf Hctx_holds
                (spine_src_evals_wf allowed d_src)
                (spine_src_evals_ret penv foracle d_src dv_src)
                (spine_branch_conds_ret penv foracle d_src dv_src)
                Hdag_ref Hev_ds)
      as [dv_tgt [Hev_dt Href_dv]].
    destruct Htgt_out as [Hev_dt_ub | (sigma_tgt' & env_out_t & dv_tgt' & Hev_dt' & Hst_ret_t)].
    + rewrite Hev_dt in Hev_dt_ub; discriminate Hev_dt_ub.
    + rewrite Hev_dt in Hev_dt'; injection Hev_dt' as <-.
      exact (cfg_steps_ret_det_ref dvalue_refines
               sigma_src (init_cfg_locals (args src_cfg) vs) (denote_cfg src_cfg None)
               sigma_src' env_out_s dv_src
               sigma_tgt (init_cfg_locals (args tgt_cfg) vs) (denote_cfg tgt_cfg None)
               sigma_tgt' env_out_t dv_tgt
               Hst_ret_s Hst_ret_t Href_dv).
Qed.

Theorem check_cert_cfg_sound :
  forall {Pa : Params} (src_cfg tgt_cfg : CFG.cfg dtyp) (cert : proof_certificate),
    check_cert_cfg src_cfg tgt_cfg cert = true ->
    @validator_cfg_refines Pa src_cfg tgt_cfg.
Proof.
  intros Pa src_cfg tgt_cfg cert Hchk.
  exact (check_cert_cfg_with_lrat_sound src_cfg tgt_cfg cert None Hchk).
Qed.

Theorem check_cert_defn_sound :
  forall {Pa : Params} (src_tenv tgt_tenv : list (ident * typ))
         (src_defn tgt_defn : definition typ (CFG.cfg typ))
         (cert : proof_certificate),
    check_cert_defn src_tenv tgt_tenv src_defn tgt_defn cert = true ->
    cert_fn_matches_raw_id (pc_function_name cert) (dc_name (df_prototype src_defn)) = true /\
    dc_name (df_prototype src_defn) = dc_name (df_prototype tgt_defn) /\
    check_prototype_contract (df_prototype src_defn) (df_prototype tgt_defn) = true /\
    @validator_cfg_refines Pa
      (convert_typ src_tenv (df_instrs src_defn))
      (convert_typ tgt_tenv (df_instrs tgt_defn)).
Proof.
  intros Pa src_tenv tgt_tenv src_defn tgt_defn cert Hchk.
  unfold check_cert_defn, check_cert_defn_with_lrat in Hchk.
  rewrite !andb_true_iff in Hchk; destruct Hchk as ([Hfn Hproto] & Hcfg).
  destruct (check_prototype_contract_inv _ _ Hproto) as [Hdcnm _].
  repeat split; [exact Hfn | exact Hdcnm | exact Hproto |].
  exact (check_cert_cfg_sound _ _ cert Hcfg).
Qed.


(** ** 6. Extraction-Ready Module & String-Level CLI Entrypoints *)

Definition find_unique_defn_by_name
  (fn_name : string)
  (ds : list (definition typ (CFG.cfg typ)))
  : option (definition typ (CFG.cfg typ)) :=
  match List.filter (fun d => cert_fn_matches_raw_id fn_name (dc_name (df_prototype d))) ds with
  | [d] => Some d
  | _ => None
  end.

Lemma find_unique_defn_by_name_in :
  forall fn_name ds d,
    find_unique_defn_by_name fn_name ds = Some d ->
    In d ds /\ cert_fn_matches_raw_id fn_name (dc_name (df_prototype d)) = true.
Proof.
  intros fn_name ds d H; unfold find_unique_defn_by_name in H.
  destruct (List.filter (fun d0 => cert_fn_matches_raw_id fn_name (dc_name (df_prototype d0))) ds)
    as [| d0 [| ? ?]] eqn:Hf; try discriminate H.
  inversion H; subst d0.
  assert (Hin : In d (List.filter (fun d0 => cert_fn_matches_raw_id fn_name (dc_name (df_prototype d0))) ds))
    by (rewrite Hf; left; reflexivity).
  apply filter_In in Hin; exact Hin.
Qed.

Definition validate_mcfg_with_cert_lrat
  (src_m tgt_m : CFG.mcfg typ)
  (cert : proof_certificate)
  (opt_pf : option (list lrat_step)) : string + unit :=
  match find_unique_defn_by_name (pc_function_name cert) (m_definitions src_m) with
  | None => inl "source function definition not found or ambiguous in module"
  | Some src_defn =>
      match find_unique_defn_by_name (pc_function_name cert) (m_definitions tgt_m) with
      | None => inl "target function definition not found or ambiguous in module"
      | Some tgt_defn =>
          if negb (cert_fn_matches_raw_id (pc_function_name cert)
                     (dc_name (df_prototype src_defn))) then
            inl "certificate function name mismatch"
          else if negb (check_prototype_contract (df_prototype src_defn)
                          (df_prototype tgt_defn)) then
            inl "prototype contract check failed"
          else if negb (check_validator_syntax_gates
                          (convert_typ (m_type_defs src_m) (df_instrs src_defn))
                          (convert_typ (m_type_defs tgt_m) (df_instrs tgt_defn))) then
            inl "syntax soundness gate check failed"
          else if check_cert_defn_with_lrat (m_type_defs src_m) (m_type_defs tgt_m)
                    src_defn tgt_defn cert opt_pf then
            inr tt
          else
            inl "certificate refinement obligation check failed"
      end
  end.

Definition validate_mcfg_with_cert
  (src_m tgt_m : CFG.mcfg typ)
  (cert : proof_certificate) : string + unit :=
  validate_mcfg_with_cert_lrat src_m tgt_m cert None.

Definition validate_tle_pair_with_cert
  (src_tle tgt_tle : toplevel_entities typ (block typ * list (block typ)))
  (cert : proof_certificate) : string + unit :=
  validate_mcfg_with_cert
    (mcfg_of_tle (resolve_module_refs src_tle))
    (mcfg_of_tle (resolve_module_refs tgt_tle))
    cert.

Definition validate_tle_pair_with_cert_str
  (src_tle tgt_tle : toplevel_entities typ (block typ * list (block typ)))
  (cert_str : string) : string + unit :=
  match parse_cert cert_str with
  | inl err => inl err
  | inr cert => validate_tle_pair_with_cert src_tle tgt_tle cert
  end.

Theorem validate_mcfg_with_cert_lrat_sound :
  forall {Pa : Params} (src_m tgt_m : CFG.mcfg typ)
         (cert : proof_certificate) (opt_pf : option (list lrat_step)),
    validate_mcfg_with_cert_lrat src_m tgt_m cert opt_pf = inr tt ->
    exists src_defn tgt_defn,
      In src_defn (m_definitions src_m) /\
      In tgt_defn (m_definitions tgt_m) /\
      cert_fn_matches_raw_id (pc_function_name cert) (dc_name (df_prototype src_defn)) = true /\
      dc_name (df_prototype src_defn) = dc_name (df_prototype tgt_defn) /\
      check_prototype_contract (df_prototype src_defn) (df_prototype tgt_defn) = true /\
      @validator_cfg_refines Pa
        (convert_typ (m_type_defs src_m) (df_instrs src_defn))
        (convert_typ (m_type_defs tgt_m) (df_instrs tgt_defn)).
Proof.
  intros Pa src_m tgt_m cert opt_pf Hval.
  unfold validate_mcfg_with_cert_lrat in Hval.
  destruct (find_unique_defn_by_name (pc_function_name cert) (m_definitions src_m))
    as [src_defn |] eqn:Hfs; [| discriminate Hval].
  destruct (find_unique_defn_by_name (pc_function_name cert) (m_definitions tgt_m))
    as [tgt_defn |] eqn:Hft; [| discriminate Hval].
  destruct (negb (cert_fn_matches_raw_id (pc_function_name cert)
                    (dc_name (df_prototype src_defn)))); [discriminate Hval |].
  destruct (negb (check_prototype_contract (df_prototype src_defn)
                    (df_prototype tgt_defn))); [discriminate Hval |].
  destruct (negb (check_validator_syntax_gates
                    (convert_typ (m_type_defs src_m) (df_instrs src_defn))
                    (convert_typ (m_type_defs tgt_m) (df_instrs tgt_defn)))); [discriminate Hval |].
  destruct (check_cert_defn_with_lrat (m_type_defs src_m) (m_type_defs tgt_m)
              src_defn tgt_defn cert opt_pf) eqn:Hchk; [| discriminate Hval].
  destruct (find_unique_defn_by_name_in _ _ _ Hfs) as [Hin_s _].
  destruct (find_unique_defn_by_name_in _ _ _ Hft) as [Hin_t _].
  unfold check_cert_defn_with_lrat in Hchk; rewrite !andb_true_iff in Hchk.
  destruct Hchk as ([Hfn Hproto] & Hcfg).
  destruct (check_prototype_contract_inv _ _ Hproto) as [Hdcnm _].
  exists src_defn, tgt_defn; repeat split;
    [exact Hin_s | exact Hin_t | exact Hfn | exact Hdcnm | exact Hproto |].
  exact (check_cert_cfg_with_lrat_sound _ _ cert opt_pf Hcfg).
Qed.

Theorem validate_mcfg_with_cert_sound :
  forall {Pa : Params} (src_m tgt_m : CFG.mcfg typ) (cert : proof_certificate),
    validate_mcfg_with_cert src_m tgt_m cert = inr tt ->
    exists src_defn tgt_defn,
      In src_defn (m_definitions src_m) /\
      In tgt_defn (m_definitions tgt_m) /\
      cert_fn_matches_raw_id (pc_function_name cert) (dc_name (df_prototype src_defn)) = true /\
      dc_name (df_prototype src_defn) = dc_name (df_prototype tgt_defn) /\
      check_prototype_contract (df_prototype src_defn) (df_prototype tgt_defn) = true /\
      @validator_cfg_refines Pa
        (convert_typ (m_type_defs src_m) (df_instrs src_defn))
        (convert_typ (m_type_defs tgt_m) (df_instrs tgt_defn)).
Proof.
  intros Pa src_m tgt_m cert Hval.
  exact (validate_mcfg_with_cert_lrat_sound src_m tgt_m cert None Hval).
Qed.

Theorem validate_tle_pair_with_cert_str_sound :
  forall {Pa : Params}
         (src_tle tgt_tle : toplevel_entities typ (block typ * list (block typ)))
         (cert_str : string),
    validate_tle_pair_with_cert_str src_tle tgt_tle cert_str = inr tt ->
    let src_m := mcfg_of_tle (resolve_module_refs src_tle) in
    let tgt_m := mcfg_of_tle (resolve_module_refs tgt_tle) in
    exists cert src_defn tgt_defn,
      parse_cert cert_str = inr cert /\
      wf_proof_certificate cert = true /\
      In src_defn (m_definitions src_m) /\
      In tgt_defn (m_definitions tgt_m) /\
      cert_fn_matches_raw_id (pc_function_name cert) (dc_name (df_prototype src_defn)) = true /\
      dc_name (df_prototype src_defn) = dc_name (df_prototype tgt_defn) /\
      check_prototype_contract (df_prototype src_defn) (df_prototype tgt_defn) = true /\
      @validator_cfg_refines Pa
        (convert_typ (m_type_defs src_m) (df_instrs src_defn))
        (convert_typ (m_type_defs tgt_m) (df_instrs tgt_defn)).
Proof.
  intros Pa src_tle tgt_tle cert_str Hval src_m tgt_m.
  unfold validate_tle_pair_with_cert_str in Hval.
  destruct (parse_cert cert_str) as [| cert] eqn:Ep; [discriminate Hval |].
  unfold validate_tle_pair_with_cert in Hval; fold src_m tgt_m in Hval.
  pose proof (parse_cert_wf cert_str cert Ep) as Hwf_cert.
  destruct (validate_mcfg_with_cert_sound src_m tgt_m cert Hval)
    as (src_defn & tgt_defn & Hin_s & Hin_t & Hfn & Hdcnm & Hproto & Href).
  exists cert, src_defn, tgt_defn.
  repeat split; assumption.
Qed.
