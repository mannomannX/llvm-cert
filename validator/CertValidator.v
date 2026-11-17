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
  Semantics.MemoryBytes
  Semantics.Operations.Compare
  Semantics.Operations.Conversion
  Semantics.Operations.Select
  Semantics.Operations.Freeze
  Semantics.Operations.Gep
  Theory.MemoryBytesFacts.

From CertValidator Require Import
  CertFormat
  AigLrat
  AlgRules.

Import ListNotations.
Import Sum.
Import Subevent.
Import Logic.

Unset Implicit Arguments.
Unset Strict Implicit.
Set Default Goal Selector "!".

#[local] Arguments Pos.eqb _ _ : simpl nomatch.
#[local] Arguments Pos.ltb _ _ : simpl nomatch.
#[local] Arguments Pos.leb _ _ : simpl nomatch.
#[local] Arguments N.eqb _ _ : simpl nomatch.
#[local] Arguments N.ltb _ _ : simpl nomatch.
#[local] Arguments N.leb _ _ : simpl nomatch.
#[local] Arguments Z.eqb _ _ : simpl nomatch.
#[local] Arguments Z.ltb _ _ : simpl nomatch.
#[local] Arguments Z.leb _ _ : simpl nomatch.
#[local] Arguments Z.gtb _ _ : simpl nomatch.
#[local] Arguments Z.geb _ _ : simpl nomatch.
#[local] Arguments Nat.eqb _ _ : simpl nomatch.
#[local] Arguments String.eqb _ _ : simpl nomatch.
#[local] Arguments Integers.modulus : simpl never.
#[local] Arguments Integers.half_modulus : simpl never.
#[local] Arguments Integers.max_unsigned : simpl never.
#[local] Arguments Integers.max_signed : simpl never.
#[local] Arguments Integers.min_signed : simpl never.
#[local] Arguments Integers.unsigned : simpl never.
#[local] Arguments Integers.signed : simpl never.
#[local] Arguments Integers.repr : simpl never.
#[local] Arguments Integers.zero : simpl never.
#[local] Arguments Integers.one : simpl never.
#[local] Arguments Integers.mone : simpl never.
#[local] Arguments Integers.iwordsize : simpl never.
#[local] Arguments Integers.eq : simpl never.
#[local] Arguments Integers.lt : simpl never.
#[local] Arguments Integers.ltu : simpl never.
#[local] Arguments Integers.neg : simpl never.
#[local] Arguments Integers.add : simpl never.
#[local] Arguments Integers.sub : simpl never.
#[local] Arguments Integers.mul : simpl never.
#[local] Arguments Integers.divs : simpl never.
#[local] Arguments Integers.mods : simpl never.
#[local] Arguments Integers.divu : simpl never.
#[local] Arguments Integers.modu : simpl never.
#[local] Arguments Integers.and : simpl never.
#[local] Arguments Integers.or : simpl never.
#[local] Arguments Integers.xor : simpl never.
#[local] Arguments Integers.not : simpl never.
#[local] Arguments Integers.shl : simpl never.
#[local] Arguments Integers.shru : simpl never.
#[local] Arguments Integers.shr : simpl never.
#[local] Arguments Integers.rol : simpl never.
#[local] Arguments Integers.ror : simpl never.
#[local] Arguments Integers.rolm : simpl never.
#[local] Arguments Integers.negative : simpl never.
#[local] Arguments Integers.add_carry : simpl never.
#[local] Arguments Integers.add_overflow : simpl never.
#[local] Arguments Integers.sub_borrow : simpl never.
#[local] Arguments Integers.sub_overflow : simpl never.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** 1. ITree Observation Primitives, Open-World Event Signatures & [DrawE] Strategies *)

Section ITreeObsLemmas.
  Lemma observe_bind {E : Type -> Type} {R S : Type}
    (t : itree E R) (k : R -> itree E S) :
    observe (ITree.bind t k) =
    match observe t with
    | RetF r => observe (k r)
    | TauF t' => TauF (ITree.bind t' k)
    | VisF _ e ke => VisF e (fun x => ITree.bind (ke x) k)
    end.
  Proof using Type.
    unfold ITree.bind, ITree.subst; unfold observe at 1; cbn; destruct (observe t); reflexivity.
  Qed.

  Lemma observe_translate {E F : Type -> Type} {R : Type}
    (h : E ~> F) (t : itree E R) :
    observe (translate h t) =
    match observe t with
    | RetF r => RetF r
    | TauF t' => TauF (translate h t')
    | VisF _ e ke => VisF (h _ e) (fun x => translate h (ke x))
    end.
  Proof using Type.
    unfold translate; unfold observe at 1; cbn; destruct (observe t); reflexivity.
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
    | VisF _ e k =>
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
    | VisF _ e k =>
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
    unfold observe at 1; cbn; destruct (observe t) as [r | t' | X e k]; [reflexivity | reflexivity |].
    destruct (classify_cfg_event e) as [le | oe]; [| reflexivity].
    destruct le as [id dv | id]; [reflexivity |].
    destruct (RM.find id env); reflexivity.
  Qed.

  Fixpoint init_cfg_locals (params : list raw_id) (vs : list dvalue) {struct params} : rmap dvalue :=
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
    {struct draws} : draw_strat :=
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
    | VisF _ e k =>
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
    | VisF _ e k =>
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
    unfold observe at 1; cbn; destruct (observe t) as [r | t' | X e k]; [reflexivity | reflexivity |].
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
    | VisF _ e1 k1 =>
        det_is_ub e1 = true \/
        match observe t2 with
        | VisF _ e2 k2 => det_vis_both r e1 k1 e2 k2
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

  Lemma det_ref_obs_eq {R1 R2 : Type} (RR : R1 -> R2 -> Prop)
    {r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop} :
    forall t1 t2 t1' t2',
      observe t1 = observe t1' ->
      observe t2 = observe t2' ->
      paco2 (det_ref_ RR) r t1 t2 ->
      paco2 (det_ref_ RR) r t1' t2'.
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
        rewrite observe_bind;
        cbn [observe classify_ow_event subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
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
        cbn [classify_ow_event subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun];
        unfold sigma1; cbn [prepend_draws].
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
      by (apply @Integers.unsigned_repr; unfold Integers.max_unsigned;
          rewrite (@Integers.modulus_two_power_nat w), (@Integers.natwordsize_def w);
          assert (Hp : (2 <= two_power_nat (Pos.to_nat w))%Z) by
            (rewrite two_power_nat_equiv;
             assert (Hge1 : (1 <= Z.of_nat (Pos.to_nat w))%Z) by lia;
             pose proof (Z.pow_le_mono_r 2 1 (Z.of_nat (Pos.to_nat w)) ltac:(lia) Hge1); lia);
          lia).
    assert (Hu1 : @Integers.unsigned w (@Integers.repr w 1) = 1%Z)
      by (apply @Integers.unsigned_repr; unfold Integers.max_unsigned;
          rewrite (@Integers.modulus_two_power_nat w), (@Integers.natwordsize_def w);
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

Fixpoint raw_id_in_list (r : raw_id) (xs : list raw_id) {struct xs} : bool :=
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

Fixpoint find_raw_id_index_from (r : raw_id) (xs : list raw_id) (idx : nat)
  {struct xs} : option nat :=
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
  let fix texp_list_uses (xs : list (dtyp * exp dtyp)) {struct xs} : list (nat * dtyp) :=
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

Fixpoint param_use_in (u : nat * dtyp) (us : list (nat * dtyp)) {struct us} : bool :=
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
  | Raw z => ("_RAW_" ++ show_Z_dec z)%string
  end.

Definition cert_reg_name (id : raw_id) : string :=
  ("%" ++ cert_raw_id_bare id)%string.

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
  (tail_s : @draw_strat Pa) {struct draws} : @draw_strat Pa :=
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

Fixpoint freeze_key_in (k : freeze_key) (ks : list freeze_key) {struct ks} : bool :=
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
  (pnames : list string) (vs : list (@dvalue Pa)) {struct pnames} : param_env Pa :=
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

Fixpoint var_pair_in (u : string * positive) (us : list (string * positive))
  {struct us} : bool :=
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
| CD_BlockAssume (uas : list ub_assumption) (next : cfg_dag)
| CD_Branch (cond : cert_expr) (on_true on_false : cfg_dag).

Variant dag_outcome {Pa : Params} : Type :=
| DO_UB
| DO_Ret (dv : @dvalue Pa).

Fixpoint eval_cfg_dag {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle) (d : cfg_dag)
  {struct d} : @dag_outcome Pa :=
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
  | CD_BlockAssume _ next =>
      eval_cfg_dag penv foracle next
  | CD_Branch cond on_true on_false =>
      match eval_closed_cert_expr penv foracle cond with
      | raise_ret (DVALUE_Base (@DVALUE_I _ 1%positive cbit)) =>
          if (@Integers.unsigned 1 cbit =? 1)%Z
          then eval_cfg_dag penv foracle on_true
          else eval_cfg_dag penv foracle on_false
      | _ => DO_UB
      end
  end.

Fixpoint wf_cfg_dag (allowed : list (string * positive)) (d : cfg_dag)
  {struct d} : bool :=
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
  | CD_BlockAssume _ next =>
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

Fixpoint wrap_evals (evals : list (positive * cert_expr)) (k : cfg_dag)
  {struct evals} : cfg_dag :=
  match evals with
  | [] => k
  | (w, ce) :: rest => CD_Eval w ce (wrap_evals rest k)
  end.

Fixpoint wrap_phi_evals
  (pevals : list (raw_id * positive * cert_expr)) (k : cfg_dag)
  {struct pevals} : cfg_dag :=
  match pevals with
  | [] => k
  | (_, w, ce) :: rest => CD_Eval w ce (wrap_phi_evals rest k)
  end.

Fixpoint apply_phi_smap
  (smap : rmap (positive * cert_expr))
  (pevals : list (raw_id * positive * cert_expr))
  {struct pevals} : rmap (positive * cert_expr) :=
  match pevals with
  | [] => smap
  | (id, w, ce) :: rest => apply_phi_smap (RM.add id (w, ce) smap) rest
  end.

Fixpoint apply_phi_env {Pa : Params}
  (env : rmap (@dvalue Pa)) (dvs : list (raw_id * @dvalue Pa))
  {struct dvs} : rmap (@dvalue Pa) :=
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
  {struct phis} : option (list (raw_id * positive * cert_expr) * list freeze_key) :=
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
  {struct c} : option (list (positive * cert_expr) * rmap (positive * cert_expr) * list freeze_key) :=
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

Lemma reify_exp_wt_lf :
  forall (o : exp dtyp) uf params src_pnames defs allowed smap seen0 top w ce seen1,
    wf_smap_entries allowed defs seen0 uf smap ->
    reify_exp uf params src_pnames defs smap seen0 top o = Some (w, ce, seen1) ->
    wt_cert_expr [] ce = true /\ is_let_free_expr ce = true.
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
    as (_ & Hwt & _ & Hlf & _).
  exact (conj Hwt Hlf).
Qed.

Lemma eval_closed_lf_ret_wf_param_env {Pa : Params} :
  forall (e : cert_expr) (penv : param_env Pa) (foracle : freeze_oracle) (dv : @dvalue Pa),
    is_let_free_expr e = true ->
    eval_closed_cert_expr penv foracle e = raise_ret dv ->
    wf_param_env_for (collect_free_vars [] e) penv.
Proof.
  unfold eval_closed_cert_expr.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros penv foracle dv Hlf Hev x wx Hx;
    cbn [is_let_free_expr collect_free_vars eval_cert_expr lookup_let_val] in Hlf, Hev, Hx;
    try contradiction Hx; try discriminate Hlf.
  - destruct (starts_with_dollar nm); [contradiction Hx |].
    destruct Hx as [Heq | []]; inversion Heq; subst x wx.
    destruct (penv nm) as [v |] eqn:Ep; [| discriminate Hev].
    exists v; split; [reflexivity |].
    destruct v as [db | |]; try discriminate Hev.
    destruct db as [| sz iv | | | | | |]; try discriminate Hev.
    + left; reflexivity.
    + cbn [check_scalar_width] in Hev.
      destruct (Pos.eqb sz w) eqn:Esz; [| discriminate Hev].
      apply Pos.eqb_eq in Esz; subst sz; right; exists iv; reflexivity.
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    destruct (eval_cert_expr penv [] foracle l) as [| | | vl] eqn:El; try discriminate Hev.
    cbn [eou_bind] in Hev.
    destruct (eval_cert_expr penv [] foracle r) as [| | | vr] eqn:Er; try discriminate Hev.
    apply in_app_iff in Hx as [Hxl | Hxr];
      [exact (IHl penv foracle vl Hlfl El x wx Hxl)
      | exact (IHr penv foracle vr Hlfr Er x wx Hxr)].
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    destruct (eval_cert_expr penv [] foracle l) as [| | | vl] eqn:El; try discriminate Hev.
    cbn [eou_bind] in Hev.
    destruct (eval_cert_expr penv [] foracle r) as [| | | vr] eqn:Er; try discriminate Hev.
    apply in_app_iff in Hx as [Hxl | Hxr];
      [exact (IHl penv foracle vl Hlfl El x wx Hxl)
      | exact (IHr penv foracle vr Hlfr Er x wx Hxr)].
  - destruct (eval_cert_expr penv [] foracle o) as [| | | vo] eqn:Eo; try discriminate Hev.
    exact (IHo penv foracle vo Hlf Eo x wx Hx).
  - rewrite !andb_true_iff in Hlf; destruct Hlf as ([Hlfc Hlft] & Hlff).
    destruct (eval_cert_expr penv [] foracle c) as [| | | vc] eqn:Ec; try discriminate Hev.
    cbn [eou_bind] in Hev.
    destruct (eval_cert_expr penv [] foracle t) as [| | | vt] eqn:Et; try discriminate Hev.
    cbn [eou_bind] in Hev.
    destruct (eval_cert_expr penv [] foracle f) as [| | | vf] eqn:Ef; try discriminate Hev.
    apply in_app_iff in Hx as [Hxc | Hxtf];
      [exact (IHc penv foracle vc Hlfc Ec x wx Hxc) |].
    apply in_app_iff in Hxtf as [Hxt | Hxf];
      [exact (IHt penv foracle vt Hlft Et x wx Hxt)
      | exact (IHf penv foracle vf Hlff Ef x wx Hxf)].
  - destruct (eval_cert_expr penv [] foracle o) as [| | | vo] eqn:Eo; try discriminate Hev.
    exact (IHo penv foracle vo Hlf Eo x wx Hx).
Qed.

Definition try_const_i1 (ce : cert_expr) : option bool :=
  match normalize_cert_expr [] ce with
  | CE_BvConst 1%positive v =>
      Some (@Integers.unsigned 1 (@Integers.repr 1 (Z.of_N v)) =? 1)%Z
  | _ => None
  end.

Lemma try_const_i1_sound {Pa : Params} :
  forall (ce : cert_expr) (penv : param_env Pa) (foracle : freeze_oracle) (b : bool),
    wt_cert_expr [] ce = true ->
    is_let_free_expr ce = true ->
    wf_param_env_for (collect_free_vars [] ce) penv ->
    try_const_i1 ce = Some b ->
    exists cbit : @Integers.bit_int 1,
      eval_closed_cert_expr penv foracle ce =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit)) /\
      (@Integers.unsigned 1 cbit =? 1)%Z = b.
Proof.
  intros ce penv foracle b Hwt Hlf Hpenv Htc.
  unfold try_const_i1 in Htc.
  pose proof (normalize_cert_expr_eval [] ce penv foracle Hwt Hlf Hpenv (Forall_nil _)) as Heq.
  destruct (normalize_cert_expr [] ce) as [w v | | | | | | | |] eqn:En; try discriminate Htc.
  destruct w as [| |]; try discriminate Htc.
  inversion Htc; subst b; clear Htc.
  cbn [eval_closed_cert_expr eval_cert_expr] in Heq.
  destruct (eval_closed_cert_expr penv foracle ce) as [| | | dv]; try contradiction Heq.
  subst dv; exists (@Integers.repr 1 (Z.of_N v)); split; reflexivity.
Qed.

Definition strip_leading_percent (s : string) : string :=
  match s with
  | String c rest =>
      if Nat.eqb (nat_of_ascii c) 37%nat then rest else s
  | EmptyString => EmptyString
  end.

Definition cert_block_matches_id (bname : string) (bid : block_id) : bool :=
  String.eqb (strip_leading_percent bname) (cert_raw_id_bare bid).

Definition block_uas_for
  (entry_bid : block_id) (bcs : list block_certificate) (bid : block_id)
  : list ub_assumption :=
  List.flat_map (fun bc =>
    let matched :=
      cert_block_matches_id (bc_src_block bc) bid ||
      match bc_kind bc with
      | BCK_Entry => raw_id_eqb bid entry_bid
      | _ => false
      end in
    if matched then bc_ub_assumptions bc else []) bcs.

Definition default_cfg_dag_fuel (G : CFG.cfg dtyp) : nat :=
  S (17 * List.length (blks G)).

Fixpoint summarize_ocfg_dag
  (fuel : nat)
  (blk_uas : block_id -> list ub_assumption)
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
                    let opt_d_term :=
                      match blk_term b with
                      | (_, TERM_Unreachable, _) =>
                          Some CD_Unreachable
                      | (_, TERM_Ret_void, _) =>
                          Some CD_RetVoid
                      | (_, TERM_Ret (DTYPE_Base (DTYPE_I w), op), _) =>
                          match reify_exp uf params src_pnames defs smap_c seen_c
                                  (Some (DTYPE_Base (DTYPE_I w))) op with
                          | Some (_, ce_ret, _) =>
                              Some (CD_RetScalar w ce_ret)
                          | None => None
                          end
                      | (_, TERM_Br_1 br, _) =>
                          summarize_ocfg_dag fuel' blk_uas uf params src_pnames defs bmap
                            false bid_cur br smap_c seen_c
                      | (_, TERM_Br (DTYPE_Base (DTYPE_I 1%positive), op) br1 br2, _) =>
                          match reify_exp uf params src_pnames defs smap_c seen_c
                                  (Some (DTYPE_Base (DTYPE_I 1%positive))) op with
                          | Some (_, ce_cond, seen_br) =>
                              match try_const_i1 ce_cond with
                              | Some true =>
                                  match summarize_ocfg_dag fuel' blk_uas uf params src_pnames defs bmap
                                          false bid_cur br1 smap_c seen_br with
                                  | Some d_t => Some (CD_Eval 1%positive ce_cond d_t)
                                  | None => None
                                  end
                              | Some false =>
                                  match summarize_ocfg_dag fuel' blk_uas uf params src_pnames defs bmap
                                          false bid_cur br2 smap_c seen_br with
                                  | Some d_f => Some (CD_Eval 1%positive ce_cond d_f)
                                  | None => None
                                  end
                              | None =>
                                  match summarize_ocfg_dag fuel' blk_uas uf params src_pnames defs bmap
                                          false bid_cur br1 smap_c seen_br,
                                        summarize_ocfg_dag fuel' blk_uas uf params src_pnames defs bmap
                                          false bid_cur br2 smap_c seen_br with
                                  | Some d_t, Some d_f =>
                                      Some (CD_Branch ce_cond d_t d_f)
                                  | _, _ => None
                                  end
                              end
                          | None => None
                          end
                      | _ => None
                      end in
                    match opt_d_term with
                    | Some d_term =>
                        Some (CD_BlockAssume (blk_uas bid_cur)
                                (wrap_phi_evals pevals (wrap_evals cevals d_term)))
                    | None => None
                    end
                end
            end
      end
  end.

Definition summarize_cfg_dag_with_uas
  (blk_uas : block_id -> list ub_assumption)
  (uf : bool) (G : CFG.cfg dtyp) (src_pnames : list string) : option cfg_dag :=
  summarize_ocfg_dag
    (default_cfg_dag_fuel G)
    blk_uas
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

Definition summarize_cfg_dag
  (uf : bool) (G : CFG.cfg dtyp) (src_pnames : list string) : option cfg_dag :=
  summarize_cfg_dag_with_uas (fun _ => []) uf G src_pnames.

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
  forall fuel blk_uas uf G src_pnames allowed is_entry bid_from bid_cur smap seen d,
    (forall idx w0 pnm,
      In (idx, DTYPE_Base (DTYPE_I w0)) (param_idx_uses_cfg G) ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w0) allowed) ->
    wf_smap_entries allowed (defined_ids_of_cfg G) seen uf smap ->
    summarize_ocfg_dag fuel blk_uas uf (args G) src_pnames (defined_ids_of_cfg G)
      (ocfg_map (blks G)) is_entry bid_from bid_cur smap seen = Some d ->
    wf_cfg_dag allowed d = true.
Proof.
  induction fuel as [| fuel' IH];
    intros blk_uas uf G src_pnames allowed is_entry bid_from bid_cur smap seen d Hpu_cfg Hsmap Hr;
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
  cbn zeta in Hr.
  match type of Hr with
  | match ?ot with Some _ => _ | None => _ end = Some _ =>
      destruct ot as [d_term |] eqn:Hopt; [| discriminate Hr]
  end.
  inversion Hr; subst d; clear Hr.
  cbn [wf_cfg_dag]; apply (wrap_phi_evals_wf _ _ _ _ _ _ Hfa_p); apply Hwrap_c.
  destruct (blk_term b) as [[tiid tm] tmd] eqn:Htm.
  destruct tm; try discriminate Hopt.
  - (* TERM_Ret *)
    destruct v as [dt op].
    destruct dt as [tb | |]; try discriminate Hopt; destruct tb as [w | | | | | | | | | |]; try discriminate Hopt.
    destruct (reify_exp uf (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                (Some (DTYPE_Base (DTYPE_I w))) op)
      as [[[w1 ce_ret] seen_ret] |] eqn:Hr_ret; [| discriminate Hopt].
    inversion Hopt; subst d_term; clear Hopt.
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
    cbn [wf_cfg_dag].
    rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv); reflexivity.
  - (* TERM_Ret_void *)
    inversion Hopt; subst d_term; reflexivity.
  - (* TERM_Br *)
    destruct v as [dt op].
    destruct dt as [tb | |]; try discriminate Hopt; destruct tb as [wc | | | | | | | | | |]; try discriminate Hopt.
    destruct wc as [| |]; try discriminate Hopt.
    destruct (reify_exp uf (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                (Some (DTYPE_Base (DTYPE_I 1%positive))) op)
      as [[[wc' ce_cond] seen_br] |] eqn:Hr_cond; [| discriminate Hopt].
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
    destruct (try_const_i1 ce_cond) as [[|] |].
    + destruct (summarize_ocfg_dag fuel' blk_uas uf (args G) src_pnames (defined_ids_of_cfg G)
                  (ocfg_map (blks G)) false bid_cur br1 smap_c seen_br)
        as [d_t |] eqn:Hr_t; [| discriminate Hopt].
      inversion Hopt; subst d_term.
      pose proof (IH blk_uas uf G src_pnames allowed false bid_cur br1 smap_c seen_br d_t Hpu_cfg Hsmap_br Hr_t) as Hwft.
      cbn [wf_cfg_dag]; rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv), Hwft; reflexivity.
    + destruct (summarize_ocfg_dag fuel' blk_uas uf (args G) src_pnames (defined_ids_of_cfg G)
                  (ocfg_map (blks G)) false bid_cur br2 smap_c seen_br)
        as [d_f |] eqn:Hr_f; [| discriminate Hopt].
      inversion Hopt; subst d_term.
      pose proof (IH blk_uas uf G src_pnames allowed false bid_cur br2 smap_c seen_br d_f Hpu_cfg Hsmap_br Hr_f) as Hwff.
      cbn [wf_cfg_dag]; rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv), Hwff; reflexivity.
    + destruct (summarize_ocfg_dag fuel' blk_uas uf (args G) src_pnames (defined_ids_of_cfg G)
                  (ocfg_map (blks G)) false bid_cur br1 smap_c seen_br)
        as [d_t |] eqn:Hr_t; [| discriminate Hopt].
      destruct (summarize_ocfg_dag fuel' blk_uas uf (args G) src_pnames (defined_ids_of_cfg G)
                  (ocfg_map (blks G)) false bid_cur br2 smap_c seen_br)
        as [d_f |] eqn:Hr_f; [| discriminate Hopt].
      inversion Hopt; subst d_term.
      pose proof (IH blk_uas uf G src_pnames allowed false bid_cur br1 smap_c seen_br d_t Hpu_cfg Hsmap_br Hr_t) as Hwft.
      pose proof (IH blk_uas uf G src_pnames allowed false bid_cur br2 smap_c seen_br d_f Hpu_cfg Hsmap_br Hr_f) as Hwff.
      cbn [wf_cfg_dag]; rewrite Hwt, Hbw, Pos.eqb_refl, Hlf, (incl_vars_subset_b _ _ Hfv), Hwft, Hwff; reflexivity.
  - (* TERM_Br_1 *)
    exact (IH blk_uas uf G src_pnames allowed false bid_cur br smap_c seen_c d_term Hpu_cfg Hsmap_c Hopt).
  - (* TERM_Unreachable *)
    inversion Hopt; subst d_term; reflexivity.
Qed.

Lemma summarize_cfg_dag_with_uas_wf :
  forall blk_uas uf G src_pnames allowed d,
    (forall idx w0 pnm,
      In (idx, DTYPE_Base (DTYPE_I w0)) (param_idx_uses_cfg G) ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w0) allowed) ->
    summarize_cfg_dag_with_uas blk_uas uf G src_pnames = Some d ->
    wf_cfg_dag allowed d = true.
Proof.
  intros blk_uas uf G src_pnames allowed d Hpu Hr.
  exact (summarize_ocfg_dag_wf (default_cfg_dag_fuel G) blk_uas uf G src_pnames allowed
           true (init G) (init G) (RM.empty _) [] d Hpu
           (wf_smap_entries_empty allowed (defined_ids_of_cfg G) [] uf) Hr).
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
  exact (summarize_cfg_dag_with_uas_wf (fun _ => []) uf G src_pnames allowed d Hpu Hr).
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
  forall fuel blk_uas G src_pnames allowed arg_dtys (vs : list (@dvalue Pa))
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
    summarize_ocfg_dag fuel blk_uas false (args G) src_pnames (defined_ids_of_cfg G)
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
    intros blk_uas G src_pnames allowed arg_dtys vs foracle is_entry bid_from bid_cur smap env seen d
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
  cbn zeta in Hr.
  match type of Hr with
  | match ?ot with Some _ => _ | None => _ end = Some _ =>
      destruct ot as [d_term |] eqn:Hopt; [| discriminate Hr]
  end.
  inversion Hr; subst d; clear Hr.
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
    + cbn [eval_cfg_dag]; exact (Hev_ub_p (wrap_evals cevals d_term)).
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
      * cbn [eval_cfg_dag]; rewrite Hev_kp; exact (Hev_ub_c d_term).
    + destruct (reify_code_wf_smap (blk_code b) false (args G) src_pnames (defined_ids_of_cfg G)
                  ext_p (apply_phi_smap smap pevals) seen_p cevals smap_c seen_c Hwfs_p Hr_code)
        as (ext_c & _ & Hwfs_c).
      destruct (blk_term b) as [[tiid tm] tmd] eqn:Htm.
      destruct tm; try discriminate Hopt.
      * (* TERM_Ret *)
        destruct v as [dt op].
        destruct dt as [tb | |]; try discriminate Hopt; destruct tb as [w | | | | | | | | | |]; try discriminate Hopt.
        destruct (reify_exp false (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                    (Some (DTYPE_Base (DTYPE_I w))) op)
          as [[[w1 ce_ret] seen_ret] |] eqn:Hr_ret; [| discriminate Hopt].
        inversion Hopt; subst d_term; clear Hopt.
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
           ++ cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc; cbn [eval_cfg_dag]; rewrite Hev_r; reflexivity.
        -- exists ((draws_p ++ draws_c) ++ draws_r).
           split; [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dr] | right].
           exists env_c, dv_r; split.
           ++ cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc; cbn [eval_cfg_dag]; rewrite Hev_r; reflexivity.
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
        inversion Hopt; subst d_term; clear Hopt.
        exists (draws_p ++ draws_c); split; [apply Forall_app; split; assumption | right].
        exists env_c, NONE; split; [cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc; reflexivity |].
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
        destruct dt as [tb | |]; try discriminate Hopt; destruct tb as [wc | | | | | | | | | |]; try discriminate Hopt.
        destruct wc as [| |]; try discriminate Hopt.
        destruct (reify_exp false (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                    (Some (DTYPE_Base (DTYPE_I 1%positive))) op)
          as [[[wc' ce_cond] seen_br] |] eqn:Hr_cond; [| discriminate Hopt].
        pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr_cond)) as ->.
        destruct (reify_exp_wt_lf op false (args G) src_pnames (defined_ids_of_cfg G)
                    ext_c smap_c seen_c (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive ce_cond seen_br
                    Hwfs_c Hr_cond) as [Hwt_cond Hlf_cond].
        pose proof (wf_smap_entries_false_seen ext_c (defined_ids_of_cfg G) seen_c seen_br smap_c Hwfs_c) as Hwfs_br.
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
           ++ cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc.
              destruct (try_const_i1 ce_cond) as [[|] |].
              ** destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br1 _ _); [| discriminate Hopt].
                 inversion Hopt; subst d_term; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
              ** destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br2 _ _); [| discriminate Hopt].
                 inversion Hopt; subst d_term; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
              ** destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br1 _ _); [| discriminate Hopt].
                 destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br2 _ _); [| discriminate Hopt].
                 inversion Hopt; subst d_term; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
        -- pose proof (eval_closed_lf_ret_wf_param_env ce_cond (build_param_env src_pnames vs)
                         foracle dv_br Hlf_cond Hev_br) as Hp_cond.
           destruct Hsc_br as [-> | [cbit ->]].
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
              ** destruct (try_const_i1 ce_cond) as [b_tc |] eqn:Etc.
                 --- destruct (try_const_i1_sound ce_cond (build_param_env src_pnames vs)
                                 foracle b_tc Hwt_cond Hlf_cond Hp_cond Etc) as [cbit_tc [Hev_tc _]].
                     congruence.
                 --- destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br1 _ _); [| discriminate Hopt].
                     destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br2 _ _); [| discriminate Hopt].
                     inversion Hopt; subst d_term.
                     cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
           ++ set (br_tgt := if (@Integers.unsigned 1 cbit =? 1)%Z then br1 else br2).
              assert (Hnext_br :
                exists d_next,
                  summarize_ocfg_dag fuel' blk_uas false (args G) src_pnames (defined_ids_of_cfg G)
                    (ocfg_map (blks G)) false bid_cur br_tgt smap_c seen_br = Some d_next /\
                  eval_cfg_dag (build_param_env src_pnames vs) foracle d_term =
                  eval_cfg_dag (build_param_env src_pnames vs) foracle d_next).
              { destruct (try_const_i1 ce_cond) as [[|] |] eqn:Etc.
                - destruct (try_const_i1_sound ce_cond (build_param_env src_pnames vs)
                              foracle true Hwt_cond Hlf_cond Hp_cond Etc) as [cbit' [Hev_tc Ecbit']].
                  rewrite Hev_br in Hev_tc; injection Hev_tc as Heq_dv.
                  pose proof (dvalue_I_same_sz_inj 1 cbit cbit' Heq_dv) as <-.
                  unfold br_tgt; rewrite Ecbit'.
                  destruct (summarize_ocfg_dag fuel' blk_uas false (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br1 smap_c seen_br) as [d_t |] eqn:Hr_t;
                    [| discriminate Hopt].
                  inversion Hopt; subst d_term; exists d_t; split; [exact Hr_t |].
                  cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
                - destruct (try_const_i1_sound ce_cond (build_param_env src_pnames vs)
                              foracle false Hwt_cond Hlf_cond Hp_cond Etc) as [cbit' [Hev_tc Ecbit']].
                  rewrite Hev_br in Hev_tc; injection Hev_tc as Heq_dv.
                  pose proof (dvalue_I_same_sz_inj 1 cbit cbit' Heq_dv) as <-.
                  unfold br_tgt; rewrite Ecbit'.
                  destruct (summarize_ocfg_dag fuel' blk_uas false (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br2 smap_c seen_br) as [d_f |] eqn:Hr_f;
                    [| discriminate Hopt].
                  inversion Hopt; subst d_term; exists d_f; split; [exact Hr_f |].
                  cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
                - destruct (summarize_ocfg_dag fuel' blk_uas false (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br1 smap_c seen_br) as [d_t |] eqn:Hr_t;
                    [| discriminate Hopt].
                  destruct (summarize_ocfg_dag fuel' blk_uas false (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br2 smap_c seen_br) as [d_f |] eqn:Hr_f;
                    [| discriminate Hopt].
                  inversion Hopt; subst d_term.
                  exists (if (@Integers.unsigned 1 cbit =? 1)%Z then d_t else d_f); split.
                  + unfold br_tgt; destruct (@Integers.unsigned 1 cbit =? 1)%Z; [exact Hr_t | exact Hr_f].
                  + cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity. }
              destruct Hnext_br as [d_next [Hr_next Hev_term]].
              destruct (IH blk_uas G src_pnames ext_c arg_dtys vs foracle false bid_cur br_tgt
                          smap_c env_c seen_br d_next
                          Hnd Hlp Hls Hla Hcomp Hvs Hpe_c Hwfs_br Henv_c Hr_next)
                as (draws_n & Hfa_dn & [[Hub_n Hev_ub_n] | [env_out [dv_out [Hev_out Hst_n]]]]).
              ** exists (((draws_p ++ draws_c) ++ draws_br) ++ draws_n).
                 split;
                   [apply Forall_app; split;
                      [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dbr] | exact Hfa_dn]
                   | left; split].
                 --- intros tail_s; rewrite !chain_draws_app.
                     eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
                     unfold denote_block; rewrite Htm.
                     eapply cfg_steps_to_ub_bind_r.
                     +++ eapply cfg_steps_to_ret_bind.
                         *** eapply cfg_steps_to_ret_bind;
                               [exact (Hphis_step (chain_draws draws_c (chain_draws draws_br (chain_draws draws_n tail_s)))) |].
                             eapply cfg_steps_to_ret_bind;
                               [exact (Hst_c (chain_draws draws_br (chain_draws draws_n tail_s))) |].
                             cbn [denote_terminator]; unfold denote_exp'.
                             eapply cfg_steps_to_ret_bind;
                               [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst_br (chain_draws draws_n tail_s))) |].
                             rewrite bit_int_1_equ_one_eq_unsigned; unfold br_tgt.
                             destruct (@Integers.unsigned 1 cbit =? 1)%Z; apply CSR_Ret; reflexivity.
                         *** apply CSR_Ret; reflexivity.
                     +++ eapply CSU_Tau; [reflexivity | exact (Hub_n tail_s)].
                 --- cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc, Hev_term; exact Hev_ub_n.
              ** exists (((draws_p ++ draws_c) ++ draws_br) ++ draws_n).
                 split;
                   [apply Forall_app; split;
                      [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dbr] | exact Hfa_dn]
                   | right; exists env_out, dv_out; split].
                 --- cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc, Hev_term; exact Hev_out.
                 --- intros tail_s; rewrite !chain_draws_app.
                     eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
                     unfold denote_block; rewrite Htm.
                     eapply cfg_steps_to_ret_bind.
                     +++ eapply cfg_steps_to_ret_bind.
                         *** eapply cfg_steps_to_ret_bind;
                               [exact (Hphis_step (chain_draws draws_c (chain_draws draws_br (chain_draws draws_n tail_s)))) |].
                             eapply cfg_steps_to_ret_bind;
                               [exact (Hst_c (chain_draws draws_br (chain_draws draws_n tail_s))) |].
                             cbn [denote_terminator]; unfold denote_exp'.
                             eapply cfg_steps_to_ret_bind;
                               [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (Hst_br (chain_draws draws_n tail_s))) |].
                             rewrite bit_int_1_equ_one_eq_unsigned; unfold br_tgt.
                             destruct (@Integers.unsigned 1 cbit =? 1)%Z; apply CSR_Ret; reflexivity.
                         *** apply CSR_Ret; reflexivity.
                     +++ eapply CSR_Tau; [reflexivity | exact (Hst_n tail_s)].
      * (* TERM_Br_1 *)
        destruct (IH blk_uas G src_pnames ext_c arg_dtys vs foracle false bid_cur br smap_c env_c seen_c d_term
                    Hnd Hlp Hls Hla Hcomp Hvs Hpe_c Hwfs_c Henv_c Hopt)
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
           ++ cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc; exact Hev_ub_n.
        -- exists ((draws_p ++ draws_c) ++ draws_n).
           split; [apply Forall_app; split; [apply Forall_app; split; assumption | exact Hfa_dn] | right].
           exists env_out, dv_out; split; [cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc; exact Hev_out |].
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
        inversion Hopt; subst d_term; clear Hopt.
        exists (draws_p ++ draws_c); split; [apply Forall_app; split; assumption | left; split].
        -- intros tail_s; rewrite chain_draws_app.
           eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
           unfold denote_block; rewrite Htm.
           apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l.
           eapply cfg_steps_to_ub_bind_r; [exact (Hphis_step (chain_draws draws_c tail_s)) |].
           eapply cfg_steps_to_ub_bind_r; [exact (Hst_c tail_s) | eapply CSU_UB; reflexivity].
        -- cbn [eval_cfg_dag]; rewrite Hev_kp, Hev_kc; reflexivity.
Qed.

Lemma summarize_src_dag_with_uas_sound {Pa : Params} :
  forall blk_uas G src_pnames arg_dtys (vs : list (@dvalue Pa)) (foracle : freeze_oracle) d,
    NoDup (args G) ->
    NoDup src_pnames ->
    List.length src_pnames = List.length (args G) ->
    List.length arg_dtys = List.length (args G) ->
    cfg_param_dtyp_compatible G arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    summarize_cfg_dag_with_uas blk_uas false G src_pnames = Some d ->
    exists sigma_src : @draw_strat Pa,
      wf_draw_strat sigma_src /\
      ((cfg_steps_to_ub sigma_src (init_cfg_locals (args G) vs) (denote_cfg G None) /\
        eval_cfg_dag (build_param_env src_pnames vs) foracle d = DO_UB) \/
       (exists sigma_src' env_out dv,
          eval_cfg_dag (build_param_env src_pnames vs) foracle d = DO_Ret dv /\
          cfg_steps_to_ret sigma_src (init_cfg_locals (args G) vs) (denote_cfg G None)
            sigma_src' env_out dv)).
Proof.
  intros blk_uas G src_pnames arg_dtys vs foracle d Hnd_p Hnd_s Hlen_sp Hlen_da Hcomp Hvs Hr.
  assert (Hlen_vs : List.length vs = List.length arg_dtys) by exact (Forall2_length Hvs).
  assert (Hlp : List.length (args G) = List.length vs) by lia.
  assert (Hls : List.length src_pnames = List.length vs) by lia.
  assert (Hpe0 : forall idx r, nth_error (args G) idx = Some r -> ~ In r (defined_ids_of_cfg G) ->
    exists dv, nth_error vs idx = Some dv /\ RM.find r (init_cfg_locals (args G) vs) = Some dv).
  { intros idx r Hnth _; exact (init_cfg_locals_nth (args G) vs idx r Hnd_p Hlp Hnth). }
  destruct (summarize_ocfg_src_sound (default_cfg_dag_fuel G) blk_uas G src_pnames [] arg_dtys vs foracle
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
  intros G src_pnames arg_dtys vs foracle d.
  exact (summarize_src_dag_with_uas_sound (fun _ => []) G src_pnames arg_dtys vs foracle d).
Qed.

Lemma summarize_ocfg_tgt_sound {Pa : Params} :
  forall fuel blk_uas G src_pnames allowed arg_dtys (vs : list (@dvalue Pa))
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
    summarize_ocfg_dag fuel blk_uas true (args G) src_pnames (defined_ids_of_cfg G)
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
    intros blk_uas G src_pnames allowed arg_dtys vs sigma0 fmap0 is_entry bid_from bid_cur smap env seen0 d
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
  cbn zeta in Hr.
  match type of Hr with
  | match ?ot with Some _ => _ | None => _ end = Some _ =>
      destruct ot as [d_term |] eqn:Hopt; [| discriminate Hr]
  end.
  inversion Hr; subst d; clear Hr.
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
    cbn [eval_cfg_dag]; exact (Hev_ub_p (wrap_evals cevals d_term)).
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
      cbn [eval_cfg_dag]; rewrite <- app_assoc.
      rewrite (Hev_kp added_c (wrap_evals cevals d_term) (fun q z H => proj2 (Had_c q z H))).
      exact (Hev_ub_c d_term).
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
      destruct tm; try discriminate Hopt.
      * (* TERM_Ret *)
        destruct v as [dt op].
        destruct dt as [tb | |]; try discriminate Hopt; destruct tb as [w | | | | | | | | | |]; try discriminate Hopt.
        destruct (reify_exp true (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                    (Some (DTYPE_Base (DTYPE_I w))) op)
          as [[[w1 ce_ret] seen_ret] |] eqn:Hr_ret; [| discriminate Hopt].
        inversion Hopt; subst d_term; clear Hopt.
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
           cbn [eval_cfg_dag].
           rewrite (Hstrip_blk added_r (CD_RetScalar w ce_ret) (fun k z H => proj2 (Had_r k z H))).
           cbn [eval_cfg_dag]; rewrite Hev_r; reflexivity.
        -- exists (added_r ++ added_c ++ added_p).
           split; [exact (Hdisj_all added_r (fun k z H => proj2 (Had_r k z H))) | right].
           exists sigma_r, env_c, dv_r; split; [exact Hwfd_r | split].
           ++ cbn [eval_cfg_dag].
              rewrite (Hstrip_blk added_r (CD_RetScalar w ce_ret) (fun k z H => proj2 (Had_r k z H))).
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
        inversion Hopt; subst d_term; clear Hopt.
        exists ([] ++ added_c ++ added_p).
        split; [exact (Hdisj_all [] (fun _ _ H => False_ind _ H)) | right].
        exists sigma_c, env_c, NONE; split; [exact Hwfd_c | split].
        -- cbn [eval_cfg_dag]; rewrite (Hstrip_blk [] CD_RetVoid (fun _ _ H => False_ind _ H)); reflexivity.
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
        destruct dt as [tb | |]; try discriminate Hopt; destruct tb as [wc | | | | | | | | | |]; try discriminate Hopt.
        destruct wc as [| |]; try discriminate Hopt.
        destruct (reify_exp true (args G) src_pnames (defined_ids_of_cfg G) smap_c seen_c
                    (Some (DTYPE_Base (DTYPE_I 1%positive))) op)
          as [[[wc' ce_cond] seen_br] |] eqn:Hr_cond; [| discriminate Hopt].
        pose proof (check_opt_int_width_some_inv _ _ (reify_exp_top_width _ _ _ _ _ _ _ _ _ _ _ Hr_cond)) as ->.
        destruct (reify_exp_wt_lf op true (args G) src_pnames (defined_ids_of_cfg G)
                    ext_c smap_c seen_c (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive ce_cond seen_br
                    Hwfs_c Hr_cond) as [Hwt_cond _].
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
           cbn [eval_cfg_dag]; rewrite (Hstrip_blk added_br d_term (fun k z H => proj2 (Had_br k z H))).
           destruct (try_const_i1 ce_cond) as [[|] |].
           ++ destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br1 _ _); [| discriminate Hopt].
              inversion Hopt; subst d_term; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
           ++ destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br2 _ _); [| discriminate Hopt].
              inversion Hopt; subst d_term; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
           ++ destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br1 _ _); [| discriminate Hopt].
              destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br2 _ _); [| discriminate Hopt].
              inversion Hopt; subst d_term; cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
        -- pose proof (eval_closed_lf_ret_wf_param_env ce_cond (build_param_env src_pnames vs)
                         (oracle_of_fmap (added_br ++ added_c ++ added_p ++ fmap0))
                         dv_br Hlf_cond Hev_br) as Hp_cond.
           destruct Hsc_br as [-> | [cbit ->]].
           ++ exists (added_br ++ added_c ++ added_p).
              split; [exact (Hdisj_all added_br (fun k z H => proj2 (Had_br k z H))) | left].
              destruct (try_const_i1 ce_cond) as [b_tc |] eqn:Etc.
              ** destruct (try_const_i1_sound ce_cond (build_param_env src_pnames vs)
                             (oracle_of_fmap (added_br ++ added_c ++ added_p ++ fmap0))
                             b_tc Hwt_cond Hlf_cond Hp_cond Etc) as [cbit_tc [Hev_tc _]].
                 congruence.
              ** destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br1 _ _); [| discriminate Hopt].
                 destruct (summarize_ocfg_dag fuel' _ _ _ _ _ _ _ _ br2 _ _); [| discriminate Hopt].
                 inversion Hopt; subst d_term.
                 cbn [eval_cfg_dag]; rewrite (Hstrip_blk added_br _ (fun k z H => proj2 (Had_br k z H))).
                 cbn [eval_cfg_dag]; rewrite Hev_br; reflexivity.
           ++ pose proof (env_matches_smap_oracle_prepend ext_c (defined_ids_of_cfg G) seen_c
                            added_br (added_c ++ added_p ++ fmap0)
                            (build_param_env src_pnames vs) smap_c env_c Hwfs_c
                            (fun k z H => proj2 (Had_br k z H)) Henv_c) as Henv_br.
              set (br_tgt := if (@Integers.unsigned 1 cbit =? 1)%Z then br1 else br2).
              assert (Hnext_br :
                exists d_next,
                  summarize_ocfg_dag fuel' blk_uas true (args G) src_pnames (defined_ids_of_cfg G)
                    (ocfg_map (blks G)) false bid_cur br_tgt smap_c seen_br = Some d_next /\
                  (forall fo,
                     eval_closed_cert_expr (build_param_env src_pnames vs) fo ce_cond =
                       raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit)) ->
                     eval_cfg_dag (build_param_env src_pnames vs) fo d_term =
                     eval_cfg_dag (build_param_env src_pnames vs) fo d_next)).
              { destruct (try_const_i1 ce_cond) as [[|] |] eqn:Etc.
                - destruct (try_const_i1_sound ce_cond (build_param_env src_pnames vs)
                              (oracle_of_fmap (added_br ++ added_c ++ added_p ++ fmap0))
                              true Hwt_cond Hlf_cond Hp_cond Etc) as [cbit' [Hev_tc Ecbit']].
                  rewrite Hev_br in Hev_tc; injection Hev_tc as Heq_dv.
                  pose proof (dvalue_I_same_sz_inj 1 cbit cbit' Heq_dv) as <-.
                  unfold br_tgt; rewrite Ecbit'.
                  destruct (summarize_ocfg_dag fuel' blk_uas true (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br1 smap_c seen_br) as [d_t |] eqn:Hr_t;
                    [| discriminate Hopt].
                  inversion Hopt; subst d_term; exists d_t; split; [exact Hr_t |].
                  intros fo Hfo; cbn [eval_cfg_dag]; rewrite Hfo; reflexivity.
                - destruct (try_const_i1_sound ce_cond (build_param_env src_pnames vs)
                              (oracle_of_fmap (added_br ++ added_c ++ added_p ++ fmap0))
                              false Hwt_cond Hlf_cond Hp_cond Etc) as [cbit' [Hev_tc Ecbit']].
                  rewrite Hev_br in Hev_tc; injection Hev_tc as Heq_dv.
                  pose proof (dvalue_I_same_sz_inj 1 cbit cbit' Heq_dv) as <-.
                  unfold br_tgt; rewrite Ecbit'.
                  destruct (summarize_ocfg_dag fuel' blk_uas true (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br2 smap_c seen_br) as [d_f |] eqn:Hr_f;
                    [| discriminate Hopt].
                  inversion Hopt; subst d_term; exists d_f; split; [exact Hr_f |].
                  intros fo Hfo; cbn [eval_cfg_dag]; rewrite Hfo; reflexivity.
                - destruct (summarize_ocfg_dag fuel' blk_uas true (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br1 smap_c seen_br) as [d_t |] eqn:Hr_t;
                    [| discriminate Hopt].
                  destruct (summarize_ocfg_dag fuel' blk_uas true (args G) src_pnames (defined_ids_of_cfg G)
                              (ocfg_map (blks G)) false bid_cur br2 smap_c seen_br) as [d_f |] eqn:Hr_f;
                    [| discriminate Hopt].
                  inversion Hopt; subst d_term.
                  exists (if (@Integers.unsigned 1 cbit =? 1)%Z then d_t else d_f); split.
                  + unfold br_tgt; destruct (@Integers.unsigned 1 cbit =? 1)%Z; [exact Hr_t | exact Hr_f].
                  + intros fo Hfo; cbn [eval_cfg_dag]; rewrite Hfo; reflexivity. }
              destruct Hnext_br as [d_next [Hr_next Hev_term]].
              destruct (IH blk_uas G src_pnames ext_c arg_dtys vs sigma_br
                          (added_br ++ added_c ++ added_p ++ fmap0)
                          false bid_cur br_tgt smap_c env_c seen_br d_next
                          Hnd Hlp Hls Hla Hcomp Hvs Hpe_c Hwfd_br Hwfs_br Henv_br Hr_next)
                as (added_n & Had_n & [Hev_ub_n | (sigma_out & env_out & dv_out & Hwfd_out & Hev_out & Hst_n)]).
              ** assert (Hdisj_nbr : forall k z, In (k, z) (added_n ++ added_br) -> ~ In k seen_c).
                 { intros k z Hkz; apply in_app_iff in Hkz as [Hn | Hb0].
                   - intros Hsc0; exact (Had_n k z Hn (Hinc_cbr k Hsc0)).
                   - exact (proj2 (Had_br k z Hb0)). }
                 exists ((added_n ++ added_br) ++ added_c ++ added_p).
                 split; [exact (Hdisj_all (added_n ++ added_br) Hdisj_nbr) | left].
                 cbn [eval_cfg_dag]; rewrite (Hstrip_blk (added_n ++ added_br) d_term Hdisj_nbr).
                 replace ((added_n ++ added_br) ++ added_c ++ added_p ++ fmap0)
                   with (added_n ++ added_br ++ added_c ++ added_p ++ fmap0)
                   by (rewrite !app_assoc; reflexivity).
                 pose proof (eval_let_free_prepend_fmap ce_cond (build_param_env src_pnames vs)
                               added_n (added_br ++ added_c ++ added_p ++ fmap0) seen_br
                               Hlf_cond (Hfk_cond eq_refl) Had_n) as Hev_br'.
                 rewrite Hev_br in Hev_br'.
                 rewrite (Hev_term _ Hev_br'); exact Hev_ub_n.
              ** assert (Hdisj_nbr : forall k z, In (k, z) (added_n ++ added_br) -> ~ In k seen_c).
                 { intros k z Hkz; apply in_app_iff in Hkz as [Hn | Hb0].
                   - intros Hsc0; exact (Had_n k z Hn (Hinc_cbr k Hsc0)).
                   - exact (proj2 (Had_br k z Hb0)). }
                 exists ((added_n ++ added_br) ++ added_c ++ added_p).
                 split; [exact (Hdisj_all (added_n ++ added_br) Hdisj_nbr) | right].
                 exists sigma_out, env_out, dv_out; split; [exact Hwfd_out | split].
                 --- cbn [eval_cfg_dag]; rewrite (Hstrip_blk (added_n ++ added_br) d_term Hdisj_nbr).
                     replace ((added_n ++ added_br) ++ added_c ++ added_p ++ fmap0)
                       with (added_n ++ added_br ++ added_c ++ added_p ++ fmap0)
                       by (rewrite !app_assoc; reflexivity).
                     pose proof (eval_let_free_prepend_fmap ce_cond (build_param_env src_pnames vs)
                                   added_n (added_br ++ added_c ++ added_p ++ fmap0) seen_br
                                   Hlf_cond (Hfk_cond eq_refl) Had_n) as Hev_br'.
                     rewrite Hev_br in Hev_br'.
                     rewrite (Hev_term _ Hev_br'); exact Hev_out.
                 --- eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
                     unfold denote_block; rewrite Htm.
                     eapply cfg_steps_to_ret_bind.
                     +++ eapply cfg_steps_to_ret_bind.
                         *** eapply cfg_steps_to_ret_bind; [exact Hphis_step |].
                             eapply cfg_steps_to_ret_bind; [exact Hst_c |].
                             cbn [denote_terminator]; unfold denote_exp'.
                             eapply cfg_steps_to_ret_bind;
                               [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ Hst_br) |].
                             rewrite bit_int_1_equ_one_eq_unsigned; unfold br_tgt.
                             destruct (@Integers.unsigned 1 cbit =? 1)%Z; apply CSR_Ret; reflexivity.
                         *** apply CSR_Ret; reflexivity.
                     +++ eapply CSR_Tau; [reflexivity | exact Hst_n].
      * (* TERM_Br_1 *)
        destruct (IH blk_uas G src_pnames ext_c arg_dtys vs sigma_c (added_c ++ added_p ++ fmap0)
                    false bid_cur br smap_c env_c seen_c d_term
                    Hnd Hlp Hls Hla Hcomp Hvs Hpe_c Hwfd_c Hwfs_c Henv_c Hopt)
          as (added_n & Had_n & [Hev_ub_n | (sigma_out & env_out & dv_out & Hwfd_out & Hev_out & Hst_n)]).
        -- exists (added_n ++ added_c ++ added_p).
           split; [exact (Hdisj_all added_n Had_n) | left].
           cbn [eval_cfg_dag]; rewrite (Hstrip_blk added_n d_term Had_n); exact Hev_ub_n.
        -- exists (added_n ++ added_c ++ added_p).
           split; [exact (Hdisj_all added_n Had_n) | right].
           exists sigma_out, env_out, dv_out; split; [exact Hwfd_out | split].
           ++ cbn [eval_cfg_dag]; rewrite (Hstrip_blk added_n d_term Had_n); exact Hev_out.
           ++ eapply cfg_steps_to_ret_obs; [symmetry; exact (denote_ocfg_map_step_obs _ _ _ _ Hfb) |].
              unfold denote_block; rewrite Htm.
              eapply cfg_steps_to_ret_bind.
              ** eapply cfg_steps_to_ret_bind.
                 --- eapply cfg_steps_to_ret_bind; [exact Hphis_step |].
                     eapply cfg_steps_to_ret_bind; [exact Hst_c | apply CSR_Ret; reflexivity].
                 --- apply CSR_Ret; reflexivity.
              ** eapply CSR_Tau; [reflexivity | exact Hst_n].
      * (* TERM_Unreachable *)
        inversion Hopt; subst d_term; clear Hopt.
        exists ([] ++ added_c ++ added_p).
        split; [exact (Hdisj_all [] (fun _ _ H => False_ind _ H)) | left].
        cbn [eval_cfg_dag]; rewrite (Hstrip_blk [] CD_Unreachable (fun _ _ H => False_ind _ H)); reflexivity.
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
  destruct (summarize_ocfg_tgt_sound (default_cfg_dag_fuel G) (fun _ => []) G src_pnames [] arg_dtys vs
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

Fixpoint spine_is_unreachable (d : cfg_dag) {struct d} : bool :=
  match d with
  | CD_Unreachable => true
  | CD_Eval _ _ next => spine_is_unreachable next
  | CD_BlockAssume _ next => spine_is_unreachable next
  | CD_Branch _ on_t on_f => spine_is_unreachable on_t && spine_is_unreachable on_f
  | CD_RetVoid | CD_RetScalar _ _ => false
  end.

Lemma spine_is_unreachable_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle d,
    spine_is_unreachable d = true ->
    eval_cfg_dag penv foracle d = DO_UB.
Proof.
  intros penv foracle d;
    induction d as [| | w ret_e | w step_e next IH | uas next IH | cond on_t IHt on_f IHf];
    intros H; cbn in H |- *; try discriminate; [reflexivity | | |].
  - destruct (eval_closed_cert_expr penv foracle step_e) as [| | | dv];
      [reflexivity | reflexivity | reflexivity | exact (IH H)].
  - exact (IH H).
  - apply andb_true_iff in H as [Ht Hf].
    destruct (eval_closed_cert_expr penv foracle cond) as [| | | dvc]; try reflexivity.
    destruct dvc as [dbc | |]; try reflexivity.
    destruct dbc as [| wc cbit | | | | | |]; try reflexivity.
    destruct wc as [| |]; try reflexivity.
    destruct (@Integers.unsigned 1 cbit =? 1)%Z; [exact (IHt Ht) | exact (IHf Hf)].
Qed.

Fixpoint spine_src_evals (d : cfg_dag) {struct d} : list cert_expr :=
  match d with
  | CD_Unreachable | CD_RetVoid => []
  | CD_RetScalar _ ret_e => [ret_e]
  | CD_Eval _ step_e next => step_e :: spine_src_evals next
  | CD_BlockAssume _ next => spine_src_evals next
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
  intros penv foracle d;
    induction d as [| | w ret_e | w step_e next IH | uas next IH | cond on_t IHt on_f IHf];
    intros v e Hev Hin; cbn [eval_cfg_dag spine_src_evals] in Hev, Hin.
  - discriminate Hev.
  - contradiction.
  - destruct Hin as [<- | []].
    destruct (eval_closed_cert_expr penv foracle ret_e) as [| | | dv]; try discriminate Hev.
    exists dv; reflexivity.
  - destruct (eval_closed_cert_expr penv foracle step_e) as [| | | dv0] eqn:Es; try discriminate Hev.
    destruct Hin as [<- | Hin]; [exists dv0; reflexivity | exact (IH v e Hev Hin)].
  - exact (IH v e Hev Hin).
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
  intros allowed d;
    induction d as [| | w ret_e | w step_e next IH | uas next IH | cond on_t IHt on_f IHf];
    intros e Hwf Hin; cbn [wf_cfg_dag spine_src_evals] in Hwf, Hin; try contradiction.
  - destruct Hin as [<- | []].
    rewrite !andb_true_iff in Hwf; destruct Hwf as (((Hwt & _) & Hlf) & Hfv).
    exact (conj Hwt (conj Hlf (vars_subset_b_incl _ _ Hfv))).
  - rewrite !andb_true_iff in Hwf; destruct Hwf as ((((Hwt & _) & Hlf) & Hfv) & Hwfn).
    destruct Hin as [<- | Hin];
      [exact (conj Hwt (conj Hlf (vars_subset_b_incl _ _ Hfv))) | exact (IH e Hwfn Hin)].
  - exact (IH e Hwf Hin).
  - rewrite !andb_true_iff in Hwf; destruct Hwf as (((((Hwt & _) & Hlf) & Hfv) & Hwft) & Hwff).
    destruct (spine_is_unreachable on_f).
    + destruct Hin as [<- | Hin];
        [exact (conj Hwt (conj Hlf (vars_subset_b_incl _ _ Hfv))) | exact (IHt e Hwft Hin)].
    + destruct (spine_is_unreachable on_t).
      * destruct Hin as [<- | Hin];
          [exact (conj Hwt (conj Hlf (vars_subset_b_incl _ _ Hfv))) | exact (IHf e Hwff Hin)].
      * destruct Hin as [<- | []]; exact (conj Hwt (conj Hlf (vars_subset_b_incl _ _ Hfv))).
Qed.

Fixpoint spine_branch_conds (d : cfg_dag) {struct d} : list cert_expr :=
  match d with
  | CD_Unreachable | CD_RetVoid | CD_RetScalar _ _ => []
  | CD_Eval _ _ next => spine_branch_conds next
  | CD_BlockAssume _ next => spine_branch_conds next
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
  intros penv foracle d;
    induction d as [| | w ret_e | w step_e next IH | uas next IH | cond on_t IHt on_f IHf];
    intros v c Hev Hin; cbn [eval_cfg_dag spine_branch_conds] in Hev, Hin; try contradiction.
  - destruct (eval_closed_cert_expr penv foracle step_e) as [| | | _]; try discriminate Hev.
    exact (IH v c Hev Hin).
  - exact (IH v c Hev Hin).
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
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
    destruct Hwt as ((((_ & Hwtl) & Hwtr) & _) & _); destruct Hlf as [Hlfl Hlfr].
    apply orb_true_iff in Hsub as [Hsl | Hsr].
    + exact (IHl allowed Hsl Hwtl Hlfl (fun u Hu => Hfv u (proj2 (in_app_iff _ _ _) (or_introl Hu)))).
    + exact (IHr allowed Hsr Hwtr Hlfr (fun u Hu => Hfv u (proj2 (in_app_iff _ _ _) (or_intror Hu)))).
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf, Hfv.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
    destruct Hwt as (((Hwtl & Hwtr) & _) & _); destruct Hlf as [Hlfl Hlfr].
    apply orb_true_iff in Hsub as [Hsl | Hsr].
    + exact (IHl allowed Hsl Hwtl Hlfl (fun u Hu => Hfv u (proj2 (in_app_iff _ _ _) (or_introl Hu)))).
    + exact (IHr allowed Hsr Hwtr Hlfr (fun u Hu => Hfv u (proj2 (in_app_iff _ _ _) (or_intror Hu)))).
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf, Hfv.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((_ & Hwto) & _).
    exact (IHo allowed Hsub Hwto Hlf Hfv).
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf, Hfv.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
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

Fixpoint ctx_has_sdiv_no_ovf (ctx : ub_ctx) (el er : cert_expr) {struct ctx} : bool :=
  match ctx with
  | [] => false
  | UBA_SignedDivNoOverflow l r :: rest =>
      (match_expanded_bounded l el && match_expanded_bounded r er) ||
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
  apply match_expanded_bounded_eq in Hl; apply match_expanded_bounded_eq in Hr; subst el er.
  exact (Hua w il ir El Er).
Qed.

Fixpoint ctx_has_any_nonpoison (ctx : ub_ctx) (nm : string) {struct ctx} : bool :=
  match ctx with
  | [] => false
  | UBA_ParamNoUndef p _ :: rest
  | UBA_LoadNoUndef p _ :: rest
  | UBA_PtrNonNull p :: rest
  | UBA_PtrDereferenceable p _ :: rest
  | UBA_PtrAligned p _ :: rest =>
      String.eqb p nm || ctx_has_any_nonpoison rest nm
  | _ :: rest => ctx_has_any_nonpoison rest nm
  end.

Lemma ctx_has_any_nonpoison_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle ctx nm dv,
    ctx_has_any_nonpoison ctx nm = true ->
    ub_ctx_holds penv foracle ctx ->
    penv nm = Some dv ->
    dv <> DVALUE_Base DVALUE_Poison.
Proof.
  intros penv foracle ctx nm dv H Hctx Hpm.
  induction Hctx as [| ua rest Hua Hrest IH]; [discriminate H |].
  destruct ua; cbn in H; try exact (IH H);
    apply orb_true_iff in H as [Hhere | Hlater]; try exact (IH Hlater);
    apply String.eqb_eq in Hhere; subst.
  - exact (Hua dv Hpm).
  - exact (Hua dv Hpm).
  - exact (proj1 (Hua dv Hpm)).
  - exact (Hua dv Hpm).
  - exact (Hua dv Hpm).
Qed.

Fixpoint ctx_has_ptr_aligned_exact
  (ctx : ub_ctx) (nm : string) (align : N) {struct ctx} : bool :=
  match ctx with
  | [] => false
  | UBA_PtrAligned p align0 :: rest =>
      (String.eqb p nm && N.eqb align0 align) ||
      ctx_has_ptr_aligned_exact rest nm align
  | _ :: rest => ctx_has_ptr_aligned_exact rest nm align
  end.

Lemma ctx_has_ptr_aligned_exact_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle ctx nm align,
    ctx_has_ptr_aligned_exact ctx nm align = true ->
    ub_ctx_holds penv foracle ctx ->
    ub_assumption_holds penv foracle (UBA_PtrAligned nm align).
Proof.
  intros penv foracle ctx nm align H Hctx.
  induction Hctx as [| ua rest Hua Hrest IH]; [discriminate H |].
  destruct ua as [| | p align0 | | | | | |]; cbn in H; try exact (IH H).
  apply orb_true_iff in H as [Hhere | Hlater]; [| exact (IH Hlater)].
  apply andb_true_iff in Hhere as [Hp Ha].
  apply String.eqb_eq in Hp; apply N.eqb_eq in Ha; subst p align0.
  exact Hua.
Qed.

Definition param_nonpoison_by_use
  (allowed : list (string * positive))
  (ctx : ub_ctx)
  (all_evals all_brs : list cert_expr)
  (nm : string) : bool :=
  negb (starts_with_dollar nm) &&
  existsb (fun '(p, w) =>
    String.eqb p nm &&
    (ctx_has_branch_cond_defined ctx (CE_Var nm w) ||
     existsb (cert_expr_eqb (CE_Var nm w)) all_brs ||
     existsb (expr_has_div_with_rhs (CE_Var nm w)) all_evals)) allowed.

Lemma param_nonpoison_by_use_sound {Pa : Params} :
  forall allowed ctx all_evals all_brs nm (penv : param_env Pa) foracle dv,
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv foracle ctx ->
    (forall big, In big all_evals ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed) ->
    (forall big, In big all_evals ->
      exists dv0, eval_closed_cert_expr penv foracle big = raise_ret dv0) ->
    (forall c, In c all_brs ->
      exists cbit : @Integers.bit_int 1,
        eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))) ->
    param_nonpoison_by_use allowed ctx all_evals all_brs nm = true ->
    penv nm = Some dv ->
    dv <> DVALUE_Base DVALUE_Poison.
Proof.
  intros allowed ctx all_evals all_brs nm penv foracle dv
         Hpenv Hctx Hwf_ev Hret_ev Hret_br Huse Hpm ->.
  unfold param_nonpoison_by_use in Huse; apply andb_true_iff in Huse as [_ Hex].
  apply existsb_exists in Hex as [[p w] [Hin Hpjust]].
  apply andb_true_iff in Hpjust as [Hp Hjust]; apply String.eqb_eq in Hp; subst p.
  destruct (Hpenv nm w Hin) as [dv0 [Hpm0 Hwfv]]; rewrite Hpm in Hpm0; injection Hpm0 as <-.
  assert (Hev_var : eval_closed_cert_expr penv foracle (CE_Var nm w) =
                    raise_ret (DVALUE_Base DVALUE_Poison)).
  { unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val].
    rewrite Hpm; exact (check_scalar_width_ok w (DVALUE_Base DVALUE_Poison) Hwfv). }
  rewrite !orb_true_iff in Hjust; destruct Hjust as [[Hbrc | Hex_br] | Hex_div].
  - exact (ctx_has_branch_cond_defined_sound penv foracle ctx _ _ Hbrc Hctx Hev_var eq_refl).
  - apply existsb_exists in Hex_br as [c [Hcin Hceq]]; apply cert_expr_eqb_eq in Hceq; subst c.
    destruct (Hret_br _ Hcin) as [cbit Ec]; congruence.
  - apply existsb_exists in Hex_div as [big [Hbin Hdiv]].
    destruct (expr_has_div_with_rhs_spec _ big Hdiv) as (op & w0 & fl & lhs & Hop & Hsub).
    destruct (Hwf_ev big Hbin) as (Hwtb & Hlfb & Hfvb).
    destruct (is_syntactic_subexpr_wt_fv _ big allowed Hsub Hwtb Hlfb Hfvb) as (Hwts & _ & _).
    destruct (Hret_ev big Hbin) as [vbig Hvbig].
    destruct (is_syntactic_subexpr_eval_ret _ big penv [] foracle vbig Hsub Hvbig) as [vsub Hvsub].
    exact (div_subexpr_rhs_not_poison penv foracle op w0 fl lhs (CE_Var nm w) vsub
             Hop Hwts Hvsub Hev_var).
Qed.

Definition check_ub_assumption_justified
  (allowed : list (string * positive))
  (prior_evals prior_brs : list cert_expr)
  (d_src : cfg_dag)
  (ctx : ub_ctx)
  (ua : ub_assumption) : bool :=
  let all_evals := prior_evals ++ spine_src_evals d_src in
  let all_brs := prior_brs ++ spine_branch_conds d_src in
  match ua with
  | UBA_UnreachableEliminated =>
      spine_is_unreachable d_src || ctx_has_unreachable ctx
  | UBA_ParamNoUndef param w =>
      negb (starts_with_dollar param) &&
      var_pair_in (param, w) allowed &&
      (spine_is_unreachable d_src ||
       ctx_has_unreachable ctx ||
       ctx_has_any_nonpoison ctx param ||
       param_nonpoison_by_use allowed ctx all_evals all_brs param)
  | UBA_PtrNonNull param
  | UBA_PtrDereferenceable param _ =>
      negb (starts_with_dollar param) &&
      (spine_is_unreachable d_src ||
       ctx_has_unreachable ctx ||
       ctx_has_any_nonpoison ctx param ||
       param_nonpoison_by_use allowed ctx all_evals all_brs param)
  | UBA_LoadNoUndef slot _ =>
      negb (starts_with_dollar slot) &&
      (spine_is_unreachable d_src ||
       ctx_has_unreachable ctx ||
       ctx_has_any_nonpoison ctx slot ||
       param_nonpoison_by_use allowed ctx all_evals all_brs slot)
  | UBA_PtrAligned param align =>
      negb (starts_with_dollar param) &&
      (spine_is_unreachable d_src ||
       ctx_has_unreachable ctx ||
       ctx_has_ptr_aligned_exact ctx param align ||
       ((align <=? 1)%N &&
        (ctx_has_any_nonpoison ctx param ||
         param_nonpoison_by_use allowed ctx all_evals all_brs param)))
  | UBA_BranchCondDefined cond_e =>
      wt_cert_expr [] cond_e &&
      check_wf_let_dag_fast default_let_expand_budget cond_e &&
      vars_subset_b (collect_free_vars [] cond_e) allowed &&
      match expand_lets_fueled default_let_expand_budget cond_e with
      | None => false
      | Some ec =>
          spine_is_unreachable d_src ||
          ctx_has_unreachable ctx ||
          ctx_has_branch_cond_defined ctx ec ||
          expr_guaranteed_defined ctx ec ||
          existsb (cert_expr_eqb ec) all_brs ||
          existsb (expr_has_div_with_rhs ec) all_evals
      end
  | UBA_DivisorNonZero div_e =>
      wt_cert_expr [] div_e &&
      check_wf_let_dag_fast default_let_expand_budget div_e &&
      vars_subset_b (collect_free_vars [] div_e) allowed &&
      match expand_lets_fueled default_let_expand_budget div_e with
      | None => false
      | Some ed =>
          spine_is_unreachable d_src ||
          ctx_has_unreachable ctx ||
          ctx_has_divisor_nonzero ctx ed ||
          is_nonzero_bv_const ed ||
          existsb (expr_has_defined_div_rhs ctx ed) all_evals
      end
  | UBA_SignedDivNoOverflow lhs_e rhs_e =>
      wt_cert_expr [] lhs_e &&
      wt_cert_expr [] rhs_e &&
      Pos.eqb (cert_expr_bit_width lhs_e) (cert_expr_bit_width rhs_e) &&
      check_wf_let_dag_fast default_let_expand_budget lhs_e &&
      check_wf_let_dag_fast default_let_expand_budget rhs_e &&
      vars_subset_b (collect_free_vars [] lhs_e) allowed &&
      vars_subset_b (collect_free_vars [] rhs_e) allowed &&
      match expand_lets_fueled default_let_expand_budget lhs_e,
            expand_lets_fueled default_let_expand_budget rhs_e with
      | Some el, Some er =>
          spine_is_unreachable d_src ||
          ctx_has_unreachable ctx ||
          ctx_has_sdiv_no_ovf ctx el er ||
          is_safe_sdiv_bv_const er ||
          existsb (expr_has_sdiv_pair el er) all_evals
      | _, _ => false
      end
  end.

Lemma check_ub_assumption_justified_sound {Pa : Params} :
  forall allowed prior_evals prior_brs d_src ctx ua (penv : param_env Pa) foracle v_src,
    wf_cfg_dag allowed d_src = true ->
    wf_param_env_for allowed penv ->
    (forall big, In big prior_evals ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed) ->
    (forall big, In big prior_evals ->
      exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv) ->
    (forall c, In c prior_brs ->
      exists cbit : @Integers.bit_int 1,
        eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))) ->
    eval_cfg_dag penv foracle d_src = DO_Ret v_src ->
    ub_ctx_holds penv foracle ctx ->
    check_ub_assumption_justified allowed prior_evals prior_brs d_src ctx ua = true ->
    ub_assumption_holds penv foracle ua.
Proof.
  intros allowed prior_evals prior_brs d_src ctx ua penv foracle v_src
         Hwfd Hpenv Hpwf Hpret Hpbr Hevd Hctx Hchk.
  set (all_evals := prior_evals ++ spine_src_evals d_src) in *.
  set (all_brs := prior_brs ++ spine_branch_conds d_src) in *.
  assert (Hall_wf : forall big, In big all_evals ->
    wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed).
  { intros big Hin; apply in_app_iff in Hin as [Hp | Hs];
      [exact (Hpwf big Hp) | exact (spine_src_evals_wf allowed d_src big Hwfd Hs)]. }
  assert (Hall_ret : forall big, In big all_evals ->
    exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv).
  { intros big Hin; apply in_app_iff in Hin as [Hp | Hs];
      [exact (Hpret big Hp) | exact (spine_src_evals_ret penv foracle d_src v_src big Hevd Hs)]. }
  assert (Hall_br : forall c, In c all_brs ->
    exists cbit : @Integers.bit_int 1,
      eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))).
  { intros c Hin; apply in_app_iff in Hin as [Hp | Hs];
      [exact (Hpbr c Hp) | exact (spine_branch_conds_ret penv foracle d_src v_src c Hevd Hs)]. }
  destruct ua as
    [ param w | param | param align | param bytes | slot w
    | div_e | lhs_e rhs_e | cond_e | ];
    cbn [check_ub_assumption_justified ub_assumption_holds] in Hchk |- *;
    fold all_evals all_brs in Hchk.
  - (* UBA_ParamNoUndef *)
    rewrite !andb_true_iff in Hchk; destruct Hchk as ([_ _] & Hjust).
    intros dv Hpm; rewrite !orb_true_iff in Hjust.
    destruct Hjust as [[[Hunr | Hcu] | Hnp] | Huse].
    + rewrite (spine_is_unreachable_sound penv foracle d_src Hunr) in Hevd; discriminate Hevd.
    + exfalso; exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + exact (ctx_has_any_nonpoison_sound penv foracle ctx param dv Hnp Hctx Hpm).
    + exact (param_nonpoison_by_use_sound allowed ctx all_evals all_brs param penv foracle dv
               Hpenv Hctx Hall_wf Hall_ret Hall_br Huse Hpm).
  - (* UBA_PtrNonNull *)
    apply andb_true_iff in Hchk as [_ Hjust].
    intros dv Hpm; rewrite !orb_true_iff in Hjust.
    destruct Hjust as [[[Hunr | Hcu] | Hnp] | Huse].
    + rewrite (spine_is_unreachable_sound penv foracle d_src Hunr) in Hevd; discriminate Hevd.
    + exfalso; exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + exact (ctx_has_any_nonpoison_sound penv foracle ctx param dv Hnp Hctx Hpm).
    + exact (param_nonpoison_by_use_sound allowed ctx all_evals all_brs param penv foracle dv
               Hpenv Hctx Hall_wf Hall_ret Hall_br Huse Hpm).
  - (* UBA_PtrAligned *)
    apply andb_true_iff in Hchk as [_ Hjust].
    rewrite !orb_true_iff in Hjust.
    destruct Hjust as [[[Hunr | Hcu] | Hexact] | Hle1].
    + rewrite (spine_is_unreachable_sound penv foracle d_src Hunr) in Hevd; discriminate Hevd.
    + exfalso; exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + exact (ctx_has_ptr_aligned_exact_sound penv foracle ctx param align Hexact Hctx).
    + apply andb_true_iff in Hle1 as [Hal1 Hnp_or].
      intros dv Hpm; split.
      * apply orb_true_iff in Hnp_or as [Hnp | Huse].
        -- exact (ctx_has_any_nonpoison_sound penv foracle ctx param dv Hnp Hctx Hpm).
        -- exact (param_nonpoison_by_use_sound allowed ctx all_evals all_brs param penv foracle dv
                    Hpenv Hctx Hall_wf Hall_ret Hall_br Huse Hpm).
      * intros w iv _ _.
        destruct align as [| p_al]; [left; reflexivity |].
        destruct p_al as [? | ? |]; try discriminate Hal1.
        right; apply Z.mod_1_r.
  - (* UBA_PtrDereferenceable *)
    apply andb_true_iff in Hchk as [_ Hjust].
    intros dv Hpm; rewrite !orb_true_iff in Hjust.
    destruct Hjust as [[[Hunr | Hcu] | Hnp] | Huse].
    + rewrite (spine_is_unreachable_sound penv foracle d_src Hunr) in Hevd; discriminate Hevd.
    + exfalso; exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + exact (ctx_has_any_nonpoison_sound penv foracle ctx param dv Hnp Hctx Hpm).
    + exact (param_nonpoison_by_use_sound allowed ctx all_evals all_brs param penv foracle dv
               Hpenv Hctx Hall_wf Hall_ret Hall_br Huse Hpm).
  - (* UBA_LoadNoUndef *)
    apply andb_true_iff in Hchk as [_ Hjust].
    intros dv Hpm; rewrite !orb_true_iff in Hjust.
    destruct Hjust as [[[Hunr | Hcu] | Hnp] | Huse].
    + rewrite (spine_is_unreachable_sound penv foracle d_src Hunr) in Hevd; discriminate Hevd.
    + exfalso; exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + exact (ctx_has_any_nonpoison_sound penv foracle ctx slot dv Hnp Hctx Hpm).
    + exact (param_nonpoison_by_use_sound allowed ctx all_evals all_brs slot penv foracle dv
               Hpenv Hctx Hall_wf Hall_ret Hall_br Huse Hpm).
  - (* UBA_DivisorNonZero *)
    rewrite !andb_true_iff in Hchk.
    destruct Hchk as (((Hwt & _) & Hsub_fv) & Hjust).
    destruct (expand_lets_fueled default_let_expand_budget div_e) as [ed |] eqn:Eed;
      [| discriminate Hjust].
    pose proof (expand_lets_fueled_eq default_let_expand_budget div_e ed Eed) as Hed_eq.
    subst ed; set (ed := expand_lets div_e) in *.
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
      destruct (Hall_wf big Hbin) as (Hwtb & Hlfb & Hfvb).
      destruct (is_syntactic_subexpr_wt_fv _ big allowed Hsub Hwtb Hlfb Hfvb)
        as (Hwts & _ & Hfvs).
      assert (Hps : wf_param_env_for (collect_free_vars [] (CE_BinOp op w0 fl lhs ed)) penv)
        by (intros x wx Hx; exact (Hpenv x wx (Hfvs (x, wx) Hx))).
      destruct (Hall_ret big Hbin) as [vbig Hvbig].
      destruct (is_syntactic_subexpr_eval_ret _ big penv [] foracle vbig Hsub Hvbig) as [vsub Hvsub].
      destruct (defined_div_subexpr_rhs_nonzero penv foracle ctx op w0 fl lhs ed vsub
                  Hop Hdefl Hwts Hps Hctx Hvsub) as [ir [Eed_ev Hnz]].
      exists w0, ir; split; [exact Eed_ev | exact Hnz].
  - (* UBA_SignedDivNoOverflow *)
    rewrite !andb_true_iff in Hchk.
    destruct Hchk as (((((((_ & _) & _) & _) & _) & _) & _) & Hjust).
    destruct (expand_lets_fueled default_let_expand_budget lhs_e) as [el |] eqn:Eel;
      [| discriminate Hjust].
    destruct (expand_lets_fueled default_let_expand_budget rhs_e) as [er |] eqn:Eer;
      [| discriminate Hjust].
    pose proof (expand_lets_fueled_eq default_let_expand_budget lhs_e el Eel) as ->.
    pose proof (expand_lets_fueled_eq default_let_expand_budget rhs_e er Eer) as ->.
    set (el := expand_lets lhs_e) in *; set (er := expand_lets rhs_e) in *.
    intros w il ir El Er.
    rewrite !orb_true_iff in Hjust.
    destruct Hjust as [[[[Hunr | Hcu] | Hcsdiv] | Hsafe] | Hex_sdiv].
    + rewrite (spine_is_unreachable_sound penv foracle d_src Hunr) in Hevd; discriminate Hevd.
    + exfalso; exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
    + exact (ctx_has_sdiv_no_ovf_sound penv foracle ctx el er w il ir Hcsdiv Hctx El Er).
    + destruct (is_safe_sdiv_bv_const_sound penv foracle er Hsafe)
        as (w' & ir' & Eer' & _ & _ & Hnm1).
      rewrite Er in Eer'; injection Eer' as Heq_dv.
      pose proof (dvalue_I_width_eq _ _ _ _ Heq_dv) as Hweq; subst w'.
      pose proof (dvalue_I_same_sz_inj _ _ _ Heq_dv) as <-.
      intros [_ Hm1]; exact (Hnm1 Hm1).
    + apply existsb_exists in Hex_sdiv as [big [Hbin Hsdiv]].
      destruct (expr_has_sdiv_pair_spec el er big Hsdiv) as (op & w0 & fl & Hop & Hsub).
      destruct (Hall_wf big Hbin) as (Hwtb & Hlfb & Hfvb).
      destruct (is_syntactic_subexpr_wt_fv _ big allowed Hsub Hwtb Hlfb Hfvb) as (Hwts & _ & _).
      destruct (Hall_ret big Hbin) as [vbig Hvbig].
      destruct (is_syntactic_subexpr_eval_ret _ big penv [] foracle vbig Hsub Hvbig) as [vsub Hvsub].
      exact (sdiv_subexpr_no_ovf penv foracle op w0 fl el er vsub w il ir Hop Hwts Hvsub El Er).
  - (* UBA_BranchCondDefined *)
    rewrite !andb_true_iff in Hchk.
    destruct Hchk as (((Hwt & _) & Hsub_fv) & Hjust).
    destruct (expand_lets_fueled default_let_expand_budget cond_e) as [ec |] eqn:Eec;
      [| discriminate Hjust].
    pose proof (expand_lets_fueled_eq default_let_expand_budget cond_e ec Eec) as ->.
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
      destruct (Hall_br ec Hcin) as [cbit Ec]; congruence.
    + apply existsb_exists in Hex_div as [big [Hbin Hdiv]].
      destruct (expr_has_div_with_rhs_spec ec big Hdiv) as (op & w0 & fl & lhs & Hop & Hsub).
      destruct (Hall_wf big Hbin) as (Hwtb & Hlfb & Hfvb).
      destruct (is_syntactic_subexpr_wt_fv _ big allowed Hsub Hwtb Hlfb Hfvb) as (Hwts & _ & _).
      destruct (Hall_ret big Hbin) as [vbig Hvbig].
      destruct (is_syntactic_subexpr_eval_ret _ big penv [] foracle vbig Hsub Hvbig) as [vsub Hvsub].
      exact (div_subexpr_rhs_not_poison penv foracle op w0 fl lhs ec vsub Hop Hwts Hvsub Hevc).
  - (* UBA_UnreachableEliminated *)
    apply orb_true_iff in Hchk as [Hunr | Hcu].
    + rewrite (spine_is_unreachable_sound penv foracle d_src Hunr) in Hevd; discriminate Hevd.
    + exact (ctx_has_unreachable_sound penv foracle ctx Hcu Hctx).
Qed.

Fixpoint check_ub_assumptions_list
  (allowed : list (string * positive))
  (prior_evals prior_brs : list cert_expr)
  (d_src : cfg_dag)
  (acc_ctx : ub_ctx)
  (uas : list ub_assumption) {struct uas} : option ub_ctx :=
  match uas with
  | [] => Some acc_ctx
  | ua :: rest =>
      if check_ub_assumption_justified allowed prior_evals prior_brs d_src acc_ctx ua
      then check_ub_assumptions_list allowed prior_evals prior_brs d_src (ua :: acc_ctx) rest
      else None
  end.

Lemma check_ub_assumptions_list_sound {Pa : Params} :
  forall uas allowed prior_evals prior_brs d_src acc_ctx final_ctx (penv : param_env Pa) foracle v_src,
    wf_cfg_dag allowed d_src = true ->
    wf_param_env_for allowed penv ->
    (forall big, In big prior_evals ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed) ->
    (forall big, In big prior_evals ->
      exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv) ->
    (forall c, In c prior_brs ->
      exists cbit : @Integers.bit_int 1,
        eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))) ->
    eval_cfg_dag penv foracle d_src = DO_Ret v_src ->
    ub_ctx_holds penv foracle acc_ctx ->
    check_ub_assumptions_list allowed prior_evals prior_brs d_src acc_ctx uas = Some final_ctx ->
    ub_ctx_holds penv foracle final_ctx.
Proof.
  induction uas as [| ua rest IH];
    intros allowed prior_evals prior_brs d_src acc_ctx final_ctx penv foracle v_src
           Hwfd Hpenv Hpwf Hpret Hpbr Hevd Hacc Hchk;
    cbn [check_ub_assumptions_list] in Hchk.
  - inversion Hchk; subst; exact Hacc.
  - destruct (check_ub_assumption_justified allowed prior_evals prior_brs d_src acc_ctx ua) eqn:Hua;
      [| discriminate Hchk].
    pose proof (check_ub_assumption_justified_sound allowed prior_evals prior_brs d_src acc_ctx ua
                  penv foracle v_src Hwfd Hpenv Hpwf Hpret Hpbr Hevd Hacc Hua) as Hua_holds.
    exact (IH allowed prior_evals prior_brs d_src (ua :: acc_ctx) final_ctx penv foracle v_src
              Hwfd Hpenv Hpwf Hpret Hpbr Hevd (Forall_cons ua Hua_holds Hacc) Hchk).
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
                     unfold cert_to_ibinop, eval_int_op in Hev; cbn - [andb Z.eqb] in Hev.
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
                     unfold cert_to_ibinop, eval_int_op in Hev; cbn - [andb Z.eqb] in Hev.
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

Fixpoint src_dag_to_expr (w : positive) (d : cfg_dag) {struct d} : option cert_expr :=
  match d with
  | CD_Unreachable | CD_RetVoid => None
  | CD_RetScalar w' ret_e =>
      if Pos.eqb w' w then Some ret_e else None
  | CD_Eval _ _ next => src_dag_to_expr w next
  | CD_BlockAssume uas next =>
      match uas with
      | [] => src_dag_to_expr w next
      | _ :: _ => None
      end
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
  intros allowed w d;
  induction d as [| | w' ret_e | ws step_e next IH | uas next IH | cond on_t IHt on_f IHf];
    intros e Hwf Hr; cbn [wf_cfg_dag src_dag_to_expr] in Hwf, Hr; try discriminate Hr.
  - destruct (Pos.eqb w' w) eqn:Ebw; [| discriminate Hr]; apply Pos.eqb_eq in Ebw; subst w'.
    inversion Hr; subst e.
    rewrite !andb_true_iff in Hwf; destruct Hwf as (((Hwt & Hbw) & Hlf) & Hfv).
    apply Pos.eqb_eq in Hbw.
    exact (conj Hwt (conj Hbw (conj Hlf (vars_subset_b_incl _ _ Hfv)))).
  - rewrite !andb_true_iff in Hwf; destruct Hwf as (_ & Hwfn); exact (IH e Hwfn Hr).
  - destruct uas as [| _ _]; [exact (IH e Hwf Hr) | discriminate Hr].
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
  intros allowed w d;
  induction d as [| | w' ret_e | ws step_e next IH | uas next IH | cond on_t IHt on_f IHf];
    intros e penv foracle dv_src Hwf Hpenv Hr Hevd;
    cbn [wf_cfg_dag src_dag_to_expr eval_cfg_dag] in Hwf, Hr, Hevd; try discriminate Hr; try discriminate Hevd.
  - destruct (Pos.eqb w' w); [| discriminate Hr]; inversion Hr; subst e.
    destruct (eval_closed_cert_expr penv foracle ret_e) as [| | | dv]; try discriminate Hevd.
    inversion Hevd; subst dv; reflexivity.
  - rewrite !andb_true_iff in Hwf; destruct Hwf as (_ & Hwfn).
    destruct (eval_closed_cert_expr penv foracle step_e) as [| | | _]; try discriminate Hevd.
    exact (IH e penv foracle dv_src Hwfn Hpenv Hr Hevd).
  - destruct uas as [| _ _]; [exact (IH e penv foracle dv_src Hwf Hpenv Hr Hevd) | discriminate Hr].
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
  (d : cfg_dag) {struct d} : option cert_expr :=
  match d with
  | CD_Unreachable | CD_RetVoid => None
  | CD_RetScalar w' ret_e =>
      if Pos.eqb w' w && expr_safe_under_src ctx src_evals ret_e
      then Some ret_e else None
  | CD_Eval _ step_e next =>
      if expr_safe_under_src ctx src_evals step_e
      then tgt_dag_to_expr ctx src_evals src_br_conds w next
      else None
  | CD_BlockAssume uas next =>
      match uas with
      | [] => tgt_dag_to_expr ctx src_evals src_br_conds w next
      | _ :: _ => None
      end
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
  induction d as [| | w' ret_e | ws step_e next IH | uas next IH | cond on_t IHt on_f IHf];
    intros e Hwf Hr; cbn [wf_cfg_dag tgt_dag_to_expr] in Hwf, Hr; try discriminate Hr.
  - destruct (Pos.eqb w' w && expr_safe_under_src ctx src_evals ret_e) eqn:Eok; [| discriminate Hr].
    apply andb_true_iff in Eok as [Ebw _]; apply Pos.eqb_eq in Ebw; subst w'.
    inversion Hr; subst e.
    rewrite !andb_true_iff in Hwf; destruct Hwf as (((Hwt & Hbw) & Hlf) & Hfv).
    apply Pos.eqb_eq in Hbw.
    exact (conj Hwt (conj Hbw (conj Hlf (vars_subset_b_incl _ _ Hfv)))).
  - destruct (expr_safe_under_src ctx src_evals step_e); [| discriminate Hr].
    rewrite !andb_true_iff in Hwf; destruct Hwf as (_ & Hwfn); exact (IH e Hwfn Hr).
  - destruct uas as [| _ _]; [exact (IH e Hwf Hr) | discriminate Hr].
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
  induction d as [| | w' ret_e | ws step_e next IH | uas next IH | cond on_t IHt on_f IHf];
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
  - destruct uas as [| _ _]; [exact (IH e penv foracle Hwf Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hr) | discriminate Hr].
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
  (d : cfg_dag) {struct d} : bool :=
  match d with
  | CD_RetVoid => true
  | CD_Unreachable | CD_RetScalar _ _ => false
  | CD_Eval _ step_e next =>
      expr_safe_under_src ctx src_evals step_e &&
      tgt_dag_void_safe ctx src_evals src_br_conds next
  | CD_BlockAssume uas next =>
      match uas with
      | [] => tgt_dag_void_safe ctx src_evals src_br_conds next
      | _ :: _ => false
      end
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
  induction d as [| | w' ret_e | ws step_e next IH | uas next IH | cond on_t IHt on_f IHf];
    intros penv foracle Hwf Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hvs;
    cbn [wf_cfg_dag tgt_dag_void_safe eval_cfg_dag] in Hwf, Hvs |- *; try discriminate Hvs; [reflexivity | | |].
  - apply andb_true_iff in Hvs as [Hsafe Hvsn].
    rewrite !andb_true_iff in Hwf; destruct Hwf as ((((Hwt & _) & _) & Hfv) & Hwfn).
    pose proof (vars_subset_b_wf_param _ allowed penv Hfv Hpenv) as Hps.
    destruct (expr_safe_under_src_sound step_e ctx src_evals penv foracle Hsafe Hwt Hps Hctx Hsrc_ret)
      as [dvs [Es _]].
    rewrite Es; exact (IH penv foracle Hwfn Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hvsn).
  - destruct uas as [| _ _]; [exact (IH penv foracle Hwf Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hvs) | discriminate Hvs].
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

Lemma expand_lets_let_free_id :
  forall e, is_let_free_expr e = true -> expand_lets e = e.
Proof.
  unfold expand_lets; induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ];
    intros Hlf; cbn [is_let_free_expr expand_lets_with] in Hlf |- *; try discriminate Hlf;
    try reflexivity.
  - apply andb_true_iff in Hlf as [Hl Hr]; rewrite (IHl Hl), (IHr Hr); reflexivity.
  - apply andb_true_iff in Hlf as [Hl Hr]; rewrite (IHl Hl), (IHr Hr); reflexivity.
  - rewrite (IHo Hlf); reflexivity.
  - rewrite !andb_true_iff in Hlf; destruct Hlf as ([Hc Ht] & Hf).
    rewrite (IHc Hc), (IHt Ht), (IHf Hf); reflexivity.
  - rewrite (IHo Hlf); reflexivity.
Qed.

Lemma bit1_unsigned_zero : @Integers.unsigned 1 (@Integers.zero 1) = 0%Z.
Proof.
  exact (@Integers.unsigned_zero 1).
Qed.

Lemma bit1_unsigned_one : @Integers.unsigned 1 (@Integers.one 1) = 1%Z.
Proof.
  exact (@Integers.unsigned_one 1).
Qed.

Definition is_zero_bv_const (e : cert_expr) : bool :=
  match e with
  | CE_BvConst w z => Z.eqb (@Integers.unsigned w (@Integers.repr w (Z.of_N z))) 0%Z
  | _ => false
  end.

Lemma is_zero_bv_const_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle e,
    is_zero_bv_const e = true ->
    exists w iz,
      eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa w iz)) /\
      @Integers.unsigned w iz = 0%Z.
Proof.
  intros penv foracle [w z | | | | | | | |] H; cbn in H; try discriminate H.
  apply Z.eqb_eq in H; exists w, (@Integers.repr w (Z.of_N z)).
  split; [reflexivity | exact H].
Qed.

Definition extract_branch_cond_assumptions (on_true : bool) (cs : cert_expr) : list ub_assumption :=
  let base := [UBA_BranchCondDefined cs] in
  match cs with
  | CE_ICmp pr _ _ l r =>
      if on_true then
        match pr with
        | CIP_Ne =>
            if is_zero_bv_const r then UBA_DivisorNonZero l :: base
            else if is_zero_bv_const l then UBA_DivisorNonZero r :: base
            else base
        | CIP_Ugt =>
            if is_zero_bv_const r then UBA_DivisorNonZero l :: base else base
        | CIP_Ult =>
            if is_zero_bv_const l then UBA_DivisorNonZero r :: base else base
        | _ => base
        end
      else
        match pr with
        | CIP_Eq =>
            if is_zero_bv_const r then UBA_DivisorNonZero l :: base
            else if is_zero_bv_const l then UBA_DivisorNonZero r :: base
            else base
        | _ => base
        end
  | _ => base
  end.

Lemma icmp_eval_cbit_operands {Pa : Params} :
  forall (penv : param_env Pa) foracle pr ss w l r (cbit : @Integers.bit_int 1),
    wt_cert_expr [] (CE_ICmp pr ss w l r) = true ->
    eval_closed_cert_expr penv foracle (CE_ICmp pr ss w l r) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit)) ->
    exists il ir : @Integers.bit_int w,
      eval_closed_cert_expr penv foracle l = raise_ret (DVALUE_Base (@DVALUE_I Pa w il)) /\
      eval_closed_cert_expr penv foracle r = raise_ret (DVALUE_Base (@DVALUE_I Pa w ir)) /\
      @eval_int_icmp (@Integers.bit_int w) _ ss (cert_to_icmp pr) il ir =
        raise_ret (@DVALUE_I Pa 1 cbit).
Proof.
  intros penv foracle pr ss w l r cbit Hwt Hev.
  cbn [wt_cert_expr] in Hwt; rewrite !andb_true_iff in Hwt.
  destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr).
  apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
  unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev.
  destruct (eval_cert_expr penv [] foracle l) as [| | | vl] eqn:El; try discriminate Hev.
  cbn [eou_bind] in Hev.
  destruct (eval_cert_expr penv [] foracle r) as [| | | vr] eqn:Er; try discriminate Hev.
  cbn [eou_bind] in Hev.
  pose proof (eval_cert_expr_ret_wf_scalar l _ _ _ _ _ Hwtl El) as Hwfl; rewrite Hwl in Hwfl.
  pose proof (eval_cert_expr_ret_wf_scalar r _ _ _ _ _ Hwtr Er) as Hwfr; rewrite Hwr in Hwfr.
  destruct Hwfl as [-> | [il ->]]; [cbn in Hev; discriminate Hev |].
  destruct Hwfr as [-> | [ir ->]]; [cbn in Hev; discriminate Hev |].
  unfold eval_icmp in Hev; rewrite eval_icmp_base_same_width in Hev.
  destruct (@eval_int_icmp (@Integers.bit_int w) _ ss (cert_to_icmp pr) il ir)
    as [| | | db_out] eqn:Eint; cbn in Hev; try discriminate Hev.
  inversion Hev; subst db_out.
  exists il, ir; repeat split; assumption.
Qed.

Lemma extract_branch_cond_assumptions_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle on_true cs (cbit : @Integers.bit_int 1) ctx,
    wt_cert_expr [] cs = true ->
    is_let_free_expr cs = true ->
    eval_closed_cert_expr penv foracle cs = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit)) ->
    ((@Integers.unsigned 1 cbit =? 1)%Z = on_true) ->
    ub_ctx_holds penv foracle ctx ->
    ub_ctx_holds penv foracle (extract_branch_cond_assumptions on_true cs ++ ctx).
Proof.
  intros penv foracle on_true cs cbit ctx Hwt Hlf Ecs Hon Hctx.
  assert (Hbase : ub_ctx_holds penv foracle (UBA_BranchCondDefined cs :: ctx)).
  { constructor; [| exact Hctx].
    cbn [ub_assumption_holds]; rewrite (expand_lets_let_free_id cs Hlf), Ecs.
    intros v Hv ->; discriminate Hv. }
  destruct cs as [| | | | pr ss w l r | | | |];
    cbn [extract_branch_cond_assumptions app]; try exact Hbase.
  cbn [is_let_free_expr] in Hlf; apply andb_true_iff in Hlf as [Hlfl Hlfr].
  destruct (icmp_eval_cbit_operands penv foracle pr ss w l r cbit Hwt Ecs)
    as (il & ir & El & Er & Eint).
  destruct on_true.
  - destruct pr; try exact Hbase.
    + (* CIP_Ne on true *)
      unfold cert_to_icmp, eval_int_icmp in Eint; cbn in Eint.
      destruct (ss && negb (msamesign il ir)); [discriminate Eint |].
      destruct (negb (@Integers.eq w il ir)) eqn:Ene;
        [| inversion Eint; subst cbit; rewrite bit1_unsigned_zero in Hon; discriminate Hon].
      apply negb_true_iff in Ene; unfold Integers.eq in Ene.
      destruct (Numeric.Rocqlib.zeq (@Integers.unsigned w il) (@Integers.unsigned w ir)) as [Heq | Hneq];
        [discriminate Ene |].
      destruct (is_zero_bv_const r) eqn:Ezr.
      * constructor; [| exact Hbase].
        cbn [ub_assumption_holds]; rewrite (expand_lets_let_free_id l Hlfl).
        destruct (is_zero_bv_const_sound penv foracle r Ezr) as (wr & iz & Er' & Huz).
        rewrite Er in Er'; injection Er' as Heq_dv.
        pose proof (dvalue_I_width_eq _ _ _ _ Heq_dv) as ->.
        pose proof (dvalue_I_same_sz_inj _ _ _ Heq_dv) as <-.
        exists w, il; split; [exact El | lia].
      * destruct (is_zero_bv_const l) eqn:Ezl; [| exact Hbase].
        constructor; [| exact Hbase].
        cbn [ub_assumption_holds]; rewrite (expand_lets_let_free_id r Hlfr).
        destruct (is_zero_bv_const_sound penv foracle l Ezl) as (wl & iz & El' & Huz).
        rewrite El in El'; injection El' as Heq_dv.
        pose proof (dvalue_I_width_eq _ _ _ _ Heq_dv) as ->.
        pose proof (dvalue_I_same_sz_inj _ _ _ Heq_dv) as <-.
        exists w, ir; split; [exact Er | lia].
    + (* CIP_Ult on true *)
      destruct (is_zero_bv_const l) eqn:Ezl; [| exact Hbase].
      unfold cert_to_icmp, eval_int_icmp in Eint; cbn in Eint.
      destruct (ss && negb (msamesign il ir)); [discriminate Eint |].
      destruct (@Integers.ltu w il ir) eqn:Elt;
        [| inversion Eint; subst cbit; rewrite bit1_unsigned_zero in Hon; discriminate Hon].
      unfold Integers.ltu in Elt.
      destruct (Numeric.Rocqlib.zlt (@Integers.unsigned w il) (@Integers.unsigned w ir)) as [Hlt | _];
        [| discriminate Elt].
      constructor; [| exact Hbase].
      cbn [ub_assumption_holds]; rewrite (expand_lets_let_free_id r Hlfr).
      destruct (is_zero_bv_const_sound penv foracle l Ezl) as (wl & iz & El' & Huz).
      rewrite El in El'; injection El' as Heq_dv.
      pose proof (dvalue_I_width_eq _ _ _ _ Heq_dv) as ->.
      pose proof (dvalue_I_same_sz_inj _ _ _ Heq_dv) as <-.
      exists w, ir; split; [exact Er | lia].
    + (* CIP_Ugt on true *)
      destruct (is_zero_bv_const r) eqn:Ezr; [| exact Hbase].
      unfold cert_to_icmp, eval_int_icmp in Eint; cbn in Eint.
      destruct (ss && negb (msamesign il ir)); [discriminate Eint |].
      destruct (@Integers.ltu w ir il) eqn:Egt;
        [| inversion Eint; subst cbit; rewrite bit1_unsigned_zero in Hon; discriminate Hon].
      unfold Integers.ltu in Egt.
      destruct (Numeric.Rocqlib.zlt (@Integers.unsigned w ir) (@Integers.unsigned w il)) as [Hgt | _];
        [| discriminate Egt].
      constructor; [| exact Hbase].
      cbn [ub_assumption_holds]; rewrite (expand_lets_let_free_id l Hlfl).
      destruct (is_zero_bv_const_sound penv foracle r Ezr) as (wr & iz & Er' & Huz).
      rewrite Er in Er'; injection Er' as Heq_dv.
      pose proof (dvalue_I_width_eq _ _ _ _ Heq_dv) as ->.
      pose proof (dvalue_I_same_sz_inj _ _ _ Heq_dv) as <-.
      exists w, il; split; [exact El | lia].
  - destruct pr; try exact Hbase.
    (* CIP_Eq on false *)
    unfold cert_to_icmp, eval_int_icmp in Eint; cbn in Eint.
    destruct (ss && negb (msamesign il ir)); [discriminate Eint |].
    destruct (@Integers.eq w il ir) eqn:Eeq;
      [inversion Eint; subst cbit; rewrite bit1_unsigned_one in Hon; discriminate Hon |].
    unfold Integers.eq in Eeq.
    destruct (Numeric.Rocqlib.zeq (@Integers.unsigned w il) (@Integers.unsigned w ir)) as [Heq | Hneq];
      [discriminate Eeq |].
    destruct (is_zero_bv_const r) eqn:Ezr.
    + constructor; [| exact Hbase].
      cbn [ub_assumption_holds]; rewrite (expand_lets_let_free_id l Hlfl).
      destruct (is_zero_bv_const_sound penv foracle r Ezr) as (wr & iz & Er' & Huz).
      rewrite Er in Er'; injection Er' as Heq_dv.
      pose proof (dvalue_I_width_eq _ _ _ _ Heq_dv) as ->.
      pose proof (dvalue_I_same_sz_inj _ _ _ Heq_dv) as <-.
      exists w, il; split; [exact El | lia].
    + destruct (is_zero_bv_const l) eqn:Ezl; [| exact Hbase].
      constructor; [| exact Hbase].
      cbn [ub_assumption_holds]; rewrite (expand_lets_let_free_id r Hlfr).
      destruct (is_zero_bv_const_sound penv foracle l Ezl) as (wl & iz & El' & Huz).
      rewrite El in El'; injection El' as Heq_dv.
      pose proof (dvalue_I_width_eq _ _ _ _ Heq_dv) as ->.
      pose proof (dvalue_I_same_sz_inj _ _ _ Heq_dv) as <-.
      exists w, ir; split; [exact Er | lia].
Qed.

Fixpoint dag_node_count (d : cfg_dag) {struct d} : nat :=
  match d with
  | CD_Unreachable | CD_RetVoid | CD_RetScalar _ _ => 1%nat
  | CD_Eval _ _ next => S (dag_node_count next)
  | CD_BlockAssume _ next => S (dag_node_count next)
  | CD_Branch _ on_t on_f => S (dag_node_count on_t + dag_node_count on_f)
  end.

Definition as_block_assume (d : cfg_dag) : option (list ub_assumption * cfg_dag) :=
  match d with
  | CD_BlockAssume uas next => Some (uas, next)
  | _ => None
  end.

Lemma as_block_assume_some_inv : forall d uas next,
  as_block_assume d = Some (uas, next) -> d = CD_BlockAssume uas next.
Proof.
  intros [| | ? ? | ? ? ? | ? ? | ? ? ?] uas next H; cbn in H; try discriminate H.
  inversion H; reflexivity.
Qed.

Fixpoint check_dag_refines_cert
  (fuel : nat)
  (allowed : list (string * positive))
  (ctx : ub_ctx)
  (ro : return_obligation)
  (opt_pf : option (list lrat_step))
  (src_evals src_br_conds : list cert_expr)
  (d_src d_tgt : cfg_dag) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if spine_is_unreachable d_src || ctx_has_unreachable ctx then true
      else
        match as_block_assume d_src with
        | Some (uas, next_s) =>
            match check_ub_assumptions_list allowed src_evals src_br_conds next_s ctx uas with
            | Some ctx' =>
                check_dag_refines_cert fuel' allowed ctx' ro opt_pf
                  src_evals src_br_conds next_s d_tgt
            | None => false
            end
        | None =>
            match as_block_assume d_tgt with
            | Some (uas_t, next_t) =>
                match uas_t with
                | [] =>
                    check_dag_refines_cert fuel' allowed ctx ro opt_pf
                      src_evals src_br_conds d_src next_t
                | _ :: _ => false
                end
            | None =>
                if check_scalar_dag_via_ro allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt
                then true
                else
                  match d_src with
                  | CD_Unreachable => true
                  | CD_BlockAssume _ _ => false
                  | CD_Eval _ se next_s =>
                      check_dag_refines_cert fuel' allowed ctx ro opt_pf
                        (se :: src_evals) src_br_conds next_s d_tgt
                  | CD_Branch cs ts fs =>
                      let ctx_t := extract_branch_cond_assumptions true cs ++ ctx in
                      let ctx_f := extract_branch_cond_assumptions false cs ++ ctx in
                      if spine_is_unreachable fs then
                        check_dag_refines_cert fuel' allowed ctx_t ro opt_pf
                          (cs :: src_evals) (cs :: src_br_conds) ts d_tgt
                      else if spine_is_unreachable ts then
                        check_dag_refines_cert fuel' allowed ctx_f ro opt_pf
                          (cs :: src_evals) (cs :: src_br_conds) fs d_tgt
                      else
                        match d_tgt with
                        | CD_Eval _ te next_t =>
                            expr_safe_under_src ctx src_evals te &&
                            check_dag_refines_cert fuel' allowed ctx ro opt_pf
                              src_evals src_br_conds d_src next_t
                        | CD_Branch ct tt ft =>
                            check_expr_refines ctx cs ct &&
                            check_dag_refines_cert fuel' allowed ctx_t ro opt_pf
                              (cs :: src_evals) (cs :: src_br_conds) ts tt &&
                            check_dag_refines_cert fuel' allowed ctx_f ro opt_pf
                              (cs :: src_evals) (cs :: src_br_conds) fs ft
                        | CD_RetScalar _ _ | CD_RetVoid =>
                            check_dag_refines_cert fuel' allowed ctx_t ro opt_pf
                              (cs :: src_evals) (cs :: src_br_conds) ts d_tgt &&
                            check_dag_refines_cert fuel' allowed ctx_f ro opt_pf
                              (cs :: src_evals) (cs :: src_br_conds) fs d_tgt
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
  destruct (as_block_assume d_src) as [[uas next_s] |] eqn:Eba_s.
  { pose proof (as_block_assume_some_inv d_src uas next_s Eba_s) as ->.
    cbn [wf_cfg_dag eval_cfg_dag] in Hwfs, Hevs.
    destruct (check_ub_assumptions_list allowed src_evals src_br_conds next_s ctx uas)
      as [ctx' |] eqn:Ectx'; [| discriminate Hchk].
    pose proof (check_ub_assumptions_list_sound uas allowed src_evals src_br_conds next_s ctx ctx'
                  penv foracle dv_src Hwfs Hpenv Hsrc_wf Hsrc_ret Hbr_ret Hevs Hctx Ectx') as Hctx'.
    exact (IH allowed ctx' ro opt_pf src_evals src_br_conds next_s d_tgt
             penv foracle dv_src Hwfs Hwft Hpenv Hctx' Hsrc_wf Hsrc_ret Hbr_ret Hchk Hevs). }
  destruct (as_block_assume d_tgt) as [[uas_t next_t] |] eqn:Eba_t.
  { pose proof (as_block_assume_some_inv d_tgt uas_t next_t Eba_t) as ->.
    destruct uas_t as [| _ _]; [| discriminate Hchk].
    cbn [wf_cfg_dag eval_cfg_dag] in Hwft |- *.
    exact (IH allowed ctx ro opt_pf src_evals src_br_conds d_src next_t
             penv foracle dv_src Hwfs Hwft Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hchk Hevs). }
  destruct (check_scalar_dag_via_ro allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt) eqn:Ero.
  { exact (check_scalar_dag_via_ro_sound allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt
             penv foracle dv_src Hwfs Hwft Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Ero Hevs). }
  destruct d_src as [| | ws es | ws se next_s | uas next_s | cs ts fs].
  - discriminate Hevs.
  - (* CD_RetVoid *)
    destruct ro as [| ? ? ? ?]; [| discriminate Hchk].
    cbn [eval_cfg_dag] in Hevs; inversion Hevs; subst dv_src.
    exists NONE; split;
      [exact (tgt_dag_void_safe_sound allowed ctx src_evals src_br_conds d_tgt penv foracle
                Hwft Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hchk)
      | apply dvalue_refines_refl].
  - (* CD_RetScalar *)
    destruct d_tgt as [| | wt et | wt te next_t | uas_t next_t | ct tt ft]; try discriminate Hchk.
    + destruct ro as [| w _ _ _]; [discriminate Hchk |].
      rewrite !andb_true_iff in Hchk; destruct Hchk as ([_ _] & Href).
      cbn [wf_cfg_dag eval_cfg_dag] in Hwfs, Hwft, Hevs.
      rewrite !andb_true_iff in Hwfs; rewrite !andb_true_iff in Hwft.
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
  - (* CD_BlockAssume impossible since as_block_assume d_src = None *)
    discriminate Eba_s.
  - (* CD_Branch on d_src *)
    cbn zeta in Hchk.
    pose proof Hwfs as Hwfs_all; pose proof Hevs as Hevs_all.
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
    + destruct (@Integers.unsigned 1 cbit =? 1)%Z eqn:Ecbit.
      * pose proof (extract_branch_cond_assumptions_sound penv foracle true cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_t.
        exact (IH allowed (extract_branch_cond_assumptions true cs ++ ctx) ro opt_pf
                 (cs :: src_evals) (cs :: src_br_conds) ts d_tgt
                 penv foracle dv_src Hwfts Hwft Hpenv Hctx_t Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk Hevs).
      * rewrite (spine_is_unreachable_sound penv foracle fs Eufs) in Hevs; discriminate Hevs.
    + destruct (spine_is_unreachable ts) eqn:Euts.
      * destruct (@Integers.unsigned 1 cbit =? 1)%Z eqn:Ecbit.
        -- rewrite (spine_is_unreachable_sound penv foracle ts Euts) in Hevs; discriminate Hevs.
        -- pose proof (extract_branch_cond_assumptions_sound penv foracle false cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_f.
           exact (IH allowed (extract_branch_cond_assumptions false cs ++ ctx) ro opt_pf
                    (cs :: src_evals) (cs :: src_br_conds) fs d_tgt
                    penv foracle dv_src Hwffs Hwft Hpenv Hctx_f Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk Hevs).
      * destruct d_tgt as [| | wt et | wt te next_t | uas_t next_t | ct tt ft]; try discriminate Hchk.
        -- (* d_tgt = CD_RetVoid *)
           apply andb_true_iff in Hchk as [Hchk_t Hchk_f].
           destruct (@Integers.unsigned 1 cbit =? 1)%Z eqn:Ecbit.
           ++ pose proof (extract_branch_cond_assumptions_sound penv foracle true cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_t.
              exact (IH allowed (extract_branch_cond_assumptions true cs ++ ctx) ro opt_pf
                       (cs :: src_evals) (cs :: src_br_conds) ts CD_RetVoid
                       penv foracle dv_src Hwfts Hwft Hpenv Hctx_t Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_t Hevs).
           ++ pose proof (extract_branch_cond_assumptions_sound penv foracle false cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_f.
              exact (IH allowed (extract_branch_cond_assumptions false cs ++ ctx) ro opt_pf
                       (cs :: src_evals) (cs :: src_br_conds) fs CD_RetVoid
                       penv foracle dv_src Hwffs Hwft Hpenv Hctx_f Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_f Hevs).
        -- (* d_tgt = CD_RetScalar wt et *)
           apply andb_true_iff in Hchk as [Hchk_t Hchk_f].
           destruct (@Integers.unsigned 1 cbit =? 1)%Z eqn:Ecbit.
           ++ pose proof (extract_branch_cond_assumptions_sound penv foracle true cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_t.
              exact (IH allowed (extract_branch_cond_assumptions true cs ++ ctx) ro opt_pf
                       (cs :: src_evals) (cs :: src_br_conds) ts (CD_RetScalar wt et)
                       penv foracle dv_src Hwfts Hwft Hpenv Hctx_t Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_t Hevs).
           ++ pose proof (extract_branch_cond_assumptions_sound penv foracle false cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_f.
              exact (IH allowed (extract_branch_cond_assumptions false cs ++ ctx) ro opt_pf
                       (cs :: src_evals) (cs :: src_br_conds) fs (CD_RetScalar wt et)
                       penv foracle dv_src Hwffs Hwft Hpenv Hctx_f Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_f Hevs).
        -- (* d_tgt = CD_Eval wt te next_t *)
           apply andb_true_iff in Hchk as [Hsafe Hchk'].
           cbn [wf_cfg_dag] in Hwft; rewrite !andb_true_iff in Hwft.
           destruct Hwft as ((((Hwte & _) & _) & Hfve) & Hwfnt).
           pose proof (vars_subset_b_wf_param _ allowed penv Hfve Hpenv) as Hpte.
           destruct (expr_safe_under_src_sound te ctx src_evals penv foracle Hsafe Hwte Hpte Hctx Hsrc_ret)
             as [dve [Ete _]].
           cbn [eval_cfg_dag]; rewrite Ete.
           exact (IH allowed ctx ro opt_pf src_evals src_br_conds (CD_Branch cs ts fs) next_t
                    penv foracle dv_src Hwfs_all Hwfnt Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hchk' Hevs_all).
        -- (* d_tgt = CD_Branch ct tt ft *)
           rewrite !andb_true_iff in Hchk; destruct Hchk as ([Hc_ref Hchk_t] & Hchk_f).
           cbn [wf_cfg_dag] in Hwft; rewrite !andb_true_iff in Hwft.
           destruct Hwft as (((((Hwtct & _) & _) & Hfvct) & Hwftt) & Hwfft).
           pose proof (vars_subset_b_wf_param _ allowed penv Hfvcs Hpenv) as Hpcs.
           pose proof (vars_subset_b_wf_param _ allowed penv Hfvct Hpenv) as Hpct.
           pose proof (check_expr_refines_sound ctx cs ct penv foracle Hc_ref Hpcs Hpct Hctx) as Hcref.
           rewrite Ecs in Hcref; cbn [refine_eou_dvalue] in Hcref.
           destruct (eval_closed_cert_expr penv foracle ct) as [| | | dvct] eqn:Ect; try contradiction Hcref.
           destruct Hcref as [Hps | ->]; [discriminate Hps |].
           cbn [eval_cfg_dag]; rewrite Ect.
           destruct (@Integers.unsigned 1 cbit =? 1)%Z eqn:Ecbit.
           ++ pose proof (extract_branch_cond_assumptions_sound penv foracle true cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_t.
              exact (IH allowed (extract_branch_cond_assumptions true cs ++ ctx) ro opt_pf
                       (cs :: src_evals) (cs :: src_br_conds) ts tt
                       penv foracle dv_src Hwfts Hwftt Hpenv Hctx_t Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_t Hevs).
           ++ pose proof (extract_branch_cond_assumptions_sound penv foracle false cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_f.
              exact (IH allowed (extract_branch_cond_assumptions false cs ++ ctx) ro opt_pf
                       (cs :: src_evals) (cs :: src_br_conds) fs ft
                       penv foracle dv_src Hwffs Hwfft Hpenv Hctx_f Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_f Hevs).
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

(** *** 5.6a [F-46]: [DTYPE_Pointer] Operations & 64-Bit Modular [OP_GetElementPtr] Reassociation *)

Definition wf_ptr_dvalue {Pa : Params} (v : @dvalue Pa) : Prop :=
  v = DVALUE_Base DVALUE_Poison \/ exists p : ptr, v = DVALUE_Base (DVALUE_Pointer p).

Lemma eval_select_ptr_refines {Pa : Params} :
  forall (dt : dtyp) (vc1 vc2 vp1 vp2 vq1 vq2 : @dvalue Pa),
    wf_scalar_dvalue 1%positive vc1 ->
    wf_scalar_dvalue 1%positive vc2 ->
    dvalue_refines vc1 vc2 ->
    dvalue_refines vp1 vp2 ->
    dvalue_refines vq1 vq2 ->
    refine_eou_dvalue (eval_select vc1 dt vp1 vq1) (eval_select vc2 dt vp2 vq2).
Proof.
  intros dt vc1 vc2 vp1 vp2 vq1 vq2 Hsc1 Hsc2 Hrc Hrp Hrq.
  destruct Hsc1 as [-> | [ic1 ->]].
  - destruct Hsc2 as [-> | [ic2 ->]]; cbn.
    + left; reflexivity.
    + destruct (@Integers.unsigned 1%positive ic2 =? 1)%Z; cbn; left; reflexivity.
  - destruct Hrc as [Habs | <-]; [discriminate Habs |].
    cbn; destruct (@Integers.unsigned 1%positive ic1 =? 1)%Z; cbn; assumption.
Qed.

Lemma eval_icmp_ptr_poison_l {Pa : Params} :
  forall samesign cmp (v2 : @dvalue Pa),
    wf_ptr_dvalue v2 ->
    eval_icmp samesign cmp (DVALUE_Base DVALUE_Poison) v2 =
    raise_ret (DVALUE_Base DVALUE_Poison).
Proof.
  intros samesign cmp v2 [-> | [p2 ->]]; reflexivity.
Qed.

Lemma eval_icmp_ptr_poison_r {Pa : Params} :
  forall samesign cmp (v1 : @dvalue Pa),
    wf_ptr_dvalue v1 ->
    eval_icmp samesign cmp v1 (DVALUE_Base DVALUE_Poison) =
    raise_ret (DVALUE_Base DVALUE_Poison).
Proof.
  intros samesign cmp v1 [-> | [p1 ->]]; reflexivity.
Qed.

Lemma eval_icmp_ptr_defined {Pa : Params} :
  forall samesign cmp (p1 p2 : @ptr _ (@PTR Pa)),
    eval_icmp samesign cmp
      (DVALUE_Base (DVALUE_Pointer p1))
      (DVALUE_Base (DVALUE_Pointer p2)) =
    Functor.fmap (fun b => DVALUE_Base b)
      (eval_int_icmp samesign cmp (ptr_to_int p1) (ptr_to_int p2)).
Proof.
  intros samesign cmp p1 p2; reflexivity.
Qed.

Theorem gep_inbounds_ptr_wrap64_sound {Pa : Params} :
  forall flags (dt : dtyp) (a p' : @ptr _ (@PTR Pa)) (vs : list (@dvalue Pa)) steps,
    @pointer_size Pa = 8%N ->
    (0 <= ptr_to_int a < 2 ^ 64)%Z ->
    gep_steps dt vs = raise_ret (Some steps) ->
    steps <> [] ->
    gep_inbounds flags = true ->
    handle_gep_ptr flags dt a vs = raise_ret (Some p') ->
    ptr_provenance p' = ptr_provenance a /\
    ptr_to_int p' = (ptr_to_int a + gep_offset steps)%Z /\
    (0 <= ptr_to_int p' < 2 ^ 64)%Z /\
    wrap_ptr64 (ptr_to_int p') = ptr_to_int p'.
Proof.
  intros flags dt a p' vs steps Hptr64 Hbase Hsteps Hne Hinb Hgep.
  unfold handle_gep_ptr in Hgep; rewrite Hsteps in Hgep; cbn in Hgep.
  destruct (gep_flags_violated flags (ptr_to_int a) steps) eqn:Hviol;
    [discriminate Hgep |].
  destruct (int_to_ptr (ptr_to_int a + gep_offset steps)%Z (ptr_provenance a))
    as [| | | q] eqn:Hitp; cbn in Hgep; try discriminate Hgep.
  inversion Hgep; subst q; clear Hgep.
  pose proof (int_to_ptr_provenance _ _ _ Hitp) as Hprov.
  pose proof (ptr_to_int_int_to_ptr _ _ _ Hitp) as Haddr.
  destruct (@gep_inbounds_flags_implies_wrap64_eq Pa flags (ptr_to_int a) steps
              Hptr64 Hbase Hne Hinb Hviol)
    as [Hrng Hwrap].
  rewrite Haddr.
  split; [exact Hprov | split; [reflexivity | split; [exact Hrng | exact Hwrap]]].
Qed.

Theorem gep_chained_no_flags_reassoc_sound {Pa : Params} :
  forall (dt1 dt2 : dtyp) (p0 p1 p2 : @ptr _ (@PTR Pa))
         (vs1 vs2 : list (@dvalue Pa)) steps1 steps2,
    gep_steps dt1 vs1 = raise_ret (Some steps1) ->
    gep_steps dt2 vs2 = raise_ret (Some steps2) ->
    handle_gep_ptr gep_no_flags dt1 p0 vs1 = raise_ret (Some p1) ->
    handle_gep_ptr gep_no_flags dt2 p1 vs2 = raise_ret (Some p2) ->
    ptr_provenance p2 = ptr_provenance p0 /\
    ptr_to_int p2 = (ptr_to_int p0 + gep_offset (steps1 ++ steps2))%Z /\
    wrap_ptr64 (ptr_to_int p2) =
      wrap_ptr64 (wrap_ptr64 (ptr_to_int p0 + gep_offset steps1) + gep_offset steps2)%Z.
Proof.
  intros dt1 dt2 p0 p1 p2 vs1 vs2 steps1 steps2 Hs1 Hs2 Hg1 Hg2.
  unfold handle_gep_ptr in Hg1, Hg2.
  rewrite Hs1 in Hg1; rewrite Hs2 in Hg2; cbn in Hg1, Hg2.
  destruct (int_to_ptr (ptr_to_int p0 + gep_offset steps1)%Z (ptr_provenance p0))
    as [| | | q1] eqn:Hitp1; cbn in Hg1; try discriminate Hg1.
  inversion Hg1; subst q1; clear Hg1.
  destruct (int_to_ptr (ptr_to_int p1 + gep_offset steps2)%Z (ptr_provenance p1))
    as [| | | q2] eqn:Hitp2; cbn in Hg2; try discriminate Hg2.
  inversion Hg2; subst q2; clear Hg2.
  pose proof (int_to_ptr_provenance _ _ _ Hitp1) as Hpr1.
  pose proof (ptr_to_int_int_to_ptr _ _ _ Hitp1) as Had1.
  pose proof (int_to_ptr_provenance _ _ _ Hitp2) as Hpr2.
  pose proof (ptr_to_int_int_to_ptr _ _ _ Hitp2) as Had2.
  rewrite Hpr2, Hpr1, Had2, Had1.
  split; [reflexivity | split].
  - rewrite gep_offset_app; lia.
  - symmetry; rewrite gep_steps_wrap64_reassoc, gep_offset_app.
    f_equal; lia.
Qed.

(** *** 5.6b [F-48]: Padded-Aggregate Slice Forwarding & Memory/Alias Certificate Obligations *)

Theorem validator_padded_struct_slice_forwarding_sound {Pa : Params} :
  forall (packed : bool) (dts : list dtyp) (dv_src dv_tgt : @dvalue Pa)
         (ta : option N) (mb_tgt : list memory_byte)
         (idx : nat) (ft : dtyp),
    serializable (DTYPE_Struct packed dts) ->
    dvalue_has_dtyp dv_src (DTYPE_Struct packed dts) ->
    dvalue_has_dtyp dv_tgt (DTYPE_Struct packed dts) ->
    dvalue_refines dv_src dv_tgt ->
    dvalue_to_memory_bytes (DTYPE_Struct packed dts) dv_tgt ta = raise_ret mb_tgt ->
    nth_error dts idx = Some ft ->
    exists foff fv_src fv_tgt,
      struct_field_offset packed dts idx = Some foff /\
      project_struct_field dv_src idx = Some fv_src /\
      project_struct_field dv_tgt idx = Some fv_tgt /\
      dvalue_refines fv_src fv_tgt /\
      (foff + store_size_dtyp ft <= N.of_nat (List.length mb_tgt))%N /\
      memory_bytes_to_dvalue (take (store_size_dtyp ft) (drop foff mb_tgt)) ft = raise_ret fv_tgt.
Proof.
  intros packed dts dv_src dv_tgt ta mb_tgt idx ft Hser Htys Htyt Href Hwt Hnth.
  destruct (@padded_struct_dvalue_field_slice_round_trip Pa
              packed dts dv_tgt ta mb_tgt idx ft Hser Htyt Hwt Hnth)
    as (foff & fv_tgt & Hfoff & Hpt & Hlen & Hrd).
  destruct Href as [-> | ->].
  - exists foff, (DVALUE_Base DVALUE_Poison), fv_tgt.
    split; [exact Hfoff | split; [reflexivity | split; [exact Hpt |]]].
    split; [left; reflexivity | split; [exact Hlen | exact Hrd]].
  - exists foff, fv_tgt, fv_tgt.
    split; [exact Hfoff | split; [exact Hpt | split; [exact Hpt |]]].
    split; [right; reflexivity | split; [exact Hlen | exact Hrd]].
Qed.

Definition cfg_alloca_slot_names (G : CFG.cfg dtyp) : list string :=
  List.flat_map (fun b =>
    List.flat_map (fun '(iid, ins, _) =>
      match iid, ins with
      | IId r, INSTR_Alloca _ _ => [cert_reg_name r]
      | _, _ => []
      end) (blk_code b)) (blks G).

Definition check_memory_invariant_valid
  (allowed : list (string * positive))
  (ctx : ub_ctx)
  (mi : memory_invariant) : bool :=
  wf_memory_invariant mi &&
  match mi with
  | MI_AllocaPromoted _ _ pe =>
      vars_subset_b (collect_free_vars [] pe) allowed &&
      check_expr_refines ctx pe pe
  | MI_SlotRefines _ _ _ se te =>
      vars_subset_b (collect_free_vars [] se) allowed &&
      vars_subset_b (collect_free_vars [] te) allowed &&
      check_expr_refines ctx se te
  end.

Lemma check_memory_invariant_valid_sound {Pa : Params} :
  forall allowed ctx mi (penv : param_env Pa) foracle,
    check_memory_invariant_valid allowed ctx mi = true ->
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv foracle ctx ->
    match mi with
    | MI_AllocaPromoted _ _ pe =>
        refine_eou_dvalue
          (eval_closed_cert_expr penv foracle pe)
          (eval_closed_cert_expr penv foracle pe)
    | MI_SlotRefines _ _ _ se te =>
        refine_eou_dvalue
          (eval_closed_cert_expr penv foracle se)
          (eval_closed_cert_expr penv foracle te)
    end.
Proof.
  intros allowed ctx mi penv foracle Hchk Hpenv Hctx.
  unfold check_memory_invariant_valid in Hchk.
  apply andb_true_iff in Hchk as [_ Hbody].
  destruct mi as [ss w pe | ss ts w se te].
  - apply andb_true_iff in Hbody as [Hsub Href].
    pose proof (vars_subset_b_wf_param _ allowed penv Hsub Hpenv) as Hpf.
    exact (check_expr_refines_sound ctx pe pe penv foracle Href Hpf Hpf Hctx).
  - rewrite !andb_true_iff in Hbody; destruct Hbody as ([Hs1 Hs2] & Href).
    exact (check_expr_refines_sound ctx se te penv foracle Href
             (vars_subset_b_wf_param _ allowed penv Hs1 Hpenv)
             (vars_subset_b_wf_param _ allowed penv Hs2 Hpenv) Hctx).
Qed.

Definition check_alias_witness_valid
  (src_alloca_slots : list string)
  (aw : alias_witness) : bool :=
  wf_alias_witness aw &&
  match aw_kind aw with
  | ARK_MustAlias => String.eqb (aw_lhs_ptr aw) (aw_rhs_ptr aw)
  | ARK_NoAlias =>
      negb (String.eqb (aw_lhs_ptr aw) (aw_rhs_ptr aw)) &&
      string_in_list (aw_lhs_ptr aw) src_alloca_slots &&
      string_in_list (aw_rhs_ptr aw) src_alloca_slots
  end.

Lemma check_alias_witness_valid_inv :
  forall src_alloca_slots aw,
    check_alias_witness_valid src_alloca_slots aw = true ->
    match aw_kind aw with
    | ARK_MustAlias => aw_lhs_ptr aw = aw_rhs_ptr aw
    | ARK_NoAlias =>
        aw_lhs_ptr aw <> aw_rhs_ptr aw /\
        string_in_list (aw_lhs_ptr aw) src_alloca_slots = true /\
        string_in_list (aw_rhs_ptr aw) src_alloca_slots = true
    end.
Proof.
  intros slots aw H; unfold check_alias_witness_valid in H.
  apply andb_true_iff in H as [_ Hb].
  destruct (aw_kind aw).
  - rewrite !andb_true_iff in Hb; destruct Hb as ([Hneq Hl] & Hr).
    apply negb_true_iff in Hneq.
    split; [intros Heq; apply String.eqb_eq in Heq; congruence | split; assumption].
  - apply String.eqb_eq; exact Hb.
Qed.

(** *** 5.6c [F-26]: Single-Header Natural Loop Cut-Point Validator & Coinductive Soundness *)

Lemma dvalue_refines_antisym {Pa : Params} :
  forall (v1 v2 : @dvalue Pa),
    dvalue_refines v1 v2 -> dvalue_refines v2 v1 -> v1 = v2.
Proof.
  intros v1 v2 [-> | ->] [-> | ->]; reflexivity.
Qed.

Definition dummy_freeze_oracle : freeze_oracle := fun _ _ => 0%Z.

Fixpoint reify_pure_exp
  (lmap : rmap (positive * cert_expr))
  (top : option dtyp)
  (o : exp dtyp)
  {struct o} : option (positive * cert_expr) :=
  match o with
  | EXP_Ident (ID_Local r) =>
      match RM.find r lmap with
      | Some (w, ce) =>
          if check_opt_int_width top w then Some (w, ce) else None
      | None => None
      end
  | EXP_Integer x =>
      match top with
      | Some (DTYPE_Base (DTYPE_I w)) =>
          Some (w, CE_BvConst w (reify_int_const w (denote_int_syntax x)))
      | _ => None
      end
  | EXP_Bool b =>
      if check_opt_int_width top 1%positive
      then Some (1%positive, CE_BvConst 1%positive (if b then 1%N else 0%N))
      else None
  | EXP_Undef | EXP_Poison =>
      match top with
      | Some (DTYPE_Base (DTYPE_I w)) => Some (w, CE_Poison w)
      | _ => None
      end
  | OP_IBinop iop (DTYPE_Base (DTYPE_I w)) e1 e2 =>
      if check_opt_int_width top w then
        match reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) e1,
              reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) e2 with
        | Some (_, ce1), Some (_, ce2) =>
            let '(cop, cfl) := ibinop_to_cert iop in
            Some (w, CE_BinOp cop w cfl ce1 ce2)
        | _, _ => None
        end
      else None
  | OP_ICmp ss cmp (DTYPE_Base (DTYPE_I w)) e1 e2 =>
      if check_opt_int_width top 1%positive then
        match reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) e1,
              reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) e2 with
        | Some (_, ce1), Some (_, ce2) =>
            Some (1%positive, CE_ICmp (icmp_to_cert cmp) ss w ce1 ce2)
        | _, _ => None
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
              match reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I fw))) e1 with
              | Some (_, ce1) => Some (tw, CE_Cast ck fw tw cfl ce1)
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
        match reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I 1%positive))) ec,
              reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e1,
              reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e2 with
        | Some (_, cec), Some (_, ce1), Some (_, ce2) =>
            Some (w1, CE_Select w1 cec ce1 ce2)
        | _, _, _ => None
        end
      else None
  | _ => None
  end.

Definition wf_pure_lmap
  (allowed : list (string * positive))
  (lmap : rmap (positive * cert_expr)) : Prop :=
  forall r w ce,
    RM.find r lmap = Some (w, ce) ->
    wt_cert_expr [] ce = true /\
    cert_expr_bit_width ce = w /\
    is_let_free_expr ce = true /\
    incl (collect_free_vars [] ce) allowed.

Lemma reify_pure_exp_typing :
  forall (o : exp dtyp) allowed lmap top w ce,
    wf_pure_lmap allowed lmap ->
    reify_pure_exp lmap top o = Some (w, ce) ->
    check_opt_int_width top w = true /\
    wt_cert_expr [] ce = true /\
    cert_expr_bit_width ce = w /\
    is_let_free_expr ce = true /\
    incl (collect_free_vars [] ce) allowed.
Proof.
  apply (scalar_exp_ind (fun o =>
    forall allowed lmap top w ce,
      wf_pure_lmap allowed lmap ->
      reify_pure_exp lmap top o = Some (w, ce) ->
      check_opt_int_width top w = true /\
      wt_cert_expr [] ce = true /\
      cert_expr_bit_width ce = w /\
      is_let_free_expr ce = true /\
      incl (collect_free_vars [] ce) allowed)).
  - intros iop dt e1 e2 IH1 IH2 allowed lmap top w ce Hlmap Hr.
    cbn [reify_pure_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e1) as [[w1 ce1] |] eqn:Hr1; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e2) as [[w2 ce2] |] eqn:Hr2; [| discriminate].
    destruct (ibinop_to_cert iop) as [cop cfl] eqn:Hiop.
    inversion Hr; subst wb ce; clear Hr.
    destruct (ibinop_to_cert_roundtrip iop cop cfl Hiop) as [_ Hfl].
    destruct (IH1 allowed lmap _ w1 ce1 Hlmap Hr1) as (Hcw1 & Hwt1 & Hbw1 & Hlf1 & Hfv1).
    destruct (IH2 allowed lmap _ w2 ce2 Hlmap Hr2) as (Hcw2 & Hwt2 & Hbw2 & Hlf2 & Hfv2).
    apply check_opt_int_width_some_inv in Hcw1; apply check_opt_int_width_some_inv in Hcw2; subst w1 w2.
    repeat split; [exact Hcw | | |].
    + cbn; rewrite Hfl, Hwt1, Hwt2, Hbw1, Hbw2, !Pos.eqb_refl; reflexivity.
    + cbn; rewrite Hlf1, Hlf2; reflexivity.
    + cbn; apply incl_app; assumption.
  - intros ss cmp dt e1 e2 IH1 IH2 allowed lmap top w ce Hlmap Hr.
    cbn [reify_pure_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e1) as [[w1 ce1] |] eqn:Hr1; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e2) as [[w2 ce2] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w ce; clear Hr.
    destruct (IH1 allowed lmap _ w1 ce1 Hlmap Hr1) as (Hcw1 & Hwt1 & Hbw1 & Hlf1 & Hfv1).
    destruct (IH2 allowed lmap _ w2 ce2 Hlmap Hr2) as (Hcw2 & Hwt2 & Hbw2 & Hlf2 & Hfv2).
    apply check_opt_int_width_some_inv in Hcw1; apply check_opt_int_width_some_inv in Hcw2; subst w1 w2.
    repeat split; [exact Hcw | | |].
    + cbn; rewrite Hwt1, Hwt2, Hbw1, Hbw2, !Pos.eqb_refl; reflexivity.
    + cbn; rewrite Hlf1, Hlf2; reflexivity.
    + cbn; apply incl_app; assumption.
  - intros ct dtf e1 dtt IH1 allowed lmap top w ce Hlmap Hr.
    cbn [reify_pure_exp] in Hr.
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
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I fw))) e1) as [[w1 ce1] |] eqn:Hr1; [| discriminate].
    inversion Hr; subst w ce; clear Hr.
    destruct (IH1 allowed lmap _ w1 ce1 Hlmap Hr1) as (Hcw1 & Hwt1 & Hbw1 & Hlf1 & Hfv1).
    apply check_opt_int_width_some_inv in Hcw1; subst w1.
    repeat split; [exact Hcw | | exact Hlf1 | exact Hfv1].
    + cbn; unfold w_ok in Hwok; rewrite Hwok, Hwt1, Hbw1, Pos.eqb_refl; reflexivity.
  - intros fm dtc ec dt1 e1 dt2 e2 IHc IH1 IH2 allowed lmap top w ce Hlmap Hr.
    cbn [reify_pure_exp] in Hr.
    destruct dtc as [tbc | |]; try discriminate; destruct tbc as [wc | | | | | | | | | |]; try discriminate.
    destruct wc as [| |]; try discriminate.
    destruct dt1 as [tb1 | |]; try discriminate; destruct tb1 as [w1 | | | | | | | | | |]; try discriminate.
    destruct dt2 as [tb2 | |]; try discriminate; destruct tb2 as [w2 | | | | | | | | | |]; try discriminate.
    destruct (Pos.eqb w1 w2 && check_opt_int_width top w1) eqn:Hcw; [| discriminate].
    apply andb_true_iff in Hcw as [Hw12 Hcw]; apply Pos.eqb_eq in Hw12; subst w2.
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I 1%positive))) ec) as [[wc' cec] |] eqn:Hrc; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e1) as [[wa ce1] |] eqn:Hr1; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e2) as [[wb ce2] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w1 ce; clear Hr.
    destruct (IHc allowed lmap _ wc' cec Hlmap Hrc) as (Hcwc & Hwtc & Hbwc & Hlfc & Hfvc).
    destruct (IH1 allowed lmap _ wa ce1 Hlmap Hr1) as (Hcwa & Hwta & Hbwa & Hlfa & Hfva).
    destruct (IH2 allowed lmap _ wb ce2 Hlmap Hr2) as (Hcwb & Hwtb & Hbwb & Hlfb & Hfvb).
    apply check_opt_int_width_some_inv in Hcwc;
    apply check_opt_int_width_some_inv in Hcwa;
    apply check_opt_int_width_some_inv in Hcwb; subst wc' wa wb.
    repeat split; [exact Hcw | | |].
    + cbn; rewrite Hwtc, Hwta, Hwtb, Hbwc, Hbwa, Hbwb, !Pos.eqb_refl; reflexivity.
    + cbn; rewrite Hlfc, Hlfa, Hlfb; reflexivity.
    + cbn; apply incl_app; [exact Hfvc | apply incl_app; assumption].
  - intros dt e1 _ allowed lmap top w ce _ Hr; cbn [reify_pure_exp] in Hr; discriminate Hr.
  - intros o; destruct o; try exact I;
      intros allowed lmap top w ce Hlmap Hr; cbn [reify_pure_exp] in Hr; try discriminate.
    + destruct id as [| r]; [discriminate |].
      destruct (RM.find r lmap) as [[wr cer] |] eqn:Hf; [| discriminate].
      destruct (check_opt_int_width top wr) eqn:Hcw; [| discriminate].
      inversion Hr; subst wr ce; clear Hr.
      destruct (Hlmap r w cer Hf) as (Hwt & Hbw & Hlf & Hfv).
      repeat split; assumption.
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce; clear Hr.
      repeat split; [cbn; apply Pos.eqb_refl | intros u []].
    + destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
      inversion Hr; subst w ce; clear Hr.
      repeat split; [exact Hcw | intros u []].
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce; clear Hr.
      repeat split; [cbn; apply Pos.eqb_refl | intros u []].
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce; clear Hr.
      repeat split; [cbn; apply Pos.eqb_refl | intros u []].
Qed.

Definition lmap_matches_env {Pa : Params}
  (penv : param_env Pa)
  (lmap : rmap (positive * cert_expr))
  (env : rmap (@dvalue Pa)) : Prop :=
  forall r w ce,
    RM.find r lmap = Some (w, ce) ->
    exists dv,
      RM.find r env = Some dv /\
      eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
      wf_scalar_dvalue w dv.

Lemma lmap_matches_env_add {Pa : Params} :
  forall (penv : param_env Pa) lmap env id w ce dv,
    lmap_matches_env penv lmap env ->
    eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv ->
    wf_scalar_dvalue w dv ->
    lmap_matches_env penv (RM.add id (w, ce) lmap) (RM.add id dv env).
Proof.
  intros penv lmap env id w ce dv Henv Hev Hsc r wr cer Hf.
  destruct (RawIDOrd.eq_dec id r) as [Heq | Hneq].
  - rewrite RMF.F.add_eq_o in Hf by exact Heq; inversion Hf; subst r wr cer.
    exists dv; split; [apply RMF.F.add_eq_o; reflexivity | split; assumption].
  - rewrite RMF.F.add_neq_o in Hf by exact Hneq.
    destruct (Henv r wr cer Hf) as [dv' [Hfe [Hev' Hsc']]].
    exists dv'; split; [rewrite RMF.F.add_neq_o by exact Hneq; exact Hfe | split; assumption].
Qed.

Lemma reify_pure_exp_top_width :
  forall (o : exp dtyp) lmap top w ce,
    reify_pure_exp lmap top o = Some (w, ce) ->
    check_opt_int_width top w = true.
Proof.
  apply (scalar_exp_ind (fun o =>
    forall lmap top w ce,
      reify_pure_exp lmap top o = Some (w, ce) ->
      check_opt_int_width top w = true)).
  - intros iop dt e1 e2 _ _ lmap top w ce Hr; cbn [reify_pure_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e1) as [[w1 ce1] |]; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e2) as [[w2 ce2] |]; [| discriminate].
    destruct (ibinop_to_cert iop); inversion Hr; subst; exact Hcw.
  - intros ss cmp dt e1 e2 _ _ lmap top w ce Hr; cbn [reify_pure_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e1) as [[w1 ce1] |]; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e2) as [[w2 ce2] |]; [| discriminate].
    inversion Hr; subst; exact Hcw.
  - intros ct dtf e1 dtt _ lmap top w ce Hr; cbn [reify_pure_exp] in Hr.
    destruct ct as [pc | |]; try discriminate.
    destruct dtf as [tbf | |]; try discriminate; destruct tbf as [fw | | | | | | | | | |]; try discriminate.
    destruct dtt as [tbt | |]; try discriminate; destruct tbt as [tw | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top tw) eqn:Hcw; [| discriminate].
    destruct (pure_conv_to_cert pc) as [[ck cfl] |]; [| discriminate].
    destruct (match ck with CCK_ZExt => _ | CCK_SExt => _ | CCK_Trunc => _ end); [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I fw))) e1) as [[w1 ce1] |]; [| discriminate].
    inversion Hr; subst; exact Hcw.
  - intros fm dtc ec dt1 e1 dt2 e2 _ _ _ lmap top w ce Hr; cbn [reify_pure_exp] in Hr.
    destruct dtc as [tbc | |]; try discriminate; destruct tbc as [wc | | | | | | | | | |]; try discriminate.
    destruct wc as [| |]; try discriminate.
    destruct dt1 as [tb1 | |]; try discriminate; destruct tb1 as [w1 | | | | | | | | | |]; try discriminate.
    destruct dt2 as [tb2 | |]; try discriminate; destruct tb2 as [w2 | | | | | | | | | |]; try discriminate.
    destruct (Pos.eqb w1 w2 && check_opt_int_width top w1) eqn:Hcw; [| discriminate].
    apply andb_true_iff in Hcw as [_ Hcw].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I 1%positive))) ec) as [[wc' cec] |]; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e1) as [[wa ce1] |]; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e2) as [[wb ce2] |]; [| discriminate].
    inversion Hr; subst; exact Hcw.
  - intros dt e1 _ lmap top w ce Hr; cbn [reify_pure_exp] in Hr; discriminate Hr.
  - intros o; destruct o; try exact I;
      intros lmap top w ce Hr; cbn [reify_pure_exp] in Hr; try discriminate.
    + destruct id as [| r]; [discriminate |].
      destruct (RM.find r lmap) as [[wr cer] |]; [| discriminate].
      destruct (check_opt_int_width top wr) eqn:Hcw; [| discriminate].
      inversion Hr; subst; exact Hcw.
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst; cbn; apply Pos.eqb_refl.
    + destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
      inversion Hr; subst; exact Hcw.
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst; cbn; apply Pos.eqb_refl.
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst; cbn; apply Pos.eqb_refl.
Qed.

Inductive pure_mcfg_steps {Pa : Params} {R : Type}
  : rmap (@dvalue Pa) -> MCFGtop R -> rmap (@dvalue Pa) -> R -> Prop :=
| PMS_Ret env (t : MCFGtop R) (r : R) :
    observe t = RetF r ->
    pure_mcfg_steps env t env r
| PMS_Tau env (t t' : MCFGtop R) env' r :
    observe t = TauF t' ->
    pure_mcfg_steps env t' env' r ->
    pure_mcfg_steps env t env' r
| PMS_LocalRead env (t : MCFGtop R) id dv (k : @dvalue Pa -> MCFGtop R) env' r :
    observe t = VisF (@subevent LocalE MCFGEtop _ (@dvalue Pa) (LocalRead id)) k ->
    RM.find id env = Some dv ->
    pure_mcfg_steps env (k dv) env' r ->
    pure_mcfg_steps env t env' r
| PMS_LocalWrite env (t : MCFGtop R) id dv (k : unit -> MCFGtop R) env' r :
    observe t = VisF (@subevent LocalE MCFGEtop _ unit (LocalWrite id dv)) k ->
    pure_mcfg_steps (RM.add id dv env) (k tt) env' r ->
    pure_mcfg_steps env t env' r.

Inductive pure_cfg_steps {Pa : Params} {R : Type}
  : rmap (@dvalue Pa) -> CFGtop R -> rmap (@dvalue Pa) -> R -> Prop :=
| PCS_Ret env (t : CFGtop R) (r : R) :
    observe t = RetF r ->
    pure_cfg_steps env t env r
| PCS_Tau env (t t' : CFGtop R) env' r :
    observe t = TauF t' ->
    pure_cfg_steps env t' env' r ->
    pure_cfg_steps env t env' r
| PCS_LocalRead env (t : CFGtop R) id dv (k : @dvalue Pa -> CFGtop R) env' r :
    observe t = VisF (@subevent LocalE CFGEtop _ (@dvalue Pa) (LocalRead id)) k ->
    RM.find id env = Some dv ->
    pure_cfg_steps env (k dv) env' r ->
    pure_cfg_steps env t env' r
| PCS_LocalWrite env (t : CFGtop R) id dv (k : unit -> CFGtop R) env' r :
    observe t = VisF (@subevent LocalE CFGEtop _ unit (LocalWrite id dv)) k ->
    pure_cfg_steps (RM.add id dv env) (k tt) env' r ->
    pure_cfg_steps env t env' r.

Lemma pure_mcfg_steps_obs {Pa : Params} {R : Type} :
  forall env (t1 t2 : MCFGtop R) env' r,
    observe t1 = observe t2 ->
    @pure_mcfg_steps Pa R env t1 env' r ->
    @pure_mcfg_steps Pa R env t2 env' r.
Proof.
  intros env t1 t2 env' r Ho H.
  inversion H; subst;
    [apply PMS_Ret | eapply PMS_Tau | eapply PMS_LocalRead | eapply PMS_LocalWrite];
    try (rewrite <- Ho; eassumption); eassumption.
Qed.

Lemma pure_mcfg_steps_bind {Pa : Params} {R S : Type} :
  forall env0 (t : MCFGtop R) env1 x (k : R -> MCFGtop S) env2 y,
    @pure_mcfg_steps Pa R env0 t env1 x ->
    @pure_mcfg_steps Pa S env1 (k x) env2 y ->
    @pure_mcfg_steps Pa S env0 (ITree.bind t k) env2 y.
Proof.
  intros env0 t env1 x k env2 y H1 H2.
  induction H1 as [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH].
  - eapply pure_mcfg_steps_obs; [symmetry; rewrite observe_bind, Ho; reflexivity | exact H2].
  - eapply PMS_Tau; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
  - eapply PMS_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact (IH H2)].
  - eapply PMS_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
Qed.

Lemma pure_mcfg_to_mcfg_ret {Pa : Params} {R : Type} :
  forall (sigma : @draw_strat Pa) env (t : MCFGtop R) env' r,
    @pure_mcfg_steps Pa R env t env' r ->
    mcfg_steps_to_ret sigma env t sigma env' r.
Proof.
  intros sigma env t env' r H.
  induction H as [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH].
  - apply MSR_Ret; exact Ho.
  - eapply MSR_Tau; [exact Ho | exact IH].
  - eapply MSR_LocalRead; [exact Ho | exact Hf | exact IH].
  - eapply MSR_LocalWrite; [exact Ho | exact IH].
Qed.

Lemma pure_mcfg_to_pure_cfg {Pa : Params} {R : Type} :
  forall env (t : MCFGtop R) env' r,
    @pure_mcfg_steps Pa R env t env' r ->
    @pure_cfg_steps Pa R env (withCall t) env' r.
Proof.
  intros env t env' r H.
  induction H as [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH];
    unfold withCall in *.
  - apply PCS_Ret; rewrite observe_translate, Ho; reflexivity.
  - eapply PCS_Tau; [rewrite observe_translate, Ho; reflexivity | exact IH].
  - eapply PCS_LocalRead; [rewrite observe_translate, Ho; reflexivity | exact Hf | exact IH].
  - eapply PCS_LocalWrite; [rewrite observe_translate, Ho; reflexivity | exact IH].
Qed.

Lemma pure_cfg_steps_obs {Pa : Params} {R : Type} :
  forall env (t1 t2 : CFGtop R) env' r,
    observe t1 = observe t2 ->
    @pure_cfg_steps Pa R env t1 env' r ->
    @pure_cfg_steps Pa R env t2 env' r.
Proof.
  intros env t1 t2 env' r Ho H.
  inversion H; subst;
    [apply PCS_Ret | eapply PCS_Tau | eapply PCS_LocalRead | eapply PCS_LocalWrite];
    try (rewrite <- Ho; eassumption); eassumption.
Qed.

Lemma pure_cfg_steps_bind {Pa : Params} {R S : Type} :
  forall env0 (t : CFGtop R) env1 x (k : R -> CFGtop S) env2 y,
    @pure_cfg_steps Pa R env0 t env1 x ->
    @pure_cfg_steps Pa S env1 (k x) env2 y ->
    @pure_cfg_steps Pa S env0 (ITree.bind t k) env2 y.
Proof.
  intros env0 t env1 x k env2 y H1 H2.
  induction H1 as [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH].
  - eapply pure_cfg_steps_obs; [symmetry; rewrite observe_bind, Ho; reflexivity | exact H2].
  - eapply PCS_Tau; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
  - eapply PCS_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact (IH H2)].
  - eapply PCS_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
Qed.

Lemma pure_cfg_steps_lwrite {Pa : Params} :
  forall (env : rmap (@dvalue Pa)) (id : raw_id) (dv : @dvalue Pa),
    pure_cfg_steps env (lwrite (E := CFGEtop) id dv) (RM.add id dv env) tt.
Proof.
  intros env id dv; eapply PCS_LocalWrite; [reflexivity | apply PCS_Ret; reflexivity].
Qed.

Lemma pure_cfg_steps_lwrite_list {Pa : Params} :
  forall (dvs : list (raw_id * @dvalue Pa)) (env : rmap (@dvalue Pa)),
    pure_cfg_steps env
      (map_monad (m := CFGtop) (fun '(id, dv) => lwrite id dv) dvs)
      (apply_phi_env env dvs) (List.map (fun _ => tt) dvs).
Proof.
  induction dvs as [| [id dv] rest IH]; intros env; cbn [map_monad apply_phi_env List.map].
  - apply PCS_Ret; reflexivity.
  - eapply pure_cfg_steps_bind; [apply pure_cfg_steps_lwrite |].
    eapply pure_cfg_steps_bind; [apply IH | apply PCS_Ret; reflexivity].
Qed.

Lemma pure_cfg_steps_det_ref_bind_l {Pa : Params} {A R1 R2 : Type}
  (RR : R1 -> R2 -> Prop)
  (self : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop) :
  forall (s1 : @draw_strat Pa) env1 (t1 : CFGtop A) env1' x1
         (k1 : A -> CFGtop R1) (u2 : itree (@Det_OW_E Pa) R2),
    @pure_cfg_steps Pa A env1 t1 env1' x1 ->
    det_ref_ (Pa := Pa) RR self
      (run_draws s1 (run_cfg_locals env1' (k1 x1))) u2 ->
    det_ref_ (Pa := Pa) RR self
      (run_draws s1 (run_cfg_locals env1 (ITree.bind t1 k1))) u2.
Proof.
  intros s1 env1 t1 env1' x1 k1 u2 H1 Hk.
  induction H1 as [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH].
  - eapply det_ref__obs_eq;
      [symmetry; rewrite !observe_run_draws, !observe_run_cfg_locals, observe_bind, Ho; reflexivity
      | reflexivity | exact Hk].
  - eapply DR_TauL;
      [rewrite observe_run_draws, observe_run_cfg_locals, observe_bind, Ho; reflexivity | exact (IH Hk)].
  - eapply DR_TauL;
      [rewrite observe_run_draws, observe_run_cfg_locals, observe_bind, Ho; cbn; rewrite Hf; reflexivity | exact (IH Hk)].
  - eapply DR_TauL;
      [rewrite observe_run_draws, observe_run_cfg_locals, observe_bind, Ho; reflexivity | exact (IH Hk)].
Qed.

Lemma pure_cfg_steps_det_ref_bind_r {Pa : Params} {A R1 R2 : Type}
  (RR : R1 -> R2 -> Prop)
  (self : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop) :
  forall (u1 : itree (@Det_OW_E Pa) R1)
         (s2 : @draw_strat Pa) env2 (t2 : CFGtop A) env2' x2 (k2 : A -> CFGtop R2),
    @pure_cfg_steps Pa A env2 t2 env2' x2 ->
    det_ref_ (Pa := Pa) RR self
      u1 (run_draws s2 (run_cfg_locals env2' (k2 x2))) ->
    det_ref_ (Pa := Pa) RR self
      u1 (run_draws s2 (run_cfg_locals env2 (ITree.bind t2 k2))).
Proof.
  intros u1 s2 env2 t2 env2' x2 k2 H2 Hk.
  induction H2 as [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH].
  - eapply det_ref__obs_eq;
      [reflexivity
      | symmetry; rewrite !observe_run_draws, !observe_run_cfg_locals, observe_bind, Ho; reflexivity
      | exact Hk].
  - eapply DR_TauR;
      [rewrite observe_run_draws, observe_run_cfg_locals, observe_bind, Ho; reflexivity | exact (IH Hk)].
  - eapply DR_TauR;
      [rewrite observe_run_draws, observe_run_cfg_locals, observe_bind, Ho; cbn; rewrite Hf; reflexivity | exact (IH Hk)].
  - eapply DR_TauR;
      [rewrite observe_run_draws, observe_run_cfg_locals, observe_bind, Ho; reflexivity | exact (IH Hk)].
Qed.

Lemma eval_reified_pure_exp {Pa : Params} :
  forall (o : exp dtyp) (penv : param_env Pa)
         lmap (env : rmap (@dvalue Pa)) top w ce,
    lmap_matches_env penv lmap env ->
    reify_pure_exp lmap top o = Some (w, ce) ->
    ((forall sigma, mcfg_steps_to_ub sigma env (denote_exp top o)) /\
     exists msg, eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ub msg) \/
    (exists dv,
       eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
       wf_scalar_dvalue w dv /\
       pure_mcfg_steps env (denote_exp top o) env dv).
Proof.
  apply (scalar_exp_ind (fun o =>
    forall (penv : param_env Pa)
           lmap (env : rmap (@dvalue Pa)) top w ce,
      lmap_matches_env penv lmap env ->
      reify_pure_exp lmap top o = Some (w, ce) ->
      ((forall sigma, mcfg_steps_to_ub sigma env (denote_exp top o)) /\
       exists msg, eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ub msg) \/
      (exists dv,
         eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
         wf_scalar_dvalue w dv /\
         pure_mcfg_steps env (denote_exp top o) env dv))).
  - intros iop dt e1 e2 IH1 IH2 penv lmap env top w ce Henv Hr.
    cbn [reify_pure_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e1) as [[w1 ce1] |] eqn:Hr1; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e2) as [[w2 ce2] |] eqn:Hr2; [| discriminate].
    destruct (ibinop_to_cert iop) as [cop cfl] eqn:Hiop.
    inversion Hr; subst wb ce; clear Hr.
    destruct (ibinop_to_cert_roundtrip iop cop cfl Hiop) as [Heq_iop _].
    destruct (IH1 penv lmap env (Some (DTYPE_Base (DTYPE_I w))) w1 ce1 Henv Hr1)
      as [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]].
    + left; split; [intros sigma; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hub1 sigma)
                   | exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity].
    + destruct (IH2 penv lmap env (Some (DTYPE_Base (DTYPE_I w))) w2 ce2 Henv Hr2)
        as [[Hub2 [msg2 Hev2]] | [dv2 [Hev2 [Hsc2 Hst2]]]].
      * left; split;
          [intros sigma; cbn [denote_exp]; eapply mcfg_steps_to_ub_bind_r;
             [exact (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1) | apply mcfg_steps_to_ub_bind_l; exact (Hub2 sigma)]
          | exists msg2; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
              rewrite Hev1, Hev2; reflexivity].
      * pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr1)) as Hw1.
        pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr2)) as Hw2.
        subst w1 w2.
        destruct (eval_iop_wf_scalar cop cfl w dv1 dv2 Hsc1 Hsc2)
          as [[msg_op Hev_op] | [vout [Hev_op Hsc_out]]].
        -- left; split.
           ++ intros sigma; cbn [denote_exp]; eapply mcfg_steps_to_ub_bind_r;
                [exact (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1) |].
              eapply mcfg_steps_to_ub_bind_r;
                [exact (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst2) |].
              rewrite <- Heq_iop, Hev_op; apply mcfg_steps_eou_ub.
           ++ exists msg_op; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hev1, Hev2; cbn [eou_bind]; exact Hev_op.
        -- right; exists vout; split; [| split; [exact Hsc_out |]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hev1, Hev2; cbn [eou_bind]; exact Hev_op.
           ++ cbn [denote_exp]; eapply pure_mcfg_steps_bind; [exact Hst1 |].
              eapply pure_mcfg_steps_bind; [exact Hst2 |].
              rewrite <- Heq_iop, Hev_op; apply PMS_Ret; reflexivity.
  - intros ss cmp dt e1 e2 IH1 IH2 penv lmap env top w ce Henv Hr.
    cbn [reify_pure_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e1) as [[w1 ce1] |] eqn:Hr1; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e2) as [[w2 ce2] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w ce; clear Hr.
    destruct (IH1 penv lmap env (Some (DTYPE_Base (DTYPE_I wb))) w1 ce1 Henv Hr1)
      as [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]].
    + left; split; [intros sigma; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hub1 sigma)
                   | exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity].
    + destruct (IH2 penv lmap env (Some (DTYPE_Base (DTYPE_I wb))) w2 ce2 Henv Hr2)
        as [[Hub2 [msg2 Hev2]] | [dv2 [Hev2 [Hsc2 Hst2]]]].
      * left; split;
          [intros sigma; cbn [denote_exp]; eapply mcfg_steps_to_ub_bind_r;
             [exact (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1) | apply mcfg_steps_to_ub_bind_l; exact (Hub2 sigma)]
          | exists msg2; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
              rewrite Hev1, Hev2; reflexivity].
      * pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr1)) as Hw1.
        pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr2)) as Hw2.
        subst w1 w2.
        destruct (eval_icmp_wf_scalar ss (icmp_to_cert cmp) wb dv1 dv2 Hsc1 Hsc2)
          as [vout [Hev_cmp Hsc_out]].
        right; exists vout; split; [| split; [exact Hsc_out |]].
        -- unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hev1, Hev2; cbn [eou_bind]; exact Hev_cmp.
        -- cbn [denote_exp]; eapply pure_mcfg_steps_bind; [exact Hst1 |].
           eapply pure_mcfg_steps_bind; [exact Hst2 |].
           rewrite <- (icmp_to_cert_roundtrip cmp), Hev_cmp; apply PMS_Ret; reflexivity.
  - intros ct dtf e1 dtt IH1 penv lmap env top w ce Henv Hr.
    cbn [reify_pure_exp] in Hr.
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
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I fw))) e1) as [[w1 ce1] |] eqn:Hr1; [| discriminate].
    inversion Hr; subst w ce; clear Hr.
    pose proof (pure_conv_to_cert_roundtrip pc ck cfl Hpc) as Heq_pc.
    destruct (IH1 penv lmap env (Some (DTYPE_Base (DTYPE_I fw))) w1 ce1 Henv Hr1)
      as [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]].
    + left; split; [intros sigma; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hub1 sigma)
                   | exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity].
    + pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr1)) as Hw1.
      subst w1; unfold w_ok in Hwok.
      destruct (eval_cast_wf_scalar ck fw tw cfl dv1 Hwok Hsc1) as [vout [Hev_cast Hsc_out]].
      right; exists vout; split; [| split; [exact Hsc_out |]].
      * unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; cbn [eou_bind]; exact Hev_cast.
      * cbn [denote_exp convert]; eapply pure_mcfg_steps_bind; [exact Hst1 |].
        rewrite <- Heq_pc, Hev_cast; apply PMS_Ret; reflexivity.
  - intros fm dtc ec dt1 e1 dt2 e2 IHc IH1 IH2 penv lmap env top w ce Henv Hr.
    cbn [reify_pure_exp] in Hr.
    destruct dtc as [tbc | |]; try discriminate; destruct tbc as [wc | | | | | | | | | |]; try discriminate.
    destruct wc as [| |]; try discriminate.
    destruct dt1 as [tb1 | |]; try discriminate; destruct tb1 as [w1 | | | | | | | | | |]; try discriminate.
    destruct dt2 as [tb2 | |]; try discriminate; destruct tb2 as [w2 | | | | | | | | | |]; try discriminate.
    destruct (Pos.eqb w1 w2 && check_opt_int_width top w1) eqn:Hcw; [| discriminate].
    apply andb_true_iff in Hcw as [Hw12 Hcw]; apply Pos.eqb_eq in Hw12; subst w2.
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I 1%positive))) ec) as [[wc' cec] |] eqn:Hrc; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e1) as [[wa ce1] |] eqn:Hr1; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e2) as [[wb ce2] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w1 ce; clear Hr.
    destruct (IHc penv lmap env (Some (DTYPE_Base (DTYPE_I 1%positive))) wc' cec Henv Hrc)
      as [[Hubc [msgc Hevc]] | [dvc [Hevc [Hscc Hstc]]]].
    + left; split; [intros sigma; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hubc sigma)
                   | exists msgc; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hevc; reflexivity].
    + destruct (IH1 penv lmap env (Some (DTYPE_Base (DTYPE_I w))) wa ce1 Henv Hr1)
        as [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]].
      * left; split;
          [intros sigma; cbn [denote_exp]; eapply mcfg_steps_to_ub_bind_r;
             [exact (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hstc) | apply mcfg_steps_to_ub_bind_l; exact (Hub1 sigma)]
          | exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
              rewrite Hevc, Hev1; reflexivity].
      * destruct (IH2 penv lmap env (Some (DTYPE_Base (DTYPE_I w))) wb ce2 Henv Hr2)
          as [[Hub2 [msg2 Hev2]] | [dv2 [Hev2 [Hsc2 Hst2]]]].
        -- left; split;
             [intros sigma; cbn [denote_exp];
                eapply mcfg_steps_to_ub_bind_r; [exact (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hstc) |];
                eapply mcfg_steps_to_ub_bind_r; [exact (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1)
                                                 | apply mcfg_steps_to_ub_bind_l; exact (Hub2 sigma)]
             | exists msg2; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                 rewrite Hevc, Hev1, Hev2; reflexivity].
        -- pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hrc)) as Hwc.
           pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr1)) as Hwa.
           pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr2)) as Hwb.
           subst wc' wa wb.
           destruct (eval_select_wf_scalar w dvc dv1 dv2 Hscc Hsc1 Hsc2) as [vout [Hev_sel Hsc_out]].
           right; exists vout; split; [| split; [exact Hsc_out |]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hevc, Hev1, Hev2; cbn [eou_bind]; exact Hev_sel.
           ++ cbn [denote_exp]; eapply pure_mcfg_steps_bind; [exact Hstc |].
              eapply pure_mcfg_steps_bind; [exact Hst1 |].
              eapply pure_mcfg_steps_bind; [exact Hst2 |].
              rewrite Hev_sel; apply PMS_Ret; reflexivity.
  - intros dt e1 _ penv lmap env top w ce _ Hr; cbn [reify_pure_exp] in Hr; discriminate Hr.
  - intros o; destruct o; try exact I;
      intros penv lmap env top w ce Henv Hr; cbn [reify_pure_exp] in Hr; try discriminate.
    + destruct id as [| r]; [discriminate |].
      destruct (RM.find r lmap) as [[wr cer] |] eqn:Hf; [| discriminate].
      destruct (check_opt_int_width top wr) eqn:Hcw; [| discriminate].
      inversion Hr; subst wr ce; clear Hr.
      destruct (Henv r w cer Hf) as [dv [Hfe [Hev Hsc]]].
      right; exists dv; split; [exact Hev | split; [exact Hsc |]].
      cbn [denote_exp lookup_id]; eapply PMS_LocalRead; [reflexivity | exact Hfe | apply PMS_Ret; reflexivity].
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce; clear Hr.
      right; exists (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N (reify_int_const w (denote_int_syntax x)))))).
      split; [reflexivity | split; [right; eexists; reflexivity |]].
      cbn [denote_exp]; rewrite repr_reify_int_const; apply PMS_Ret; reflexivity.
    + destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
      inversion Hr; subst w ce; clear Hr.
      right; destruct b.
      * exists (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.repr 1%positive (Z.of_N 1%N)))).
        split; [reflexivity | split; [right; eexists; reflexivity |]].
        cbn [denote_exp]; rewrite repr_one_N; apply PMS_Ret; reflexivity.
      * exists (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.repr 1%positive (Z.of_N 0%N)))).
        split; [reflexivity | split; [right; eexists; reflexivity |]].
        cbn [denote_exp]; rewrite repr_zero_N; apply PMS_Ret; reflexivity.
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce; clear Hr.
      right; exists (DVALUE_Base DVALUE_Poison).
      split; [reflexivity | split; [left; reflexivity | apply PMS_Ret; reflexivity]].
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce; clear Hr.
      right; exists (DVALUE_Base DVALUE_Poison).
      split; [reflexivity | split; [left; reflexivity | apply PMS_Ret; reflexivity]].
Qed.

Fixpoint reify_pure_phis
  (bid_from : block_id)
  (lmap : rmap (positive * cert_expr))
  (phis : list (local_id * phi dtyp * list metadata))
  {struct phis} : option (list (raw_id * positive * cert_expr)) :=
  match phis with
  | [] => Some []
  | (id, Phi _ (DTYPE_Base (DTYPE_I w)) pargs, _) :: rest =>
      if is_supported_bit_width w then
        match assoc bid_from pargs with
        | Some op =>
            match reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) op,
                  reify_pure_phis bid_from lmap rest with
            | Some (_, ce), Some rrest => Some ((id, w, ce) :: rrest)
            | _, _ => None
            end
        | None => None
        end
      else None
  | _ :: _ => None
  end.

Definition wf_pure_eval_entry (allowed : list (string * positive)) (ce : cert_expr) : Prop :=
  wt_cert_expr [] ce = true /\
  is_let_free_expr ce = true /\
  incl (collect_free_vars [] ce) allowed.

Lemma reify_pure_phis_typing :
  forall phis allowed bid_from lmap pevals,
    wf_pure_lmap allowed lmap ->
    reify_pure_phis bid_from lmap phis = Some pevals ->
    Forall (fun '(_, w, ce) =>
      is_supported_bit_width w = true /\
      cert_expr_bit_width ce = w /\
      wf_pure_eval_entry allowed ce) pevals.
Proof.
  induction phis as [| [[id [fm dt pargs]] md] rest IH];
    intros allowed bid_from lmap pevals Hlmap Hr;
    cbn [reify_pure_phis] in Hr.
  - inversion Hr; constructor.
  - destruct dt as [tb | |]; try discriminate; destruct tb as [w | | | | | | | | | |]; try discriminate.
    destruct (is_supported_bit_width w) eqn:Hsup; [| discriminate].
    destruct (assoc bid_from pargs) as [op |] eqn:Hassoc; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) op) as [[w1 ce] |] eqn:Hre; [| discriminate].
    destruct (reify_pure_phis bid_from lmap rest) as [rrest |] eqn:Hrr; [| discriminate].
    inversion Hr; subst pevals; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hre)) as ->.
    destruct (reify_pure_exp_typing op allowed lmap (Some (DTYPE_Base (DTYPE_I w))) w ce Hlmap Hre)
      as (_ & Hwt & Hbw & Hlf & Hfv).
    constructor; [repeat split; assumption | exact (IH allowed bid_from lmap rrest Hlmap Hrr)].
Qed.

Lemma eval_reified_pure_phis {Pa : Params} :
  forall phis (penv : param_env Pa) bid_from lmap (env : rmap (@dvalue Pa)) pevals,
    lmap_matches_env penv lmap env ->
    reify_pure_phis bid_from lmap phis = Some pevals ->
    ((forall sigma, cfg_steps_to_ub sigma env (map_monad (m := CFGtop) (denote_phi bid_from) phis)) /\
     exists id w ce msg,
       In (id, w, ce) pevals /\
       eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ub msg) \/
    (exists dvs,
       Forall2 (phi_eval_pair_matches penv dummy_freeze_oracle) pevals dvs /\
       pure_cfg_steps env (map_monad (m := CFGtop) (denote_phi bid_from) phis) env dvs).
Proof.
  induction phis as [| [[id [fm dt pargs]] md] rest IH];
    intros penv bid_from lmap env pevals Henv Hr;
    cbn [reify_pure_phis] in Hr.
  - inversion Hr; subst pevals; right; exists []; split; [constructor | apply PCS_Ret; reflexivity].
  - destruct dt as [tb | |]; try discriminate; destruct tb as [w | | | | | | | | | |]; try discriminate.
    destruct (is_supported_bit_width w); [| discriminate].
    destruct (assoc bid_from pargs) as [op |] eqn:Hassoc; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) op) as [[w1 ce] |] eqn:Hre; [| discriminate].
    destruct (reify_pure_phis bid_from lmap rest) as [rrest |] eqn:Hrr; [| discriminate].
    inversion Hr; subst pevals; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hre)) as ->.
    destruct (eval_reified_pure_exp op penv lmap env (Some (DTYPE_Base (DTYPE_I w))) w ce Henv Hre)
      as [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]].
    + left; split.
      * intros sigma; cbn [map_monad denote_phi]; rewrite Hassoc; unfold denote_exp'.
        apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub1 sigma).
      * exists id, w, ce, msg1; split; [left; reflexivity | exact Hev1].
    + destruct (IH penv bid_from lmap env rrest Henv Hrr)
        as [[Hub2 (id2 & w2 & ce2 & msg2 & Hin2 & Hev2)] | [dvs_r [Hpm_r Hst_r]]].
      * left; split.
        -- intros sigma; cbn [map_monad denote_phi]; rewrite Hassoc; unfold denote_exp'.
           eapply cfg_steps_to_ub_bind_r.
           ++ eapply cfg_steps_to_ret_bind;
                [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1))
                | apply CSR_Ret; reflexivity].
           ++ apply cfg_steps_to_ub_bind_l; exact (Hub2 sigma).
        -- exists id2, w2, ce2, msg2; split; [right; exact Hin2 | exact Hev2].
      * right; exists ((id, dv1) :: dvs_r); split.
        -- constructor; [split; [reflexivity | split; assumption] | exact Hpm_r].
        -- cbn [map_monad denote_phi]; rewrite Hassoc; unfold denote_exp'.
           eapply pure_cfg_steps_bind.
           ++ eapply pure_cfg_steps_bind; [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst1) | apply PCS_Ret; reflexivity].
           ++ eapply pure_cfg_steps_bind; [exact Hst_r | apply PCS_Ret; reflexivity].
Qed.

Fixpoint reify_pure_code
  (lmap : rmap (positive * cert_expr))
  (c : code dtyp)
  {struct c} : option (list cert_expr * rmap (positive * cert_expr)) :=
  match c with
  | [] => Some ([], lmap)
  | (IId id, INSTR_Op op, _) :: rest =>
      match reify_pure_exp lmap None op with
      | Some (w, ce) =>
          match reify_pure_code (RM.add id (w, ce) lmap) rest with
          | Some (cevals, lmap2) => Some (ce :: cevals, lmap2)
          | None => None
          end
      | None => None
      end
  | (IVoid _, INSTR_Comment _, _) :: rest =>
      reify_pure_code lmap rest
  | _ :: _ => None
  end.

Definition code_written_ids (c : code dtyp) : list raw_id :=
  List.flat_map (fun '(iid, _, _) =>
    match iid with
    | IId id => [id]
    | IVoid _ => []
    end) c.

Lemma wf_pure_lmap_add :
  forall allowed lmap id w ce,
    wf_pure_lmap allowed lmap ->
    wt_cert_expr [] ce = true ->
    cert_expr_bit_width ce = w ->
    is_let_free_expr ce = true ->
    incl (collect_free_vars [] ce) allowed ->
    wf_pure_lmap allowed (RM.add id (w, ce) lmap).
Proof.
  intros allowed lmap id w ce Hlmap Hwt Hbw Hlf Hfv r wr cer Hf.
  destruct (RawIDOrd.eq_dec id r) as [Heq | Hneq].
  - rewrite RMF.F.add_eq_o in Hf by exact Heq; inversion Hf; subst wr cer; repeat split; assumption.
  - rewrite RMF.F.add_neq_o in Hf by exact Hneq; exact (Hlmap r wr cer Hf).
Qed.

Lemma reify_pure_code_typing :
  forall c allowed lmap0 cevals lmap2,
    wf_pure_lmap allowed lmap0 ->
    reify_pure_code lmap0 c = Some (cevals, lmap2) ->
    Forall (wf_pure_eval_entry allowed) cevals /\
    wf_pure_lmap allowed lmap2.
Proof.
  induction c as [| [[iid ins] md] rest IH];
    intros allowed lmap0 cevals lmap2 Hlmap0 Hr;
    cbn [reify_pure_code] in Hr.
  - inversion Hr; subst; split; [constructor | exact Hlmap0].
  - destruct iid as [id | vid]; destruct ins; try discriminate Hr.
    + destruct (reify_pure_exp lmap0 None op) as [[w ce] |] eqn:Hre; [| discriminate].
      destruct (reify_pure_code (RM.add id (w, ce) lmap0) rest) as [[cevals_r lmap2'] |] eqn:Hrr; [| discriminate].
      inversion Hr; subst cevals lmap2'; clear Hr.
      destruct (reify_pure_exp_typing op allowed lmap0 None w ce Hlmap0 Hre)
        as (_ & Hwt & Hbw & Hlf & Hfv).
      pose proof (wf_pure_lmap_add allowed lmap0 id w ce Hlmap0 Hwt Hbw Hlf Hfv) as Hlmap1.
      destruct (IH allowed (RM.add id (w, ce) lmap0) cevals_r lmap2 Hlmap1 Hrr) as [Hfa Hlmap2].
      split; [constructor; [repeat split; assumption | exact Hfa] | exact Hlmap2].
    + exact (IH allowed lmap0 cevals lmap2 Hlmap0 Hr).
Qed.

Lemma eval_reified_pure_code {Pa : Params} :
  forall c (varargs : option (@ptr _ (@PTR Pa))) (penv : param_env Pa)
         lmap0 (env0 : rmap (@dvalue Pa)) cevals lmap2,
    lmap_matches_env penv lmap0 env0 ->
    reify_pure_code lmap0 c = Some (cevals, lmap2) ->
    ((forall sigma, cfg_steps_to_ub sigma env0 (denote_code c varargs)) /\
     exists ce msg,
       In ce cevals /\
       eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ub msg) \/
    (exists env2,
       lmap_matches_env penv lmap2 env2 /\
       Forall (fun ce => exists dv, eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv) cevals /\
       (forall r, ~ In r (code_written_ids c) -> RM.find r env2 = RM.find r env0) /\
       pure_cfg_steps env0 (denote_code c varargs) env2 tt).
Proof.
  induction c as [| [[iid ins] md] rest IH];
    intros varargs penv lmap0 env0 cevals lmap2 Henv0 Hr;
    cbn [reify_pure_code] in Hr.
  - inversion Hr; subst cevals lmap2; right; exists env0.
    split; [exact Henv0 | split; [constructor | split; [intros _ _; reflexivity | apply PCS_Ret; reflexivity]]].
  - destruct iid as [id | vid]; destruct ins; try discriminate Hr.
    + destruct (reify_pure_exp lmap0 None op) as [[w ce] |] eqn:Hre; [| discriminate].
      destruct (reify_pure_code (RM.add id (w, ce) lmap0) rest) as [[cevals_r lmap2'] |] eqn:Hrr; [| discriminate].
      inversion Hr; subst cevals lmap2'; clear Hr.
      destruct (eval_reified_pure_exp op penv lmap0 env0 None w ce Henv0 Hre)
        as [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]].
      * left; split.
        -- intros sigma; unfold denote_code; cbn [loop_monad denote_instr]; unfold denote_exp'.
           apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub1 sigma).
        -- exists ce, msg1; split; [left; reflexivity | exact Hev1].
      * pose proof (lmap_matches_env_add penv lmap0 env0 id w ce dv1 Henv0 Hev1 Hsc1) as Henv1.
        destruct (IH varargs penv (RM.add id (w, ce) lmap0) (RM.add id dv1 env0) cevals_r lmap2 Henv1 Hrr)
          as [[Hub2 (ce2 & msg2 & Hin2 & Hev2)] | (env2 & Henv2 & Hfa2 & Hpres2 & Hst2)].
        -- left; split.
           ++ intros sigma; unfold denote_code; cbn [loop_monad denote_instr]; unfold denote_exp'.
              eapply cfg_steps_to_ub_bind_r.
              ** eapply cfg_steps_to_ret_bind;
                   [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1)) |].
                 eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite | apply CSR_Ret; reflexivity].
              ** exact (Hub2 sigma).
           ++ exists ce2, msg2; split; [right; exact Hin2 | exact Hev2].
        -- right; exists env2; split; [exact Henv2 | split; [| split]].
           ++ constructor; [exists dv1; exact Hev1 | exact Hfa2].
           ++ intros r Hnin; cbn [code_written_ids] in Hnin.
              rewrite (Hpres2 r (fun Hin => Hnin (or_intror Hin))).
              rewrite RMF.F.add_neq_o; [reflexivity | intros ->; exact (Hnin (or_introl eq_refl))].
           ++ unfold denote_code; cbn [loop_monad denote_instr]; unfold denote_exp'.
              eapply pure_cfg_steps_bind.
              ** eapply pure_cfg_steps_bind; [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst1) |].
                 eapply pure_cfg_steps_bind; [apply pure_cfg_steps_lwrite | apply PCS_Ret; reflexivity].
              ** exact Hst2.
    + destruct (IH varargs penv lmap0 env0 cevals lmap2 Henv0 Hr)
        as [[Hub2 Hce2] | (env2 & Henv2 & Hfa2 & Hpres2 & Hst2)].
      * left; split; [| exact Hce2].
        intros sigma; unfold denote_code; cbn [loop_monad denote_instr].
        eapply cfg_steps_to_ub_bind_r; [apply CSR_Ret; reflexivity | exact (Hub2 sigma)].
      * right; exists env2; repeat split; try assumption.
        unfold denote_code; cbn [loop_monad denote_instr].
        eapply pure_cfg_steps_bind; [apply PCS_Ret; reflexivity | exact Hst2].
Qed.

(** **** Relational Cut-State Bijection & Coinductive Natural-Loop Checker ([F-26]) *)

Definition cut_p_name (k : nat) : string := ("!p" ++ show_Z_dec (Z.of_nat k))%string.
Definition cut_v_name (k : nat) : string := ("!v" ++ show_Z_dec (Z.of_nat k))%string.

Lemma cut_p_name_not_dollar : forall k, starts_with_dollar (cut_p_name k) = false.
Proof. reflexivity. Qed.

Lemma cut_v_name_not_dollar : forall k, starts_with_dollar (cut_v_name k) = false.
Proof. reflexivity. Qed.

Definition cut_src_expr (k : nat) (w : positive) : cert_expr :=
  CE_Select w (CE_Var (cut_p_name k) 1%positive) (CE_Var (cut_v_name k) w) (CE_Poison w).

Definition cut_tgt_expr (k : nat) (w : positive) : cert_expr :=
  CE_Var (cut_v_name k) w.

Fixpoint extend_penv {Pa : Params}
  (bs : list (string * @dvalue Pa)) (penv : param_env Pa)
  {struct bs} : param_env Pa :=
  match bs with
  | [] => penv
  | (nm, dv) :: rest =>
      fun q => if String.eqb q nm then Some dv else extend_penv rest penv q
  end.

Lemma extend_penv_not_in {Pa : Params} :
  forall bs (penv : param_env Pa) q,
    ~ In q (List.map fst bs) ->
    extend_penv bs penv q = penv q.
Proof.
  induction bs as [| [nm dv] rest IH]; intros penv q Hnin; cbn in *; [reflexivity |].
  destruct (String.eqb q nm) eqn:Eq.
  - apply String.eqb_eq in Eq; exfalso; exact (Hnin (or_introl (eq_sym Eq))).
  - exact (IH penv q (fun H => Hnin (or_intror H))).
Qed.

Lemma extend_penv_nodup_in {Pa : Params} :
  forall bs (penv : param_env Pa) nm dv,
    NoDup (List.map fst bs) ->
    In (nm, dv) bs ->
    extend_penv bs penv nm = Some dv.
Proof.
  induction bs as [| [nm0 dv0] rest IH]; intros penv nm dv Hnd Hin; cbn in *; [contradiction |].
  inversion Hnd as [| ? ? Hnin Hndr]; subst.
  destruct Hin as [Heq | Hin_r].
  - inversion Heq; subst nm0 dv0; rewrite String.eqb_refl; reflexivity.
  - destruct (String.eqb nm nm0) eqn:Eq.
    + apply String.eqb_eq in Eq; subst nm0.
      exfalso; apply Hnin; exact (in_map fst rest (nm, dv) Hin_r).
    + exact (IH penv nm dv Hndr Hin_r).
Qed.

Lemma eval_let_free_penv_agree {Pa : Params} :
  forall (ce : cert_expr) (penv1 penv2 : param_env Pa) foracle,
    is_let_free_expr ce = true ->
    (forall nm w, In (nm, w) (collect_free_vars [] ce) -> penv1 nm = penv2 nm) ->
    eval_closed_cert_expr penv1 foracle ce = eval_closed_cert_expr penv2 foracle ce.
Proof.
  unfold eval_closed_cert_expr.
  induction ce as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros penv1 penv2 foracle Hlf Hag;
    cbn [is_let_free_expr collect_free_vars eval_cert_expr lookup_let_val] in Hlf, Hag |- *;
    try reflexivity; try discriminate Hlf.
  - destruct (starts_with_dollar nm); [reflexivity |].
    rewrite (Hag nm w (or_introl eq_refl)); reflexivity.
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    rewrite (IHl penv1 penv2 foracle Hlfl (fun n w0 H => Hag n w0 (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHr penv1 penv2 foracle Hlfr (fun n w0 H => Hag n w0 (proj2 (in_app_iff _ _ _) (or_intror H)))).
    reflexivity.
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    rewrite (IHl penv1 penv2 foracle Hlfl (fun n w0 H => Hag n w0 (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHr penv1 penv2 foracle Hlfr (fun n w0 H => Hag n w0 (proj2 (in_app_iff _ _ _) (or_intror H)))).
    reflexivity.
  - rewrite (IHo penv1 penv2 foracle Hlf Hag); reflexivity.
  - rewrite !andb_true_iff in Hlf; destruct Hlf as ([Hlfc Hlft] & Hlff).
    rewrite (IHc penv1 penv2 foracle Hlfc (fun n w0 H => Hag n w0 (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHt penv1 penv2 foracle Hlft (fun n w0 H => Hag n w0 (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl H)))))).
    rewrite (IHf penv1 penv2 foracle Hlff (fun n w0 H => Hag n w0 (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_intror H)))))).
    reflexivity.
  - rewrite (IHo penv1 penv2 foracle Hlf Hag); reflexivity.
Qed.

Lemma bit1_zero_unsigned :
  (@Integers.unsigned 1%positive (@Integers.zero 1%positive) =? 1)%Z = false.
Proof.
  rewrite (@Integers.unsigned_zero 1%positive); reflexivity.
Qed.

Lemma bit1_one_unsigned :
  (@Integers.unsigned 1%positive (@Integers.one 1%positive) =? 1)%Z = true.
Proof.
  unfold Integers.one; rewrite (@Integers.unsigned_repr 1%positive 1); [reflexivity |].
  unfold Integers.max_unsigned.
  rewrite (@Integers.modulus_two_power_nat 1%positive), (@Integers.natwordsize_def 1%positive).
  vm_compute; split; discriminate.
Qed.

Definition cut_p_dvalue {Pa : Params} (dv_s : @dvalue Pa) : @dvalue Pa :=
  match dv_s with
  | DVALUE_Base DVALUE_Poison => DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.zero 1%positive))
  | _ => DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive))
  end.

Lemma eval_cut_pair {Pa : Params} :
  forall (penv : param_env Pa) k w (dv_s dv_t : @dvalue Pa),
    wf_scalar_dvalue w dv_s ->
    wf_scalar_dvalue w dv_t ->
    dvalue_refines dv_s dv_t ->
    penv (cut_p_name k) = Some (cut_p_dvalue dv_s) ->
    penv (cut_v_name k) = Some dv_t ->
    eval_closed_cert_expr penv dummy_freeze_oracle (cut_src_expr k w) = raise_ret dv_s /\
    eval_closed_cert_expr penv dummy_freeze_oracle (cut_tgt_expr k w) = raise_ret dv_t.
Proof.
  intros penv k w dv_s dv_t Hsc_s Hsc_t Href Hp Hv.
  assert (Hev_t : eval_closed_cert_expr penv dummy_freeze_oracle (cut_tgt_expr k w) = raise_ret dv_t).
  { unfold cut_tgt_expr, eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val].
    rewrite Hv.
    destruct Hsc_t as [-> | [it ->]];
      [reflexivity | cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity]. }
  split; [| exact Hev_t].
  unfold cut_src_expr, eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val].
  rewrite Hp; fold (eval_closed_cert_expr penv dummy_freeze_oracle (cut_tgt_expr k w)); rewrite Hev_t.
  destruct Hsc_s as [-> | [is0 ->]].
  - cbn [cut_p_dvalue check_scalar_width eou_bind eval_select]; rewrite bit1_zero_unsigned; reflexivity.
  - destruct Href as [Habs | <-]; [discriminate Habs |].
    cbn [cut_p_dvalue check_scalar_width eou_bind eval_select]; rewrite bit1_one_unsigned; reflexivity.
Qed.

Fixpoint cut_names_from (idx : nat) (pspecs : list (raw_id * raw_id * positive))
  {struct pspecs} : list string :=
  match pspecs with
  | [] => []
  | _ :: rest => cut_p_name idx :: cut_v_name idx :: cut_names_from (S idx) rest
  end.

Fixpoint cut_vars_from (idx : nat) (pspecs : list (raw_id * raw_id * positive))
  {struct pspecs} : list (string * positive) :=
  match pspecs with
  | [] => []
  | (_, _, w) :: rest =>
      (cut_p_name idx, 1%positive) :: (cut_v_name idx, w) :: cut_vars_from (S idx) rest
  end.

Fixpoint cut_bindings_from {Pa : Params}
  (idx : nat)
  (pspecs : list (raw_id * raw_id * positive))
  (dvs_s dvs_t : list (raw_id * @dvalue Pa))
  {struct pspecs} : list (string * @dvalue Pa) :=
  match pspecs, dvs_s, dvs_t with
  | _ :: rp, (_, dv_s) :: rs, (_, dv_t) :: rt =>
      (cut_p_name idx, cut_p_dvalue dv_s) ::
      (cut_v_name idx, dv_t) ::
      cut_bindings_from (S idx) rp rs rt
  | _, _, _ => []
  end.

Fixpoint overlay_cut_lmap_s
  (idx : nat) (lmap : rmap (positive * cert_expr))
  (pspecs : list (raw_id * raw_id * positive))
  {struct pspecs} : rmap (positive * cert_expr) :=
  match pspecs with
  | [] => lmap
  | (id_s, _, w) :: rest =>
      overlay_cut_lmap_s (S idx) (RM.add id_s (w, cut_src_expr idx w) lmap) rest
  end.

Fixpoint overlay_cut_lmap_t
  (idx : nat) (lmap : rmap (positive * cert_expr))
  (pspecs : list (raw_id * raw_id * positive))
  {struct pspecs} : rmap (positive * cert_expr) :=
  match pspecs with
  | [] => lmap
  | (_, id_t, w) :: rest =>
      overlay_cut_lmap_t (S idx) (RM.add id_t (w, cut_tgt_expr idx w) lmap) rest
  end.

Inductive cut_phi_rel {Pa : Params}
  : list (raw_id * raw_id * positive) ->
    list (raw_id * @dvalue Pa) ->
    list (raw_id * @dvalue Pa) -> Prop :=
| CPR_Nil : cut_phi_rel [] [] []
| CPR_Cons id_s id_t w dv_s dv_t rest rs rt :
    is_supported_bit_width w = true ->
    wf_scalar_dvalue w dv_s ->
    wf_scalar_dvalue w dv_t ->
    dvalue_refines dv_s dv_t ->
    cut_phi_rel rest rs rt ->
    cut_phi_rel ((id_s, id_t, w) :: rest) ((id_s, dv_s) :: rs) ((id_t, dv_t) :: rt).

Lemma cut_bindings_fst {Pa : Params} :
  forall pspecs (dvs_s dvs_t : list (raw_id * @dvalue Pa)) idx,
    cut_phi_rel pspecs dvs_s dvs_t ->
    List.map fst (cut_bindings_from idx pspecs dvs_s dvs_t) = cut_names_from idx pspecs.
Proof.
  intros pspecs dvs_s dvs_t idx Hrel; revert idx.
  induction Hrel as [| id_s id_t w dv_s dv_t rest rs rt _ _ _ _ _ IH]; intros idx; cbn; [reflexivity |].
  f_equal; f_equal; exact (IH (S idx)).
Qed.

Lemma overlay_cut_lmap_typing :
  forall pspecs idx allowed lmap_s lmap_t,
    Forall (fun '(_, _, w) => is_supported_bit_width w = true) pspecs ->
    incl (cut_vars_from idx pspecs) allowed ->
    wf_pure_lmap allowed lmap_s ->
    wf_pure_lmap allowed lmap_t ->
    wf_pure_lmap allowed (overlay_cut_lmap_s idx lmap_s pspecs) /\
    wf_pure_lmap allowed (overlay_cut_lmap_t idx lmap_t pspecs).
Proof.
  induction pspecs as [| [[id_s id_t] w] rest IH];
    intros idx allowed lmap_s lmap_t Hfa Hinc Hs Ht; cbn [overlay_cut_lmap_s overlay_cut_lmap_t cut_vars_from] in *.
  - split; assumption.
  - inversion Hfa as [| ? ? Hsup Hfa_r]; subst.
    assert (Hin_p : In (cut_p_name idx, 1%positive) allowed) by (apply Hinc; left; reflexivity).
    assert (Hin_v : In (cut_v_name idx, w) allowed) by (apply Hinc; right; left; reflexivity).
    assert (Hinc_r : incl (cut_vars_from (S idx) rest) allowed)
      by (intros u Hu; apply Hinc; right; right; exact Hu).
    assert (Hs' : wf_pure_lmap allowed (RM.add id_s (w, cut_src_expr idx w) lmap_s)).
    { apply wf_pure_lmap_add; try assumption.
      - unfold cut_src_expr; cbn [wt_cert_expr cert_expr_bit_width].
        rewrite cut_p_name_not_dollar, cut_v_name_not_dollar, Hsup, !Pos.eqb_refl; reflexivity.
      - reflexivity.
      - reflexivity.
      - intros u Hu; cbn [cut_src_expr collect_free_vars] in Hu.
        rewrite cut_p_name_not_dollar, cut_v_name_not_dollar in Hu; cbn in Hu.
        destruct Hu as [<- | [<- | []]]; assumption. }
    assert (Ht' : wf_pure_lmap allowed (RM.add id_t (w, cut_tgt_expr idx w) lmap_t)).
    { apply wf_pure_lmap_add; try assumption.
      - unfold cut_tgt_expr; cbn [wt_cert_expr]; rewrite cut_v_name_not_dollar, Hsup; reflexivity.
      - reflexivity.
      - reflexivity.
      - intros u Hu; cbn [cut_tgt_expr collect_free_vars] in Hu.
        rewrite cut_v_name_not_dollar in Hu; destruct Hu as [<- | []]; exact Hin_v. }
    exact (IH (S idx) allowed _ _ Hfa_r Hinc_r Hs' Ht').
Qed.

Lemma cut_p_dvalue_wf_1 {Pa : Params} :
  forall (dv : @dvalue Pa), wf_scalar_dvalue 1%positive (cut_p_dvalue dv).
Proof.
  intros dv; unfold cut_p_dvalue; destruct dv as [db | |];
    try (right; eexists; reflexivity);
    destruct db; right; eexists; reflexivity.
Qed.

Lemma cut_bindings_wf_param {Pa : Params} :
  forall pspecs (dvs_s dvs_t : list (raw_id * @dvalue Pa)) idx
         (all_bs : list (string * @dvalue Pa)) (penv : param_env Pa),
    cut_phi_rel pspecs dvs_s dvs_t ->
    NoDup (List.map fst all_bs) ->
    incl (cut_bindings_from idx pspecs dvs_s dvs_t) all_bs ->
    wf_param_env_for (cut_vars_from idx pspecs) (extend_penv all_bs penv).
Proof.
  intros pspecs dvs_s dvs_t idx all_bs penv Hrel Hnd.
  revert idx; induction Hrel as [| id_s id_t w dv_s dv_t rest rs rt _ Hsc_s Hsc_t _ _ IH];
    intros idx Hinc nm w0 Hin; cbn [cut_vars_from cut_bindings_from] in *.
  - contradiction Hin.
  - destruct Hin as [Heq | [Heq | Hin_r]].
    + inversion Heq; subst nm w0.
      exists (cut_p_dvalue dv_s); split;
        [apply extend_penv_nodup_in; [exact Hnd | apply Hinc; left; reflexivity]
        | apply cut_p_dvalue_wf_1].
    + inversion Heq; subst nm w0.
      exists dv_t; split;
        [apply extend_penv_nodup_in; [exact Hnd | apply Hinc; right; left; reflexivity]
        | exact Hsc_t].
    + exact (IH (S idx) (fun u Hu => Hinc u (or_intror (or_intror Hu))) nm w0 Hin_r).
Qed.

Lemma overlay_cut_lmap_matches {Pa : Params} :
  forall pspecs (dvs_s dvs_t : list (raw_id * @dvalue Pa)) idx
         (all_bs : list (string * @dvalue Pa)) (penv : param_env Pa)
         lmap_s lmap_t env_s env_t,
    cut_phi_rel pspecs dvs_s dvs_t ->
    NoDup (List.map fst all_bs) ->
    incl (cut_bindings_from idx pspecs dvs_s dvs_t) all_bs ->
    lmap_matches_env (extend_penv all_bs penv) lmap_s env_s ->
    lmap_matches_env (extend_penv all_bs penv) lmap_t env_t ->
    lmap_matches_env (extend_penv all_bs penv)
      (overlay_cut_lmap_s idx lmap_s pspecs) (apply_phi_env env_s dvs_s) /\
    lmap_matches_env (extend_penv all_bs penv)
      (overlay_cut_lmap_t idx lmap_t pspecs) (apply_phi_env env_t dvs_t).
Proof.
  intros pspecs dvs_s dvs_t idx all_bs penv lmap_s lmap_t env_s env_t Hrel Hnd.
  revert idx lmap_s lmap_t env_s env_t.
  induction Hrel as [| id_s id_t w dv_s dv_t rest rs rt _ Hsc_s Hsc_t Href _ IH];
    intros idx lmap_s lmap_t env_s env_t Hinc Hs Ht;
    cbn [overlay_cut_lmap_s overlay_cut_lmap_t apply_phi_env cut_bindings_from] in *.
  - split; assumption.
  - assert (Hp : extend_penv all_bs penv (cut_p_name idx) = Some (cut_p_dvalue dv_s))
      by (apply extend_penv_nodup_in; [exact Hnd | apply Hinc; left; reflexivity]).
    assert (Hv : extend_penv all_bs penv (cut_v_name idx) = Some dv_t)
      by (apply extend_penv_nodup_in; [exact Hnd | apply Hinc; right; left; reflexivity]).
    destruct (eval_cut_pair (extend_penv all_bs penv) idx w dv_s dv_t Hsc_s Hsc_t Href Hp Hv)
      as [Hev_s Hev_t].
    exact (IH (S idx)
             (RM.add id_s (w, cut_src_expr idx w) lmap_s)
             (RM.add id_t (w, cut_tgt_expr idx w) lmap_t)
             (RM.add id_s dv_s env_s)
             (RM.add id_t dv_t env_t)
             (fun u Hu => Hinc u (or_intror (or_intror Hu)))
             (lmap_matches_env_add _ _ _ _ _ _ _ Hs Hev_s Hsc_s)
             (lmap_matches_env_add _ _ _ _ _ _ _ Ht Hev_t Hsc_t)).
Qed.

Fixpoint init_param_lmap
  (params : list raw_id) (src_pnames : list string) (uses : list (nat * dtyp))
  {struct uses} : rmap (positive * cert_expr) :=
  match uses with
  | [] => RM.empty _
  | (idx, DTYPE_Base (DTYPE_I w)) :: rest =>
      let rmap_r := init_param_lmap params src_pnames rest in
      if is_supported_bit_width w then
        match nth_error params idx, nth_error src_pnames idx with
        | Some r, Some pnm =>
            if starts_with_dollar pnm then rmap_r
            else RM.add r (w, CE_Var pnm w) rmap_r
        | _, _ => rmap_r
        end
      else rmap_r
  | _ :: rest => init_param_lmap params src_pnames rest
  end.

Lemma init_param_lmap_typing :
  forall uses params src_pnames allowed,
    (forall idx w pnm,
      In (idx, DTYPE_Base (DTYPE_I w)) uses ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w) allowed) ->
    wf_pure_lmap allowed (init_param_lmap params src_pnames uses).
Proof.
  induction uses as [| [idx dt] rest IH]; intros params src_pnames allowed Hpu;
    cbn [init_param_lmap].
  - intros r w ce Hf; rewrite RMF.F.empty_o in Hf; discriminate Hf.
  - pose proof (IH params src_pnames allowed (fun i w0 p Hin => Hpu i w0 p (or_intror Hin))) as Hrest.
    destruct dt as [tb | |]; try exact Hrest; destruct tb as [w | | | | | | | | | |]; try exact Hrest.
    destruct (is_supported_bit_width w) eqn:Hsup; [| exact Hrest].
    destruct (nth_error params idx) as [r |]; [| exact Hrest].
    destruct (nth_error src_pnames idx) as [pnm |] eqn:Hpnm; [| exact Hrest].
    destruct (starts_with_dollar pnm) eqn:Ed; [exact Hrest |].
    apply wf_pure_lmap_add; [exact Hrest | cbn; rewrite Ed, Hsup; reflexivity | reflexivity | reflexivity |].
    intros u Hu; cbn [collect_free_vars] in Hu; rewrite Ed in Hu; destruct Hu as [<- | []].
    exact (Hpu idx w pnm (or_introl eq_refl) Hpnm).
Qed.

Lemma init_param_lmap_dom :
  forall uses params src_pnames r w ce,
    RM.find r (init_param_lmap params src_pnames uses) = Some (w, ce) ->
    In r params.
Proof.
  induction uses as [| [idx dt] rest IH]; intros params src_pnames r w ce Hf;
    cbn [init_param_lmap] in Hf.
  - rewrite RMF.F.empty_o in Hf; discriminate Hf.
  - destruct dt as [tb | |]; try exact (IH _ _ _ _ _ Hf);
      destruct tb as [w0 | | | | | | | | | |]; try exact (IH _ _ _ _ _ Hf).
    destruct (is_supported_bit_width w0); [| exact (IH _ _ _ _ _ Hf)].
    destruct (nth_error params idx) as [r0 |] eqn:Hnth; [| exact (IH _ _ _ _ _ Hf)].
    destruct (nth_error src_pnames idx) as [pnm |]; [| exact (IH _ _ _ _ _ Hf)].
    destruct (starts_with_dollar pnm); [exact (IH _ _ _ _ _ Hf) |].
    destruct (RawIDOrd.eq_dec r0 r) as [Heq | Hneq].
    + subst r0; exact (nth_error_In params idx Hnth).
    + rewrite RMF.F.add_neq_o in Hf by exact Hneq; exact (IH _ _ _ _ _ Hf).
Qed.

Lemma init_param_lmap_matches {Pa : Params} :
  forall uses params src_pnames arg_dtys (vs : list (@dvalue Pa)),
    NoDup params ->
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx dt, In (idx, dt) uses -> nth_error arg_dtys idx = Some dt) ->
    lmap_matches_env (build_param_env src_pnames vs)
      (init_param_lmap params src_pnames uses)
      (init_cfg_locals params vs).
Proof.
  induction uses as [| [idx dt] rest IH];
    intros params src_pnames arg_dtys vs Hnd_p Hnd_s Hlp Hls Hvs Hdt;
    cbn [init_param_lmap].
  - intros r w ce Hf; rewrite RMF.F.empty_o in Hf; discriminate Hf.
  - pose proof (IH params src_pnames arg_dtys vs Hnd_p Hnd_s Hlp Hls Hvs
                  (fun i d Hin => Hdt i d (or_intror Hin))) as Hrest.
    destruct dt as [tb | |]; try exact Hrest;
      destruct tb as [w | | | | | | | | | |]; try exact Hrest.
    destruct (is_supported_bit_width w) eqn:Hsup; [| exact Hrest].
    destruct (nth_error params idx) as [r0 |] eqn:Hnth_r; [| exact Hrest].
    destruct (nth_error src_pnames idx) as [pnm |] eqn:Hnth_p; [| exact Hrest].
    destruct (starts_with_dollar pnm) eqn:Ed; [exact Hrest |].
    destruct (init_cfg_locals_nth params vs idx r0 Hnd_p Hlp Hnth_r) as [dv [Hnth_v Hfe]].
    destruct (build_param_env_nth src_pnames vs idx pnm Hnd_s Hls Hnth_p) as [dv' [Hnth_v' Hp]].
    rewrite Hnth_v in Hnth_v'; injection Hnth_v' as <-.
    pose proof (Hdt idx (DTYPE_Base (DTYPE_I w)) (or_introl eq_refl)) as Hnth_dt.
    pose proof (Forall2_nth_error_l dvalue_has_dtyp vs arg_dtys Hvs idx dv (DTYPE_Base (DTYPE_I w)) Hnth_v Hnth_dt) as Hty.
    apply dvalue_has_dtyp_i_iff_wf_scalar in Hty.
    intros r wr cer Hf.
    destruct (RawIDOrd.eq_dec r0 r) as [Heq | Hneq].
    + rewrite RMF.F.add_eq_o in Hf by exact Heq; inversion Hf; subst r wr cer.
      exists dv; split; [exact Hfe | split; [| exact Hty]].
      unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite Ed, Hp.
      destruct Hty as [-> | [iv ->]];
        [reflexivity | cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity].
    + rewrite RMF.F.add_neq_o in Hf by exact Hneq; exact (Hrest r wr cer Hf).
Qed.

Lemma apply_phi_env_preserves_not_in {Pa : Params} :
  forall (dvs : list (raw_id * @dvalue Pa)) (env : rmap (@dvalue Pa)) r,
    ~ In r (List.map fst dvs) ->
    RM.find r (apply_phi_env env dvs) = RM.find r env.
Proof.
  induction dvs as [| [id dv] rest IH]; intros env r Hnin; cbn in *; [reflexivity |].
  rewrite (IH (RM.add id dv env) r (fun H => Hnin (or_intror H))).
  rewrite RMF.F.add_neq_o; [reflexivity | intros ->; exact (Hnin (or_introl eq_refl))].
Qed.

Lemma lmap_dom_code :
  forall c lmap0 cevals lmap2 dom0,
    (forall r w ce, RM.find r lmap0 = Some (w, ce) -> In r dom0) ->
    reify_pure_code lmap0 c = Some (cevals, lmap2) ->
    forall r w ce, RM.find r lmap2 = Some (w, ce) -> In r (dom0 ++ code_written_ids c).
Proof.
  induction c as [| [[iid ins] md] rest IH];
    intros lmap0 cevals lmap2 dom0 Hdom0 Hr r w ce Hf;
    cbn [reify_pure_code code_written_ids] in *.
  - inversion Hr; subst; rewrite app_nil_r; exact (Hdom0 r w ce Hf).
  - destruct iid as [id | vid]; destruct ins; try discriminate Hr.
    + destruct (reify_pure_exp lmap0 None op) as [[w0 ce0] |]; [| discriminate Hr].
      destruct (reify_pure_code (RM.add id (w0, ce0) lmap0) rest) as [[cr l2] |] eqn:Hrr; [| discriminate Hr].
      inversion Hr; subst cevals lmap2; clear Hr.
      assert (Hdom1 : forall r' w' ce', RM.find r' (RM.add id (w0, ce0) lmap0) = Some (w', ce') -> In r' (dom0 ++ [id])).
      { intros r' w' ce' Hf'.
        destruct (RawIDOrd.eq_dec id r') as [<- | Hneq].
        - apply in_app_iff; right; left; reflexivity.
        - rewrite RMF.F.add_neq_o in Hf' by exact Hneq; apply in_app_iff; left; exact (Hdom0 r' w' ce' Hf'). }
      pose proof (IH _ _ _ _ Hdom1 Hrr r w ce Hf) as Hin.
      rewrite <- app_assoc in Hin; exact Hin.
    + exact (IH _ _ _ _ Hdom0 Hr r w ce Hf).
Qed.

Lemma lmap_matches_env_transfer {Pa : Params} :
  forall allowed dom (penv1 penv2 : param_env Pa) lmap (env1 env2 : rmap (@dvalue Pa)),
    wf_pure_lmap allowed lmap ->
    (forall r w ce, RM.find r lmap = Some (w, ce) -> In r dom) ->
    (forall nm w, In (nm, w) allowed -> penv1 nm = penv2 nm) ->
    (forall r, In r dom -> RM.find r env2 = RM.find r env1) ->
    lmap_matches_env penv1 lmap env1 ->
    lmap_matches_env penv2 lmap env2.
Proof.
  intros allowed dom penv1 penv2 lmap env1 env2 Hwf Hdom Hp He Henv r w ce Hf.
  destruct (Henv r w ce Hf) as [dv [Hfe1 [Hev1 Hsc]]].
  destruct (Hwf r w ce Hf) as (_ & _ & Hlf & Hfv).
  exists dv; split; [rewrite (He r (Hdom r w ce Hf)); exact Hfe1 | split; [| exact Hsc]].
  rewrite <- (eval_let_free_penv_agree ce penv1 penv2 dummy_freeze_oracle Hlf
               (fun nm w0 Hin => Hp nm w0 (Hfv (nm, w0) Hin))).
  exact Hev1.
Qed.

Inductive pure_cfg_steps_to_tau {Pa : Params} {R : Type}
  : rmap (@dvalue Pa) -> CFGtop R -> rmap (@dvalue Pa) -> CFGtop R -> Prop :=
| PCT_Tau env (t m : CFGtop R) :
    observe t = TauF m ->
    pure_cfg_steps_to_tau env t env m
| PCT_StepTau env (t t' : CFGtop R) env' m :
    observe t = TauF t' ->
    pure_cfg_steps_to_tau env t' env' m ->
    pure_cfg_steps_to_tau env t env' m
| PCT_LocalRead env (t : CFGtop R) id dv (k : @dvalue Pa -> CFGtop R) env' m :
    observe t = VisF (@subevent LocalE CFGEtop _ (@dvalue Pa) (LocalRead id)) k ->
    RM.find id env = Some dv ->
    pure_cfg_steps_to_tau env (k dv) env' m ->
    pure_cfg_steps_to_tau env t env' m
| PCT_LocalWrite env (t : CFGtop R) id dv (k : unit -> CFGtop R) env' m :
    observe t = VisF (@subevent LocalE CFGEtop _ unit (LocalWrite id dv)) k ->
    pure_cfg_steps_to_tau (RM.add id dv env) (k tt) env' m ->
    pure_cfg_steps_to_tau env t env' m.

Lemma pure_cfg_steps_to_tau_obs {Pa : Params} {R : Type} :
  forall env (t1 t2 : CFGtop R) env' m,
    observe t1 = observe t2 ->
    @pure_cfg_steps_to_tau Pa R env t1 env' m ->
    @pure_cfg_steps_to_tau Pa R env t2 env' m.
Proof.
  intros env t1 t2 env' m Ho H.
  inversion H; subst;
    [apply PCT_Tau | eapply PCT_StepTau | eapply PCT_LocalRead | eapply PCT_LocalWrite];
    try (rewrite <- Ho; eassumption); eassumption.
Qed.

Lemma pure_cfg_steps_bind_to_tau {Pa : Params} {R S : Type} :
  forall env0 (t : CFGtop R) env1 x (k : R -> CFGtop S) env2 m,
    @pure_cfg_steps Pa R env0 t env1 x ->
    @pure_cfg_steps_to_tau Pa S env1 (k x) env2 m ->
    @pure_cfg_steps_to_tau Pa S env0 (ITree.bind t k) env2 m.
Proof.
  intros env0 t env1 x k env2 m H1 H2.
  induction H1 as [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH].
  - eapply pure_cfg_steps_to_tau_obs; [symmetry; rewrite observe_bind, Ho; reflexivity | exact H2].
  - eapply PCT_StepTau; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
  - eapply PCT_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact (IH H2)].
  - eapply PCT_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
Qed.

Lemma pure_cfg_steps_to_tau_bind {Pa : Params} {R S : Type} :
  forall env0 (t : CFGtop R) env1 m (k : R -> CFGtop S),
    @pure_cfg_steps_to_tau Pa R env0 t env1 m ->
    @pure_cfg_steps_to_tau Pa S env0 (ITree.bind t k) env1 (ITree.bind m k).
Proof.
  intros env0 t env1 m k H.
  induction H as [env t m Ho | env t t' env' m Ho _ IH | env t id dv ke env' m Ho Hf _ IH | env t id dv ke env' m Ho _ IH].
  - apply PCT_Tau; rewrite observe_bind, Ho; reflexivity.
  - eapply PCT_StepTau; [rewrite observe_bind, Ho; reflexivity | exact IH].
  - eapply PCT_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact IH].
  - eapply PCT_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact IH].
Qed.

Lemma pure_cfg_steps_to_tau_trans {Pa : Params} {R : Type} :
  forall env0 (t0 : CFGtop R) env1 m1 env2 m2,
    @pure_cfg_steps_to_tau Pa R env0 t0 env1 m1 ->
    @pure_cfg_steps_to_tau Pa R env1 m1 env2 m2 ->
    @pure_cfg_steps_to_tau Pa R env0 t0 env2 m2.
Proof.
  intros env0 t0 env1 m1 env2 m2 H1 H2.
  induction H1 as [env t m Ho | env t t' env' m Ho _ IH | env t id dv ke env' m Ho Hf _ IH | env t id dv ke env' m Ho _ IH].
  - eapply PCT_StepTau; [exact Ho | exact H2].
  - eapply PCT_StepTau; [exact Ho | exact (IH H2)].
  - eapply PCT_LocalRead; [exact Ho | exact Hf | exact (IH H2)].
  - eapply PCT_LocalWrite; [exact Ho | exact (IH H2)].
Qed.

Lemma pure_cfg_steps_to_tau_then_ret {Pa : Params} {R : Type} :
  forall env0 (t0 : CFGtop R) env1 m1 env2 v,
    @pure_cfg_steps_to_tau Pa R env0 t0 env1 m1 ->
    @pure_cfg_steps Pa R env1 m1 env2 v ->
    @pure_cfg_steps Pa R env0 t0 env2 v.
Proof.
  intros env0 t0 env1 m1 env2 v H1 H2.
  induction H1 as [env t m Ho | env t t' env' m Ho _ IH | env t id dv ke env' m Ho Hf _ IH | env t id dv ke env' m Ho _ IH].
  - eapply PCS_Tau; [exact Ho | exact H2].
  - eapply PCS_Tau; [exact Ho | exact (IH H2)].
  - eapply PCS_LocalRead; [exact Ho | exact Hf | exact (IH H2)].
  - eapply PCS_LocalWrite; [exact Ho | exact (IH H2)].
Qed.

Lemma pure_cfg_steps_to_tau_then_ub {Pa : Params} {R : Type} :
  forall (sigma : @draw_strat Pa) env0 (t0 : CFGtop R) env1 m1,
    @pure_cfg_steps_to_tau Pa R env0 t0 env1 m1 ->
    cfg_steps_to_ub sigma env1 m1 ->
    cfg_steps_to_ub sigma env0 t0.
Proof.
  intros sigma env0 t0 env1 m1 H1 H2.
  induction H1 as [env t m Ho | env t t' env' m Ho _ IH | env t id dv ke env' m Ho Hf _ IH | env t id dv ke env' m Ho _ IH].
  - eapply CSU_Tau; [exact Ho | exact H2].
  - eapply CSU_Tau; [exact Ho | exact (IH H2)].
  - eapply CSU_LocalRead; [exact Ho | exact Hf | exact (IH H2)].
  - eapply CSU_LocalWrite; [exact Ho | exact (IH H2)].
Qed.

Lemma pure_cfg_steps_to_tau_det_ref_l {Pa : Params} {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop)
  (self : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop) :
  forall (s1 : @draw_strat Pa) env1 (t1 : CFGtop R1) env1' m1 (u2 : itree (@Det_OW_E Pa) R2),
    @pure_cfg_steps_to_tau Pa R1 env1 t1 env1' m1 ->
    det_ref_ (Pa := Pa) RR self
      (run_draws s1 (run_cfg_locals env1' m1)) u2 ->
    det_ref_ (Pa := Pa) RR self
      (run_draws s1 (run_cfg_locals env1 t1)) u2.
Proof.
  intros s1 env1 t1 env1' m1 u2 H1 Hk.
  induction H1 as [env t m Ho | env t t' env' m Ho _ IH | env t id dv ke env' m Ho Hf _ IH | env t id dv ke env' m Ho _ IH].
  - eapply DR_TauL; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | exact Hk].
  - eapply DR_TauL; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | exact (IH Hk)].
  - eapply DR_TauL; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; cbn; rewrite Hf; reflexivity | exact (IH Hk)].
  - eapply DR_TauL; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | exact (IH Hk)].
Qed.

Lemma pure_cfg_steps_to_tau_sync {Pa : Params} {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop)
  (self : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop) :
  forall (s1 s2 : @draw_strat Pa)
         env1 (t1 : CFGtop R1) env1' m1
         env2 (t2 : CFGtop R2) env2' m2,
    @pure_cfg_steps_to_tau Pa R1 env1 t1 env1' m1 ->
    @pure_cfg_steps_to_tau Pa R2 env2 t2 env2' m2 ->
    self (run_draws s1 (run_cfg_locals env1' m1))
         (run_draws s2 (run_cfg_locals env2' m2)) ->
    det_ref_ (Pa := Pa) RR self
      (run_draws s1 (run_cfg_locals env1 t1))
      (run_draws s2 (run_cfg_locals env2 t2)).
Proof.
  intros s1 s2 env1 t1 env1' m1 env2 t2 env2' m2 H1 H2 Hself.
  induction H1 as [env t m Ho1 | env t t' env' m Ho1 _ IH1 | env t id dv ke env' m Ho1 Hf _ IH1 | env t id dv ke env' m Ho1 _ IH1].
  - induction H2 as [eb tb mb Ho2 | eb tb tb' eb' mb Ho2 _ IH2 | eb tb id dv ke eb' mb Ho2 Hf _ IH2 | eb tb id dv ke eb' mb Ho2 _ IH2].
    + apply DR_Step; unfold det_step_body.
      rewrite !observe_run_draws, !observe_run_cfg_locals, Ho1, Ho2; exact Hself.
    + eapply DR_TauR; [rewrite observe_run_draws, observe_run_cfg_locals, Ho2; reflexivity | exact (IH2 Hself)].
    + eapply DR_TauR; [rewrite observe_run_draws, observe_run_cfg_locals, Ho2; cbn; rewrite Hf; reflexivity | exact (IH2 Hself)].
    + eapply DR_TauR; [rewrite observe_run_draws, observe_run_cfg_locals, Ho2; reflexivity | exact (IH2 Hself)].
  - eapply DR_TauL; [rewrite observe_run_draws, observe_run_cfg_locals, Ho1; reflexivity | exact (IH1 Hself)].
  - eapply DR_TauL; [rewrite observe_run_draws, observe_run_cfg_locals, Ho1; cbn; rewrite Hf; reflexivity | exact (IH1 Hself)].
  - eapply DR_TauL; [rewrite observe_run_draws, observe_run_cfg_locals, Ho1; reflexivity | exact (IH1 Hself)].
Qed.

Lemma denote_ocfg_map_step_varargs_obs {Pa : Params} :
  forall (bmap : rmap (block dtyp)) (varargs : option (@ptr _ (@PTR Pa)))
         (bid_from bid_cur : block_id) (b : block dtyp),
    RM.find bid_cur bmap = Some b ->
    observe (@denote_ocfg_map Pa bmap varargs (bid_from, bid_cur)) =
    observe (ITree.bind
      (ITree.bind (denote_block b bid_from varargs)
        (fun bd => match bd with
                   | inr dv => Ret (inr (inr dv))
                   | inl bid_target => Ret (inl (bid_cur, bid_target))
                   end))
      (fun lr => match lr with
                 | inl j => Tau (denote_ocfg_map bmap varargs j)
                 | inr r => Ret r
                 end)).
Proof.
  intros bmap varargs bid_from bid_cur b Hf.
  unfold denote_ocfg_map; rewrite observe_iter; cbn beta; rewrite Hf; reflexivity.
Qed.

Definition denote_cfg_from {Pa : Params}
  (bmap : rmap (block dtyp)) (varargs : option (@ptr _ (@PTR Pa)))
  (j : block_id * block_id) : CFGtop (@dvalue Pa) :=
  r <- @denote_ocfg_map Pa bmap varargs j ;;
  match r with
  | inl bid => raise ("Can't find block in denote_cfg " ++ show (snd bid))%string
  | inr uv => ret uv
  end.

Lemma denote_cfg_from_block_ub {Pa : Params} :
  forall bmap varargs bid_from bid_cur b (sigma : @draw_strat Pa) env,
    RM.find bid_cur bmap = Some b ->
    cfg_steps_to_ub sigma env (denote_block b bid_from varargs) ->
    cfg_steps_to_ub sigma env (@denote_cfg_from Pa bmap varargs (bid_from, bid_cur)).
Proof.
  intros bmap varargs bid_from bid_cur b sigma env Hfb Hub.
  unfold denote_cfg_from; apply cfg_steps_to_ub_bind_l.
  eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_varargs_obs _ _ _ _ _ Hfb) |].
  apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l; exact Hub.
Qed.

Lemma denote_cfg_from_block_jump {Pa : Params} :
  forall bmap varargs bid_from bid_cur b env0 env1 bid_next,
    RM.find bid_cur bmap = Some b ->
    @pure_cfg_steps Pa (block_id + @dvalue Pa) env0 (denote_block b bid_from varargs) env1 (inl bid_next) ->
    @pure_cfg_steps_to_tau Pa (@dvalue Pa)
      env0 (denote_cfg_from bmap varargs (bid_from, bid_cur))
      env1 (denote_cfg_from bmap varargs (bid_cur, bid_next)).
Proof.
  intros bmap varargs bid_from bid_cur b env0 env1 bid_next Hfb Hst.
  unfold denote_cfg_from; apply pure_cfg_steps_to_tau_bind.
  eapply pure_cfg_steps_to_tau_obs; [symmetry; exact (denote_ocfg_map_step_varargs_obs _ _ _ _ _ Hfb) |].
  eapply pure_cfg_steps_bind_to_tau.
  - eapply pure_cfg_steps_bind; [exact Hst | apply PCS_Ret; reflexivity].
  - apply PCT_Tau; reflexivity.
Qed.

Lemma denote_cfg_from_block_ret {Pa : Params} :
  forall bmap varargs bid_from bid_cur b env0 env1 dv,
    RM.find bid_cur bmap = Some b ->
    @pure_cfg_steps Pa (block_id + @dvalue Pa) env0 (denote_block b bid_from varargs) env1 (inr dv) ->
    @pure_cfg_steps Pa (@dvalue Pa)
      env0 (denote_cfg_from bmap varargs (bid_from, bid_cur))
      env1 dv.
Proof.
  intros bmap varargs bid_from bid_cur b env0 env1 dv Hfb Hst.
  unfold denote_cfg_from; eapply pure_cfg_steps_bind.
  - eapply pure_cfg_steps_obs; [symmetry; exact (denote_ocfg_map_step_varargs_obs _ _ _ _ _ Hfb) |].
    eapply pure_cfg_steps_bind.
    + eapply pure_cfg_steps_bind; [exact Hst | apply PCS_Ret; reflexivity].
    + apply PCS_Ret; reflexivity.
  - apply PCS_Ret; reflexivity.
Qed.

Definition eff_loop_cond (pol : bool) (ce : cert_expr) : cert_expr :=
  if pol then ce
  else CE_Select 1%positive ce (CE_BvConst 1%positive 0%N) (CE_BvConst 1%positive 1%N).

Lemma bit1_repr_zero_unsigned :
  (@Integers.unsigned 1%positive (@Integers.repr 1%positive (Z.of_N 0%N)) =? 1)%Z = false.
Proof.
  cbn [Z.of_N]; rewrite (@Integers.unsigned_repr 1%positive 0); [reflexivity |].
  unfold Integers.max_unsigned.
  rewrite (@Integers.modulus_two_power_nat 1%positive), (@Integers.natwordsize_def 1%positive).
  vm_compute; split; discriminate.
Qed.

Lemma bit1_repr_one_unsigned :
  (@Integers.unsigned 1%positive (@Integers.repr 1%positive (Z.of_N 1%N)) =? 1)%Z = true.
Proof.
  cbn [Z.of_N]; rewrite (@Integers.unsigned_repr 1%positive 1); [reflexivity |].
  unfold Integers.max_unsigned.
  rewrite (@Integers.modulus_two_power_nat 1%positive), (@Integers.natwordsize_def 1%positive).
  vm_compute; split; discriminate.
Qed.

Lemma eval_eff_loop_cond {Pa : Params} :
  forall (penv : param_env Pa) pol ce (cbit : @Integers.bit_int 1),
    eval_closed_cert_expr penv dummy_freeze_oracle ce =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit)) ->
    exists ebit : @Integers.bit_int 1,
      eval_closed_cert_expr penv dummy_freeze_oracle (eff_loop_cond pol ce) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1 ebit)) /\
      (@Integers.unsigned 1 ebit =? 1)%Z = Bool.eqb (@Integers.unsigned 1 cbit =? 1)%Z pol.
Proof.
  intros penv pol ce cbit Hev; destruct pol; cbn [eff_loop_cond].
  - exists cbit; split; [exact Hev | destruct (@Integers.unsigned 1 cbit =? 1)%Z; reflexivity].
  - unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev; cbn [eou_bind eval_select].
    destruct (@Integers.unsigned 1 cbit =? 1)%Z.
    + exists (@Integers.repr 1%positive (Z.of_N 0%N)); split; [reflexivity | exact bit1_repr_zero_unsigned].
    + exists (@Integers.repr 1%positive (Z.of_N 1%N)); split; [reflexivity | exact bit1_repr_one_unsigned].
Qed.

Fixpoint extract_hdr_phi_specs
  (phis : list (local_id * phi dtyp * list metadata))
  {struct phis} : option (list (raw_id * positive)) :=
  match phis with
  | [] => Some []
  | (id, Phi _ (DTYPE_Base (DTYPE_I w)) _, _) :: rest =>
      if is_supported_bit_width w then
        match extract_hdr_phi_specs rest with
        | Some r => Some ((id, w) :: r)
        | None => None
        end
      else None
  | _ :: _ => None
  end.

Fixpoint pair_phi_specs
  (xs ys : list (raw_id * positive))
  {struct xs} : option (list (raw_id * raw_id * positive)) :=
  match xs, ys with
  | [], [] => Some []
  | (id_s, w_s) :: rx, (id_t, w_t) :: ry =>
      if Pos.eqb w_s w_t && is_supported_bit_width w_s then
        match pair_phi_specs rx ry with
        | Some r => Some ((id_s, id_t, w_s) :: r)
        | None => None
        end
      else None
  | _, _ => None
  end.

Lemma pair_phi_specs_supported :
  forall xs ys pspecs,
    pair_phi_specs xs ys = Some pspecs ->
    Forall (fun '(_, _, w) => is_supported_bit_width w = true) pspecs.
Proof.
  induction xs as [| [id_s w_s] rx IH]; intros ys pspecs H;
    destruct ys as [| [id_t w_t] ry]; cbn [pair_phi_specs] in H; try discriminate H.
  - inversion H; constructor.
  - destruct (Pos.eqb w_s w_t && is_supported_bit_width w_s) eqn:E; [| discriminate H].
    apply andb_true_iff in E as [_ Hsup].
    destruct (pair_phi_specs rx ry) as [r |] eqn:Er; [| discriminate H].
    inversion H; subst; constructor; [exact Hsup | exact (IH ry r Er)].
Qed.

Fixpoint check_pevals_refine
  (ctx : ub_ctx) (opt_pf : option (list lrat_step))
  (pspecs : list (raw_id * raw_id * positive))
  (pevals_s pevals_t : list (raw_id * positive * cert_expr))
  {struct pspecs} : bool :=
  match pspecs, pevals_s, pevals_t with
  | [], [], [] => true
  | (id_s, id_t, w) :: rp, (id_s', w_s, ce_s) :: rs, (id_t', w_t, ce_t) :: rt =>
      raw_id_eqb id_s id_s' && raw_id_eqb id_t id_t' &&
      Pos.eqb w w_s && Pos.eqb w w_t &&
      is_supported_bit_width w &&
      check_expr_refines_with_lrat ctx ce_s ce_t opt_pf &&
      check_pevals_refine ctx opt_pf rp rs rt
  | _, _, _ => false
  end.

Lemma check_pevals_refine_sound {Pa : Params} :
  forall pspecs pevals_s pevals_t dvs_s dvs_t allowed ctx opt_pf (penv : param_env Pa),
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv dummy_freeze_oracle ctx ->
    Forall (fun '(_, w, ce) =>
      is_supported_bit_width w = true /\ cert_expr_bit_width ce = w /\ wf_pure_eval_entry allowed ce) pevals_s ->
    Forall (fun '(_, w, ce) =>
      is_supported_bit_width w = true /\ cert_expr_bit_width ce = w /\ wf_pure_eval_entry allowed ce) pevals_t ->
    Forall2 (phi_eval_pair_matches penv dummy_freeze_oracle) pevals_s dvs_s ->
    Forall2 (phi_eval_pair_matches penv dummy_freeze_oracle) pevals_t dvs_t ->
    check_pevals_refine ctx opt_pf pspecs pevals_s pevals_t = true ->
    cut_phi_rel pspecs dvs_s dvs_t /\
    List.map fst dvs_s = List.map (fun '(id_s, _, _) => id_s) pspecs /\
    List.map fst dvs_t = List.map (fun '(_, id_t, _) => id_t) pspecs.
Proof.
  induction pspecs as [| [[id_s id_t] w] rp IH];
    intros pevals_s pevals_t dvs_s dvs_t allowed ctx opt_pf penv Hpenv Hctx Hfas Hfat Hms Hmt Hchk;
    destruct pevals_s as [| [[id_s' w_s] ce_s] rs];
    destruct pevals_t as [| [[id_t' w_t] ce_t] rt];
    cbn [check_pevals_refine] in Hchk; try discriminate Hchk.
  - inversion Hms; inversion Hmt; subst; repeat split; constructor.
  - rewrite !andb_true_iff in Hchk.
    destruct Hchk as ((((((Heqs & Heqt) & Hws) & Hwt) & Hsup) & Href) & Hrest).
    apply raw_id_eqb_eq in Heqs; apply raw_id_eqb_eq in Heqt;
      apply Pos.eqb_eq in Hws; apply Pos.eqb_eq in Hwt; subst id_s' id_t' w_s w_t.
    inversion Hfas as [| ? ? (_ & _ & (_ & _ & Hfvs)) Hfas_r]; subst.
    inversion Hfat as [| ? ? (_ & _ & (_ & _ & Hfvt)) Hfat_r]; subst.
    inversion Hms as [| ? [id_sd dv_s] ? dvs_sr [-> [Hev_s Hsc_s]] Hms_r]; subst.
    inversion Hmt as [| ? [id_td dv_t] ? dvs_tr [-> [Hev_t Hsc_t]] Hmt_r]; subst.
    pose proof (fun nm w0 H => Hpenv nm w0 (Hfvs (nm, w0) H)) as Hps.
    pose proof (fun nm w0 H => Hpenv nm w0 (Hfvt (nm, w0) H)) as Hpt.
    pose proof (check_expr_refines_with_lrat_sound ctx ce_s ce_t opt_pf penv dummy_freeze_oracle Href Hps Hpt Hctx) as Hdv.
    rewrite Hev_s, Hev_t in Hdv; cbn [refine_eou_dvalue] in Hdv.
    destruct (IH rs rt dvs_sr dvs_tr allowed ctx opt_pf penv Hpenv Hctx Hfas_r Hfat_r Hms_r Hmt_r Hrest)
      as (Hrel_r & Hmap_s & Hmap_t).
    split; [exact (CPR_Cons id_s id_t w dv_s dv_t rp dvs_sr dvs_tr Hsup Hsc_s Hsc_t Hdv Hrel_r) |].
    cbn; split; f_equal; assumption.
Qed.

Definition disjoint_raw_ids (xs ys : list raw_id) : bool :=
  forallb (fun x => negb (raw_id_in_list x ys)) xs.

Lemma disjoint_raw_ids_spec :
  forall xs ys r,
    disjoint_raw_ids xs ys = true ->
    In r xs ->
    ~ In r ys.
Proof.
  intros xs ys r Hdisj Hin Hiny.
  unfold disjoint_raw_ids in Hdisj; rewrite forallb_forall in Hdisj.
  pose proof (Hdisj r Hin) as Hnr.
  apply raw_id_in_list_spec in Hiny; rewrite Hiny in Hnr; discriminate Hnr.
Qed.

Lemma exprs_safe_under_src_sound {Pa : Params} :
  forall es allowed ctx src_evals (penv : param_env Pa),
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv dummy_freeze_oracle ctx ->
    (forall big, In big src_evals -> exists dv, eval_closed_cert_expr penv dummy_freeze_oracle big = raise_ret dv) ->
    Forall (wf_pure_eval_entry allowed) es ->
    forallb (expr_safe_under_src ctx src_evals) es = true ->
    forall ce msg, In ce es -> eval_closed_cert_expr penv dummy_freeze_oracle ce <> raise_ub msg.
Proof.
  intros es allowed ctx src_evals penv Hpenv Hctx Hsrc Hfa Hsafe ce msg Hin Hev.
  rewrite Forall_forall in Hfa; rewrite forallb_forall in Hsafe.
  destruct (Hfa ce Hin) as (Hwt & _ & Hfv).
  pose proof (Hsafe ce Hin) as Hsc.
  pose proof (fun nm w0 H => Hpenv nm w0 (Hfv (nm, w0) H)) as Hpce.
  destruct (expr_safe_under_src_sound ce ctx src_evals penv dummy_freeze_oracle Hsc Hwt Hpce Hctx Hsrc)
    as [dv [Hret _]].
  rewrite Hret in Hev; discriminate Hev.
Qed.

Definition peval_exprs (pevals : list (raw_id * positive * cert_expr)) : list cert_expr :=
  List.map (fun '(_, _, ce) => ce) pevals.

Lemma peval_exprs_typing :
  forall allowed pevals,
    Forall (fun '(_, w, ce) =>
      is_supported_bit_width w = true /\ cert_expr_bit_width ce = w /\ wf_pure_eval_entry allowed ce) pevals ->
    Forall (wf_pure_eval_entry allowed) (peval_exprs pevals).
Proof.
  intros allowed pevals Hfa; induction Hfa as [| [[id w] ce] rest (_ & _ & Hwf) _ IH];
    cbn [peval_exprs List.map]; [constructor | constructor; assumption].
Qed.

Lemma peval_exprs_ret {Pa : Params} :
  forall (penv : param_env Pa) pevals dvs,
    Forall2 (phi_eval_pair_matches penv dummy_freeze_oracle) pevals dvs ->
    Forall (fun ce => exists dv, eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv)
      (peval_exprs pevals).
Proof.
  intros penv pevals dvs Hfa2.
  induction Hfa2 as [| [[id w] ce] [id' dv] rp rd [_ [Hev _]] _ IH];
    cbn [peval_exprs List.map]; [constructor | constructor; [exists dv; exact Hev | exact IH]].
Qed.

Lemma pure_phis_denote_step {Pa : Params} :
  forall phis (penv : param_env Pa) bid_from lmap (env : rmap (@dvalue Pa)) pevals,
    lmap_matches_env penv lmap env ->
    reify_pure_phis bid_from lmap phis = Some pevals ->
    ((forall sigma, cfg_steps_to_ub sigma env (denote_phis bid_from phis)) /\
     exists ce msg,
       In ce (peval_exprs pevals) /\
       eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ub msg) \/
    (exists dvs,
       Forall2 (phi_eval_pair_matches penv dummy_freeze_oracle) pevals dvs /\
       pure_cfg_steps env (denote_phis bid_from phis) (apply_phi_env env dvs) tt).
Proof.
  intros phis penv bid_from lmap env pevals Henv Hr.
  destruct (eval_reified_pure_phis phis penv bid_from lmap env pevals Henv Hr)
    as [[Hub (id & w & ce & msg & Hin & Hev)] | [dvs [Hpm Hst]]].
  - left; split.
    + intros sigma; unfold denote_phis; apply cfg_steps_to_ub_bind_l; exact (Hub sigma).
    + exists ce, msg; split; [| exact Hev].
      unfold peval_exprs; exact (in_map (fun '(_, _, e) => e) pevals (id, w, ce) Hin).
  - right; exists dvs; split; [exact Hpm |].
    unfold denote_phis; eapply pure_cfg_steps_bind; [exact Hst |].
    eapply pure_cfg_steps_bind; [apply pure_cfg_steps_lwrite_list | apply PCS_Ret; reflexivity].
Qed.

Definition is_latch_edge_b (bmap : rmap (block dtyp)) (bid_hdr br : block_id) : bool :=
  if raw_id_eqb br bid_hdr then true
  else
    match RM.find br bmap with
    | Some b_body =>
        list_empty_b (blk_phis b_body) &&
        match blk_term b_body with
        | (_, TERM_Br_1 br_back, _) => raw_id_eqb br_back bid_hdr
        | _ => false
        end
    | None => false
    end.

Record natural_loop_summary : Type := mk_natural_loop_summary {
  nls_bid_hdr : block_id;
  nls_bid_latch_entry : block_id;
  nls_bid_latch_from : block_id;
  nls_bid_exit : block_id;
  nls_latch_on_true : bool;
  nls_evals_entry : list cert_expr;
  nls_lmap_entry : rmap (positive * cert_expr);
  nls_init_pevals : list (raw_id * positive * cert_expr);
  nls_evals_hdr : list cert_expr;
  nls_lmap_hdr_c : rmap (positive * cert_expr);
  nls_ce_cond : cert_expr;
  nls_evals_body : list cert_expr;
  nls_lmap_latch : rmap (positive * cert_expr);
  nls_next_pevals : list (raw_id * positive * cert_expr);
  nls_evals_exit : list cert_expr;
  nls_w_ret : positive;
  nls_ce_ret : cert_expr;
}.

Definition reify_natural_loop
  (G : CFG.cfg dtyp)
  (hdr_name : string)
  (lmap0 : rmap (positive * cert_expr))
  (wrap_cut : rmap (positive * cert_expr) -> list (raw_id * positive) -> rmap (positive * cert_expr))
  : option (list (raw_id * positive) * natural_loop_summary) :=
  let bmap := ocfg_map (blks G) in
  match RM.find (init G) bmap with
  | None => None
  | Some b_entry =>
      if negb (list_empty_b (blk_phis b_entry)) then None
      else
        match blk_term b_entry with
        | (_, TERM_Br_1 bid_hdr, _) =>
            if negb (cert_block_matches_id hdr_name bid_hdr) || raw_id_eqb bid_hdr (init G) then None
            else
              match RM.find bid_hdr bmap, reify_pure_code lmap0 (blk_code b_entry) with
              | Some b_hdr, Some (evals_entry, lmap_entry) =>
                  match extract_hdr_phi_specs (blk_phis b_hdr),
                        reify_pure_phis (init G) lmap_entry (blk_phis b_hdr) with
                  | Some hspecs, Some init_pevals =>
                      let lmap_hdr0 := wrap_cut lmap_entry hspecs in
                      match reify_pure_code lmap_hdr0 (blk_code b_hdr) with
                      | None => None
                      | Some (evals_hdr, lmap_hdr_c) =>
                          match blk_term b_hdr with
                          | (_, TERM_Br (DTYPE_Base (DTYPE_I 1%positive), op_cond) br1 br2, _) =>
                              match reify_pure_exp lmap_hdr_c (Some (DTYPE_Base (DTYPE_I 1%positive))) op_cond with
                              | None => None
                              | Some (_, ce_cond) =>
                                  let l1 := is_latch_edge_b bmap bid_hdr br1 in
                                  let l2 := is_latch_edge_b bmap bid_hdr br2 in
                                  let opt_pol :=
                                    if l1 && negb l2 then Some (true, br1, br2)
                                    else if l2 && negb l1 then Some (false, br2, br1)
                                    else None in
                                  match opt_pol with
                                  | None => None
                                  | Some (pol, br_latch, br_exit) =>
                                      let opt_latch :=
                                        if raw_id_eqb br_latch bid_hdr then
                                          Some (bid_hdr, [], lmap_hdr_c, [] : list raw_id)
                                        else
                                          match RM.find br_latch bmap with
                                          | Some b_body =>
                                              if list_empty_b (blk_phis b_body) then
                                                match blk_term b_body, reify_pure_code lmap_hdr_c (blk_code b_body) with
                                                | (_, TERM_Br_1 br_back, _), Some (evals_body, lmap_latch) =>
                                                    if raw_id_eqb br_back bid_hdr then
                                                      Some (br_latch, evals_body, lmap_latch, code_written_ids (blk_code b_body))
                                                    else None
                                                | _, _ => None
                                                end
                                              else None
                                          | None => None
                                          end in
                                      match opt_latch with
                                      | None => None
                                      | Some (bid_latch_from, evals_body, lmap_latch, body_wr) =>
                                          let dom_entry := args G ++ code_written_ids (blk_code b_entry) in
                                          let loop_wr := List.map fst hspecs ++ code_written_ids (blk_code b_hdr) ++ body_wr in
                                          if negb (disjoint_raw_ids dom_entry loop_wr) || raw_id_eqb br_exit bid_hdr then None
                                          else
                                            match reify_pure_phis bid_latch_from lmap_latch (blk_phis b_hdr),
                                                  RM.find br_exit bmap with
                                            | Some next_pevals, Some b_exit =>
                                                if negb (list_empty_b (blk_phis b_exit)) then None
                                                else
                                                  match reify_pure_code lmap_hdr_c (blk_code b_exit), blk_term b_exit with
                                                  | Some (evals_exit, lmap_exit),
                                                    (_, TERM_Ret (DTYPE_Base (DTYPE_I w_ret), op_ret), _) =>
                                                      if is_supported_bit_width w_ret then
                                                        match reify_pure_exp lmap_exit (Some (DTYPE_Base (DTYPE_I w_ret))) op_ret with
                                                        | Some (_, ce_ret) =>
                                                            Some (hspecs, {|
                                                              nls_bid_hdr := bid_hdr;
                                                              nls_bid_latch_entry := br_latch;
                                                              nls_bid_latch_from := bid_latch_from;
                                                              nls_bid_exit := br_exit;
                                                              nls_latch_on_true := pol;
                                                              nls_evals_entry := evals_entry;
                                                              nls_lmap_entry := lmap_entry;
                                                              nls_init_pevals := init_pevals;
                                                              nls_evals_hdr := evals_hdr;
                                                              nls_lmap_hdr_c := lmap_hdr_c;
                                                              nls_ce_cond := ce_cond;
                                                              nls_evals_body := evals_body;
                                                              nls_lmap_latch := lmap_latch;
                                                              nls_next_pevals := next_pevals;
                                                              nls_evals_exit := evals_exit;
                                                              nls_w_ret := w_ret;
                                                              nls_ce_ret := ce_ret;
                                                            |})
                                                        | None => None
                                                        end
                                                      else None
                                                  | _, _ => None
                                                  end
                                            | _, _ => None
                                            end
                                      end
                                  end
                              end
                          | _ => None
                          end
                      end
                  | _, _ => None
                  end
              | _, _ => None
              end
        | _ => None
        end
  end.

Lemma list_empty_b_nil {A : Type} : forall (xs : list A), list_empty_b xs = true -> xs = [].
Proof. intros [| _ _] H; [reflexivity | discriminate H]. Qed.

Lemma denote_empty_phis_ret {Pa : Params} :
  forall bid_from (env : rmap (@dvalue Pa)),
    pure_cfg_steps env (denote_phis bid_from []) env tt.
Proof.
  intros bid_from env; unfold denote_phis; cbn [map_monad].
  eapply pure_cfg_steps_bind; [apply PCS_Ret; reflexivity |].
  eapply pure_cfg_steps_bind; [apply PCS_Ret; reflexivity | apply PCS_Ret; reflexivity].
Qed.

Fixpoint overlay_hspecs_s
  (idx : nat) (lmap : rmap (positive * cert_expr))
  (hspecs : list (raw_id * positive))
  {struct hspecs} : rmap (positive * cert_expr) :=
  match hspecs with
  | [] => lmap
  | (id_s, w) :: rest =>
      overlay_hspecs_s (S idx) (RM.add id_s (w, cut_src_expr idx w) lmap) rest
  end.

Fixpoint overlay_hspecs_t
  (idx : nat) (lmap : rmap (positive * cert_expr))
  (hspecs : list (raw_id * positive))
  {struct hspecs} : rmap (positive * cert_expr) :=
  match hspecs with
  | [] => lmap
  | (id_t, w) :: rest =>
      overlay_hspecs_t (S idx) (RM.add id_t (w, cut_tgt_expr idx w) lmap) rest
  end.

Lemma pair_phi_specs_overlay :
  forall hspecs_s hspecs_t pspecs idx lmap_s lmap_t,
    pair_phi_specs hspecs_s hspecs_t = Some pspecs ->
    overlay_hspecs_s idx lmap_s hspecs_s = overlay_cut_lmap_s idx lmap_s pspecs /\
    overlay_hspecs_t idx lmap_t hspecs_t = overlay_cut_lmap_t idx lmap_t pspecs /\
    List.map fst hspecs_s = List.map (fun '(id_s, _, _) => id_s) pspecs /\
    List.map fst hspecs_t = List.map (fun '(_, id_t, _) => id_t) pspecs.
Proof.
  induction hspecs_s as [| [id_s w_s] rx IH];
    intros hspecs_t pspecs idx lmap_s lmap_t H;
    destruct hspecs_t as [| [id_t w_t] ry]; cbn [pair_phi_specs] in H; try discriminate H.
  - inversion H; subst; repeat split; reflexivity.
  - destruct (Pos.eqb w_s w_t && is_supported_bit_width w_s) eqn:E; [| discriminate H].
    apply andb_true_iff in E as [Heqw _]; apply Pos.eqb_eq in Heqw; subst w_t.
    destruct (pair_phi_specs rx ry) as [r |] eqn:Er; [| discriminate H].
    inversion H; subst pspecs; cbn.
    destruct (IH ry r (S idx)
                (RM.add id_s (w_s, cut_src_expr idx w_s) lmap_s)
                (RM.add id_t (w_s, cut_tgt_expr idx w_s) lmap_t) Er)
      as (Hs & Ht & Hms & Hmt).
    repeat split; [exact Hs | exact Ht | f_equal; exact Hms | f_equal; exact Hmt].
Qed.

Lemma pure_cfg_to_cfg_ret {Pa : Params} {R : Type} :
  forall (sigma : @draw_strat Pa) env (t : CFGtop R) env' r,
    @pure_cfg_steps Pa R env t env' r ->
    cfg_steps_to_ret sigma env t sigma env' r.
Proof.
  intros sigma env t env' r H.
  induction H as [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH].
  - apply CSR_Ret; exact Ho.
  - eapply CSR_Tau; [exact Ho | exact IH].
  - eapply CSR_LocalRead; [exact Ho | exact Hf | exact IH].
  - eapply CSR_LocalWrite; [exact Ho | exact IH].
Qed.

Lemma reify_natural_loop_spec :
  forall G hdr_name allowed cut_allowed lmap0 wrap_cut hspecs s,
    wf_pure_lmap allowed lmap0 ->
    (forall r w ce, RM.find r lmap0 = Some (w, ce) -> In r (args G)) ->
    (forall lmap, wf_pure_lmap allowed lmap -> wf_pure_lmap cut_allowed (wrap_cut lmap hspecs)) ->
    reify_natural_loop G hdr_name lmap0 wrap_cut = Some (hspecs, s) ->
    exists b_entry b_hdr,
      let bmap := ocfg_map (blks G) in
      let dom_entry := args G ++ code_written_ids (blk_code b_entry) in
      RM.find (init G) bmap = Some b_entry /\
      RM.find (nls_bid_hdr s) bmap = Some b_hdr /\
      extract_hdr_phi_specs (blk_phis b_hdr) = Some hspecs /\
      reify_pure_phis (init G) (nls_lmap_entry s) (blk_phis b_hdr) = Some (nls_init_pevals s) /\
      reify_pure_phis (nls_bid_latch_from s) (nls_lmap_latch s) (blk_phis b_hdr) = Some (nls_next_pevals s) /\
      wf_pure_lmap allowed (nls_lmap_entry s) /\
      (forall r w ce, RM.find r (nls_lmap_entry s) = Some (w, ce) -> In r dom_entry) /\
      Forall (wf_pure_eval_entry allowed) (nls_evals_entry s) /\
      Forall (fun '(_, w, ce) =>
        is_supported_bit_width w = true /\ cert_expr_bit_width ce = w /\ wf_pure_eval_entry allowed ce)
        (nls_init_pevals s) /\
      Forall (wf_pure_eval_entry cut_allowed) (nls_evals_hdr s) /\
      wf_pure_eval_entry cut_allowed (nls_ce_cond s) /\
      cert_expr_bit_width (nls_ce_cond s) = 1%positive /\
      Forall (wf_pure_eval_entry cut_allowed) (nls_evals_body s) /\
      Forall (fun '(_, w, ce) =>
        is_supported_bit_width w = true /\ cert_expr_bit_width ce = w /\ wf_pure_eval_entry cut_allowed ce)
        (nls_next_pevals s) /\
      Forall (wf_pure_eval_entry cut_allowed) (nls_evals_exit s) /\
      wf_pure_eval_entry cut_allowed (nls_ce_ret s) /\
      cert_expr_bit_width (nls_ce_ret s) = nls_w_ret s /\
      is_supported_bit_width (nls_w_ret s) = true /\
      (forall (Pa : Params) (varargs : option (@ptr _ (@PTR Pa)))
              (penv : param_env Pa) (env0 : rmap (@dvalue Pa)),
         lmap_matches_env penv lmap0 env0 ->
         ((forall sigma, cfg_steps_to_ub sigma env0 (denote_cfg_from bmap varargs (init G, init G))) /\
          exists ce msg, In ce (nls_evals_entry s) /\
            eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ub msg) \/
         (exists env_entry,
            lmap_matches_env penv (nls_lmap_entry s) env_entry /\
            Forall (fun ce => exists dv, eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv)
              (nls_evals_entry s) /\
            pure_cfg_steps_to_tau env0 (denote_cfg_from bmap varargs (init G, init G))
              env_entry (denote_cfg_from bmap varargs (init G, nls_bid_hdr s)))) /\
      (forall (Pa : Params) (varargs : option (@ptr _ (@PTR Pa)))
              (penv_cut : param_env Pa) bid_prev (env_prev : rmap (@dvalue Pa))
              (dvs : list (raw_id * @dvalue Pa)),
         List.map fst dvs = List.map fst hspecs ->
         pure_cfg_steps env_prev (denote_phis bid_prev (blk_phis b_hdr)) (apply_phi_env env_prev dvs) tt ->
         lmap_matches_env penv_cut (wrap_cut (nls_lmap_entry s) hspecs) (apply_phi_env env_prev dvs) ->
         ((forall sigma, cfg_steps_to_ub sigma env_prev (denote_cfg_from bmap varargs (bid_prev, nls_bid_hdr s))) /\
          ((exists ce msg, In ce (nls_ce_cond s :: nls_evals_hdr s) /\
              eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ub msg) \/
           eval_closed_cert_expr penv_cut dummy_freeze_oracle (nls_ce_cond s) =
             raise_ret (DVALUE_Base DVALUE_Poison))) \/
         (exists (cbit : @Integers.bit_int 1),
            Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
              (nls_evals_hdr s) /\
            eval_closed_cert_expr penv_cut dummy_freeze_oracle (nls_ce_cond s) =
              raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit)) /\
            (Bool.eqb (@Integers.unsigned 1 cbit =? 1)%Z (nls_latch_on_true s) = true ->
             ((forall sigma, cfg_steps_to_ub sigma env_prev (denote_cfg_from bmap varargs (bid_prev, nls_bid_hdr s))) /\
              exists ce msg, In ce (nls_evals_body s) /\
                eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ub msg) \/
             (exists env_latch,
                lmap_matches_env penv_cut (nls_lmap_latch s) env_latch /\
                Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
                  (nls_evals_body s) /\
                (forall r, In r dom_entry -> RM.find r env_latch = RM.find r env_prev) /\
                pure_cfg_steps_to_tau env_prev (denote_cfg_from bmap varargs (bid_prev, nls_bid_hdr s))
                  env_latch (denote_cfg_from bmap varargs (nls_bid_latch_from s, nls_bid_hdr s)))) /\
            (Bool.eqb (@Integers.unsigned 1 cbit =? 1)%Z (nls_latch_on_true s) = false ->
             ((forall sigma, cfg_steps_to_ub sigma env_prev (denote_cfg_from bmap varargs (bid_prev, nls_bid_hdr s))) /\
              exists ce msg, In ce (nls_ce_ret s :: nls_evals_exit s) /\
                eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ub msg) \/
             (exists env_exit dv_ret,
                Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
                  (nls_evals_exit s) /\
                eval_closed_cert_expr penv_cut dummy_freeze_oracle (nls_ce_ret s) = raise_ret dv_ret /\
                wf_scalar_dvalue (nls_w_ret s) dv_ret /\
                pure_cfg_steps env_prev (denote_cfg_from bmap varargs (bid_prev, nls_bid_hdr s))
                  env_exit dv_ret)))).
Proof.
  intros G hdr_name allowed cut_allowed lmap0 wrap_cut hspecs s Hlmap0 Hdom0 Hwrap Hr.
  unfold reify_natural_loop in Hr; cbn zeta in Hr.
  set (bmap := ocfg_map (blks G)) in *.
  destruct (RM.find (init G) bmap) as [b_entry |] eqn:Hf_ent; [| discriminate Hr].
  destruct (negb (list_empty_b (blk_phis b_entry))) eqn:Ep_ent; [discriminate Hr |].
  apply negb_false_iff, list_empty_b_nil in Ep_ent.
  destruct (blk_term b_entry) as [[ti_e tm_e] md_e] eqn:Htm_ent.
  destruct tm_e as [| | | bid_hdr | | | | |]; try discriminate Hr.
  destruct (negb (cert_block_matches_id hdr_name bid_hdr) || raw_id_eqb bid_hdr (init G)); [discriminate Hr |].
  destruct (RM.find bid_hdr bmap) as [b_hdr |] eqn:Hf_hdr; [| discriminate Hr].
  destruct (reify_pure_code lmap0 (blk_code b_entry)) as [[evals_entry lmap_entry] |] eqn:Hr_ent; [| discriminate Hr].
  destruct (extract_hdr_phi_specs (blk_phis b_hdr)) as [hspecs' |] eqn:Ehspecs; [| discriminate Hr].
  destruct (reify_pure_phis (init G) lmap_entry (blk_phis b_hdr)) as [init_pevals |] eqn:Hr_init; [| discriminate Hr].
  destruct (reify_pure_code (wrap_cut lmap_entry hspecs') (blk_code b_hdr))
    as [[evals_hdr lmap_hdr_c] |] eqn:Hr_hdr; [| discriminate Hr].
  destruct (blk_term b_hdr) as [[ti_h tm_h] md_h] eqn:Htm_hdr.
  destruct tm_h as [| | [dt_c op_cond] br1 br2 | | | | | |]; try discriminate Hr.
  destruct dt_c as [tb_c | |]; try discriminate Hr;
    destruct tb_c as [wc | | | | | | | | | |]; try discriminate Hr;
    destruct wc as [| |]; try discriminate Hr.
  destruct (reify_pure_exp lmap_hdr_c (Some (DTYPE_Base (DTYPE_I 1%positive))) op_cond)
    as [[wc' ce_cond] |] eqn:Hr_cond; [| discriminate Hr].
  pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr_cond)) as ->.
  set (opt_pol :=
    if is_latch_edge_b bmap bid_hdr br1 && negb (is_latch_edge_b bmap bid_hdr br2)
    then Some (true, br1, br2)
    else if is_latch_edge_b bmap bid_hdr br2 && negb (is_latch_edge_b bmap bid_hdr br1)
    then Some (false, br2, br1)
    else None) in *.
  destruct opt_pol as [[[pol br_latch] br_exit] |] eqn:Epol; [| discriminate Hr].
  assert (Hpol_br :
    forall b : bool,
      (if b then br1 else br2) =
      (if Bool.eqb b pol then br_latch else br_exit)).
  { unfold opt_pol in Epol.
    destruct (is_latch_edge_b bmap bid_hdr br1 && negb (is_latch_edge_b bmap bid_hdr br2)).
    - inversion Epol; subst pol br_latch br_exit; intros []; reflexivity.
    - destruct (is_latch_edge_b bmap bid_hdr br2 && negb (is_latch_edge_b bmap bid_hdr br1)); [| discriminate Epol].
      inversion Epol; subst pol br_latch br_exit; intros []; reflexivity. }
  match type of Hr with
  | match ?ol with Some _ => _ | None => _ end = Some _ =>
      destruct ol as [[[[bid_latch_from evals_body] lmap_latch] body_wr] |] eqn:Elatch; [| discriminate Hr]
  end.
  destruct (negb (disjoint_raw_ids (args G ++ code_written_ids (blk_code b_entry))
                    (List.map fst hspecs' ++ code_written_ids (blk_code b_hdr) ++ body_wr)) ||
            raw_id_eqb br_exit bid_hdr) eqn:Edisj_bad; [discriminate Hr |].
  apply orb_false_iff in Edisj_bad as [Edisj _]; apply negb_false_iff in Edisj.
  destruct (reify_pure_phis bid_latch_from lmap_latch (blk_phis b_hdr)) as [next_pevals |] eqn:Hr_next; [| discriminate Hr].
  destruct (RM.find br_exit bmap) as [b_exit |] eqn:Hf_exit; [| discriminate Hr].
  destruct (negb (list_empty_b (blk_phis b_exit))) eqn:Ep_exit; [discriminate Hr |].
  apply negb_false_iff, list_empty_b_nil in Ep_exit.
  destruct (reify_pure_code lmap_hdr_c (blk_code b_exit)) as [[evals_exit lmap_exit] |] eqn:Hr_exit; [| discriminate Hr].
  destruct (blk_term b_exit) as [[ti_x tm_x] md_x] eqn:Htm_exit.
  destruct tm_x as [[dt_r op_ret] | | | | | | | |]; try discriminate Hr.
  destruct dt_r as [tb_r | |]; try discriminate Hr;
    destruct tb_r as [w_ret | | | | | | | | | |]; try discriminate Hr.
  destruct (is_supported_bit_width w_ret) eqn:Hsup_ret; [| discriminate Hr].
  destruct (reify_pure_exp lmap_exit (Some (DTYPE_Base (DTYPE_I w_ret))) op_ret)
    as [[wr' ce_ret] |] eqn:Hr_ret; [| discriminate Hr].
  pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr_ret)) as ->.
  inversion Hr; subst hspecs' s; clear Hr; cbn [
    nls_bid_hdr nls_bid_latch_entry nls_bid_latch_from nls_bid_exit nls_latch_on_true
    nls_evals_entry nls_lmap_entry nls_init_pevals nls_evals_hdr nls_lmap_hdr_c nls_ce_cond
    nls_evals_body nls_lmap_latch nls_next_pevals nls_evals_exit nls_w_ret nls_ce_ret ].
  destruct (reify_pure_code_typing _ allowed lmap0 evals_entry lmap_entry Hlmap0 Hr_ent)
    as [Hfa_ent Hlmap_ent].
  pose proof (lmap_dom_code _ lmap0 evals_entry lmap_entry (args G) Hdom0 Hr_ent) as Hdom_ent.
  pose proof (reify_pure_phis_typing _ allowed (init G) lmap_entry init_pevals Hlmap_ent Hr_init) as Hfa_init.
  pose proof (Hwrap lmap_entry Hlmap_ent) as Hlmap_hdr0.
  destruct (reify_pure_code_typing _ cut_allowed _ evals_hdr lmap_hdr_c Hlmap_hdr0 Hr_hdr)
    as [Hfa_hdr Hlmap_hdrc].
  destruct (reify_pure_exp_typing op_cond cut_allowed lmap_hdr_c
              (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive ce_cond Hlmap_hdrc Hr_cond)
    as (_ & Hwt_cond & Hbw_cond & Hlf_cond & Hfv_cond).
  assert (Hlatch_ty :
    Forall (wf_pure_eval_entry cut_allowed) evals_body /\
    wf_pure_lmap cut_allowed lmap_latch).
  { destruct (raw_id_eqb br_latch bid_hdr) eqn:Eself.
    - inversion Elatch; subst; split; [constructor | exact Hlmap_hdrc].
    - destruct (RM.find br_latch bmap) as [b_body |]; [| discriminate Elatch].
      destruct (list_empty_b (blk_phis b_body)); [| discriminate Elatch].
      destruct (blk_term b_body) as [[_ tm_b] _]; destruct tm_b; try discriminate Elatch.
      destruct (reify_pure_code lmap_hdr_c (blk_code b_body)) as [[eb ll] |] eqn:Hrb; [| discriminate Elatch].
      destruct (raw_id_eqb br bid_hdr); [| discriminate Elatch].
      inversion Elatch; subst; exact (reify_pure_code_typing _ cut_allowed lmap_hdr_c evals_body lmap_latch Hlmap_hdrc Hrb). }
  destruct Hlatch_ty as [Hfa_body Hlmap_latch].
  pose proof (reify_pure_phis_typing _ cut_allowed bid_latch_from lmap_latch next_pevals Hlmap_latch Hr_next)
    as Hfa_next.
  destruct (reify_pure_code_typing _ cut_allowed lmap_hdr_c evals_exit lmap_exit Hlmap_hdrc Hr_exit)
    as [Hfa_exit Hlmap_exit].
  destruct (reify_pure_exp_typing op_ret cut_allowed lmap_exit
              (Some (DTYPE_Base (DTYPE_I w_ret))) w_ret ce_ret Hlmap_exit Hr_ret)
    as (_ & Hwt_ret & Hbw_ret & Hlf_ret & Hfv_ret).
  exists b_entry, b_hdr.
  split; [exact Hf_ent | split; [exact Hf_hdr | split; [exact Ehspecs | split; [exact Hr_init | split; [exact Hr_next |]]]]].
  split; [exact Hlmap_ent | split; [exact Hdom_ent | split; [exact Hfa_ent | split; [exact Hfa_init |]]]].
  split; [exact Hfa_hdr | split; [repeat split; assumption | split; [exact Hbw_cond |]]].
  split; [exact Hfa_body | split; [exact Hfa_next | split; [exact Hfa_exit |]]].
  split; [repeat split; assumption | split; [exact Hbw_ret | split; [exact Hsup_ret | split]]].
  - (* Entry block step *)
    intros Pa varargs penv env0 Henv0.
    destruct (eval_reified_pure_code (blk_code b_entry) varargs penv lmap0 env0 evals_entry lmap_entry Henv0 Hr_ent)
      as [[Hub_e Hce_e] | (env_entry & Henv_e & Hfa_ev_e & _ & Hst_e)].
    + left; split; [| exact Hce_e].
      intros sigma; eapply denote_cfg_from_block_ub; [exact Hf_ent |].
      unfold denote_block; rewrite Ep_ent, Htm_ent.
      eapply cfg_steps_to_ub_bind_r;
        [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ (denote_empty_phis_ret (init G) env0))
        | apply cfg_steps_to_ub_bind_l; exact (Hub_e sigma)].
    + right; exists env_entry; split; [exact Henv_e | split; [exact Hfa_ev_e |]].
      eapply denote_cfg_from_block_jump; [exact Hf_ent |].
      unfold denote_block; rewrite Ep_ent, Htm_ent.
      eapply pure_cfg_steps_bind; [apply denote_empty_phis_ret |].
      eapply pure_cfg_steps_bind; [exact Hst_e | apply PCS_Ret; reflexivity].
  - (* Header + Latch/Exit step *)
    intros Pa varargs penv_cut bid_prev env_prev dvs Hmap_dvs Hst_phis Henv_hdr0.
    destruct (eval_reified_pure_code (blk_code b_hdr) varargs penv_cut
                (wrap_cut lmap_entry hspecs) (apply_phi_env env_prev dvs)
                evals_hdr lmap_hdr_c Henv_hdr0 Hr_hdr)
      as [[Hub_h (ce_h & msg_h & Hin_h & Hev_h)] | (env_hdr_c & Henv_hc & Hfa_ev_h & Hpres_h & Hst_h)].
    + left; split.
      * intros sigma; eapply denote_cfg_from_block_ub; [exact Hf_hdr |].
        unfold denote_block.
        eapply cfg_steps_to_ub_bind_r;
          [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_phis)
          | apply cfg_steps_to_ub_bind_l; exact (Hub_h sigma)].
      * left; exists ce_h, msg_h; split; [right; exact Hin_h | exact Hev_h].
    + destruct (eval_reified_pure_exp op_cond penv_cut lmap_hdr_c env_hdr_c
                  (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive ce_cond Henv_hc Hr_cond)
        as [[Hub_c [msg_c Hev_c]] | [dv_c [Hev_c [Hsc_c Hst_c]]]].
      * left; split.
        -- intros sigma; eapply denote_cfg_from_block_ub; [exact Hf_hdr |].
           unfold denote_block; rewrite Htm_hdr.
           eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_phis) |].
           eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_h) |].
           cbn [denote_terminator]; unfold denote_exp'.
           apply cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub_c sigma).
        -- left; exists ce_cond, msg_c; split; [left; reflexivity | exact Hev_c].
      * destruct Hsc_c as [-> | [cbit ->]].
        -- left; split; [| right; exact Hev_c].
           intros sigma; eapply denote_cfg_from_block_ub; [exact Hf_hdr |].
           unfold denote_block; rewrite Htm_hdr.
           eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_phis) |].
           eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_h) |].
           cbn [denote_terminator]; unfold denote_exp'.
           eapply cfg_steps_to_ub_bind_r;
             [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst_c))
             | eapply CSU_UB; reflexivity].
        -- right; exists cbit; split; [exact Hfa_ev_h | split; [exact Hev_c |]].
           set (br_tgt := if (@Integers.unsigned 1 cbit =? 1)%Z then br1 else br2).
           assert (Hhdr_jump :
             pure_cfg_steps_to_tau env_prev
               (denote_cfg_from bmap varargs (bid_prev, bid_hdr))
               env_hdr_c
               (denote_cfg_from bmap varargs (bid_hdr, br_tgt))).
           { eapply denote_cfg_from_block_jump; [exact Hf_hdr |].
             unfold denote_block; rewrite Htm_hdr.
             eapply pure_cfg_steps_bind; [exact Hst_phis |].
             eapply pure_cfg_steps_bind; [exact Hst_h |].
             cbn [denote_terminator]; unfold denote_exp'.
             eapply pure_cfg_steps_bind; [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst_c) |].
             rewrite bit_int_1_equ_one_eq_unsigned; unfold br_tgt.
             destruct (@Integers.unsigned 1 cbit =? 1)%Z; apply PCS_Ret; reflexivity. }
           assert (Hpres_hc_dom :
             forall r, In r (args G ++ code_written_ids (blk_code b_entry)) ->
               ~ In r body_wr ->
               RM.find r env_hdr_c = RM.find r env_prev).
           { intros r Hdom _.
             pose proof (disjoint_raw_ids_spec _ _ r Edisj Hdom) as Hnin_loop.
             rewrite (Hpres_h r (fun Hc => Hnin_loop (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl Hc)))))).
             apply apply_phi_env_preserves_not_in.
             rewrite Hmap_dvs; intros Hp; exact (Hnin_loop (proj2 (in_app_iff _ _ _) (or_introl Hp))). }
           split.
           ++ (* Latch branch *)
              intros Econt.
              assert (Hbr_latch : br_tgt = br_latch).
              { unfold br_tgt; rewrite (Hpol_br (@Integers.unsigned 1 cbit =? 1)%Z), Econt; reflexivity. }
              rewrite Hbr_latch in Hhdr_jump.
              destruct (raw_id_eqb br_latch bid_hdr) eqn:Eself.
              ** apply raw_id_eqb_eq in Eself; inversion Elatch;
                   subst br_latch bid_latch_from evals_body lmap_latch body_wr.
                 right; exists env_hdr_c.
                 split; [exact Henv_hc | split; [constructor | split; [intros r Hr; exact (Hpres_hc_dom r Hr (fun H => H)) | exact Hhdr_jump]]].
              ** destruct (RM.find br_latch bmap) as [b_body |] eqn:Hf_body; [| discriminate Elatch].
                 destruct (list_empty_b (blk_phis b_body)) eqn:Ep_body; [| discriminate Elatch].
                 apply list_empty_b_nil in Ep_body.
                 destruct (blk_term b_body) as [[ti_b tm_b] md_b] eqn:Htm_body.
                 destruct tm_b as [| | | br_back | | | | |]; try discriminate Elatch.
                 destruct (reify_pure_code lmap_hdr_c (blk_code b_body))
                   as [[eb0 ll0] |] eqn:Hr_body; [| discriminate Elatch].
                 destruct (raw_id_eqb br_back bid_hdr) eqn:Eback; [| discriminate Elatch].
                 apply raw_id_eqb_eq in Eback; inversion Elatch;
                   subst br_back bid_latch_from evals_body lmap_latch body_wr; clear Elatch.
                 destruct (eval_reified_pure_code (blk_code b_body) varargs penv_cut lmap_hdr_c env_hdr_c eb0 ll0 Henv_hc Hr_body)
                   as [[Hub_b Hce_b] | (env_latch & Henv_l & Hfa_ev_b & Hpres_b & Hst_b)].
                 --- left; split; [| exact Hce_b].
                     intros sigma; eapply pure_cfg_steps_to_tau_then_ub; [exact Hhdr_jump |].
                     eapply denote_cfg_from_block_ub; [exact Hf_body |].
                     unfold denote_block; rewrite Ep_body, Htm_body.
                     eapply cfg_steps_to_ub_bind_r;
                       [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ (denote_empty_phis_ret bid_hdr env_hdr_c))
                       | apply cfg_steps_to_ub_bind_l; exact (Hub_b sigma)].
                 --- right; exists env_latch.
                     split; [exact Henv_l | split; [exact Hfa_ev_b | split]].
                     +++ intros r Hdom.
                         pose proof (disjoint_raw_ids_spec _ _ r Edisj Hdom) as Hnin_loop.
                         assert (Hnin_b : ~ In r (code_written_ids (blk_code b_body)))
                           by (intros Hb; exact (Hnin_loop (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_intror Hb)))))).
                         rewrite (Hpres_b r Hnin_b); exact (Hpres_hc_dom r Hdom Hnin_b).
                     +++ eapply pure_cfg_steps_to_tau_trans; [exact Hhdr_jump |].
                         eapply denote_cfg_from_block_jump; [exact Hf_body |].
                         unfold denote_block; rewrite Ep_body, Htm_body.
                         eapply pure_cfg_steps_bind; [apply denote_empty_phis_ret |].
                         eapply pure_cfg_steps_bind; [exact Hst_b | apply PCS_Ret; reflexivity].
           ++ (* Exit branch *)
              intros Eexit.
              assert (Hbr_exit : br_tgt = br_exit).
              { unfold br_tgt; rewrite (Hpol_br (@Integers.unsigned 1 cbit =? 1)%Z), Eexit; reflexivity. }
              rewrite Hbr_exit in Hhdr_jump.
              destruct (eval_reified_pure_code (blk_code b_exit) varargs penv_cut lmap_hdr_c env_hdr_c evals_exit lmap_exit Henv_hc Hr_exit)
                as [[Hub_x (ce_x & msg_x & Hin_x & Hev_x)] | (env_exit & Henv_x & Hfa_ev_x & _ & Hst_x)].
              ** left; split.
                 --- intros sigma; eapply pure_cfg_steps_to_tau_then_ub; [exact Hhdr_jump |].
                     eapply denote_cfg_from_block_ub; [exact Hf_exit |].
                     unfold denote_block; rewrite Ep_exit, Htm_exit.
                     eapply cfg_steps_to_ub_bind_r;
                       [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ (denote_empty_phis_ret bid_hdr env_hdr_c))
                       | apply cfg_steps_to_ub_bind_l; exact (Hub_x sigma)].
                 --- exists ce_x, msg_x; split; [right; exact Hin_x | exact Hev_x].
              ** destruct (eval_reified_pure_exp op_ret penv_cut lmap_exit env_exit
                             (Some (DTYPE_Base (DTYPE_I w_ret))) w_ret ce_ret Henv_x Hr_ret)
                   as [[Hub_r [msg_r Hev_r]] | [dv_ret [Hev_r [Hsc_r Hst_r]]]].
                 --- left; split.
                     +++ intros sigma; eapply pure_cfg_steps_to_tau_then_ub; [exact Hhdr_jump |].
                         eapply denote_cfg_from_block_ub; [exact Hf_exit |].
                         unfold denote_block; rewrite Ep_exit, Htm_exit.
                         eapply cfg_steps_to_ub_bind_r;
                           [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ (denote_empty_phis_ret bid_hdr env_hdr_c)) |].
                         eapply cfg_steps_to_ub_bind_r;
                           [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_x) |].
                         cbn [denote_terminator]; unfold denote_exp'.
                         apply cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub_r sigma).
                     +++ exists ce_ret, msg_r; split; [left; reflexivity | exact Hev_r].
                 --- right; exists env_exit, dv_ret.
                     split; [exact Hfa_ev_x | split; [exact Hev_r | split; [exact Hsc_r |]]].
                     eapply pure_cfg_steps_to_tau_then_ret; [exact Hhdr_jump |].
                     eapply denote_cfg_from_block_ret; [exact Hf_exit |].
                     unfold denote_block; rewrite Ep_exit, Htm_exit.
                     eapply pure_cfg_steps_bind; [apply denote_empty_phis_ret |].
                     eapply pure_cfg_steps_bind; [exact Hst_x |].
                     cbn [denote_terminator]; unfold denote_exp'.
                     eapply pure_cfg_steps_bind;
                       [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst_r) | apply PCS_Ret; reflexivity].
Qed.

Lemma wf_pure_lmap_mono :
  forall allowed1 allowed2 lmap,
    incl allowed1 allowed2 ->
    wf_pure_lmap allowed1 lmap ->
    wf_pure_lmap allowed2 lmap.
Proof.
  intros allowed1 allowed2 lmap Hinc H r w ce Hf.
  destruct (H r w ce Hf) as (Hwt & Hbw & Hlf & Hfv).
  repeat split; try assumption; intros u Hu; exact (Hinc u (Hfv u Hu)).
Qed.

Lemma NoDup_app_r {A : Type} :
  forall (xs ys : list A), NoDup (xs ++ ys) -> NoDup ys.
Proof.
  induction xs as [| x rx IH]; intros ys Hnd; cbn in Hnd; [exact Hnd |].
  inversion Hnd as [| ? ? _ Hndr]; exact (IH ys Hndr).
Qed.

Lemma NoDup_app_disj {A : Type} :
  forall (xs ys : list A) x, NoDup (xs ++ ys) -> In x xs -> ~ In x ys.
Proof.
  induction xs as [| x0 rx IH]; intros ys x Hnd Hin; cbn in *; [contradiction |].
  inversion Hnd as [| ? ? Hnin Hndr]; subst.
  destruct Hin as [-> | Hrx].
  - intros Hy; apply Hnin, in_app_iff; right; exact Hy.
  - exact (IH ys x Hndr Hrx).
Qed.

Lemma bool_eqb_swap_inv :
  forall x p b : bool, Bool.eqb x p = b -> x = Bool.eqb b p.
Proof.
  intros [] [] [] H; try discriminate H; reflexivity.
Qed.

Lemma eff_loop_cond_typing :
  forall allowed pol ce,
    wf_pure_eval_entry allowed ce ->
    cert_expr_bit_width ce = 1%positive ->
    wf_pure_eval_entry allowed (eff_loop_cond pol ce) /\
    cert_expr_bit_width (eff_loop_cond pol ce) = 1%positive.
Proof.
  intros allowed [|] ce (Hwt & Hlf & Hfv) Hbw; cbn [eff_loop_cond].
  - split; [repeat split; assumption | exact Hbw].
  - split; [| reflexivity].
    repeat split.
    + cbn [wt_cert_expr]; rewrite Hwt, Hbw; reflexivity.
    + cbn [is_let_free_expr]; rewrite Hlf, !Bool.andb_true_r; reflexivity.
    + cbn [collect_free_vars]; rewrite !app_nil_r; exact Hfv.
Qed.

Lemma eff_loop_cond_poison {Pa : Params} :
  forall (penv : param_env Pa) pol ce,
    eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret (DVALUE_Base DVALUE_Poison) ->
    eval_closed_cert_expr penv dummy_freeze_oracle (eff_loop_cond pol ce) =
    raise_ret (DVALUE_Base DVALUE_Poison).
Proof.
  intros penv [|] ce Hev; [exact Hev |].
  unfold eval_closed_cert_expr in *; cbn [eff_loop_cond eval_cert_expr]; rewrite Hev; reflexivity.
Qed.

Fixpoint filter_param_ub_ctx (src_pnames : list string) (ctx : ub_ctx)
  {struct ctx} : ub_ctx :=
  match ctx with
  | [] => []
  | UBA_ParamNoUndef nm w :: rest =>
      if string_in_list nm src_pnames
      then UBA_ParamNoUndef nm w :: filter_param_ub_ctx src_pnames rest
      else filter_param_ub_ctx src_pnames rest
  | UBA_PtrNonNull nm :: rest =>
      if string_in_list nm src_pnames
      then UBA_PtrNonNull nm :: filter_param_ub_ctx src_pnames rest
      else filter_param_ub_ctx src_pnames rest
  | UBA_PtrDereferenceable nm n :: rest =>
      if string_in_list nm src_pnames
      then UBA_PtrDereferenceable nm n :: filter_param_ub_ctx src_pnames rest
      else filter_param_ub_ctx src_pnames rest
  | UBA_PtrAligned nm al :: rest =>
      if string_in_list nm src_pnames
      then UBA_PtrAligned nm al :: filter_param_ub_ctx src_pnames rest
      else filter_param_ub_ctx src_pnames rest
  | _ :: rest => filter_param_ub_ctx src_pnames rest
  end.

Lemma filter_param_ub_ctx_holds {Pa : Params} :
  forall src_pnames ctx (bs : list (string * @dvalue Pa)) (penv : param_env Pa) foracle,
    (forall x, In x src_pnames -> ~ In x (List.map fst bs)) ->
    ub_ctx_holds penv foracle ctx ->
    ub_ctx_holds (extend_penv bs penv) foracle (filter_param_ub_ctx src_pnames ctx).
Proof.
  intros src_pnames ctx bs penv foracle Hdisj Hctx.
  induction Hctx as [| ua rest Hua _ IH]; cbn [filter_param_ub_ctx]; [constructor |].
  destruct ua as [nm w | nm | nm al | nm n | | | | |]; try exact IH;
    (destruct (string_in_list nm src_pnames) eqn:Ein; [| exact IH]);
    apply string_in_list_spec in Ein;
    (constructor; [| exact IH]);
    cbn [ub_assumption_holds] in *; intros dv Hpm;
    rewrite (extend_penv_not_in bs penv nm (Hdisj nm Ein)) in Hpm;
    exact (Hua dv Hpm).
Qed.

Fixpoint fold_ub_assumptions
  (allowed : list (string * positive))
  (prior_evals prior_brs : list cert_expr)
  (ctx : ub_ctx)
  (uas : list ub_assumption)
  {struct uas} : option ub_ctx :=
  match uas with
  | [] => Some ctx
  | ua :: rest =>
      if check_ub_assumption_justified allowed prior_evals prior_brs CD_RetVoid ctx ua
      then fold_ub_assumptions allowed prior_evals prior_brs (ua :: ctx) rest
      else None
  end.

Lemma fold_ub_assumptions_sound {Pa : Params} :
  forall uas allowed prior_evals prior_brs ctx ctx_out (penv : param_env Pa) foracle,
    wf_param_env_for allowed penv ->
    (forall big, In big prior_evals ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed) ->
    (forall big, In big prior_evals ->
      exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv) ->
    (forall c, In c prior_brs ->
      exists cbit : @Integers.bit_int 1,
        eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))) ->
    ub_ctx_holds penv foracle ctx ->
    fold_ub_assumptions allowed prior_evals prior_brs ctx uas = Some ctx_out ->
    ub_ctx_holds penv foracle ctx_out.
Proof.
  induction uas as [| ua rest IH];
    intros allowed prior_evals prior_brs ctx ctx_out penv foracle Hpenv Hpwf Hpret Hpbr Hctx Hf;
    cbn [fold_ub_assumptions] in Hf.
  - inversion Hf; subst; exact Hctx.
  - destruct (check_ub_assumption_justified allowed prior_evals prior_brs CD_RetVoid ctx ua) eqn:Ej;
      [| discriminate Hf].
    pose proof (check_ub_assumption_justified_sound allowed prior_evals prior_brs CD_RetVoid ctx ua
                  penv foracle NONE eq_refl Hpenv Hpwf Hpret Hpbr eq_refl Hctx Ej) as Hua.
    exact (IH allowed prior_evals prior_brs (ua :: ctx) ctx_out penv foracle
             Hpenv Hpwf Hpret Hpbr (Forall_cons _ Hua Hctx) Hf).
Qed.

Lemma extend_penv_wf_param_union {Pa : Params} :
  forall allowed pspecs (dvs_s dvs_t : list (raw_id * @dvalue Pa)) (penv : param_env Pa),
    wf_param_env_for allowed penv ->
    cut_phi_rel pspecs dvs_s dvs_t ->
    NoDup (cut_names_from 0%nat pspecs) ->
    (forall nm w, In (nm, w) allowed -> ~ In nm (cut_names_from 0%nat pspecs)) ->
    wf_param_env_for (allowed ++ cut_vars_from 0%nat pspecs)
      (extend_penv (cut_bindings_from 0%nat pspecs dvs_s dvs_t) penv).
Proof.
  intros allowed pspecs dvs_s dvs_t penv Hpenv Hrel Hnd Hdisj nm w Hin.
  set (bs := cut_bindings_from 0%nat pspecs dvs_s dvs_t).
  pose proof (cut_bindings_fst pspecs dvs_s dvs_t 0%nat Hrel) as Hfst; fold bs in Hfst.
  apply in_app_iff in Hin as [Hina | Hinc].
  - destruct (Hpenv nm w Hina) as [dv [Hpm Hsc]].
    exists dv; split; [| exact Hsc].
    rewrite extend_penv_not_in; [exact Hpm | rewrite Hfst; exact (Hdisj nm w Hina)].
  - assert (Hnd_bs : NoDup (List.map fst bs)) by (rewrite Hfst; exact Hnd).
    exact (cut_bindings_wf_param pspecs dvs_s dvs_t 0%nat bs penv Hrel Hnd_bs (incl_refl bs) nm w Hinc).
Qed.

Definition check_loop_cutpoint_cfg
  (allowed : list (string * positive))
  (init_ctx : ub_ctx)
  (src_cfg tgt_cfg : CFG.cfg dtyp)
  (cert : proof_certificate)
  (lci : loop_cutpoint_invariant)
  (opt_pf : option (list lrat_step)) : bool :=
  let src_pnames := List.map cert_reg_name (args src_cfg) in
  let src_uses := param_idx_uses_cfg src_cfg in
  let tgt_uses := param_idx_uses_cfg tgt_cfg in
  forallb (fun '(nm, _) => string_in_list nm src_pnames) allowed &&
  let lmap0_s := init_param_lmap (args src_cfg) src_pnames src_uses in
  let lmap0_t := init_param_lmap (args tgt_cfg) src_pnames tgt_uses in
  match reify_natural_loop src_cfg (lci_src_header lci) lmap0_s (overlay_hspecs_s 0%nat),
        reify_natural_loop tgt_cfg (lci_tgt_header lci) lmap0_t (overlay_hspecs_t 0%nat) with
  | Some (hspecs_s, s_s), Some (hspecs_t, s_t) =>
      match pair_phi_specs hspecs_s hspecs_t with
      | None => false
      | Some pspecs =>
          let cut_allowed := allowed ++ cut_vars_from 0%nat pspecs in
          no_dup_strings (src_pnames ++ cut_names_from 0%nat pspecs) &&
          match fold_ub_assumptions allowed (nls_evals_entry s_s) [] init_ctx
                  (block_uas_for (init src_cfg) (pc_blocks cert)) with
          | None => false
          | Some ctx_ent =>
              forallb (expr_safe_under_src ctx_ent (nls_evals_entry s_s)) (nls_evals_entry s_t) &&
              forallb (expr_safe_under_src ctx_ent
                         (nls_evals_entry s_s ++ peval_exprs (nls_init_pevals s_s)))
                      (peval_exprs (nls_init_pevals s_t)) &&
              check_pevals_refine ctx_ent opt_pf pspecs
                (nls_init_pevals s_s) (nls_init_pevals s_t) &&
              let base_loop_ctx := filter_param_ub_ctx src_pnames ctx_ent in
              match fold_ub_assumptions cut_allowed (nls_evals_hdr s_s) [nls_ce_cond s_s]
                      base_loop_ctx (block_uas_for (nls_bid_hdr s_s) (pc_blocks cert)) with
              | None => false
              | Some ctx_hdr =>
                  let eff_s := eff_loop_cond (nls_latch_on_true s_s) (nls_ce_cond s_s) in
                  let eff_t := eff_loop_cond (nls_latch_on_true s_t) (nls_ce_cond s_t) in
                  forallb (expr_safe_under_src ctx_hdr (nls_evals_hdr s_s))
                    (nls_ce_cond s_t :: nls_evals_hdr s_t) &&
                  check_expr_refines_with_lrat ctx_hdr eff_s eff_t opt_pf &&
                  let ctx_cont_0 :=
                    extract_branch_cond_assumptions (nls_latch_on_true s_s) (nls_ce_cond s_s) ++ ctx_hdr in
                  let latch_uas :=
                    if raw_id_eqb (nls_bid_latch_entry s_s) (nls_bid_hdr s_s) then []
                    else block_uas_for (nls_bid_latch_entry s_s) (pc_blocks cert) in
                  match fold_ub_assumptions cut_allowed
                          (nls_evals_hdr s_s ++ nls_evals_body s_s) [nls_ce_cond s_s]
                          ctx_cont_0 latch_uas with
                  | None => false
                  | Some ctx_cont =>
                      forallb (expr_safe_under_src ctx_cont
                                 (nls_evals_hdr s_s ++ nls_evals_body s_s))
                              (nls_evals_body s_t) &&
                      forallb (expr_safe_under_src ctx_cont
                                 ((nls_evals_hdr s_s ++ nls_evals_body s_s) ++
                                  peval_exprs (nls_next_pevals s_s)))
                              (peval_exprs (nls_next_pevals s_t)) &&
                      check_pevals_refine ctx_cont opt_pf pspecs
                        (nls_next_pevals s_s) (nls_next_pevals s_t) &&
                      let ctx_exit_0 :=
                        extract_branch_cond_assumptions
                          (negb (nls_latch_on_true s_s)) (nls_ce_cond s_s) ++ ctx_hdr in
                      match fold_ub_assumptions cut_allowed
                              (nls_evals_hdr s_s ++ nls_evals_exit s_s) [nls_ce_cond s_s]
                              ctx_exit_0 (block_uas_for (nls_bid_exit s_s) (pc_blocks cert)) with
                      | None => false
                      | Some ctx_exit =>
                          match pc_return_obligation cert with
                          | RO_VoidEquiv => false
                          | RO_ScalarRefines w _ _ _ =>
                              Pos.eqb w (nls_w_ret s_s) &&
                              Pos.eqb w (nls_w_ret s_t) &&
                              forallb (expr_safe_under_src ctx_exit
                                         (nls_evals_hdr s_s ++ nls_evals_exit s_s))
                                      (nls_ce_ret s_t :: nls_evals_exit s_t) &&
                              check_expr_refines_with_lrat ctx_exit
                                (nls_ce_ret s_s) (nls_ce_ret s_t) opt_pf
                          end
                      end
                  end
              end
          end
      end
  | _, _ => false
  end.

Lemma forall_ret_in {Pa : Params} :
  forall (es : list cert_expr) (penv : param_env Pa) foracle,
    Forall (fun ce => exists dv, eval_closed_cert_expr penv foracle ce = raise_ret dv) es ->
    forall big, In big es -> exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv.
Proof.
  intros es penv foracle Hfa; rewrite Forall_forall in Hfa; exact Hfa.
Qed.

Lemma forall_wf_pure_in :
  forall allowed es,
    Forall (wf_pure_eval_entry allowed) es ->
    forall big, In big es ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed.
Proof.
  intros allowed es Hfa; rewrite Forall_forall in Hfa; exact Hfa.
Qed.

Lemma check_loop_cutpoint_cfg_open_sound {Pa : Params} :
  forall allowed init_ctx (src_cfg tgt_cfg : CFG.cfg dtyp)
         cert lci opt_pf arg_dtys (vs : list (@dvalue Pa)),
    NoDup (args src_cfg) ->
    NoDup (args tgt_cfg) ->
    NoDup (List.map cert_reg_name (args src_cfg)) ->
    List.length (args src_cfg) = List.length (args tgt_cfg) ->
    List.length arg_dtys = List.length (args src_cfg) ->
    cfg_param_dtyp_compatible src_cfg arg_dtys = true ->
    cfg_param_dtyp_compatible tgt_cfg arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx w0 pnm,
       In (idx, DTYPE_Base (DTYPE_I w0)) (param_idx_uses_cfg src_cfg) ->
       nth_error (List.map cert_reg_name (args src_cfg)) idx = Some pnm ->
       In (pnm, w0) allowed) ->
    (forall idx w0 pnm,
       In (idx, DTYPE_Base (DTYPE_I w0)) (param_idx_uses_cfg tgt_cfg) ->
       nth_error (List.map cert_reg_name (args src_cfg)) idx = Some pnm ->
       In (pnm, w0) allowed) ->
    wf_param_env_for allowed (build_param_env (List.map cert_reg_name (args src_cfg)) vs) ->
    ub_ctx_holds (build_param_env (List.map cert_reg_name (args src_cfg)) vs)
      dummy_freeze_oracle init_ctx ->
    check_loop_cutpoint_cfg allowed init_ctx src_cfg tgt_cfg cert lci opt_pf = true ->
    ow_itree_refines dvalue_refines
      (eval_cfg_open src_cfg vs)
      (eval_cfg_open tgt_cfg vs).
Proof.
  intros allowed init_ctx src_cfg tgt_cfg cert lci opt_pf arg_dtys vs
         Hnd_sa Hnd_ta Hnd_sp Hlen_st Hlen_da Hcomp_s Hcomp_t Hvs
         Hpu_s Hpu_t Hpenv0 Hinit_ctx Hchk.
  unfold check_loop_cutpoint_cfg in Hchk; cbn zeta in Hchk.
  set (src_pnames := List.map cert_reg_name (args src_cfg)) in *.
  set (src_uses := param_idx_uses_cfg src_cfg) in *.
  set (tgt_uses := param_idx_uses_cfg tgt_cfg) in *.
  set (lmap0_s := init_param_lmap (args src_cfg) src_pnames src_uses) in *.
  set (lmap0_t := init_param_lmap (args tgt_cfg) src_pnames tgt_uses) in *.
  apply andb_true_iff in Hchk as [Hall_in Hchk].
  destruct (reify_natural_loop src_cfg (lci_src_header lci) lmap0_s (overlay_hspecs_s 0%nat))
    as [[hspecs_s s_s] |] eqn:Er_s; [| discriminate Hchk].
  destruct (reify_natural_loop tgt_cfg (lci_tgt_header lci) lmap0_t (overlay_hspecs_t 0%nat))
    as [[hspecs_t s_t] |] eqn:Er_t; [| discriminate Hchk].
  destruct (pair_phi_specs hspecs_s hspecs_t) as [pspecs |] eqn:Epair; [| discriminate Hchk].
  set (cut_allowed := allowed ++ cut_vars_from 0%nat pspecs) in *.
  apply andb_true_iff in Hchk as [Hnd_all Hchk].
  apply no_dup_strings_spec in Hnd_all.
  pose proof (NoDup_app_r _ _ Hnd_all) as Hnd_cut.
  pose proof (NoDup_app_disj _ _ ) as Hdisj_gen.
  assert (Hdisj_sp_cut : forall x, In x src_pnames -> ~ In x (cut_names_from 0%nat pspecs))
    by (intros x Hx; exact (NoDup_app_disj _ _ x Hnd_all Hx)).
  assert (Hall_not_cut : forall nm w, In (nm, w) allowed -> ~ In nm (cut_names_from 0%nat pspecs)).
  { intros nm w Hin; rewrite forallb_forall in Hall_in.
    pose proof (Hall_in (nm, w) Hin) as Hsin; cbn in Hsin.
    apply string_in_list_spec in Hsin; exact (Hdisj_sp_cut nm Hsin). }
  destruct (fold_ub_assumptions allowed (nls_evals_entry s_s) [] init_ctx
              (block_uas_for (init src_cfg) (pc_blocks cert))) as [ctx_ent |] eqn:Ef_ent;
    [| discriminate Hchk].
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as (((Hsafe_ent_t & Hsafe_init_t) & Href_init) & Hchk).
  set (base_loop_ctx := filter_param_ub_ctx src_pnames ctx_ent) in *.
  destruct (fold_ub_assumptions cut_allowed (nls_evals_hdr s_s) [nls_ce_cond s_s]
              base_loop_ctx (block_uas_for (nls_bid_hdr s_s) (pc_blocks cert)))
    as [ctx_hdr |] eqn:Ef_hdr; [| discriminate Hchk].
  set (eff_s := eff_loop_cond (nls_latch_on_true s_s) (nls_ce_cond s_s)) in *.
  set (eff_t := eff_loop_cond (nls_latch_on_true s_t) (nls_ce_cond s_t)) in *.
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as (([Hsafe_hdr_t Href_eff] & Hchk)).
  set (ctx_cont_0 := extract_branch_cond_assumptions (nls_latch_on_true s_s) (nls_ce_cond s_s) ++ ctx_hdr) in *.
  set (latch_uas := if raw_id_eqb (nls_bid_latch_entry s_s) (nls_bid_hdr s_s) then []
                    else block_uas_for (nls_bid_latch_entry s_s) (pc_blocks cert)) in *.
  destruct (fold_ub_assumptions cut_allowed (nls_evals_hdr s_s ++ nls_evals_body s_s)
              [nls_ce_cond s_s] ctx_cont_0 latch_uas) as [ctx_cont |] eqn:Ef_cont;
    [| discriminate Hchk].
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as (((Hsafe_body_t & Hsafe_next_t) & Href_next) & Hchk).
  set (ctx_exit_0 := extract_branch_cond_assumptions (negb (nls_latch_on_true s_s)) (nls_ce_cond s_s) ++ ctx_hdr) in *.
  destruct (fold_ub_assumptions cut_allowed (nls_evals_hdr s_s ++ nls_evals_exit s_s)
              [nls_ce_cond s_s] ctx_exit_0 (block_uas_for (nls_bid_exit s_s) (pc_blocks cert)))
    as [ctx_exit |] eqn:Ef_exit; [| discriminate Hchk].
  destruct (pc_return_obligation cert) as [| w_ro _ _ _]; [discriminate Hchk |].
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as (((Hws_ro & Hwt_ro) & Hsafe_exit_t) & Href_ret).
  apply Pos.eqb_eq in Hws_ro; apply Pos.eqb_eq in Hwt_ro.
  pose proof (pair_phi_specs_supported _ _ _ Epair) as Hsup_ps.
  assert (Hinc_cut_vars : incl (cut_vars_from 0%nat pspecs) cut_allowed)
    by (intros u Hu; apply in_app_iff; right; exact Hu).
  assert (Hinc_all_cut : incl allowed cut_allowed)
    by (intros u Hu; apply in_app_iff; left; exact Hu).
  assert (Hwrap_s : forall lmap, wf_pure_lmap allowed lmap ->
    wf_pure_lmap cut_allowed (overlay_hspecs_s 0%nat lmap hspecs_s)).
  { intros lmap Hl; destruct (pair_phi_specs_overlay _ _ _ 0%nat lmap lmap Epair) as (Hos & _).
    rewrite Hos; pose proof (wf_pure_lmap_mono _ _ lmap Hinc_all_cut Hl) as Hlc.
    exact (proj1 (overlay_cut_lmap_typing pspecs 0%nat cut_allowed lmap lmap Hsup_ps Hinc_cut_vars Hlc Hlc)). }
  assert (Hwrap_t : forall lmap, wf_pure_lmap allowed lmap ->
    wf_pure_lmap cut_allowed (overlay_hspecs_t 0%nat lmap hspecs_t)).
  { intros lmap Hl; destruct (pair_phi_specs_overlay _ _ _ 0%nat lmap lmap Epair) as (_ & Hot & _).
    rewrite Hot; pose proof (wf_pure_lmap_mono _ _ lmap Hinc_all_cut Hl) as Hlc.
    exact (proj2 (overlay_cut_lmap_typing pspecs 0%nat cut_allowed lmap lmap Hsup_ps Hinc_cut_vars Hlc Hlc)). }
  destruct (reify_natural_loop_spec src_cfg (lci_src_header lci) allowed cut_allowed
              lmap0_s (overlay_hspecs_s 0%nat) hspecs_s s_s
              (init_param_lmap_typing src_uses (args src_cfg) src_pnames allowed Hpu_s)
              (init_param_lmap_dom src_uses (args src_cfg) src_pnames)
              Hwrap_s Er_s)
    as (b_ent_s & b_hdr_s & Hf_ent_s & Hf_hdr_s & _ & Hr_init_s & Hr_next_s &
        Hlmap_ent_s & Hdom_ent_s & Hfa_ent_s & Hfa_init_s & Hfa_hdr_s &
        Hwf_cond_s & Hbw_cond_s & Hfa_body_s & Hfa_next_s & Hfa_exit_s &
        Hwf_ret_s & Hbw_ret_s & _ & Hstep_ent_s & Hstep_hdr_s).
  destruct (reify_natural_loop_spec tgt_cfg (lci_tgt_header lci) allowed cut_allowed
              lmap0_t (overlay_hspecs_t 0%nat) hspecs_t s_t
              (init_param_lmap_typing tgt_uses (args tgt_cfg) src_pnames allowed Hpu_t)
              (init_param_lmap_dom tgt_uses (args tgt_cfg) src_pnames)
              Hwrap_t Er_t)
    as (b_ent_t & b_hdr_t & Hf_ent_t & Hf_hdr_t & _ & Hr_init_t & Hr_next_t &
        Hlmap_ent_t & Hdom_ent_t & Hfa_ent_t & Hfa_init_t & Hfa_hdr_t &
        Hwf_cond_t & Hbw_cond_t & Hfa_body_t & Hfa_next_t & Hfa_exit_t &
        Hwf_ret_t & Hbw_ret_t & _ & Hstep_ent_t & Hstep_hdr_t).
  intros sigma_tgt Hwfsig_t.
  exists sigma_tgt; split; [exact Hwfsig_t |].
  set (penv := build_param_env src_pnames vs) in *.
  set (bmap_s := ocfg_map (blks src_cfg)) in *.
  set (bmap_t := ocfg_map (blks tgt_cfg)) in *.
  pose proof (List.Forall2_length Hvs) as Hlen_vs.
  assert (Hlen_sp : List.length src_pnames = List.length (args src_cfg))
    by (unfold src_pnames; apply List.length_map).
  assert (Hlp_s : List.length (args src_cfg) = List.length vs) by lia.
  assert (Hlp_t : List.length (args tgt_cfg) = List.length vs) by lia.
  assert (Hls_v : List.length src_pnames = List.length vs) by lia.
  pose proof (init_param_lmap_matches src_uses (args src_cfg) src_pnames arg_dtys vs
                Hnd_sa Hnd_sp Hlp_s Hls_v Hvs
                (cfg_param_dtyp_compatible_nth src_cfg arg_dtys Hcomp_s)) as Henv0_s.
  pose proof (init_param_lmap_matches tgt_uses (args tgt_cfg) src_pnames arg_dtys vs
                Hnd_ta Hnd_sp Hlp_t Hls_v Hvs
                (cfg_param_dtyp_compatible_nth tgt_cfg arg_dtys Hcomp_t)) as Henv0_t.
  fold penv lmap0_s in Henv0_s; fold penv lmap0_t in Henv0_t.
  change (denote_cfg src_cfg None) with (denote_cfg_from bmap_s None (init src_cfg, init src_cfg)).
  change (denote_cfg tgt_cfg None) with (denote_cfg_from bmap_t None (init tgt_cfg, init tgt_cfg)).
  destruct (Hstep_ent_s Pa None penv (init_cfg_locals (args src_cfg) vs) Henv0_s)
    as [[Hub_ent_s _] | (env_entry_s & Henv_ent_s & Hret_ent_s & Htau_ent_s)].
  - exact (cfg_steps_ub_det_ref dvalue_refines sigma_tgt
             (init_cfg_locals (args src_cfg) vs)
             (denote_cfg_from bmap_s None (init src_cfg, init src_cfg))
             _ (Hub_ent_s sigma_tgt)).
  - pose proof (fold_ub_assumptions_sound _ allowed (nls_evals_entry s_s) [] init_ctx ctx_ent
                  penv dummy_freeze_oracle Hpenv0
                  (forall_wf_pure_in _ _ Hfa_ent_s)
                  (forall_ret_in _ _ _ Hret_ent_s)
                  (fun _ H => False_ind _ H)
                  Hinit_ctx Ef_ent) as Hctx_ent.
    destruct (Hstep_ent_t Pa None penv (init_cfg_locals (args tgt_cfg) vs) Henv0_t)
      as [[_ (ce_et & msg_et & Hin_et & Hev_et)] | (env_entry_t & Henv_ent_t & _ & Htau_ent_t)].
    + exfalso; exact (exprs_safe_under_src_sound (nls_evals_entry s_t) allowed ctx_ent
                        (nls_evals_entry s_s) penv Hpenv0 Hctx_ent
                        (forall_ret_in _ _ _ Hret_ent_s) Hfa_ent_t Hsafe_ent_t
                        ce_et msg_et Hin_et Hev_et).
    + destruct (pure_phis_denote_step (blk_phis b_hdr_s) penv (init src_cfg)
                  (nls_lmap_entry s_s) env_entry_s (nls_init_pevals s_s) Henv_ent_s Hr_init_s)
        as [[Hub_ip_s _] | [dvs0_s [Hpm0_s Hst_ip_s]]].
      * assert (Hub_from_ent : cfg_steps_to_ub sigma_tgt (init_cfg_locals (args src_cfg) vs)
                  (denote_cfg_from bmap_s None (init src_cfg, init src_cfg))).
        { eapply pure_cfg_steps_to_tau_then_ub; [exact Htau_ent_s |].
          eapply denote_cfg_from_block_ub; [exact Hf_hdr_s |].
          unfold denote_block; apply cfg_steps_to_ub_bind_l; exact (Hub_ip_s sigma_tgt). }
        exact (cfg_steps_ub_det_ref dvalue_refines sigma_tgt _ _ _ Hub_from_ent).
      * pose proof (Forall_app _ (nls_evals_entry s_s) (peval_exprs (nls_init_pevals s_s))) as Hfa_app_ip.
        assert (Hret_ent_ip_s : Forall (fun ce => exists dv, eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv)
                                  (nls_evals_entry s_s ++ peval_exprs (nls_init_pevals s_s)))
          by (apply Forall_app; split; [exact Hret_ent_s | exact (peval_exprs_ret penv _ _ Hpm0_s)]).
        destruct (pure_phis_denote_step (blk_phis b_hdr_t) penv (init tgt_cfg)
                    (nls_lmap_entry s_t) env_entry_t (nls_init_pevals s_t) Henv_ent_t Hr_init_t)
          as [[_ (ce_ipt & msg_ipt & Hin_ipt & Hev_ipt)] | [dvs0_t [Hpm0_t Hst_ip_t]]].
        -- exfalso; exact (exprs_safe_under_src_sound (peval_exprs (nls_init_pevals s_t)) allowed ctx_ent
                             (nls_evals_entry s_s ++ peval_exprs (nls_init_pevals s_s)) penv Hpenv0 Hctx_ent
                             (forall_ret_in _ _ _ Hret_ent_ip_s)
                             (peval_exprs_typing _ _ Hfa_init_t) Hsafe_init_t
                             ce_ipt msg_ipt Hin_ipt Hev_ipt).
        -- destruct (check_pevals_refine_sound pspecs (nls_init_pevals s_s) (nls_init_pevals s_t)
                       dvs0_s dvs0_t allowed ctx_ent opt_pf penv Hpenv0 Hctx_ent
                       Hfa_init_s Hfa_init_t Hpm0_s Hpm0_t Href_init)
             as (Hrel0 & _ & _).
           assert (Hloop :
             forall bid_prev_s bid_prev_t env_prev_s env_prev_t dvs_s dvs_t,
               (forall r0, In r0 (args src_cfg ++ code_written_ids (blk_code b_ent_s)) ->
                  RM.find r0 env_prev_s = RM.find r0 env_entry_s) ->
               (forall r0, In r0 (args tgt_cfg ++ code_written_ids (blk_code b_ent_t)) ->
                  RM.find r0 env_prev_t = RM.find r0 env_entry_t) ->
               pure_cfg_steps env_prev_s (denote_phis bid_prev_s (blk_phis b_hdr_s))
                 (apply_phi_env env_prev_s dvs_s) tt ->
               pure_cfg_steps env_prev_t (denote_phis bid_prev_t (blk_phis b_hdr_t))
                 (apply_phi_env env_prev_t dvs_t) tt ->
               cut_phi_rel pspecs dvs_s dvs_t ->
               det_ref dvalue_refines
                 (run_draws sigma_tgt (run_cfg_locals env_prev_s
                    (denote_cfg_from bmap_s None (bid_prev_s, nls_bid_hdr s_s))))
                 (run_draws sigma_tgt (run_cfg_locals env_prev_t
                    (denote_cfg_from bmap_t None (bid_prev_t, nls_bid_hdr s_t))))).
           { pcofix CIH.
             intros bid_prev_s bid_prev_t env_prev_s env_prev_t dvs_s dvs_t
                    Hag_s Hag_t Hphis_s Hphis_t Hrel.
             set (bs := cut_bindings_from 0%nat pspecs dvs_s dvs_t).
             set (penv_cut := extend_penv bs penv).
             pose proof (cut_bindings_fst pspecs dvs_s dvs_t 0%nat Hrel) as Hbs_fst; fold bs in Hbs_fst.
             assert (Hnd_bs : NoDup (List.map fst bs)) by (rewrite Hbs_fst; exact Hnd_cut).
             assert (Hp_agree : forall nm w, In (nm, w) allowed -> penv nm = penv_cut nm).
             { intros nm w Hin; symmetry; unfold penv_cut; apply extend_penv_not_in.
               rewrite Hbs_fst; exact (Hall_not_cut nm w Hin). }
             pose proof (lmap_matches_env_transfer allowed _ penv penv_cut
                           (nls_lmap_entry s_s) env_entry_s env_prev_s
                           Hlmap_ent_s Hdom_ent_s Hp_agree Hag_s Henv_ent_s) as Hlm_prev_s.
             pose proof (lmap_matches_env_transfer allowed _ penv penv_cut
                           (nls_lmap_entry s_t) env_entry_t env_prev_t
                           Hlmap_ent_t Hdom_ent_t Hp_agree Hag_t Henv_ent_t) as Hlm_prev_t.
             destruct (overlay_cut_lmap_matches pspecs dvs_s dvs_t 0%nat bs penv
                         (nls_lmap_entry s_s) (nls_lmap_entry s_t) env_prev_s env_prev_t
                         Hrel Hnd_bs (incl_refl bs) Hlm_prev_s Hlm_prev_t)
               as [Hlm_hdr0_s Hlm_hdr0_t].
             destruct (pair_phi_specs_overlay hspecs_s hspecs_t pspecs 0%nat
                         (nls_lmap_entry s_s) (nls_lmap_entry s_t) Epair)
               as (Hos_eq & Hot_eq & Hms_eq & Hmt_eq).
             rewrite <- Hos_eq in Hlm_hdr0_s; rewrite <- Hot_eq in Hlm_hdr0_t.
             assert (Hmap_dvs :
               List.map fst dvs_s = List.map fst hspecs_s /\
               List.map fst dvs_t = List.map fst hspecs_t).
             { rewrite Hms_eq, Hmt_eq; clear -Hrel.
               induction Hrel; cbn; [split; reflexivity | destruct IHHrel as [Hs Ht]; split; f_equal; assumption]. }
             destruct Hmap_dvs as [Hmap_dvs_s Hmap_dvs_t].
             pose proof (extend_penv_wf_param_union allowed pspecs dvs_s dvs_t penv
                           Hpenv0 Hrel Hnd_cut Hall_not_cut) as Hpenv_cut;
               fold cut_allowed bs penv_cut in Hpenv_cut.
             destruct (Hstep_hdr_s Pa None penv_cut bid_prev_s env_prev_s dvs_s
                         Hmap_dvs_s Hphis_s Hlm_hdr0_s)
               as [[Hub_hs _] | (cbit_s & Hret_hdr_s & Hev_cond_s & Hcont_s & Hexit_s)].
             - eapply paco2_mon; [exact (cfg_steps_ub_det_ref dvalue_refines sigma_tgt _ _ _ (Hub_hs sigma_tgt)) | intros ? ? []].
             - assert (Hdisj_bs : forall x, In x src_pnames -> ~ In x (List.map fst bs))
                 by (rewrite Hbs_fst; exact Hdisj_sp_cut).
               pose proof (filter_param_ub_ctx_holds src_pnames ctx_ent bs penv dummy_freeze_oracle
                             Hdisj_bs Hctx_ent) as Hbase_ctx;
                 fold penv_cut base_loop_ctx in Hbase_ctx.
               assert (Hbr_hdr_s : forall c, In c [nls_ce_cond s_s] ->
                 exists cbit : @Integers.bit_int 1,
                   eval_closed_cert_expr penv_cut dummy_freeze_oracle c =
                   raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))).
               { intros c [<- | []]; exists cbit_s; exact Hev_cond_s. }
               pose proof (fold_ub_assumptions_sound _ cut_allowed (nls_evals_hdr s_s) [nls_ce_cond s_s]
                             base_loop_ctx ctx_hdr penv_cut dummy_freeze_oracle Hpenv_cut
                             (forall_wf_pure_in _ _ Hfa_hdr_s)
                             (forall_ret_in _ _ _ Hret_hdr_s)
                             Hbr_hdr_s Hbase_ctx Ef_hdr) as Hctx_hdr.
               destruct (eff_loop_cond_typing cut_allowed (nls_latch_on_true s_s) (nls_ce_cond s_s)
                           Hwf_cond_s Hbw_cond_s) as [(_ & _ & Hfv_eff_s) _].
               destruct (eff_loop_cond_typing cut_allowed (nls_latch_on_true s_t) (nls_ce_cond s_t)
                           Hwf_cond_t Hbw_cond_t) as [(_ & _ & Hfv_eff_t) _].
               fold eff_s in Hfv_eff_s; fold eff_t in Hfv_eff_t.
               destruct (eval_eff_loop_cond penv_cut (nls_latch_on_true s_s) (nls_ce_cond s_s)
                           cbit_s Hev_cond_s) as [ebit_s [Hev_eff_s Eebit_s]]; fold eff_s in Hev_eff_s.
               pose proof (check_expr_refines_with_lrat_sound ctx_hdr eff_s eff_t opt_pf
                             penv_cut dummy_freeze_oracle Href_eff
                             (fun n w0 H => Hpenv_cut n w0 (Hfv_eff_s (n, w0) H))
                             (fun n w0 H => Hpenv_cut n w0 (Hfv_eff_t (n, w0) H))
                             Hctx_hdr) as Href_eff_ev.
               rewrite Hev_eff_s in Href_eff_ev.
               destruct (Hstep_hdr_t Pa None penv_cut bid_prev_t env_prev_t dvs_t
                           Hmap_dvs_t Hphis_t Hlm_hdr0_t)
                 as [[_ [(ce_ht & msg_ht & Hin_ht & Hev_ht) | Hev_ct_ps]]
                    | (cbit_t & _ & Hev_cond_t & Hcont_t & Hexit_t)].
               + exfalso; exact (exprs_safe_under_src_sound (nls_ce_cond s_t :: nls_evals_hdr s_t)
                                   cut_allowed ctx_hdr (nls_evals_hdr s_s) penv_cut Hpenv_cut Hctx_hdr
                                   (forall_ret_in _ _ _ Hret_hdr_s)
                                   (Forall_cons _ Hwf_cond_t Hfa_hdr_t) Hsafe_hdr_t
                                   ce_ht msg_ht Hin_ht Hev_ht).
               + exfalso.
                 pose proof (eff_loop_cond_poison penv_cut (nls_latch_on_true s_t) (nls_ce_cond s_t) Hev_ct_ps)
                   as Hev_eff_t_ps; fold eff_t in Hev_eff_t_ps.
                 rewrite Hev_eff_t_ps in Href_eff_ev; cbn [refine_eou_dvalue] in Href_eff_ev.
                 destruct Href_eff_ev as [Habs | Habs]; discriminate Habs.
               + destruct (eval_eff_loop_cond penv_cut (nls_latch_on_true s_t) (nls_ce_cond s_t)
                             cbit_t Hev_cond_t) as [ebit_t [Hev_eff_t Eebit_t]]; fold eff_t in Hev_eff_t.
                 rewrite Hev_eff_t in Href_eff_ev; cbn [refine_eou_dvalue] in Href_eff_ev.
                 assert (Heb_eq : ebit_s = ebit_t).
                 { destruct Href_eff_ev as [Habs | Heq_dv]; [discriminate Habs |].
                   injection Heq_dv as Heq_i; exact (dvalue_I_same_sz_inj 1 ebit_s ebit_t Heq_i). }
                 subst ebit_t.
                 assert (Epol_eq :
                   Bool.eqb (@Integers.unsigned 1 cbit_t =? 1)%Z (nls_latch_on_true s_t) =
                   Bool.eqb (@Integers.unsigned 1 cbit_s =? 1)%Z (nls_latch_on_true s_s))
                   by congruence.
                 destruct Hwf_cond_s as (Hwt_cs & Hlf_cs & _).
                 destruct (Bool.eqb (@Integers.unsigned 1 cbit_s =? 1)%Z (nls_latch_on_true s_s)) eqn:Econt.
                 * (* Loop continues *)
                   pose proof (bool_eqb_swap_inv _ _ true Econt) as Ecbit_cont; cbn [Bool.eqb] in Ecbit_cont.
                   pose proof (extract_branch_cond_assumptions_sound penv_cut dummy_freeze_oracle
                                 (nls_latch_on_true s_s) (nls_ce_cond s_s) cbit_s ctx_hdr
                                 Hwt_cs Hlf_cs Hev_cond_s Ecbit_cont Hctx_hdr) as Hctx_cont0;
                     fold ctx_cont_0 in Hctx_cont0.
                   destruct (Hcont_s eq_refl)
                     as [[Hub_bs _] | (env_latch_s & Hlm_latch_s & Hret_body_s & Hpres_ls & Htau_s)].
                   -- eapply paco2_mon; [exact (cfg_steps_ub_det_ref dvalue_refines sigma_tgt _ _ _ (Hub_bs sigma_tgt)) | intros ? ? []].
                   -- assert (Hret_hb_s : Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
                                            (nls_evals_hdr s_s ++ nls_evals_body s_s))
                        by (apply Forall_app; split; assumption).
                      assert (Hwf_hb_s : Forall (wf_pure_eval_entry cut_allowed) (nls_evals_hdr s_s ++ nls_evals_body s_s))
                        by (apply Forall_app; split; assumption).
                      pose proof (fold_ub_assumptions_sound _ cut_allowed
                                    (nls_evals_hdr s_s ++ nls_evals_body s_s) [nls_ce_cond s_s]
                                    ctx_cont_0 ctx_cont penv_cut dummy_freeze_oracle Hpenv_cut
                                    (forall_wf_pure_in _ _ Hwf_hb_s)
                                    (forall_ret_in _ _ _ Hret_hb_s)
                                    Hbr_hdr_s Hctx_cont0 Ef_cont) as Hctx_cont.
                      destruct (pure_phis_denote_step (blk_phis b_hdr_s) penv_cut (nls_bid_latch_from s_s)
                                  (nls_lmap_latch s_s) env_latch_s (nls_next_pevals s_s) Hlm_latch_s Hr_next_s)
                        as [[Hub_np_s _] | [dvs_next_s [Hpm_next_s Hst_np_s]]].
                      ++ assert (Hub_latch_np : cfg_steps_to_ub sigma_tgt env_prev_s
                                   (denote_cfg_from bmap_s None (bid_prev_s, nls_bid_hdr s_s))).
                         { eapply pure_cfg_steps_to_tau_then_ub; [exact Htau_s |].
                           eapply denote_cfg_from_block_ub; [exact Hf_hdr_s |].
                           unfold denote_block; apply cfg_steps_to_ub_bind_l; exact (Hub_np_s sigma_tgt). }
                         eapply paco2_mon; [exact (cfg_steps_ub_det_ref dvalue_refines sigma_tgt _ _ _ Hub_latch_np) | intros ? ? []].
                      ++ destruct (Hcont_t Epol_eq)
                           as [[_ (ce_bt & msg_bt & Hin_bt & Hev_bt)]
                              | (env_latch_t & Hlm_latch_t & _ & Hpres_lt & Htau_t)].
                         ** exfalso; exact (exprs_safe_under_src_sound (nls_evals_body s_t) cut_allowed ctx_cont
                                              (nls_evals_hdr s_s ++ nls_evals_body s_s) penv_cut Hpenv_cut Hctx_cont
                                              (forall_ret_in _ _ _ Hret_hb_s) Hfa_body_t Hsafe_body_t
                                              ce_bt msg_bt Hin_bt Hev_bt).
                         ** assert (Hret_hbn_s :
                              Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
                                ((nls_evals_hdr s_s ++ nls_evals_body s_s) ++ peval_exprs (nls_next_pevals s_s)))
                              by (apply Forall_app; split; [exact Hret_hb_s | exact (peval_exprs_ret _ _ _ Hpm_next_s)]).
                            destruct (pure_phis_denote_step (blk_phis b_hdr_t) penv_cut (nls_bid_latch_from s_t)
                                        (nls_lmap_latch s_t) env_latch_t (nls_next_pevals s_t) Hlm_latch_t Hr_next_t)
                              as [[_ (ce_npt & msg_npt & Hin_npt & Hev_npt)] | [dvs_next_t [Hpm_next_t Hst_np_t]]].
                            --- exfalso; exact (exprs_safe_under_src_sound (peval_exprs (nls_next_pevals s_t))
                                                  cut_allowed ctx_cont
                                                  ((nls_evals_hdr s_s ++ nls_evals_body s_s) ++ peval_exprs (nls_next_pevals s_s))
                                                  penv_cut Hpenv_cut Hctx_cont
                                                  (forall_ret_in _ _ _ Hret_hbn_s)
                                                  (peval_exprs_typing _ _ Hfa_next_t) Hsafe_next_t
                                                  ce_npt msg_npt Hin_npt Hev_npt).
                            --- destruct (check_pevals_refine_sound pspecs (nls_next_pevals s_s) (nls_next_pevals s_t)
                                            dvs_next_s dvs_next_t cut_allowed ctx_cont opt_pf penv_cut
                                            Hpenv_cut Hctx_cont Hfa_next_s Hfa_next_t Hpm_next_s Hpm_next_t Href_next)
                                  as (Hrel_next & _ & _).
                                pstep; eapply pure_cfg_steps_to_tau_sync; [exact Htau_s | exact Htau_t | right].
                                exact (CIH (nls_bid_latch_from s_s) (nls_bid_latch_from s_t)
                                           env_latch_s env_latch_t dvs_next_s dvs_next_t
                                           (fun r0 Hr0 => eq_trans (Hpres_ls r0 Hr0) (Hag_s r0 Hr0))
                                           (fun r0 Hr0 => eq_trans (Hpres_lt r0 Hr0) (Hag_t r0 Hr0))
                                           Hst_np_s Hst_np_t Hrel_next).
                 * (* Loop exits *)
                   pose proof (bool_eqb_swap_inv _ _ false Econt) as Ecbit_exit.
                   replace (Bool.eqb false (nls_latch_on_true s_s)) with (negb (nls_latch_on_true s_s)) in Ecbit_exit
                     by (destruct (nls_latch_on_true s_s); reflexivity).
                   pose proof (extract_branch_cond_assumptions_sound penv_cut dummy_freeze_oracle
                                 (negb (nls_latch_on_true s_s)) (nls_ce_cond s_s) cbit_s ctx_hdr
                                 Hwt_cs Hlf_cs Hev_cond_s Ecbit_exit Hctx_hdr) as Hctx_exit0;
                     fold ctx_exit_0 in Hctx_exit0.
                   destruct (Hexit_s eq_refl)
                     as [[Hub_xs _] | (env_exit_s & dv_ret_s & Hret_exit_s & Hev_ret_s & _ & Hret_st_s)].
                   -- eapply paco2_mon; [exact (cfg_steps_ub_det_ref dvalue_refines sigma_tgt _ _ _ (Hub_xs sigma_tgt)) | intros ? ? []].
                   -- assert (Hret_hx_s : Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
                                            (nls_evals_hdr s_s ++ nls_evals_exit s_s))
                        by (apply Forall_app; split; assumption).
                      assert (Hwf_hx_s : Forall (wf_pure_eval_entry cut_allowed) (nls_evals_hdr s_s ++ nls_evals_exit s_s))
                        by (apply Forall_app; split; assumption).
                      pose proof (fold_ub_assumptions_sound _ cut_allowed
                                    (nls_evals_hdr s_s ++ nls_evals_exit s_s) [nls_ce_cond s_s]
                                    ctx_exit_0 ctx_exit penv_cut dummy_freeze_oracle Hpenv_cut
                                    (forall_wf_pure_in _ _ Hwf_hx_s)
                                    (forall_ret_in _ _ _ Hret_hx_s)
                                    Hbr_hdr_s Hctx_exit0 Ef_exit) as Hctx_exit.
                      destruct (Hexit_t Epol_eq)
                        as [[_ (ce_xt & msg_xt & Hin_xt & Hev_xt)]
                           | (env_exit_t & dv_ret_t & _ & Hev_ret_t & _ & Hret_st_t)].
                      ++ exfalso; exact (exprs_safe_under_src_sound (nls_ce_ret s_t :: nls_evals_exit s_t)
                                           cut_allowed ctx_exit (nls_evals_hdr s_s ++ nls_evals_exit s_s)
                                           penv_cut Hpenv_cut Hctx_exit
                                           (forall_ret_in _ _ _ Hret_hx_s)
                                           (Forall_cons _ Hwf_ret_t Hfa_exit_t) Hsafe_exit_t
                                           ce_xt msg_xt Hin_xt Hev_xt).
                      ++ destruct Hwf_ret_s as (_ & _ & Hfv_ret_s).
                         destruct Hwf_ret_t as (_ & _ & Hfv_ret_t).
                         pose proof (check_expr_refines_with_lrat_sound ctx_exit (nls_ce_ret s_s) (nls_ce_ret s_t)
                                       opt_pf penv_cut dummy_freeze_oracle Href_ret
                                       (fun n w0 H => Hpenv_cut n w0 (Hfv_ret_s (n, w0) H))
                                       (fun n w0 H => Hpenv_cut n w0 (Hfv_ret_t (n, w0) H))
                                       Hctx_exit) as Hdv_ret.
                         rewrite Hev_ret_s, Hev_ret_t in Hdv_ret; cbn [refine_eou_dvalue] in Hdv_ret.
                         eapply paco2_mon;
                           [exact (cfg_steps_ret_det_ref dvalue_refines
                                     sigma_tgt env_prev_s _ sigma_tgt env_exit_s dv_ret_s
                                     sigma_tgt env_prev_t _ sigma_tgt env_exit_t dv_ret_t
                                     (pure_cfg_to_cfg_ret sigma_tgt _ _ _ _ Hret_st_s)
                                     (pure_cfg_to_cfg_ret sigma_tgt _ _ _ _ Hret_st_t)
                                     Hdv_ret)
                           | intros ? ? []]. }
           pstep; eapply pure_cfg_steps_to_tau_sync; [exact Htau_ent_s | exact Htau_ent_t | left].
           exact (Hloop (init src_cfg) (init tgt_cfg) env_entry_s env_entry_t dvs0_s dvs0_t
                        (fun _ _ => eq_refl) (fun _ _ => eq_refl) Hst_ip_s Hst_ip_t Hrel0).
Qed.

(** *** 5.6d [F-61] & [F-60]: Prototype Attribute Seeding & [denote_function] Refinement *)

Definition seed_one_param_ctx
  (pnm : string) (dt : dtyp) (attrs : list param_attr)
  : list (string * positive) * ub_ctx :=
  let extra_v :=
    match dt with
    | DTYPE_Base (DTYPE_I w) => [(pnm, w)]
    | _ => []
    end in
  let uas :=
    if existsb attr_is_noundef attrs then
      match dt with
      | DTYPE_Base (DTYPE_I w) => [UBA_ParamNoUndef pnm w]
      | DTYPE_Base DTYPE_Pointer =>
          (if existsb attr_is_nonnull attrs
           then [UBA_PtrNonNull pnm]
           else [UBA_PtrDereferenceable pnm 0%N]) ++
          (match find_option attr_dereferenceable attrs with
           | Some (false, n) =>
               [UBA_PtrDereferenceable pnm (Z.to_N (denote_int_syntax n))]
           | _ => []
           end) ++
          (match find_option attr_align attrs with
           | Some al =>
               [UBA_PtrAligned pnm (Z.to_N (denote_int_syntax al))]
           | None => []
           end)
      | _ => []
      end
    else [] in
  (extra_v, uas).

Fixpoint seed_proto_param_ctx
  (pnames : list string)
  (arg_dtys : list dtyp)
  (s_pattrs : list (list param_attr))
  {struct pnames} : list (string * positive) * ub_ctx :=
  match pnames, arg_dtys, s_pattrs with
  | pnm :: rp, dt :: rd, attrs :: ra =>
      let '(ev1, ua1) := seed_one_param_ctx pnm dt attrs in
      let '(evr, uar) := seed_proto_param_ctx rp rd ra in
      (ev1 ++ evr, ua1 ++ uar)
  | _, _, _ => ([], [])
  end.

Lemma seed_proto_param_ctx_in_pnames :
  forall pnames arg_dtys s_pattrs nm w,
    In (nm, w) (fst (seed_proto_param_ctx pnames arg_dtys s_pattrs)) ->
    In nm pnames.
Proof.
  induction pnames as [| pnm rp IH];
    intros [| dt rd] [| attrs ra] nm w Hin;
    cbn [seed_proto_param_ctx fst] in Hin; try contradiction Hin.
  destruct (seed_one_param_ctx pnm dt attrs) as [ev1 ua1] eqn:E1.
  destruct (seed_proto_param_ctx rp rd ra) as [evr uar] eqn:Er.
  cbn [fst] in Hin; apply in_app_iff in Hin as [H1 | Hr].
  - unfold seed_one_param_ctx in E1; inversion E1; clear E1.
    destruct dt as [tb | |]; try contradiction H1.
    destruct tb as [w0 | | | | | | | | | |]; try contradiction H1.
    destruct H1 as [Heq | []]; inversion Heq; subst; left; reflexivity.
  - right; eapply IH with (arg_dtys := rd) (s_pattrs := ra); rewrite Er; exact Hr.
Qed.

Lemma seed_one_param_ctx_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle pnm dt attrs (v : @dvalue Pa),
    penv pnm = Some v ->
    dvalue_has_dtyp v dt ->
    (existsb attr_is_noundef attrs = true -> dvalue_well_defined v = true) ->
    wf_param_env_for (fst (seed_one_param_ctx pnm dt attrs)) penv /\
    ub_ctx_holds penv foracle (snd (seed_one_param_ctx pnm dt attrs)).
Proof.
  intros penv foracle pnm dt attrs v Hp Hty Hnd.
  unfold seed_one_param_ctx; cbn [fst snd].
  split.
  - intros nm w Hin.
    destruct dt as [tb | |]; try contradiction Hin.
    destruct tb as [w0 | | | | | | | | | |]; try contradiction Hin.
    destruct Hin as [Heq | []]; inversion Heq; subst nm w0.
    apply dvalue_has_dtyp_i_iff_wf_scalar in Hty.
    exists v; split; [exact Hp | exact Hty].
  - destruct (existsb attr_is_noundef attrs) eqn:Enu; [| constructor].
    pose proof (Hnd eq_refl) as Hwd.
    assert (Hnp : v <> DVALUE_Base DVALUE_Poison)
      by (intros ->; discriminate Hwd).
    destruct dt as [tb | |]; try constructor.
    destruct tb as [w0 | | | | | | | | | |]; try constructor.
    + constructor; [| constructor].
      cbn [ub_assumption_holds]; intros dv Hpm.
      rewrite Hp in Hpm; injection Hpm as <-; exact Hnp.
    + assert (Hnot_int : forall w iv, v <> DVALUE_Base (@DVALUE_I Pa w iv)).
      { intros w iv ->; inversion Hty as [? ? Hb | | |]; subst; discriminate Hb. }
      apply Forall_app; split.
      * destruct (existsb attr_is_nonnull attrs);
          (constructor; [| constructor]);
          cbn [ub_assumption_holds]; intros dv Hpm;
          rewrite Hp in Hpm; injection Hpm as <-; exact Hnp.
      * apply Forall_app; split.
        -- destruct (find_option attr_dereferenceable attrs) as [[orn n] |];
             [destruct orn; [constructor |] | constructor].
           constructor; [| constructor].
           cbn [ub_assumption_holds]; intros dv Hpm.
           rewrite Hp in Hpm; injection Hpm as <-; exact Hnp.
        -- destruct (find_option attr_align attrs) as [al |]; [| constructor].
           constructor; [| constructor].
           cbn [ub_assumption_holds]; intros dv Hpm.
           rewrite Hp in Hpm; injection Hpm as <-.
           split; [exact Hnp | intros w iv Heq; exfalso; exact (Hnot_int w iv Heq)].
Qed.

Lemma seed_proto_param_ctx_sound_aux {Pa : Params} :
  forall pnames arg_dtys s_pattrs (vs : list (@dvalue Pa)) (penv : param_env Pa) foracle,
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    Forall2 (fun attrs v => existsb attr_is_noundef attrs = true -> dvalue_well_defined v = true)
            s_pattrs vs ->
    (forall idx pnm v,
       nth_error pnames idx = Some pnm ->
       nth_error vs idx = Some v ->
       penv pnm = Some v) ->
    wf_param_env_for (fst (seed_proto_param_ctx pnames arg_dtys s_pattrs)) penv /\
    ub_ctx_holds penv foracle (snd (seed_proto_param_ctx pnames arg_dtys s_pattrs)).
Proof.
  induction pnames as [| pnm rp IH];
    intros [| dt rd] [| attrs ra] vs penv foracle Hty Hnu Hlookup;
    try (cbn [seed_proto_param_ctx fst snd]; split; [intros ? ? [] | constructor]).
  inversion Hty as [| v ? vr ? Hty1 Htyr]; subst.
  inversion Hnu as [| ? ? ? ? Hnu1 Hnur]; subst.
  cbn [seed_proto_param_ctx].
  destruct (seed_one_param_ctx pnm dt attrs) as [ev1 ua1] eqn:E1.
  destruct (seed_proto_param_ctx rp rd ra) as [evr uar] eqn:Er.
  pose proof (seed_one_param_ctx_sound penv foracle pnm dt attrs v
                (Hlookup 0%nat pnm v eq_refl eq_refl) Hty1 Hnu1) as [Hwf1 Hua1].
  rewrite E1 in Hwf1, Hua1; cbn [fst snd] in Hwf1, Hua1.
  destruct (IH rd ra vr penv foracle Htyr Hnur
              (fun idx p' v' Hp Hv => Hlookup (S idx) p' v' Hp Hv)) as [Hwfr Huar].
  rewrite Er in Hwfr, Huar; cbn [fst snd] in Hwfr, Huar.
  cbn [fst snd]; split.
  - intros nm w Hin; apply in_app_iff in Hin as [H1 | Hr];
      [exact (Hwf1 nm w H1) | exact (Hwfr nm w Hr)].
  - apply Forall_app; split; assumption.
Qed.

Lemma seed_proto_param_ctx_sound {Pa : Params} :
  forall pnames arg_dtys s_pattrs (vs : list (@dvalue Pa)) foracle,
    NoDup pnames ->
    List.length pnames = List.length vs ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    Forall2 (fun attrs v => existsb attr_is_noundef attrs = true -> dvalue_well_defined v = true)
            s_pattrs vs ->
    let penv := build_param_env pnames vs in
    wf_param_env_for (fst (seed_proto_param_ctx pnames arg_dtys s_pattrs)) penv /\
    ub_ctx_holds penv foracle (snd (seed_proto_param_ctx pnames arg_dtys s_pattrs)).
Proof.
  intros pnames arg_dtys s_pattrs vs foracle Hnd Hlen Hty Hnu penv.
  apply (seed_proto_param_ctx_sound_aux pnames arg_dtys s_pattrs vs penv foracle Hty Hnu).
  intros idx pnm v Hp Hv.
  destruct (build_param_env_nth pnames vs idx pnm Hnd Hlen Hp) as [dv [Hdv Hfe]].
  rewrite Hv in Hdv; injection Hdv as <-; exact Hfe.
Qed.

Definition is_none_b {A : Type} (o : option A) : bool :=
  match o with
  | None => true
  | Some _ => false
  end.

Definition opt_deref_same_b (d1 d2 : option (bool * int_syntax)) : bool :=
  match d1, d2 with
  | None, None => true
  | Some (b1, n1), Some (b2, n2) => Bool.eqb b1 b2 && int_syntax_val_eqb n1 n2
  | _, _ => false
  end.

Definition attr_preserves_dtyp_b (dt : dtyp) (attrs : list param_attr) : bool :=
  match dt with
  | DTYPE_Base (DTYPE_I _)
  | DTYPE_Base DTYPE_Pointer
  | DTYPE_Base (DTYPE_FP _) => true
  | _ =>
      is_none_b (find_option attr_nofpclass attrs) &&
      is_none_b (find_option attr_range attrs)
  end.

Definition proto_deref_preserved_b (src_decl tgt_decl : declaration typ) : bool :=
  let '(s_rattrs, s_pattrs) := dc_param_attrs src_decl in
  let '(t_rattrs, t_pattrs) := dc_param_attrs tgt_decl in
  opt_deref_same_b (find_option attr_dereferenceable s_rattrs)
                   (find_option attr_dereferenceable t_rattrs) &&
  forallb2 (fun sa ta =>
    opt_deref_same_b (find_option attr_dereferenceable sa)
                     (find_option attr_dereferenceable ta))
    s_pattrs t_pattrs.

Lemma int_syntax_val_eqb_denote :
  forall a b,
    int_syntax_val_eqb a b = true ->
    denote_int_syntax a = denote_int_syntax b.
Proof.
  intros a b H; unfold int_syntax_val_eqb, denote_int_syntax in *.
  apply Z.eqb_eq; exact H.
Qed.

Lemma cconv_eqb_same_caller :
  forall f1 f2 cc,
    cconv_eqb f1 f2 = true ->
    cconv_eqb cc f1 = cconv_eqb cc f2.
Proof.
  intros f1 f2 cc H; unfold cconv_eqb in *.
  apply Z.eqb_eq in H; rewrite H; reflexivity.
Qed.

Lemma anns_cconv_tfmap :
  forall (f : typ -> dtyp) (anns : list (annotation typ)),
    anns_cconv (tfmap f anns) = anns_cconv anns.
Proof.
  intros f anns; unfold anns_cconv; f_equal.
  induction anns as [| a rest IH]; [reflexivity |].
  destruct a; cbn; try exact IH; reflexivity.
Qed.

Lemma value_attrs_poison_poison {Pa : Params} :
  forall attrs,
    @value_attrs_poison Pa attrs (DVALUE_Base DVALUE_Poison) = DVALUE_Base DVALUE_Poison.
Proof.
  intros attrs; unfold value_attrs_poison, value_attr_nonnull, value_attr_align,
    value_attr_range, value_attr_nofpclass.
  cbn [value_metadata_range value_metadata_range_base].
  destruct (find_option attr_range attrs) as [[lo hi] |];
    cbn [option_map value_metadata_range value_metadata_range_base];
    destruct (find_option attr_nofpclass attrs); reflexivity.
Qed.

Lemma value_attrs_poison_eq_of_match {Pa : Params} :
  forall s_a t_a (v : @dvalue Pa),
    value_attrs_poison_match_b s_a t_a = true ->
    value_attrs_poison s_a v = value_attrs_poison t_a v.
Proof.
  intros s_a t_a v Hm.
  unfold value_attrs_poison_match_b in Hm; rewrite !andb_true_iff in Hm.
  destruct Hm as (((((_ & Hnn) & Hal) & Hrg) & Hnfp) & _).
  apply Bool.eqb_prop in Hnn.
  assert (Ev1 : value_attr_nonnull s_a v = value_attr_nonnull t_a v).
  { unfold value_attr_nonnull; rewrite Hnn; reflexivity. }
  assert (Ev2 : forall u : @dvalue Pa, value_attr_align s_a u = value_attr_align t_a u).
  { intros u; unfold value_attr_align, opt_int_syntax_val_eqb in *.
    destruct (find_option attr_align s_a) as [a1 |],
             (find_option attr_align t_a) as [a2 |]; try discriminate Hal; [| reflexivity].
    rewrite (int_syntax_val_eqb_denote a1 a2 Hal); reflexivity. }
  assert (Ev3 : forall u : @dvalue Pa, value_attr_range s_a u = value_attr_range t_a u).
  { intros u; unfold value_attr_range, opt_range_val_eqb in *.
    destruct (find_option attr_range s_a) as [[l1 h1] |],
             (find_option attr_range t_a) as [[l2 h2] |]; try discriminate Hrg; [| reflexivity].
    apply andb_true_iff in Hrg as [Hl Hh].
    pose proof (int_syntax_val_eqb_denote l1 l2 Hl) as El.
    pose proof (int_syntax_val_eqb_denote h1 h2 Hh) as Eh.
    assert (Eb : forall w : @dvalue Pa,
      value_metadata_range_base [(l1, h1)] w = value_metadata_range_base [(l2, h2)] w).
    { intros [db | |]; try reflexivity.
      destruct db; try reflexivity.
      cbn [value_metadata_range_base in_metadata_ranges]; rewrite El, Eh; reflexivity. }
    cbn [option_map value_metadata_range].
    destruct u as [| | vec elts]; try apply Eb.
    destruct vec; [f_equal; apply map_ext; exact Eb | apply Eb]. }
  assert (Ev4 : forall u : @dvalue Pa, value_attr_nofpclass s_a u = value_attr_nofpclass t_a u).
  { intros u; unfold value_attr_nofpclass, opt_Z_eqb in *.
    destruct (find_option attr_nofpclass s_a) as [m1 |],
             (find_option attr_nofpclass t_a) as [m2 |]; try discriminate Hnfp; [| reflexivity].
    apply Z.eqb_eq in Hnfp; subst m2; reflexivity. }
  unfold value_attrs_poison; rewrite Ev1, Ev2, Ev3, Ev4; reflexivity.
Qed.

Lemma value_attrs_poison_preserves_dtyp {Pa : Params} :
  forall dt attrs (v : @dvalue Pa),
    attr_preserves_dtyp_b dt attrs = true ->
    dvalue_has_dtyp v dt ->
    dvalue_has_dtyp (value_attrs_poison attrs v) dt.
Proof.
  intros dt attrs v Hpres Hty.
  assert (Hbase_step : forall u : @dvalue Pa,
    (exists db, u = DVALUE_Base db) ->
    value_attrs_poison attrs u = u \/
    value_attrs_poison attrs u = DVALUE_Base DVALUE_Poison).
  { intros u [db ->].
    assert (Hu1 : value_attr_nonnull attrs (DVALUE_Base db) = DVALUE_Base db \/
                  value_attr_nonnull attrs (DVALUE_Base db) = DVALUE_Base DVALUE_Poison)
      by (destruct db; cbn [value_attr_nonnull]; try (left; reflexivity);
          destruct (_ && _); [right | left]; reflexivity).
    assert (Hu2 : forall w, (w = DVALUE_Base db \/ w = DVALUE_Base DVALUE_Poison) ->
      value_attr_align attrs w = DVALUE_Base db \/
      value_attr_align attrs w = DVALUE_Base DVALUE_Poison).
    { intros w [-> | ->];
        [destruct db; cbn [value_attr_align]; try (left; reflexivity);
         destruct (find_option attr_align attrs); [destruct (ptr_aligned_to _ _); [left | right] | left]; reflexivity
        | right; destruct (find_option attr_align attrs); reflexivity]. }
    assert (Hu3 : forall w, (w = DVALUE_Base db \/ w = DVALUE_Base DVALUE_Poison) ->
      value_attr_range attrs w = DVALUE_Base db \/
      value_attr_range attrs w = DVALUE_Base DVALUE_Poison).
    { intros w [-> | ->]; unfold value_attr_range;
        destruct (find_option attr_range attrs) as [rg |]; cbn [option_map value_metadata_range];
        try (left; reflexivity); try (right; reflexivity).
      destruct db; cbn [value_metadata_range_base]; try (left; reflexivity).
      destruct (in_metadata_ranges _ _ _); [left | right]; reflexivity. }
    assert (Hu4 : forall w, (w = DVALUE_Base db \/ w = DVALUE_Base DVALUE_Poison) ->
      value_attr_nofpclass attrs w = DVALUE_Base db \/
      value_attr_nofpclass attrs w = DVALUE_Base DVALUE_Poison).
    { intros w [-> | ->]; unfold value_attr_nofpclass;
        destruct (find_option attr_nofpclass attrs) as [m |]; cbn [value_nofpclass];
        try (left; reflexivity); try (right; reflexivity).
      destruct (fp_class db); [destruct (Z.land _ _ =? 0)%Z; [left | right] | left]; reflexivity. }
    unfold value_attrs_poison; exact (Hu4 _ (Hu3 _ (Hu2 _ Hu1))). }
  assert (Hother :
    is_none_b (find_option attr_nofpclass attrs) &&
    is_none_b (find_option attr_range attrs) = true ->
    (forall p, v <> DVALUE_Base (DVALUE_Pointer p)) ->
    value_attrs_poison attrs v = v).
  { intros Hnone Hnp; apply andb_true_iff in Hnone as [Hnfp Hnrg].
    unfold value_attrs_poison, value_attr_nofpclass, value_attr_range,
      value_attr_align, value_attr_nonnull.
    destruct (find_option attr_nofpclass attrs); [discriminate Hnfp |].
    destruct (find_option attr_range attrs); [discriminate Hnrg |].
    cbn [option_map value_metadata_range].
    assert (Hv1 : match v with
                  | DVALUE_Base (DVALUE_Pointer p) =>
                      if existsb attr_is_nonnull attrs && (ptr_to_int p =? ptr_to_int null)%Z
                      then DVALUE_Base DVALUE_Poison else v
                  | _ => v
                  end = v)
      by (destruct v as [[p | | | | | | | ] | |]; try reflexivity; exfalso; exact (Hnp p eq_refl)).
    rewrite Hv1.
    destruct v as [[p | | | | | | | ] | |]; try reflexivity; exfalso; exact (Hnp p eq_refl). }
  destruct dt as [tb | packed flds | vec sz et]; cbn [attr_preserves_dtyp_b] in Hpres.
  - destruct tb as [w | | | | fp | | | | | | sz];
      try (inversion Hty as [db ? _ _ Heqv _ | ? Heqv | |]; subst;
           [destruct (Hbase_step _ (ex_intro _ db eq_refl)) as [-> | ->]; [exact Hty | apply DVALUE_Poison_typ_agg]
           | rewrite value_attrs_poison_poison; apply DVALUE_Poison_typ_agg]);
      (rewrite Hother; [exact Hty | exact Hpres | intros p ->; inversion Hty as [? ? Hb | | |]; subst; discriminate Hb]).
  - rewrite Hother; [exact Hty | exact Hpres | intros p ->; inversion Hty].
  - rewrite Hother; [exact Hty | exact Hpres | intros p ->; inversion Hty].
Qed.

Lemma dvalue_refines_well_defined {Pa : Params} :
  forall (v_s v_t : @dvalue Pa),
    dvalue_refines v_s v_t ->
    dvalue_well_defined v_s = true ->
    v_s = v_t /\ dvalue_well_defined v_t = true.
Proof.
  intros v_s v_t [-> | ->] Hwd; [discriminate Hwd | split; [reflexivity | exact Hwd]].
Qed.

Definition classify_fn_event {Pa : Params} {X : Type} (e : @CFGEtop Pa X)
  : @LocalE Pa X + (@StackE Pa X + @OW_E Pa X) :=
  match e with
  | inl1 c => inr (inr (inl1 c))
  | inr1 (inl1 ec) => inr (inr (inr1 (inl1 ec)))
  | inr1 (inr1 (inl1 ic)) => inr (inr (inr1 (inr1 (inl1 ic))))
  | inr1 (inr1 (inr1 (inl1 ge))) => inr (inr (inr1 (inr1 (inr1 (inl1 ge)))))
  | inr1 (inr1 (inr1 (inr1 (inl1 (inl1 le))))) => inl le
  | inr1 (inr1 (inr1 (inr1 (inl1 (inr1 se))))) => inr (inl se)
  | inr1 (inr1 (inr1 (inr1 (inr1 rest)))) =>
      inr (inr (inr1 (inr1 (inr1 (inr1 (inr1 rest))))))
  end.

Definition push_frame_bindings {Pa : Params}
  (bs : list (raw_id * @dvalue Pa)) : rmap (@dvalue Pa) :=
  fold_right (fun '(id, dv) acc => RM.add id dv acc) (RM.empty (@dvalue Pa)) bs.

CoFixpoint run_fn_frames {Pa : Params} {R : Type}
  (env : rmap (@dvalue Pa))
  (stk : list (rmap (@dvalue Pa)))
  (exc_slot : option (@dvalue Pa))
  (t : @CFGtop Pa R) : itree (@OW_E Pa) R :=
  match observe t with
  | RetF r => Ret r
  | TauF t' => Tau (run_fn_frames env stk exc_slot t')
  | VisF _ e k =>
      match classify_fn_event e with
      | inl le =>
          match le in LocalE Y return (Y -> @CFGtop Pa R) -> itree (@OW_E Pa) R with
          | LocalWrite id dv => fun k' =>
              Tau (run_fn_frames (RM.add id dv env) stk exc_slot (k' tt))
          | LocalRead id => fun k' =>
              match RM.find id env with
              | Some dv => Tau (run_fn_frames env stk exc_slot (k' dv))
              | None => Vis (@subevent FailureE (@OW_E Pa) _ void (Throw tt)) void_elim
              end
          end k
      | inr (inl se) =>
          match se in StackE Y return (Y -> @CFGtop Pa R) -> itree (@OW_E Pa) R with
          | StackPush bs => fun k' =>
              Tau (run_fn_frames (push_frame_bindings bs) (env :: stk) exc_slot (k' tt))
          | StackPop => fun k' =>
              match stk with
              | caller_env :: stk' =>
                  Tau (run_fn_frames caller_env stk' exc_slot (k' tt))
              | [] =>
                  Vis (@subevent FailureE (@OW_E Pa) _ void (Throw tt)) void_elim
              end
          | StackRaise x => fun k' =>
              Tau (run_fn_frames env stk (Some x) (k' tt))
          | StackGetExc => fun k' =>
              Tau (run_fn_frames env stk exc_slot (k' exc_slot))
          end k
      | inr (inr oe) =>
          Vis oe (fun x => run_fn_frames env stk exc_slot (k x))
      end
  end.

Lemma observe_run_fn_frames {Pa : Params} {R : Type}
  (env : rmap (@dvalue Pa))
  (stk : list (rmap (@dvalue Pa)))
  (exc_slot : option (@dvalue Pa))
  (t : @CFGtop Pa R) :
  observe (run_fn_frames env stk exc_slot t) =
  match observe t with
  | RetF r => RetF r
  | TauF t' => TauF (run_fn_frames env stk exc_slot t')
  | VisF _ e k =>
      match classify_fn_event e with
      | inl le =>
          match le in LocalE Y return (Y -> @CFGtop Pa R) -> itree' (@OW_E Pa) R with
          | LocalWrite id dv => fun k' =>
              TauF (run_fn_frames (RM.add id dv env) stk exc_slot (k' tt))
          | LocalRead id => fun k' =>
              match RM.find id env with
              | Some dv => TauF (run_fn_frames env stk exc_slot (k' dv))
              | None => VisF (@subevent FailureE (@OW_E Pa) _ void (Throw tt)) void_elim
              end
          end k
      | inr (inl se) =>
          match se in StackE Y return (Y -> @CFGtop Pa R) -> itree' (@OW_E Pa) R with
          | StackPush bs => fun k' =>
              TauF (run_fn_frames (push_frame_bindings bs) (env :: stk) exc_slot (k' tt))
          | StackPop => fun k' =>
              match stk with
              | caller_env :: stk' =>
                  TauF (run_fn_frames caller_env stk' exc_slot (k' tt))
              | [] =>
                  VisF (@subevent FailureE (@OW_E Pa) _ void (Throw tt)) void_elim
              end
          | StackRaise x => fun k' =>
              TauF (run_fn_frames env stk (Some x) (k' tt))
          | StackGetExc => fun k' =>
              TauF (run_fn_frames env stk exc_slot (k' exc_slot))
          end k
      | inr (inr oe) =>
          VisF oe (fun x => run_fn_frames env stk exc_slot (k x))
      end
  end.
Proof.
  unfold observe at 1; cbn; destruct (observe t) as [r | t' | X e k]; [reflexivity | reflexivity |].
  destruct (classify_fn_event e) as [le | [se | oe]]; [| | reflexivity].
  - destruct le as [id dv | id]; [reflexivity | destruct (RM.find id env); reflexivity].
  - destruct se as [bs | | x |]; try reflexivity.
    destruct stk; reflexivity.
Qed.

Lemma run_fn_frames_bind_assoc_lr {Pa : Params} {A B C : Type} :
  forall (sigma : @draw_strat Pa) env stk exc_slot
         (m : @CFGtop Pa A) (f : A -> @CFGtop Pa B) (g : B -> @CFGtop Pa C),
    det_ref eq
      (run_draws sigma (run_fn_frames env stk exc_slot (ITree.bind (ITree.bind m f) g)))
      (run_draws sigma (run_fn_frames env stk exc_slot (ITree.bind m (fun x => ITree.bind (f x) g)))).
Proof.
  intros sigma env stk exc_slot m f g; revert sigma env stk exc_slot m.
  pcofix CIH; intros sigma env stk exc_slot m.
  destruct (observe m) as [a | m' | X e k] eqn:Hom.
  - eapply det_ref_obs_eq with
      (t1 := run_draws sigma (run_fn_frames env stk exc_slot (ITree.bind (f a) g)))
      (t2 := run_draws sigma (run_fn_frames env stk exc_slot (ITree.bind (f a) g))).
    + rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind, Hom; reflexivity.
    + rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind, Hom; reflexivity.
    + eapply paco2_mon; [apply det_ref_refl; intros; reflexivity | intros ? ? []].
  - pstep; apply DR_Step; unfold det_step_body.
    rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind, Hom; cbn [observe].
    right; exact (CIH sigma env stk exc_slot m').
  - pstep; apply DR_Step; unfold det_step_body.
    rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind, Hom; cbn [observe].
    destruct (classify_fn_event e) as [le | [se | oe]].
    + destruct le as [id dv | id].
      * right; exact (CIH sigma (RM.add id dv env) stk exc_slot (k tt)).
      * destruct (RM.find id env) as [dv |].
        -- right; exact (CIH sigma env stk exc_slot (k dv)).
        -- right; apply det_vis_both_refl; intros [].
    + destruct se as [bs | | x |].
      * right; exact (CIH sigma (push_frame_bindings bs) (env :: stk) exc_slot (k tt)).
      * destruct stk as [| cenv stk'];
          [right; apply det_vis_both_refl; intros []
          | right; exact (CIH sigma cenv stk' exc_slot (k tt))].
      * right; exact (CIH sigma env stk (Some x) (k tt)).
      * right; exact (CIH sigma env stk exc_slot (k exc_slot)).
    + destruct (classify_ow_event oe) as [[dt] | de].
      * right; exact (CIH (shift_draw_strat sigma) env stk exc_slot (k (sigma 0%nat dt))).
      * right; apply det_vis_both_refl; intros x; right; exact (CIH sigma env stk exc_slot (k x)).
Qed.

Lemma run_fn_frames_bind_assoc_rl {Pa : Params} {A B C : Type} :
  forall (sigma : @draw_strat Pa) env stk exc_slot
         (m : @CFGtop Pa A) (f : A -> @CFGtop Pa B) (g : B -> @CFGtop Pa C),
    det_ref eq
      (run_draws sigma (run_fn_frames env stk exc_slot (ITree.bind m (fun x => ITree.bind (f x) g))))
      (run_draws sigma (run_fn_frames env stk exc_slot (ITree.bind (ITree.bind m f) g))).
Proof.
  intros sigma env stk exc_slot m f g; revert sigma env stk exc_slot m.
  pcofix CIH; intros sigma env stk exc_slot m.
  destruct (observe m) as [a | m' | X e k] eqn:Hom.
  - eapply det_ref_obs_eq with
      (t1 := run_draws sigma (run_fn_frames env stk exc_slot (ITree.bind (f a) g)))
      (t2 := run_draws sigma (run_fn_frames env stk exc_slot (ITree.bind (f a) g))).
    + rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind, Hom; reflexivity.
    + rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind, Hom; reflexivity.
    + eapply paco2_mon; [apply det_ref_refl; intros; reflexivity | intros ? ? []].
  - pstep; apply DR_Step; unfold det_step_body.
    rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind, Hom; cbn [observe].
    right; exact (CIH sigma env stk exc_slot m').
  - pstep; apply DR_Step; unfold det_step_body.
    rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind, Hom; cbn [observe].
    destruct (classify_fn_event e) as [le | [se | oe]].
    + destruct le as [id dv | id].
      * right; exact (CIH sigma (RM.add id dv env) stk exc_slot (k tt)).
      * destruct (RM.find id env) as [dv |].
        -- right; exact (CIH sigma env stk exc_slot (k dv)).
        -- right; apply det_vis_both_refl; intros [].
    + destruct se as [bs | | x |].
      * right; exact (CIH sigma (push_frame_bindings bs) (env :: stk) exc_slot (k tt)).
      * destruct stk as [| cenv stk'];
          [right; apply det_vis_both_refl; intros []
          | right; exact (CIH sigma cenv stk' exc_slot (k tt))].
      * right; exact (CIH sigma env stk (Some x) (k tt)).
      * right; exact (CIH sigma env stk exc_slot (k exc_slot)).
    + destruct (classify_ow_event oe) as [[dt] | de].
      * right; exact (CIH (shift_draw_strat sigma) env stk exc_slot (k (sigma 0%nat dt))).
      * right; apply det_vis_both_refl; intros x; right; exact (CIH sigma env stk exc_slot (k x)).
Qed.

Lemma push_frame_bindings_eq_init {Pa : Params} :
  forall params (vs : list (@dvalue Pa)),
    List.length params = List.length vs ->
    push_frame_bindings (List.combine params vs) = init_cfg_locals params vs.
Proof.
  induction params as [| p pr IH]; intros [| v vr] Hlen; try discriminate Hlen; [reflexivity |].
  injection Hlen as Hlen'; cbn [List.combine push_frame_bindings fold_right init_cfg_locals].
  f_equal; exact (IH vr Hlen').
Qed.

Lemma combine_lists_varargs_exact {A B : Type} :
  forall (xs : list A) (ys : list B),
    List.length xs = List.length ys ->
    combine_lists_varargs xs ys = raise_ret (List.combine xs ys, []).
Proof.
  induction xs as [| x rx IH]; intros [| y ry] Hlen; try discriminate Hlen; [reflexivity |].
  injection Hlen as Hlen'; cbn [combine_lists_varargs List.combine].
  rewrite (IH ry Hlen'); reflexivity.
Qed.

Definition is_stack_det_event {Pa : Params} {X : Type} (e : @Det_OW_E Pa X) : bool :=
  match e with
  | inr1 (inr1 (inr1 (inr1 (inl1 _)))) => true
  | _ => false
  end.

Inductive no_stack_det_ {Pa : Params} {R : Type}
  (r : itree (@Det_OW_E Pa) R -> Prop) (t : itree (@Det_OW_E Pa) R) : Prop :=
| NSD_Ret (x : R) :
    observe t = RetF x -> no_stack_det_ r t
| NSD_Tau (m : itree (@Det_OW_E Pa) R) :
    observe t = TauF m -> r m -> no_stack_det_ r t
| NSD_Vis {X : Type} (e : @Det_OW_E Pa X) (k : X -> itree (@Det_OW_E Pa) R) :
    observe t = VisF e k ->
    is_stack_det_event e = false ->
    (forall x : X, r (k x)) ->
    no_stack_det_ r t.

Lemma no_stack_det__mon {Pa : Params} {R : Type} :
  monotone1 (@no_stack_det_ Pa R).
Proof.
  intros t r r' H Hle.
  destruct H as [x Ho | m Ho Hm | X e k Ho Hns Hk].
  - exact (NSD_Ret _ _ x Ho).
  - exact (NSD_Tau _ _ m Ho (Hle m Hm)).
  - exact (NSD_Vis _ _ e k Ho Hns (fun x => Hle (k x) (Hk x))).
Qed.
#[local] Hint Resolve no_stack_det__mon : paco.

Definition no_stack_det {Pa : Params} {R : Type} (t : itree (@Det_OW_E Pa) R) : Prop :=
  paco1 (@no_stack_det_ Pa R) bot1 t.

Lemma no_stack_det_obs_eq {Pa : Params} {R : Type} :
  forall (t1 t2 : itree (@Det_OW_E Pa) R),
    observe t1 = observe t2 ->
    no_stack_det t1 ->
    no_stack_det t2.
Proof.
  intros t1 t2 Ho H; punfold H; pstep.
  destruct H as [x Ho1 | m Ho1 Hm | X e k Ho1 Hns Hk]; rewrite Ho in Ho1.
  - exact (NSD_Ret _ _ x Ho1).
  - exact (NSD_Tau _ _ m Ho1 Hm).
  - exact (NSD_Vis _ _ e k Ho1 Hns Hk).
Qed.

Lemma no_stack_det_inv_tau {Pa : Params} {R : Type} :
  forall (t m : itree (@Det_OW_E Pa) R),
    observe t = TauF m ->
    no_stack_det t ->
    no_stack_det m.
Proof.
  intros t m Ho H; punfold H.
  destruct H as [? Ho' | m' Ho' Hm | ? ? ? Ho' _ _]; rewrite Ho in Ho'; try discriminate.
  injection Ho' as <-; pclearbot; exact Hm.
Qed.

Lemma run_draws_ext_no_stack_det {Pa : Params} {R : Type} :
  forall (s1 s2 : @draw_strat Pa) (t : itree (@OW_E Pa) R),
    (forall n dt, s1 n dt = s2 n dt) ->
    no_stack_det (run_draws s1 t) ->
    no_stack_det (run_draws s2 t).
Proof.
  pcofix CIH; intros s1 s2 t Heq H; punfold H; pstep.
  rewrite observe_run_draws in H.
  destruct (observe t) as [x | m | X e k] eqn:Hot.
  - apply (NSD_Ret _ _ x); rewrite observe_run_draws, Hot; reflexivity.
  - inversion H as [| m0 Ho0 Hm0 |]; try discriminate Ho0; subst.
    injection Ho0 as <-; pclearbot.
    apply (NSD_Tau _ _ (run_draws s2 m)); [rewrite observe_run_draws, Hot; reflexivity |].
    right; exact (CIH s1 s2 m Heq Hm0).
  - destruct (classify_ow_event e) as [[dt] | de] eqn:Ecl.
    + inversion H as [| m0 Ho0 Hm0 |]; try discriminate Ho0; subst.
      injection Ho0 as <-; pclearbot.
      apply (NSD_Tau _ _ (run_draws (shift_draw_strat s2) (k (s2 0%nat dt)))).
      * rewrite observe_run_draws, Hot, Ecl; reflexivity.
      * right; rewrite <- (Heq 0%nat dt).
        exact (CIH (shift_draw_strat s1) (shift_draw_strat s2) (k (s1 0%nat dt))
                 (fun n d => Heq (S n) d) Hm0).
    + inversion H as [| | X0 e0 k0 Ho0 Hns0 Hk0]; try discriminate Ho0; subst.
      assert (He_eq : e0 = de /\ exists Hcast : X0 = X,
                forall x : X, k0 (eq_rect_r (fun T => T) x Hcast) = run_draws s1 (k x)).
      { clear -Ho0; inversion Ho0; subst; split; [reflexivity | exists eq_refl; intros; reflexivity]. }
      destruct He_eq as [-> [-> Hk_eq]].
      apply (NSD_Vis _ _ de (fun x => run_draws s2 (k x))).
      * rewrite observe_run_draws, Hot, Ecl; reflexivity.
      * exact Hns0.
      * intros x; specialize (Hk0 x); pclearbot; rewrite Hk_eq in Hk0.
        right; exact (CIH s1 s2 (k x) Heq Hk0).
Qed.

Lemma cfg_steps_ub_no_stack_det {Pa : Params} {R : Type} :
  forall (s : @draw_strat Pa) env (t : @CFGtop Pa R),
    cfg_steps_to_ub s env t ->
    no_stack_det (run_draws s (run_cfg_locals env t)).
Proof.
  intros s env t H; induction H as
    [ s env t ke Ho
    | s env t t' Ho _ IH
    | s env t id dv ke Ho Hf _ IH
    | s env t id dv ke Ho _ IH
    | s env t dt ke s_sh Ho Hsh _ IH ].
  - pstep; eapply NSD_Vis.
    + rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity.
    + reflexivity.
    + intros [].
  - pstep; eapply NSD_Tau; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | left; exact IH].
  - pstep; eapply NSD_Tau; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; cbn; rewrite Hf; reflexivity | left; exact IH].
  - pstep; eapply NSD_Tau; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | left; exact IH].
  - pstep; eapply NSD_Tau; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | left].
    exact (run_draws_ext_no_stack_det s_sh (shift_draw_strat s) _ Hsh IH).
Qed.

Lemma cfg_steps_ret_no_stack_det {Pa : Params} {R : Type} :
  forall (s : @draw_strat Pa) env (t : @CFGtop Pa R) s' env' v,
    cfg_steps_to_ret s env t s' env' v ->
    no_stack_det (run_draws s (run_cfg_locals env t)).
Proof.
  intros s env t s' env' v H; induction H as
    [ s env t r Ho
    | s env t t' s' env' r Ho _ IH
    | s env t id dv ke s' env' r Ho Hf _ IH
    | s env t id dv ke s' env' r Ho _ IH
    | s env t dt ke s_sh s' env' r Ho Hsh _ IH ].
  - pstep; eapply NSD_Ret; rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity.
  - pstep; eapply NSD_Tau; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | left; exact IH].
  - pstep; eapply NSD_Tau; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; cbn; rewrite Hf; reflexivity | left; exact IH].
  - pstep; eapply NSD_Tau; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | left; exact IH].
  - pstep; eapply NSD_Tau; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | left].
    exact (run_draws_ext_no_stack_det s_sh (shift_draw_strat s) _ Hsh IH).
Qed.

Lemma det_vis_both_is_stack {Pa : Params} {R1 R2 : Type}
  (r : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop)
  {X1 X2 : Type}
  (e1 : @Det_OW_E Pa X1) (k1 : X1 -> itree (@Det_OW_E Pa) R1)
  (e2 : @Det_OW_E Pa X2) (k2 : X2 -> itree (@Det_OW_E Pa) R2) :
  det_vis_both r e1 k1 e2 k2 ->
  is_stack_det_event e1 = is_stack_det_event e2.
Proof.
  unfold Det_OW_E in e1, e2.
  repeat match type of e1 with
         | (_ +' _) _ =>
             destruct e1 as [x1 | e1]; destruct e2 as [x2 | e2];
             try (cbn; intros; contradiction)
         end;
    intros _; reflexivity.
Qed.

Lemma det_vis_both_no_stack_preserved {Pa : Params} {R1 R2 : Type}
  {X1 X2 : Type}
  (e1 : @Det_OW_E Pa X1) (k1 : X1 -> itree (@Det_OW_E Pa) R1)
  (e2 : @Det_OW_E Pa X2) (k2 : X2 -> itree (@Det_OW_E Pa) R2)
  (r : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop) :
  det_vis_both r e1 k1 e2 k2 ->
  ((is_stack_det_event e1 = false /\ forall x1, no_stack_det (k1 x1)) \/
   (is_stack_det_event e2 = false /\ forall x2, no_stack_det (k2 x2))) ->
  is_stack_det_event e1 = false /\
  is_stack_det_event e2 = false /\
  ((forall x1, no_stack_det (k1 x1)) \/ (forall x2, no_stack_det (k2 x2))).
Proof.
  intros Hvis Hdisj.
  pose proof (det_vis_both_is_stack r e1 k1 e2 k2 Hvis) as Heq.
  destruct Hdisj as [[He1 Hk1] | [He2 Hk2]].
  - rewrite He1 in Heq; symmetry in Heq; exact (conj He1 (conj Heq (or_introl Hk1))).
  - rewrite He2 in Heq; exact (conj Heq (conj He2 (or_intror Hk2))).
Qed.

Definition instr_varargs_irrel (ins : instr dtyp) : bool :=
  match ins with
  | INSTR_Call (_, fn_e) _ _ _ =>
      match intrinsic_exp fn_e with
      | Some _ => false
      | None => true
      end
  | _ => true
  end.

Definition cfg_varargs_irrel (G : CFG.cfg dtyp) : bool :=
  forallb (fun b => forallb (fun '(_, ins, _) => instr_varargs_irrel ins) (blk_code b)) (blks G).

Lemma denote_instr_varargs_eq {Pa : Params} :
  forall (i : instr_id * instr dtyp * list (metadata dtyp)) (va1 va2 : option (@ptr Pa)),
    instr_varargs_irrel (snd (fst i)) = true ->
    denote_instr i va1 = denote_instr i va2.
Proof.
  intros [[iid ins] md] va1 va2 Hirr; cbn in Hirr.
  destruct ins; try reflexivity.
  destruct fn as [dt fn_e]; destruct (intrinsic_exp fn_e); [discriminate Hirr | reflexivity].
Qed.

Lemma denote_code_varargs_eq {Pa : Params} :
  forall (c : code dtyp) (va1 va2 : option (@ptr Pa)),
    forallb (fun '(_, ins, _) => instr_varargs_irrel ins) c = true ->
    denote_code c va1 = denote_code c va2.
Proof.
  induction c as [| [[iid ins] md] rest IH]; intros va1 va2 H; [reflexivity |].
  cbn in H; apply andb_true_iff in H as [Hi Hr].
  unfold denote_code in *; cbn [loop_monad ExtLib.Structures.Monad.bind Monad_itree].
  rewrite (denote_instr_varargs_eq (iid, ins, md) va1 va2 Hi), (IH va1 va2 Hr); reflexivity.
Qed.

Lemma denote_block_varargs_eq {Pa : Params} :
  forall (G : CFG.cfg dtyp) b bid_from (va1 va2 : option (@ptr Pa)),
    cfg_varargs_irrel G = true ->
    In b (blks G) ->
    denote_block b bid_from va1 = denote_block b bid_from va2.
Proof.
  intros G b bid_from va1 va2 Hcfg Hb.
  unfold cfg_varargs_irrel in Hcfg; rewrite forallb_forall in Hcfg.
  pose proof (Hcfg b Hb) as Hbc.
  unfold denote_block; rewrite (denote_code_varargs_eq (blk_code b) va1 va2 Hbc); reflexivity.
Qed.

Lemma iter_pointwise_cfg_det_ref {Pa : Params} {I R : Type}
  (f1 f2 : I -> @CFGtop Pa (I + R))
  (Hfeq : forall i, f1 i = f2 i) :
  forall (sigma : @draw_strat Pa) env (u1 u2 : @CFGtop Pa R),
    (exists m : @CFGtop Pa (I + R),
       observe u1 = observe (ITree.bind m (fun lr =>
                      match lr with
                      | inl l => Tau (ITree.iter f1 l)
                      | inr r => Ret r
                      end)) /\
       observe u2 = observe (ITree.bind m (fun lr =>
                      match lr with
                      | inl l => Tau (ITree.iter f2 l)
                      | inr r => Ret r
                      end))) ->
    det_ref eq
      (run_draws sigma (run_cfg_locals env u1))
      (run_draws sigma (run_cfg_locals env u2)).
Proof.
  intros sigma env u1 u2 Hwit; revert sigma env u1 u2 Hwit.
  pcofix CIH; intros sigma env u1 u2 [m [Ho1 Ho2]].
  pstep; apply DR_Step; unfold det_step_body.
  rewrite !observe_run_draws, !observe_run_cfg_locals, Ho1, Ho2, !observe_bind.
  destruct (observe m) as [[l | rv] | m' | X e k].
  - cbn [observe]; right; apply CIH.
    exists (f1 l); split;
      [rewrite observe_iter; reflexivity
      | rewrite observe_iter, (Hfeq l); reflexivity].
  - cbn [observe]; reflexivity.
  - cbn [observe]; right; apply CIH; exists m'; split; reflexivity.
  - cbn [observe]; destruct (classify_cfg_event e) as [le | oe].
    + destruct le as [id dv | id].
      * right; apply CIH; exists (k tt); split; reflexivity.
      * destruct (RM.find id env) as [dv |].
        -- right; apply CIH; exists (k dv); split; reflexivity.
        -- right; apply det_vis_both_refl; intros [].
    + destruct (classify_ow_event oe) as [[dt] | de].
      * right; apply CIH; exists (k (sigma 0%nat dt)); split; reflexivity.
      * right; apply det_vis_both_refl; intros x; right; apply CIH; exists (k x); split; reflexivity.
Qed.

Lemma pure_cfg_steps_to_tau_no_stack_det_ {Pa : Params} {R : Type}
  (r : itree (@Det_OW_E Pa) R -> Prop) :
  forall (s : @draw_strat Pa) env (t : @CFGtop Pa R) env' m,
    pure_cfg_steps_to_tau env t env' m ->
    upaco1 (@no_stack_det_ Pa R) r (run_draws s (run_cfg_locals env' m)) ->
    paco1 (@no_stack_det_ Pa R) r (run_draws s (run_cfg_locals env t)).
Proof.
  intros s env t env' m H Hr.
  induction H as
    [ env t m Ho
    | env t t' env' m Ho _ IH
    | env t id dv ke env' m Ho Hf _ IH
    | env t id dv ke env' m Ho _ IH ].
  - pstep; eapply NSD_Tau; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | exact Hr].
  - pstep; eapply NSD_Tau; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | left; exact (IH Hr)].
  - pstep; eapply NSD_Tau; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; cbn; rewrite Hf; reflexivity | left; exact (IH Hr)].
  - pstep; eapply NSD_Tau; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | left; exact (IH Hr)].
Qed.

Lemma check_pevals_self_cut_rel {Pa : Params} :
  forall pspecs pevals_s pevals_t dvs_s ctx opt_pf (penv : param_env Pa),
    Forall2 (phi_eval_pair_matches penv dummy_freeze_oracle) pevals_s dvs_s ->
    check_pevals_refine ctx opt_pf pspecs pevals_s pevals_t = true ->
    exists dvs_t : list (raw_id * @dvalue Pa),
      cut_phi_rel pspecs dvs_s dvs_t.
Proof.
  induction pspecs as [| [[id_s id_t] w] rp IH];
    intros pevals_s pevals_t dvs_s ctx opt_pf penv Hms Hchk;
    destruct pevals_s as [| [[id_s' w_s] ce_s] rs];
    destruct pevals_t as [| [[id_t' w_t] ce_t] rt];
    cbn [check_pevals_refine] in Hchk; try discriminate Hchk.
  - inversion Hms; subst; exists []; constructor.
  - rewrite !andb_true_iff in Hchk.
    destruct Hchk as ((((((Heqs & _) & Hws) & _) & Hsup) & _) & Hrest).
    apply raw_id_eqb_eq in Heqs; apply Pos.eqb_eq in Hws; subst id_s' w_s.
    inversion Hms as [| ? [id_sd dv_s] ? dvs_sr [-> [_ Hsc_s]] Hms_r]; subst.
    destruct (IH rs rt dvs_sr ctx opt_pf penv Hms_r Hrest) as [dvs_tr Hrel_r].
    exists ((id_t, dv_s) :: dvs_tr).
    exact (CPR_Cons id_s id_t w dv_s dv_s rp dvs_sr dvs_tr Hsup Hsc_s Hsc_s (or_intror eq_refl) Hrel_r).
Qed.

Lemma check_loop_cutpoint_cfg_no_stack_det {Pa : Params} :
  forall allowed init_ctx (src_cfg tgt_cfg : CFG.cfg dtyp)
         (cert : proof_certificate) (lci : loop_cutpoint_info)
         (opt_pf : option (list lrat_step))
         arg_dtys (vs : list (@dvalue Pa)),
    let src_pnames := List.map cert_reg_name (args src_cfg) in
    let src_uses := param_idx_uses_cfg src_cfg in
    NoDup (args src_cfg) ->
    NoDup src_pnames ->
    List.length arg_dtys = List.length (args src_cfg) ->
    cfg_param_dtyp_compatible src_cfg arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx w pnm,
      In (idx, DTYPE_Base (DTYPE_I w)) src_uses ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w) allowed) ->
    check_loop_cutpoint_cfg allowed init_ctx src_cfg tgt_cfg cert lci opt_pf = true ->
    forall (sigma : @draw_strat Pa),
      no_stack_det (run_draws sigma (eval_cfg_open src_cfg vs)).
Proof.
  intros allowed init_ctx src_cfg tgt_cfg cert lci opt_pf arg_dtys vs
         src_pnames src_uses Hnd_sa Hnd_sp Hlen_da Hcomp_s Hvs Hpu_s Hchk sigma.
  unfold check_loop_cutpoint_cfg in Hchk; cbn zeta in Hchk.
  fold src_pnames src_uses in Hchk.
  set (lmap0_s := init_param_lmap (args src_cfg) src_pnames src_uses) in *.
  apply andb_true_iff in Hchk as [Hall_in Hchk].
  destruct (reify_natural_loop src_cfg (lci_src_header lci) lmap0_s (overlay_hspecs_s 0%nat))
    as [[hspecs_s s_s] |] eqn:Er_s; [| discriminate Hchk].
  destruct (reify_natural_loop tgt_cfg (lci_tgt_header lci)
              (init_param_lmap (args tgt_cfg) src_pnames (param_idx_uses_cfg tgt_cfg))
              (overlay_hspecs_t 0%nat))
    as [[hspecs_t s_t] |]; [| discriminate Hchk].
  destruct (pair_phi_specs hspecs_s hspecs_t) as [pspecs |] eqn:Epair; [| discriminate Hchk].
  set (cut_allowed := allowed ++ cut_vars_from 0%nat pspecs) in *.
  apply andb_true_iff in Hchk as [Hnd_all Hchk].
  apply no_dup_strings_spec in Hnd_all.
  pose proof (NoDup_app_r _ _ Hnd_all) as Hnd_cut.
  assert (Hall_not_cut : forall nm w, In (nm, w) allowed -> ~ In nm (cut_names_from 0%nat pspecs)).
  { intros nm w Hin; rewrite forallb_forall in Hall_in.
    pose proof (Hall_in (nm, w) Hin) as Hsin; cbn in Hsin.
    apply string_in_list_spec in Hsin; exact (NoDup_app_disj _ _ nm Hnd_all Hsin). }
  destruct (fold_ub_assumptions allowed (nls_evals_entry s_s) [] init_ctx
              (block_uas_for (init src_cfg) (pc_blocks cert))) as [ctx_ent |]; [| discriminate Hchk].
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as (((_ & _) & Href_init) & Hchk).
  destruct (fold_ub_assumptions cut_allowed (nls_evals_hdr s_s) [nls_ce_cond s_s]
              (filter_param_ub_ctx src_pnames ctx_ent)
              (block_uas_for (nls_bid_hdr s_s) (pc_blocks cert)))
    as [ctx_hdr |]; [| discriminate Hchk].
  rewrite !andb_true_iff in Hchk; destruct Hchk as (_ & Hchk).
  set (latch_uas := if raw_id_eqb (nls_bid_latch_entry s_s) (nls_bid_hdr s_s) then []
                    else block_uas_for (nls_bid_latch_entry s_s) (pc_blocks cert)) in *.
  destruct (fold_ub_assumptions cut_allowed (nls_evals_hdr s_s ++ nls_evals_body s_s)
              [nls_ce_cond s_s]
              (extract_branch_cond_assumptions (nls_latch_on_true s_s) (nls_ce_cond s_s) ++ ctx_hdr)
              latch_uas) as [ctx_cont |]; [| discriminate Hchk].
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as (((_ & _) & Href_next) & _).
  pose proof (pair_phi_specs_supported _ _ _ Epair) as Hsup_ps.
  assert (Hwrap_s : forall lmap, wf_pure_lmap allowed lmap ->
    wf_pure_lmap cut_allowed (overlay_hspecs_s 0%nat lmap hspecs_s)).
  { intros lmap Hl; destruct (pair_phi_specs_overlay _ _ _ 0%nat lmap lmap Epair) as (Hos & _).
    rewrite Hos.
    assert (Hlc : wf_pure_lmap cut_allowed lmap)
      by (apply (wf_pure_lmap_mono allowed cut_allowed); [intros u Hu; apply in_app_iff; left; exact Hu | exact Hl]).
    exact (proj1 (overlay_cut_lmap_typing pspecs 0%nat cut_allowed lmap lmap Hsup_ps
                    (fun u Hu => proj2 (in_app_iff _ _ _) (or_intror Hu)) Hlc Hlc)). }
  destruct (reify_natural_loop_spec src_cfg (lci_src_header lci) allowed cut_allowed
              lmap0_s (overlay_hspecs_s 0%nat) hspecs_s s_s
              (init_param_lmap_typing src_uses (args src_cfg) src_pnames allowed Hpu_s)
              (init_param_lmap_dom src_uses (args src_cfg) src_pnames)
              Hwrap_s Er_s)
    as (b_ent_s & b_hdr_s & _ & Hf_hdr_s & _ & Hr_init_s & Hr_next_s &
        Hlmap_ent_s & Hdom_ent_s & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        Hstep_ent_s & Hstep_hdr_s).
  set (penv := build_param_env src_pnames vs) in *.
  set (bmap_s := ocfg_map (blks src_cfg)) in *.
  pose proof (List.Forall2_length Hvs) as Hlen_vs.
  assert (Hlen_sp : List.length src_pnames = List.length (args src_cfg))
    by (unfold src_pnames; apply List.length_map).
  assert (Hlp_s : List.length (args src_cfg) = List.length vs) by lia.
  assert (Hls_v : List.length src_pnames = List.length vs) by lia.
  pose proof (init_param_lmap_matches src_uses (args src_cfg) src_pnames arg_dtys vs
                Hnd_sa Hnd_sp Hlp_s Hls_v Hvs
                (cfg_param_dtyp_compatible_nth src_cfg arg_dtys Hcomp_s)) as Henv0_s.
  fold penv lmap0_s in Henv0_s.
  unfold eval_cfg_open.
  change (denote_cfg src_cfg None) with (denote_cfg_from bmap_s None (init src_cfg, init src_cfg)).
  destruct (Hstep_ent_s Pa None penv (init_cfg_locals (args src_cfg) vs) Henv0_s)
    as [[Hub_ent_s _] | (env_entry_s & Henv_ent_s & _ & Htau_ent_s)].
  - exact (cfg_steps_ub_no_stack_det sigma _ _ (Hub_ent_s sigma)).
  - destruct (pure_phis_denote_step (blk_phis b_hdr_s) penv (init src_cfg)
                (nls_lmap_entry s_s) env_entry_s (nls_init_pevals s_s) Henv_ent_s Hr_init_s)
      as [[Hub_ip_s _] | [dvs0_s [Hpm0_s Hst_ip_s]]].
    + eapply cfg_steps_ub_no_stack_det; eapply pure_cfg_steps_to_tau_then_ub; [exact Htau_ent_s |].
      eapply denote_cfg_from_block_ub; [exact Hf_hdr_s |].
      unfold denote_block; apply cfg_steps_to_ub_bind_l; exact (Hub_ip_s sigma).
    + destruct (check_pevals_self_cut_rel pspecs (nls_init_pevals s_s) (nls_init_pevals s_t)
                  dvs0_s ctx_ent opt_pf penv Hpm0_s Href_init) as [dvs0_t Hrel0].
      assert (Hloop_ns :
        forall bid_prev_s env_prev_s dvs_s dvs_t,
          (forall r0, In r0 (args src_cfg ++ code_written_ids (blk_code b_ent_s)) ->
             RM.find r0 env_prev_s = RM.find r0 env_entry_s) ->
          pure_cfg_steps env_prev_s (denote_phis bid_prev_s (blk_phis b_hdr_s))
            (apply_phi_env env_prev_s dvs_s) tt ->
          cut_phi_rel pspecs dvs_s dvs_t ->
          no_stack_det (run_draws sigma (run_cfg_locals env_prev_s
             (denote_cfg_from bmap_s None (bid_prev_s, nls_bid_hdr s_s))))).
      { pcofix CIH_ns.
        intros bid_prev_s env_prev_s dvs_s dvs_t Hag_s Hphis_s Hrel.
        set (bs := cut_bindings_from 0%nat pspecs dvs_s dvs_t).
        set (penv_cut := extend_penv bs penv).
        pose proof (cut_bindings_fst pspecs dvs_s dvs_t 0%nat Hrel) as Hbs_fst; fold bs in Hbs_fst.
        assert (Hnd_bs : NoDup (List.map fst bs)) by (rewrite Hbs_fst; exact Hnd_cut).
        assert (Hp_agree : forall nm w, In (nm, w) allowed -> penv nm = penv_cut nm).
        { intros nm w Hin; symmetry; unfold penv_cut; apply extend_penv_not_in.
          rewrite Hbs_fst; exact (Hall_not_cut nm w Hin). }
        pose proof (lmap_matches_env_transfer allowed _ penv penv_cut
                      (nls_lmap_entry s_s) env_entry_s env_prev_s
                      Hlmap_ent_s Hdom_ent_s Hp_agree Hag_s Henv_ent_s) as Hlm_prev_s.
        assert (Hlm_empty : lmap_matches_env penv_cut (RM.empty _) (RM.empty _))
          by (intros r0 w0 ce0 Hf0; rewrite RMF.F.empty_o in Hf0; discriminate Hf0).
        destruct (overlay_cut_lmap_matches pspecs dvs_s dvs_t 0%nat bs penv
                    (nls_lmap_entry s_s) (RM.empty _) env_prev_s (RM.empty _)
                    Hrel Hnd_bs (incl_refl bs) Hlm_prev_s Hlm_empty)
          as [Hlm_hdr0_s _].
        destruct (pair_phi_specs_overlay hspecs_s hspecs_t pspecs 0%nat
                    (nls_lmap_entry s_s) (RM.empty _) Epair)
          as (Hos_eq & _ & Hms_eq & _).
        rewrite <- Hos_eq in Hlm_hdr0_s.
        assert (Hmap_dvs_s : List.map fst dvs_s = List.map fst hspecs_s).
        { rewrite Hms_eq; clear -Hrel; induction Hrel; cbn; [reflexivity | f_equal; assumption]. }
        destruct (Hstep_hdr_s Pa None penv_cut bid_prev_s env_prev_s dvs_s
                    Hmap_dvs_s Hphis_s Hlm_hdr0_s)
          as [[Hub_hs _] | (cbit_s & _ & _ & Hcont_s & Hexit_s)].
        - eapply paco1_mon; [exact (cfg_steps_ub_no_stack_det sigma _ _ (Hub_hs sigma)) | intros ? []].
        - destruct (Bool.eqb (@Integers.unsigned 1 cbit_s =? 1)%Z (nls_latch_on_true s_s)).
          + destruct (Hcont_s eq_refl)
              as [[Hub_bs _] | (env_latch_s & Hlm_latch_s & _ & Hpres_ls & Htau_s)].
            * eapply paco1_mon; [exact (cfg_steps_ub_no_stack_det sigma _ _ (Hub_bs sigma)) | intros ? []].
            * destruct (pure_phis_denote_step (blk_phis b_hdr_s) penv_cut (nls_bid_latch_from s_s)
                          (nls_lmap_latch s_s) env_latch_s (nls_next_pevals s_s) Hlm_latch_s Hr_next_s)
                as [[Hub_np_s _] | [dvs_next_s [Hpm_next_s Hst_np_s]]].
              -- assert (Hub_lnp : cfg_steps_to_ub sigma env_prev_s
                           (denote_cfg_from bmap_s None (bid_prev_s, nls_bid_hdr s_s))).
                 { eapply pure_cfg_steps_to_tau_then_ub; [exact Htau_s |].
                   eapply denote_cfg_from_block_ub; [exact Hf_hdr_s |].
                   unfold denote_block; apply cfg_steps_to_ub_bind_l; exact (Hub_np_s sigma). }
                 eapply paco1_mon; [exact (cfg_steps_ub_no_stack_det sigma _ _ Hub_lnp) | intros ? []].
              -- destruct (check_pevals_self_cut_rel pspecs (nls_next_pevals s_s) (nls_next_pevals s_t)
                             dvs_next_s ctx_cont opt_pf penv_cut Hpm_next_s Href_next)
                   as [dvs_next_t Hrel_next].
                 eapply pure_cfg_steps_to_tau_no_stack_det_; [exact Htau_s | right].
                 exact (CIH_ns (nls_bid_latch_from s_s) env_latch_s dvs_next_s dvs_next_t
                               (fun r0 Hr0 => eq_trans (Hpres_ls r0 Hr0) (Hag_s r0 Hr0))
                               Hst_np_s Hrel_next).
          + destruct (Hexit_s eq_refl)
              as [[Hub_xs _] | (env_exit_s & dv_ret_s & _ & _ & _ & Hret_st_s)].
            * eapply paco1_mon; [exact (cfg_steps_ub_no_stack_det sigma _ _ (Hub_xs sigma)) | intros ? []].
            * eapply paco1_mon;
                [exact (cfg_steps_ret_no_stack_det sigma _ _ _ _ _
                          (pure_cfg_to_cfg_ret sigma _ _ _ _ Hret_st_s))
                | intros ? []]. }
      eapply pure_cfg_steps_to_tau_no_stack_det_; [exact Htau_ent_s | left].
      exact (Hloop_ns (init src_cfg) env_entry_s dvs0_s dvs0_t (fun _ _ => eq_refl) Hst_ip_s Hrel0).
Qed.

Lemma rmap_find_in_elements {V : Type} :
  forall (m : rmap V) k v,
    RM.find k m = Some v ->
    exists k', In (k', v) (RM.elements m).
Proof.
  intros m k v Hf.
  pose proof (RM.elements_1 (RM.find_2 Hf)) as Hina.
  induction Hina as [[k' v'] rest [_ Heqv] | [k' v'] rest _ IH].
  - cbn in Heqv; subst v'; exists k'; left; reflexivity.
  - destruct IH as [k0 Hin]; exists k0; right; exact Hin.
Qed.

Definition bmap_varargs_irrel (bmap : rmap (block dtyp)) : bool :=
  forallb (fun '(_, b) => forallb (fun '(_, ins, _) => instr_varargs_irrel ins) (blk_code b))
    (RM.elements bmap).

Lemma obs_eq_cfg_locals_draws {Pa : Params} {S : Type} :
  forall (sigma : @draw_strat Pa) env (u1 u2 : @CFGtop Pa S),
    observe u1 = observe u2 ->
    observe (run_draws sigma (run_cfg_locals env u1)) =
    observe (run_draws sigma (run_cfg_locals env u2)).
Proof.
  intros sigma env u1 u2 Ho.
  assert (Hloc : observe (run_cfg_locals env u1) = observe (run_cfg_locals env u2))
    by (rewrite !observe_run_cfg_locals, Ho; reflexivity).
  rewrite !observe_run_draws, Hloc; reflexivity.
Qed.

Lemma no_stack_det_inv_vis {Pa : Params} {R X : Type} :
  forall (t : itree (@Det_OW_E Pa) R) (e : @Det_OW_E Pa X) (k : X -> itree (@Det_OW_E Pa) R),
    observe t = VisF e k ->
    no_stack_det t ->
    is_stack_det_event e = false /\ forall x : X, no_stack_det (k x).
Proof.
  intros t e k Ho H; punfold H.
  destruct H as [? Ho' | ? Ho' _ | X0 e0 k0 Ho' Hns Hk]; rewrite Ho in Ho'; try discriminate Ho'.
  assert (Heq : e0 = e /\ exists Hc : X0 = X, forall x : X, k0 (eq_rect_r (fun T => T) x Hc) = k x).
  { clear -Ho'; inversion Ho'; subst; split; [reflexivity | exists eq_refl; intros; reflexivity]. }
  destruct Heq as [-> [-> Hk_eq]].
  split; [exact Hns | intros x; specialize (Hk x); pclearbot; rewrite Hk_eq in Hk; exact Hk].
Qed.

Lemma iter_bind_pointwise_cfg_det_ref {Pa : Params} {I R S : Type}
  (f1 f2 : I -> @CFGtop Pa (I + R))
  (g : R -> @CFGtop Pa S)
  (Hfeq : forall i, f1 i = f2 i) :
  forall (sigma : @draw_strat Pa) env (u1 u2 : @CFGtop Pa S),
    (observe u1 = observe u2 \/
     exists m : @CFGtop Pa (I + R),
       observe u1 = observe (ITree.bind (ITree.bind m (fun lr =>
                      match lr with
                      | inl l => Tau (ITree.iter f1 l)
                      | inr r => Ret r
                      end)) g) /\
       observe u2 = observe (ITree.bind (ITree.bind m (fun lr =>
                      match lr with
                      | inl l => Tau (ITree.iter f2 l)
                      | inr r => Ret r
                      end)) g)) ->
    det_ref eq
      (run_draws sigma (run_cfg_locals env u1))
      (run_draws sigma (run_cfg_locals env u2)).
Proof.
  intros sigma env u1 u2 Hwit; revert sigma env u1 u2 Hwit.
  pcofix CIH; intros sigma env u1 u2 [Ho | [m [Ho1 Ho2]]].
  - eapply det_ref_obs_eq with
      (t1 := run_draws sigma (run_cfg_locals env u2))
      (t2 := run_draws sigma (run_cfg_locals env u2)).
    + exact (obs_eq_cfg_locals_draws sigma env u1 u2 Ho).
    + reflexivity.
    + eapply paco2_mon; [apply det_ref_refl; intros; reflexivity | intros ? ? []].
  - destruct (observe m) as [[l | rv] | m' | X e k] eqn:Hom.
    + pstep; apply DR_Step; unfold det_step_body.
      rewrite !observe_run_draws, !observe_run_cfg_locals, Ho1, Ho2, !observe_bind, Hom; cbn [observe].
      right; apply CIH; right; exists (f1 l); split.
      * rewrite observe_bind, observe_iter; symmetry; rewrite observe_bind; reflexivity.
      * rewrite observe_bind, observe_iter, <- (Hfeq l); symmetry; rewrite observe_bind; reflexivity.
    + assert (Ho_eq : observe u1 = observe u2).
      { rewrite Ho1, Ho2, !observe_bind, Hom; reflexivity. }
      eapply det_ref_obs_eq with
        (t1 := run_draws sigma (run_cfg_locals env u2))
        (t2 := run_draws sigma (run_cfg_locals env u2)).
      * exact (obs_eq_cfg_locals_draws sigma env u1 u2 Ho_eq).
      * reflexivity.
      * eapply paco2_mon; [apply det_ref_refl; intros; reflexivity | intros ? ? []].
    + pstep; apply DR_Step; unfold det_step_body.
      rewrite !observe_run_draws, !observe_run_cfg_locals, Ho1, Ho2, !observe_bind, Hom; cbn [observe].
      right; apply CIH; right; exists m'; split; reflexivity.
    + pstep; apply DR_Step; unfold det_step_body.
      rewrite !observe_run_draws, !observe_run_cfg_locals, Ho1, Ho2, !observe_bind, Hom; cbn [observe].
      destruct (classify_cfg_event e) as [le | oe].
      * destruct le as [id dv | id].
        -- right; apply CIH; right; exists (k tt); split; reflexivity.
        -- destruct (RM.find id env) as [dv |].
           ++ right; apply CIH; right; exists (k dv); split; reflexivity.
           ++ right; apply det_vis_both_refl; intros [].
      * destruct (classify_ow_event oe) as [[dt] | de].
        -- right; apply CIH; right; exists (k (sigma 0%nat dt)); split; reflexivity.
        -- right; apply det_vis_both_refl; intros x; right; apply CIH; right; exists (k x); split; reflexivity.
Qed.

Lemma iter_bind_pointwise_no_stack_det {Pa : Params} {I R S : Type}
  (f1 f2 : I -> @CFGtop Pa (I + R))
  (g : R -> @CFGtop Pa S)
  (Hfeq : forall i, f1 i = f2 i) :
  forall (sigma : @draw_strat Pa) env (u1 u2 : @CFGtop Pa S),
    (observe u1 = observe u2 \/
     exists m : @CFGtop Pa (I + R),
       observe u1 = observe (ITree.bind (ITree.bind m (fun lr =>
                      match lr with
                      | inl l => Tau (ITree.iter f1 l)
                      | inr r => Ret r
                      end)) g) /\
       observe u2 = observe (ITree.bind (ITree.bind m (fun lr =>
                      match lr with
                      | inl l => Tau (ITree.iter f2 l)
                      | inr r => Ret r
                      end)) g)) ->
    no_stack_det (run_draws sigma (run_cfg_locals env u2)) ->
    no_stack_det (run_draws sigma (run_cfg_locals env u1)).
Proof.
  intros sigma env u1 u2 Hwit Hns2; revert sigma env u1 u2 Hwit Hns2.
  pcofix CIH; intros sigma env u1 u2 [Ho | [m [Ho1 Ho2]]] Hns2.
  - eapply paco1_mon;
      [eapply no_stack_det_obs_eq;
         [symmetry; exact (obs_eq_cfg_locals_draws sigma env u1 u2 Ho) | exact Hns2]
      | intros ? []].
  - destruct (observe m) as [[l | rv] | m' | X e k] eqn:Hom.
    + assert (Ho_t2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                      TauF (run_draws sigma (run_cfg_locals env (ITree.bind (ITree.iter f2 l) g))))
        by (rewrite observe_run_draws, observe_run_cfg_locals, Ho2, !observe_bind, Hom; reflexivity).
      pose proof (no_stack_det_inv_tau _ _ Ho_t2 Hns2) as Hns2'.
      pstep; eapply NSD_Tau;
        [rewrite observe_run_draws, observe_run_cfg_locals, Ho1, !observe_bind, Hom; reflexivity | right].
      eapply CIH; [right; exists (f1 l); split | exact Hns2'].
      * rewrite observe_bind, observe_iter; symmetry; rewrite observe_bind; reflexivity.
      * rewrite observe_bind, observe_iter, <- (Hfeq l); symmetry; rewrite observe_bind; reflexivity.
    + assert (Ho_eq : observe u1 = observe u2)
        by (rewrite Ho1, Ho2, !observe_bind, Hom; reflexivity).
      eapply paco1_mon;
        [eapply no_stack_det_obs_eq;
           [symmetry; exact (obs_eq_cfg_locals_draws sigma env u1 u2 Ho_eq) | exact Hns2]
        | intros ? []].
    + assert (Ho_t2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                      TauF (run_draws sigma (run_cfg_locals env
                        (ITree.bind (ITree.bind m' (fun lr => match lr with inl l => Tau (ITree.iter f2 l) | inr r0 => Ret r0 end)) g))))
        by (rewrite observe_run_draws, observe_run_cfg_locals, Ho2, !observe_bind, Hom; reflexivity).
      pose proof (no_stack_det_inv_tau _ _ Ho_t2 Hns2) as Hns2'.
      pstep; eapply NSD_Tau;
        [rewrite observe_run_draws, observe_run_cfg_locals, Ho1, !observe_bind, Hom; reflexivity | right].
      eapply CIH; [right; exists m'; split; reflexivity | exact Hns2'].
    + destruct (classify_cfg_event e) as [le | oe] eqn:Ece.
      * destruct le as [id dv | id].
        -- assert (Ho_t2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                           TauF (run_draws sigma (run_cfg_locals (RM.add id dv env)
                             (ITree.bind (ITree.bind (k tt) (fun lr => match lr with inl l => Tau (ITree.iter f2 l) | inr r0 => Ret r0 end)) g))))
             by (rewrite observe_run_draws, observe_run_cfg_locals, Ho2, !observe_bind, Hom; cbn [observe]; rewrite Ece; reflexivity).
           pose proof (no_stack_det_inv_tau _ _ Ho_t2 Hns2) as Hns2'.
           pstep; eapply NSD_Tau;
             [rewrite observe_run_draws, observe_run_cfg_locals, Ho1, !observe_bind, Hom; cbn [observe]; rewrite Ece; reflexivity | right].
           eapply CIH; [right; exists (k tt); split; reflexivity | exact Hns2'].
        -- destruct (RM.find id env) as [dv |] eqn:Ef.
           ++ assert (Ho_t2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                              TauF (run_draws sigma (run_cfg_locals env
                                (ITree.bind (ITree.bind (k dv) (fun lr => match lr with inl l => Tau (ITree.iter f2 l) | inr r0 => Ret r0 end)) g))))
                by (rewrite observe_run_draws, observe_run_cfg_locals, Ho2, !observe_bind, Hom; cbn [observe]; rewrite Ece, Ef; reflexivity).
              pose proof (no_stack_det_inv_tau _ _ Ho_t2 Hns2) as Hns2'.
              pstep; eapply NSD_Tau;
                [rewrite observe_run_draws, observe_run_cfg_locals, Ho1, !observe_bind, Hom; cbn [observe]; rewrite Ece, Ef; reflexivity | right].
              eapply CIH; [right; exists (k dv); split; reflexivity | exact Hns2'].
           ++ assert (Ho_v : observe (run_draws sigma (run_cfg_locals env u2)) =
                             observe (run_draws sigma (run_cfg_locals env u1)))
                by (rewrite !observe_run_draws, !observe_run_cfg_locals, Ho1, Ho2, !observe_bind, Hom; cbn [observe]; rewrite Ece, Ef; reflexivity).
              eapply paco1_mon; [exact (no_stack_det_obs_eq _ _ Ho_v Hns2) | intros ? []].
      * destruct (classify_ow_event oe) as [[dt] | de] eqn:Eoe.
        -- assert (Ho_t2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                           TauF (run_draws (shift_draw_strat sigma) (run_cfg_locals env
                             (ITree.bind (ITree.bind (k (sigma 0%nat dt)) (fun lr => match lr with inl l => Tau (ITree.iter f2 l) | inr r0 => Ret r0 end)) g))))
             by (rewrite observe_run_draws, observe_run_cfg_locals, Ho2, !observe_bind, Hom; cbn [observe]; rewrite Ece, Eoe; reflexivity).
           pose proof (no_stack_det_inv_tau _ _ Ho_t2 Hns2) as Hns2'.
           pstep; eapply NSD_Tau;
             [rewrite observe_run_draws, observe_run_cfg_locals, Ho1, !observe_bind, Hom; cbn [observe]; rewrite Ece, Eoe; reflexivity | right].
           eapply CIH; [right; exists (k (sigma 0%nat dt)); split; reflexivity | exact Hns2'].
        -- assert (Ho_v2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                           VisF de (fun x => run_draws sigma (run_cfg_locals env
                             (ITree.bind (ITree.bind (k x) (fun lr => match lr with inl l => Tau (ITree.iter f2 l) | inr r0 => Ret r0 end)) g))))
             by (rewrite observe_run_draws, observe_run_cfg_locals, Ho2, !observe_bind, Hom; cbn [observe]; rewrite Ece, Eoe; reflexivity).
           destruct (no_stack_det_inv_vis _ _ _ Ho_v2 Hns2) as [Hns_de Hk_ns].
           pstep; eapply NSD_Vis;
             [rewrite observe_run_draws, observe_run_cfg_locals, Ho1, !observe_bind, Hom; cbn [observe]; rewrite Ece, Eoe; reflexivity
             | exact Hns_de
             | intros x; right; eapply CIH; [right; exists (k x); split; reflexivity | exact (Hk_ns x)]].
Qed.

Lemma ocfg_step_varargs_eq {Pa : Params} :
  forall (bmap : rmap (block dtyp)) (va1 va2 : option (@ptr Pa)),
    bmap_varargs_irrel bmap = true ->
    forall (p : block_id * block_id),
      (let '(bid_from, bid_src) := p in
       match RM.find bid_src bmap with
       | None => ret (inr (inl (bid_from, bid_src)))
       | Some block_src =>
           bd <- denote_block block_src bid_from va1 ;;
           match bd with
           | inr dv => ret (inr (inr dv))
           | inl bid_target => ret (inl (bid_src, bid_target))
           end
       end : @CFGtop Pa ((block_id * block_id) + ((block_id * block_id) + @dvalue Pa))) =
      (let '(bid_from, bid_src) := p in
       match RM.find bid_src bmap with
       | None => ret (inr (inl (bid_from, bid_src)))
       | Some block_src =>
           bd <- denote_block block_src bid_from va2 ;;
           match bd with
           | inr dv => ret (inr (inr dv))
           | inl bid_target => ret (inl (bid_src, bid_target))
           end
       end).
Proof.
  intros bmap va1 va2 Hbm [bid_from bid_src].
  destruct (RM.find bid_src bmap) as [b |] eqn:Hf; [| reflexivity].
  destruct (rmap_find_in_elements bmap bid_src b Hf) as [k' Hin].
  unfold bmap_varargs_irrel in Hbm; rewrite forallb_forall in Hbm.
  pose proof (Hbm (k', b) Hin) as Hbc; cbn in Hbc.
  unfold denote_block; rewrite (denote_code_varargs_eq (blk_code b) va1 va2 Hbc); reflexivity.
Qed.

Lemma denote_cfg_varargs_det_ref {Pa : Params} :
  forall (G : CFG.cfg dtyp) (va1 va2 : option (@ptr Pa)) (sigma : @draw_strat Pa) env,
    bmap_varargs_irrel (ocfg_map (blks G)) = true ->
    det_ref eq
      (run_draws sigma (run_cfg_locals env (denote_cfg_map (ocfg_map (blks G)) G va1)))
      (run_draws sigma (run_cfg_locals env (denote_cfg_map (ocfg_map (blks G)) G va2))).
Proof.
  intros G va1 va2 sigma env Hbm.
  unfold denote_cfg_map, denote_ocfg_map.
  eapply iter_bind_pointwise_cfg_det_ref;
    [exact (ocfg_step_varargs_eq (ocfg_map (blks G)) va1 va2 Hbm) |].
  right; eexists; split;
    (rewrite observe_bind, observe_iter; symmetry; rewrite observe_bind; reflexivity).
Qed.

Lemma denote_cfg_varargs_no_stack_det {Pa : Params} :
  forall (G : CFG.cfg dtyp) (va1 va2 : option (@ptr Pa)) (sigma : @draw_strat Pa) env,
    bmap_varargs_irrel (ocfg_map (blks G)) = true ->
    no_stack_det (run_draws sigma (run_cfg_locals env (denote_cfg_map (ocfg_map (blks G)) G va2))) ->
    no_stack_det (run_draws sigma (run_cfg_locals env (denote_cfg_map (ocfg_map (blks G)) G va1))).
Proof.
  intros G va1 va2 sigma env Hbm Hns.
  unfold denote_cfg_map, denote_ocfg_map in *.
  eapply iter_bind_pointwise_no_stack_det;
    [exact (ocfg_step_varargs_eq (ocfg_map (blks G)) va1 va2 Hbm) | | exact Hns].
  right; eexists; split;
    (rewrite observe_bind, observe_iter; symmetry; rewrite observe_bind; reflexivity).
Qed.

Lemma visf_eq_inv {E : Type -> Type} {R X1 X2 : Type}
  (e1 : E X1) (k1 : X1 -> itree E R)
  (e2 : E X2) (k2 : X2 -> itree E R) :
  VisF e1 k1 = VisF e2 k2 ->
  exists Hc : X1 = X2,
    eq_rect X1 E e1 X2 Hc = e2 /\
    (forall x : X1, k1 x = k2 (eq_rect X1 (fun T => T) x X2 Hc)).
Proof.
  intros H; inversion H; subst; exists eq_refl; split; reflexivity.
Qed.

Lemma obs_eq_fn_frames_draws {Pa : Params} {R : Type} :
  forall (sigma : @draw_strat Pa) env stk exc_slot (u1 u2 : @CFGtop Pa R),
    observe u1 = observe u2 ->
    observe (run_draws sigma (run_fn_frames env stk exc_slot u1)) =
    observe (run_draws sigma (run_fn_frames env stk exc_slot u2)).
Proof.
  intros sigma env stk exc_slot u1 u2 Ho.
  assert (Hfn : observe (run_fn_frames env stk exc_slot u1) =
                observe (run_fn_frames env stk exc_slot u2))
    by (rewrite !observe_run_fn_frames, Ho; reflexivity).
  rewrite !observe_run_draws, Hfn; reflexivity.
Qed.

Definition run_exc_k {Pa : Params} {A : Type} (w : @CFGtop Pa A) : @CFGtop Pa (@exc Pa + A) :=
  ITree.bind (Ret (inl w))
    (fun lr => match lr with inl l => Tau (run_exc l) | inr r => Ret r end).

Lemma observe_run_exc_k {Pa : Params} {A : Type} (w : @CFGtop Pa A) :
  observe (run_exc_k w) = TauF (run_exc w).
Proof.
  unfold run_exc_k; rewrite observe_bind; reflexivity.
Qed.

Lemma observe_run_exc {Pa : Params} {A : Type} (u : @CFGtop Pa A) :
  observe (run_exc u) =
  match observe u with
  | RetF a => RetF (inr a)
  | TauF u' => TauF (run_exc u')
  | VisF _ e k =>
      match exc_of_event e with
      | Some x => RetF (inl x)
      | None => VisF e (fun y => run_exc_k (k y))
      end
  end.
Proof.
  unfold run_exc; rewrite observe_iter; cbn beta.
  destruct (observe u) as [a | u' | X e k];
    [rewrite observe_bind; reflexivity
    | rewrite observe_bind; reflexivity
    | destruct (exc_of_event e) as [x |]; rewrite observe_bind; reflexivity].
Qed.

Inductive cfg_locals_tau_step {Pa : Params} {A : Type}
  : @draw_strat Pa -> rmap (@dvalue Pa) -> @CFGtop Pa A ->
    @draw_strat Pa -> rmap (@dvalue Pa) -> @CFGtop Pa A -> Prop :=
| CLTS_One s env u u' :
    observe u = TauF u' ->
    cfg_locals_tau_step s env u s env u'
| CLTS_Write s env u id dv (k : unit -> @CFGtop Pa A) :
    observe u = VisF (inr1 (inr1 (inr1 (inr1 (inl1 (inl1 (LocalWrite id dv))))))) k ->
    cfg_locals_tau_step s env u s (RM.add id dv env) (k tt)
| CLTS_Read s env u id dv (k : @dvalue Pa -> @CFGtop Pa A) :
    observe u = VisF (inr1 (inr1 (inr1 (inr1 (inl1 (inl1 (LocalRead id))))))) k ->
    RM.find id env = Some dv ->
    cfg_locals_tau_step s env u s env (k dv)
| CLTS_Draw s env u dt (k : @dvalue Pa -> @CFGtop Pa A) :
    observe u = VisF (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 (Draw dt)))))))) k ->
    cfg_locals_tau_step s env u (shift_draw_strat s) env (k (s 0%nat dt)).

Lemma inv_cfg_locals_tau {Pa : Params} {A : Type} :
  forall (s : @draw_strat Pa) env (u : @CFGtop Pa A) m,
    observe (run_draws s (run_cfg_locals env u)) = TauF m ->
    exists s' env' u',
      cfg_locals_tau_step s env u s' env' u' /\
      m = run_draws s' (run_cfg_locals env' u').
Proof.
  intros s env u m Ho.
  rewrite observe_run_draws, observe_run_cfg_locals in Ho.
  destruct (observe u) as [a | u' | X e k] eqn:Hou.
  - discriminate Ho.
  - injection Ho as <-; exists s, env, u'; split; [exact (CLTS_One _ _ _ _ Hou) | reflexivity].
  - destruct e as [c | [ec | [ic | [ge | [[le | se] | [me | [de | rest]]]]]]];
      try (cbn in Ho; discriminate Ho).
    + destruct le as [id dv | id]; cbn in Ho.
      * injection Ho as <-; exists s, (RM.add id dv env), (k tt).
        split; [exact (CLTS_Write _ _ _ _ _ _ Hou) | reflexivity].
      * destruct (RM.find id env) as [dv |] eqn:Ef; [| discriminate Ho].
        injection Ho as <-; exists s, env, (k dv).
        split; [exact (CLTS_Read _ _ _ _ _ _ Hou Ef) | reflexivity].
    + destruct de as [dt]; cbn in Ho; injection Ho as <-.
      exists (shift_draw_strat s), env, (k (s 0%nat dt)).
      split; [exact (CLTS_Draw _ _ _ _ _ Hou) | reflexivity].
Qed.

Lemma cfg_locals_tau_step_fn_frames {Pa : Params} {A B : Type} :
  forall (s : @draw_strat Pa) env (u : @CFGtop Pa A) s' env' u'
         stk exc_slot (kf : @exc Pa + A -> @CFGtop Pa B),
    cfg_locals_tau_step s env u s' env' u' ->
    let src := run_draws s (run_fn_frames env stk exc_slot (ITree.bind (run_exc u) kf)) in
    let dst := run_draws s' (run_fn_frames env' stk exc_slot (ITree.bind (run_exc u') kf)) in
    observe src = TauF dst \/
    exists mid, observe src = TauF mid /\ observe mid = TauF dst.
Proof.
  intros s env u s' env' u' stk exc_slot kf Hst src dst.
  destruct Hst as
    [ s env u u' Hou
    | s env u id dv k Hou
    | s env u id dv k Hou Ef
    | s env u dt k Hou ].
  - left; unfold src, dst.
    rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - right; exists (run_draws s (run_fn_frames (RM.add id dv env) stk exc_slot (ITree.bind (run_exc_k (k tt)) kf))).
    split;
      [unfold src; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity
      | unfold dst; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc_k; reflexivity].
  - right; exists (run_draws s (run_fn_frames env stk exc_slot (ITree.bind (run_exc_k (k dv)) kf))).
    split;
      [unfold src; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; cbn; rewrite Ef; reflexivity
      | unfold dst; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc_k; reflexivity].
  - right; exists (run_draws (shift_draw_strat s) (run_fn_frames env stk exc_slot (ITree.bind (run_exc_k (k (s 0%nat dt))) kf))).
    split;
      [unfold src; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity
      | unfold dst; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc_k; reflexivity].
Qed.

Lemma step_tau_fn_frames_l {Pa : Params} {A B1 B2 : Type}
  (RR : B1 -> B2 -> Prop)
  (self : itree (@Det_OW_E Pa) B1 -> itree (@Det_OW_E Pa) B2 -> Prop) :
  forall (s : @draw_strat Pa) env (u : @CFGtop Pa A) s' env' u'
         stk exc_slot (kf1 : @exc Pa + A -> @CFGtop Pa B1) (t2 : itree (@Det_OW_E Pa) B2),
    cfg_locals_tau_step s env u s' env' u' ->
    det_ref_ RR self
      (run_draws s' (run_fn_frames env' stk exc_slot (ITree.bind (run_exc u') kf1))) t2 ->
    det_ref_ RR self
      (run_draws s (run_fn_frames env stk exc_slot (ITree.bind (run_exc u) kf1))) t2.
Proof.
  intros s env u s' env' u' stk exc_slot kf1 t2 Hst Hdr.
  destruct (cfg_locals_tau_step_fn_frames s env u s' env' u' stk exc_slot kf1 Hst)
    as [Ho | [mid [Ho1 Ho2]]].
  - eapply DR_TauL; [exact Ho | exact Hdr].
  - eapply DR_TauL; [exact Ho1 | eapply DR_TauL; [exact Ho2 | exact Hdr]].
Qed.

Lemma step_tau_fn_frames_r {Pa : Params} {A B1 B2 : Type}
  (RR : B1 -> B2 -> Prop)
  (self : itree (@Det_OW_E Pa) B1 -> itree (@Det_OW_E Pa) B2 -> Prop) :
  forall (s : @draw_strat Pa) env (u : @CFGtop Pa A) s' env' u'
         stk exc_slot (t1 : itree (@Det_OW_E Pa) B1) (kf2 : @exc Pa + A -> @CFGtop Pa B2),
    cfg_locals_tau_step s env u s' env' u' ->
    det_ref_ RR self
      t1 (run_draws s' (run_fn_frames env' stk exc_slot (ITree.bind (run_exc u') kf2))) ->
    det_ref_ RR self
      t1 (run_draws s (run_fn_frames env stk exc_slot (ITree.bind (run_exc u) kf2))).
Proof.
  intros s env u s' env' u' stk exc_slot t1 kf2 Hst Hdr.
  destruct (cfg_locals_tau_step_fn_frames s env u s' env' u' stk exc_slot kf2 Hst)
    as [Ho | [mid [Ho1 Ho2]]].
  - eapply DR_TauR; [exact Ho | exact Hdr].
  - eapply DR_TauR; [exact Ho1 | eapply DR_TauR; [exact Ho2 | exact Hdr]].
Qed.

Lemma step_tau_fn_frames_both {Pa : Params} {A B1 B2 : Type}
  (RR : B1 -> B2 -> Prop)
  (self : itree (@Det_OW_E Pa) B1 -> itree (@Det_OW_E Pa) B2 -> Prop) :
  forall (s1 : @draw_strat Pa) env1 (u1 : @CFGtop Pa A) s1' env1' u1'
         (s2 : @draw_strat Pa) env2 (u2 : @CFGtop Pa A) s2' env2' u2'
         stk exc_slot (kf1 : @exc Pa + A -> @CFGtop Pa B1) (kf2 : @exc Pa + A -> @CFGtop Pa B2),
    cfg_locals_tau_step s1 env1 u1 s1' env1' u1' ->
    cfg_locals_tau_step s2 env2 u2 s2' env2' u2' ->
    self (run_draws s1' (run_fn_frames env1' stk exc_slot (ITree.bind (run_exc u1') kf1)))
         (run_draws s2' (run_fn_frames env2' stk exc_slot (ITree.bind (run_exc u2') kf2))) ->
    det_ref_ RR self
      (run_draws s1 (run_fn_frames env1 stk exc_slot (ITree.bind (run_exc u1) kf1)))
      (run_draws s2 (run_fn_frames env2 stk exc_slot (ITree.bind (run_exc u2) kf2))).
Proof.
  intros s1 env1 u1 s1' env1' u1' s2 env2 u2 s2' env2' u2' stk exc_slot kf1 kf2 H1 H2 Hself.
  destruct (cfg_locals_tau_step_fn_frames s1 env1 u1 s1' env1' u1' stk exc_slot kf1 H1)
    as [Ho1 | [mid1 [Ho1a Ho1b]]];
  destruct (cfg_locals_tau_step_fn_frames s2 env2 u2 s2' env2' u2' stk exc_slot kf2 H2)
    as [Ho2 | [mid2 [Ho2a Ho2b]]].
  - apply DR_Step; unfold det_step_body; rewrite Ho1, Ho2; exact Hself.
  - eapply DR_TauR; [exact Ho2a | apply DR_Step; unfold det_step_body; rewrite Ho1, Ho2b; exact Hself].
  - eapply DR_TauL; [exact Ho1a | apply DR_Step; unfold det_step_body; rewrite Ho1b, Ho2; exact Hself].
  - eapply DR_TauL; [exact Ho1a | eapply DR_TauR; [exact Ho2a | apply DR_Step; unfold det_step_body; rewrite Ho1b, Ho2b; exact Hself]].
Qed.

Definition opt_llvmexc_det_event {Pa : Params} {X : Type} (e : @Det_OW_E Pa X) : option (@exc Pa) :=
  match e with
  | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 (LLVMExc x)))))))) => Some x
  | _ => None
  end.

Definition is_failure_det_event {Pa : Params} {X : Type} (e : @Det_OW_E Pa X) : bool :=
  match e with
  | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 _))))))))) => true
  | _ => false
  end.

Lemma det_vis_both_opt_llvmexc {Pa : Params} {R1 R2 X1 X2 : Type}
  (r : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop)
  (e1 : @Det_OW_E Pa X1) (k1 : X1 -> itree (@Det_OW_E Pa) R1)
  (e2 : @Det_OW_E Pa X2) (k2 : X2 -> itree (@Det_OW_E Pa) R2) :
  det_vis_both r e1 k1 e2 k2 ->
  opt_llvmexc_det_event e1 = opt_llvmexc_det_event e2.
Proof.
  unfold Det_OW_E in e1, e2.
  repeat match type of e1 with
         | (_ +' _) _ =>
             destruct e1 as [x1 | e1]; destruct e2 as [x2 | e2];
             try (cbn; intros; contradiction)
         end;
    try (intros _; reflexivity).
  destruct x1 as [ex1]; destruct x2 as [ex2]; cbn; intros [-> _]; reflexivity.
Qed.

Lemma det_vis_both_is_failure {Pa : Params} {R1 R2 X1 X2 : Type}
  (r : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop)
  (e1 : @Det_OW_E Pa X1) (k1 : X1 -> itree (@Det_OW_E Pa) R1)
  (e2 : @Det_OW_E Pa X2) (k2 : X2 -> itree (@Det_OW_E Pa) R2) :
  det_vis_both r e1 k1 e2 k2 ->
  is_failure_det_event e1 = is_failure_det_event e2.
Proof.
  unfold Det_OW_E in e1, e2.
  repeat match type of e1 with
         | (_ +' _) _ =>
             destruct e1 as [x1 | e1]; destruct e2 as [x2 | e2];
             try (cbn; intros; contradiction)
         end;
    intros _; reflexivity.
Qed.

Lemma failure_det_event_inv {Pa : Params} {X : Type} (e : @Det_OW_E Pa X) :
  is_failure_det_event e = true ->
  exists Hc : X = void,
    eq_rect X (@Det_OW_E Pa) e void Hc =
    @subevent FailureE (@Det_OW_E Pa) _ void (Throw tt).
Proof.
  unfold Det_OW_E in e.
  repeat match type of e with
         | (_ +' _) _ =>
             destruct e as [? | e]; [cbn; intros H; discriminate H |]
         end.
  intros _; destruct e as [[]]; exists eq_refl; reflexivity.
Qed.

Lemma det_vis_both_fmap {Pa : Params} {A1 A2 R1 R2 S1 S2 : Type}
  (r : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop)
  (s : itree (@Det_OW_E Pa) S1 -> itree (@Det_OW_E Pa) S2 -> Prop)
  (f1 : A1 -> itree (@Det_OW_E Pa) R1) (g1 : A1 -> itree (@Det_OW_E Pa) S1)
  (f2 : A2 -> itree (@Det_OW_E Pa) R2) (g2 : A2 -> itree (@Det_OW_E Pa) S2)
  (P1 : A1 -> Prop)
  (Hfg : forall a1 a2, P1 a1 -> r (f1 a1) (f2 a2) -> s (g1 a1) (g2 a2))
  {X1 X2 : Type}
  (e1 : @Det_OW_E Pa X1) (k1 : X1 -> itree (@Det_OW_E Pa) R1) (ku1 : X1 -> A1)
  (e2 : @Det_OW_E Pa X2) (k2 : X2 -> itree (@Det_OW_E Pa) R2) (ku2 : X2 -> A2)
  (Hk1 : forall x1, k1 x1 = f1 (ku1 x1))
  (Hk2 : forall x2, k2 x2 = f2 (ku2 x2))
  (HP1 : forall x1, P1 (ku1 x1)) :
  det_vis_both r e1 k1 e2 k2 ->
  det_vis_both s e1 (fun x1 => g1 (ku1 x1)) e2 (fun x2 => g2 (ku2 x2)).
Proof.
  unfold Det_OW_E in e1, e2.
  repeat match type of e1 with
         | (_ +' _) _ =>
             destruct e1 as [x1 | e1]; destruct e2 as [x2 | e2];
             try (cbn; intros; contradiction)
         end;
    cbn;
    try (destruct x1, x2; cbn; try (intros; contradiction);
         intros H; intuition (try apply Hfg; try apply HP1; rewrite <- ?Hk1, <- ?Hk2; auto));
    destruct e1, e2; cbn; intros H;
    intuition (try apply Hfg; try apply HP1; rewrite <- ?Hk1, <- ?Hk2; auto).
Qed.

Inductive cfg_locals_vis_case {Pa : Params} {A X : Type}
  (s : @draw_strat Pa) (env : rmap (@dvalue Pa)) (u : @CFGtop Pa A)
  (de : @Det_OW_E Pa X) (kd : X -> itree (@Det_OW_E Pa) A) : Prop :=
| CLVC_ReadFail :
    is_failure_det_event de = true ->
    det_is_ub de = false ->
    opt_llvmexc_det_event de = None ->
    (forall B stk exc_slot (kf : @exc Pa + A -> @CFGtop Pa B),
       exists k_void : void -> itree (@Det_OW_E Pa) B,
         observe (run_draws s (run_fn_frames env stk exc_slot (ITree.bind (run_exc u) kf))) =
         VisF (@subevent FailureE (@Det_OW_E Pa) _ void (Throw tt)) k_void) ->
    cfg_locals_vis_case s env u de kd
| CLVC_Stack :
    is_stack_det_event de = true ->
    det_is_ub de = false ->
    cfg_locals_vis_case s env u de kd
| CLVC_Exc (ex : @exc Pa) :
    opt_llvmexc_det_event de = Some ex ->
    det_is_ub de = false ->
    is_failure_det_event de = false ->
    observe (run_exc u) = RetF (inl ex) ->
    cfg_locals_vis_case s env u de kd
| CLVC_Other (ku : X -> @CFGtop Pa A) :
    opt_llvmexc_det_event de = None ->
    (forall x : X, kd x = run_draws s (run_cfg_locals env (ku x))) ->
    (forall B stk exc_slot (kf : @exc Pa + A -> @CFGtop Pa B),
       observe (run_draws s (run_fn_frames env stk exc_slot (ITree.bind (run_exc u) kf))) =
       VisF de (fun x => run_draws s (run_fn_frames env stk exc_slot (ITree.bind (run_exc_k (ku x)) kf)))) ->
    cfg_locals_vis_case s env u de kd.

Lemma inv_cfg_locals_vis {Pa : Params} {A X : Type} :
  forall (s : @draw_strat Pa) env (u : @CFGtop Pa A)
         (de : @Det_OW_E Pa X) (kd : X -> itree (@Det_OW_E Pa) A),
    observe (run_draws s (run_cfg_locals env u)) = VisF de kd ->
    cfg_locals_vis_case s env u de kd.
Proof.
  intros s env u de kd Ho.
  rewrite observe_run_draws, observe_run_cfg_locals in Ho.
  destruct (observe u) as [a | u' | Y e ku] eqn:Hou; try discriminate Ho.
  destruct e as [c | [ec | [ic | [ge | [[le | se] | [me | [de_dr | [oe | [xe | [ue | [dbe | fe]]]]]]]]]]].
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [<- [<- Hk]]; cbn in Hk.
    apply (CLVC_Other s env u _ kd ku eq_refl (fun x => eq_sym (Hk x))).
    intros B stk exc_slot kf; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [<- [<- Hk]]; cbn in Hk.
    apply (CLVC_Other s env u _ kd ku eq_refl (fun x => eq_sym (Hk x))).
    intros B stk exc_slot kf; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [<- [<- Hk]]; cbn in Hk.
    apply (CLVC_Other s env u _ kd ku eq_refl (fun x => eq_sym (Hk x))).
    intros B stk exc_slot kf; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [<- [<- Hk]]; cbn in Hk.
    apply (CLVC_Other s env u _ kd ku eq_refl (fun x => eq_sym (Hk x))).
    intros B stk exc_slot kf; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - destruct le as [id dv | id]; cbn in Ho; [discriminate Ho |].
    destruct (RM.find id env) as [dv |] eqn:Ef; [discriminate Ho |].
    destruct (visf_eq_inv _ _ _ _ Ho) as [<- [<- _]].
    apply CLVC_ReadFail; [reflexivity | reflexivity | reflexivity |].
    intros B stk exc_slot kf; exists void_elim.
    rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; cbn; rewrite Ef; reflexivity.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [<- [<- _]].
    apply CLVC_Stack; reflexivity.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [<- [<- Hk]]; cbn in Hk.
    apply (CLVC_Other s env u _ kd ku eq_refl (fun x => eq_sym (Hk x))).
    intros B stk exc_slot kf; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - destruct de_dr; cbn in Ho; discriminate Ho.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [<- [<- Hk]]; cbn in Hk.
    apply (CLVC_Other s env u _ kd ku eq_refl (fun x => eq_sym (Hk x))).
    intros B stk exc_slot kf; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - destruct xe as [ex]; cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [<- [<- _]].
    apply (CLVC_Exc s env u _ kd ex); [reflexivity | reflexivity | reflexivity |].
    rewrite observe_run_exc, Hou; reflexivity.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [<- [<- Hk]]; cbn in Hk.
    apply (CLVC_Other s env u _ kd ku eq_refl (fun x => eq_sym (Hk x))).
    intros B stk exc_slot kf; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [<- [<- Hk]]; cbn in Hk.
    apply (CLVC_Other s env u _ kd ku eq_refl (fun x => eq_sym (Hk x))).
    intros B stk exc_slot kf; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [<- [<- Hk]]; cbn in Hk.
    apply (CLVC_Other s env u _ kd ku eq_refl (fun x => eq_sym (Hk x))).
    intros B stk exc_slot kf; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
Qed.

Lemma inv_cfg_locals_ret {Pa : Params} {A : Type} :
  forall (s : @draw_strat Pa) env (u : @CFGtop Pa A) r,
    observe (run_draws s (run_cfg_locals env u)) = RetF r ->
    observe u = RetF r.
Proof.
  intros s env u r Ho.
  rewrite observe_run_draws, observe_run_cfg_locals in Ho.
  destruct (observe u) as [a | u' | Y e ku];
    [injection Ho as ->; reflexivity | discriminate Ho |].
  destruct e as [c | [ec | [ic | [ge | [[le | se] | [me | [de_dr | rest]]]]]]];
    try (cbn in Ho; discriminate Ho).
  - destruct le as [id dv | id]; cbn in Ho; [discriminate Ho | destruct (RM.find id env); discriminate Ho].
  - destruct de_dr; cbn in Ho; discriminate Ho.
Qed.

Definition sum_exc_dvalue_refines {Pa : Params}
  (r1 r2 : @exc Pa + @dvalue Pa) : Prop :=
  match r1, r2 with
  | inl e1, inl e2 => e1 = e2
  | inr v1, inr v2 => dvalue_refines v1 v2
  | _, _ => False
  end.

Lemma det_ref_cfg_to_fn_body {Pa : Params} {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop)
  (stk : list (rmap (@dvalue Pa)))
  (exc_slot : option (@dvalue Pa))
  (kf1 : @exc Pa + @dvalue Pa -> @CFGtop Pa R1)
  (kf2 : @exc Pa + @dvalue Pa -> @CFGtop Pa R2)
  (Hkf : forall s1 s2 env1 env2 rv1 rv2,
           sum_exc_dvalue_refines rv1 rv2 ->
           det_ref RR
             (run_draws s1 (run_fn_frames env1 stk exc_slot (kf1 rv1)))
             (run_draws s2 (run_fn_frames env2 stk exc_slot (kf2 rv2)))) :
  forall (s1 s2 : @draw_strat Pa) env1 env2 (u1 u2 : @CFGtop Pa (@dvalue Pa)),
    det_ref dvalue_refines
      (run_draws s1 (run_cfg_locals env1 u1))
      (run_draws s2 (run_cfg_locals env2 u2)) ->
    no_stack_det (run_draws s1 (run_cfg_locals env1 u1)) ->
    det_ref RR
      (run_draws s1 (run_fn_frames env1 stk exc_slot (ITree.bind (run_exc u1) kf1)))
      (run_draws s2 (run_fn_frames env2 stk exc_slot (ITree.bind (run_exc u2) kf2))).
Proof.
  intros s1 s2 env1 env2 u1 u2 Hdr Hns.
  revert s1 s2 env1 env2 u1 u2 Hdr Hns.
  pcofix CIH.
  intros s1 s2 env1 env2 u1 u2 Hdr Hns.
  punfold Hdr; pstep.
  assert (Hgen :
    forall t1 t2,
      det_ref_ dvalue_refines (upaco2 (det_ref_ dvalue_refines) bot2) t1 t2 ->
      forall s1 s2 env1 env2 (u1 u2 : @CFGtop Pa (@dvalue Pa)),
        t1 = run_draws s1 (run_cfg_locals env1 u1) ->
        t2 = run_draws s2 (run_cfg_locals env2 u2) ->
        no_stack_det (run_draws s1 (run_cfg_locals env1 u1)) ->
        det_ref_ RR (upaco2 (det_ref_ RR) r)
          (run_draws s1 (run_fn_frames env1 stk exc_slot (ITree.bind (run_exc u1) kf1)))
          (run_draws s2 (run_fn_frames env2 stk exc_slot (ITree.bind (run_exc u2) kf2)))).
  { intros t1 t2 Hstep.
    induction Hstep as [t1 t2 Hs | t1 m1 t2 Ho1 _ IH | t1 t2 m2 Ho2 _ IH];
      intros s1_ s2_ env1_ env2_ u1_ u2_ Et1 Et2 Hns1.
    - subst t1 t2; unfold det_step_body in Hs.
      destruct (observe (run_draws s1_ (run_cfg_locals env1_ u1_))) as [x1 | m1 | X1 de1 kd1] eqn:Ho1.
      + destruct (observe (run_draws s2_ (run_cfg_locals env2_ u2_))) as [x2 | | ] eqn:Ho2; try contradiction.
        pose proof (inv_cfg_locals_ret s1_ env1_ u1_ x1 Ho1) as Hou1.
        pose proof (inv_cfg_locals_ret s2_ env2_ u2_ x2 Ho2) as Hou2.
        pose proof (Hkf s1_ s2_ env1_ env2_ (inr x1) (inr x2) Hs) as Hk_ref.
        punfold Hk_ref.
        eapply det_ref__obs_eq with
          (t1 := run_draws s1_ (run_fn_frames env1_ stk exc_slot (kf1 (inr x1))))
          (t2 := run_draws s2_ (run_fn_frames env2_ stk exc_slot (kf2 (inr x2)))).
        * apply obs_eq_fn_frames_draws; rewrite observe_bind, observe_run_exc, Hou1; reflexivity.
        * apply obs_eq_fn_frames_draws; rewrite observe_bind, observe_run_exc, Hou2; reflexivity.
        * eapply det_ref__mon; [exact Hk_ref | intros a b [Hab | []]; left; eapply paco2_mon; [exact Hab | intros ? ? []]].
      + destruct (observe (run_draws s2_ (run_cfg_locals env2_ u2_))) as [| m2 | ] eqn:Ho2; try contradiction.
        destruct Hs as [Hs | []].
        destruct (inv_cfg_locals_tau s1_ env1_ u1_ m1 Ho1) as (s1' & env1' & u1' & Hst1 & ->).
        destruct (inv_cfg_locals_tau s2_ env2_ u2_ m2 Ho2) as (s2' & env2' & u2' & Hst2 & ->).
        pose proof (no_stack_det_inv_tau _ _ Ho1 Hns1) as Hns1'.
        eapply step_tau_fn_frames_both; [exact Hst1 | exact Hst2 | right].
        exact (CIH s1' s2' env1' env2' u1' u2' Hs Hns1').
      + destruct (no_stack_det_inv_vis _ _ _ Ho1 Hns1) as [Hns_de1 Hk_ns1].
        pose proof (inv_cfg_locals_vis s1_ env1_ u1_ de1 kd1 Ho1) as Hvc1.
        destruct Hs as [Hub1 | Hvb].
        * destruct Hvc1 as [_ Hub_f _ _ | _ Hub_f | ex1 _ Hub_f _ _ | ku1 _ _ Hofn1];
            try (rewrite Hub1 in Hub_f; discriminate Hub_f).
          apply DR_Step; unfold det_step_body; rewrite (Hofn1 R1 stk exc_slot kf1); left; exact Hub1.
        * destruct (observe (run_draws s2_ (run_cfg_locals env2_ u2_))) as [| | X2 de2 kd2] eqn:Ho2; try contradiction.
          pose proof (det_vis_both_is_stack _ de1 kd1 de2 kd2 Hvb) as Hst_eq.
          rewrite Hns_de1 in Hst_eq; symmetry in Hst_eq.
          pose proof (det_vis_both_opt_llvmexc _ de1 kd1 de2 kd2 Hvb) as Hexc_eq.
          pose proof (det_vis_both_is_failure _ de1 kd1 de2 kd2 Hvb) as Hfl_eq.
          pose proof (inv_cfg_locals_vis s2_ env2_ u2_ de2 kd2 Ho2) as Hvc2.
          destruct Hvc1 as [Hfl1 _ Hne1 Hof1 | Hst1 _ | ex1 Hex1 Hub1_f Hfl1_f Hou1_exc | ku1 Hne1 Hkd1 Hofn1].
          -- rewrite Hfl1 in Hfl_eq; symmetry in Hfl_eq.
             destruct (Hof1 R1 stk exc_slot kf1) as [kv1 Ho_fn1].
             destruct Hvc2 as [_ _ _ Hof2 | Hst2 _ | ex2 _ _ Hfl2_f _ | ku2 _ _ Hofn2].
             ++ destruct (Hof2 R2 stk exc_slot kf2) as [kv2 Ho_fn2].
                apply DR_Step; unfold det_step_body; rewrite Ho_fn1, Ho_fn2; right; apply det_vis_both_refl; intros [].
             ++ rewrite Hst2 in Hst_eq; discriminate Hst_eq.
             ++ rewrite Hfl2_f in Hfl_eq; discriminate Hfl_eq.
             ++ destruct (failure_det_event_inv de2 Hfl_eq) as [<- ->]; cbn in Hofn2.
                apply DR_Step; unfold det_step_body; rewrite Ho_fn1, (Hofn2 R2 stk exc_slot kf2).
                right; apply det_vis_both_refl; intros [].
          -- rewrite Hst1 in Hns_de1; discriminate Hns_de1.
          -- rewrite Hex1 in Hexc_eq; symmetry in Hexc_eq.
             destruct Hvc2 as [_ _ Hne2 _ | Hst2 _ | ex2 Hex2 _ _ Hou2_exc | ku2 Hne2 _ _];
               try (rewrite Hne2 in Hexc_eq; discriminate Hexc_eq);
               try (rewrite Hst2 in Hst_eq; discriminate Hst_eq).
             rewrite Hex2 in Hexc_eq; injection Hexc_eq as <-.
             pose proof (Hkf s1_ s2_ env1_ env2_ (inl ex1) (inl ex1) eq_refl) as Hk_ref.
             punfold Hk_ref.
             eapply det_ref__obs_eq with
               (t1 := run_draws s1_ (run_fn_frames env1_ stk exc_slot (kf1 (inl ex1))))
               (t2 := run_draws s2_ (run_fn_frames env2_ stk exc_slot (kf2 (inl ex1)))).
             ++ apply obs_eq_fn_frames_draws; rewrite observe_bind, Hou1_exc; reflexivity.
             ++ apply obs_eq_fn_frames_draws; rewrite observe_bind, Hou2_exc; reflexivity.
             ++ eapply det_ref__mon; [exact Hk_ref | intros a b [Hab | []]; left; eapply paco2_mon; [exact Hab | intros ? ? []]].
          -- rewrite Hne1 in Hexc_eq; symmetry in Hexc_eq.
             destruct Hvc2 as [Hfl2 _ _ Hof2 | Hst2 _ | ex2 Hex2 _ _ _ | ku2 _ Hkd2 Hofn2].
             ++ rewrite Hfl2 in Hfl_eq.
                destruct (Hof2 R2 stk exc_slot kf2) as [kv2 Ho_fn2].
                destruct (failure_det_event_inv de1 Hfl_eq) as [<- ->]; cbn in Hofn1.
                apply DR_Step; unfold det_step_body; rewrite (Hofn1 R1 stk exc_slot kf1), Ho_fn2.
                right; apply det_vis_both_refl; intros [].
             ++ rewrite Hst2 in Hst_eq; discriminate Hst_eq.
             ++ rewrite Hex2 in Hexc_eq; discriminate Hexc_eq.
             ++ apply DR_Step; unfold det_step_body.
                rewrite (Hofn1 R1 stk exc_slot kf1), (Hofn2 R2 stk exc_slot kf2).
                right.
                eapply (det_vis_both_fmap
                          (upaco2 (det_ref_ dvalue_refines) bot2)
                          (upaco2 (det_ref_ RR) r)
                          (fun a1 => run_draws s1_ (run_cfg_locals env1_ a1))
                          (fun a1 => run_draws s1_ (run_fn_frames env1_ stk exc_slot (ITree.bind (run_exc_k a1) kf1)))
                          (fun a2 => run_draws s2_ (run_cfg_locals env2_ a2))
                          (fun a2 => run_draws s2_ (run_fn_frames env2_ stk exc_slot (ITree.bind (run_exc_k a2) kf2)))
                          (fun a1 => no_stack_det (run_draws s1_ (run_cfg_locals env1_ a1)))).
                ** intros a1 a2 Hns_a1 [Hdr_a | []].
                   left; pstep; apply DR_Step; unfold det_step_body.
                   rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind, !observe_run_exc_k; cbn [observe].
                   right; exact (CIH s1_ s2_ env1_ env2_ a1 a2 Hdr_a Hns_a1).
                ** exact Hkd1.
                ** exact Hkd2.
                ** intros x1; rewrite <- (Hkd1 x1); exact (Hk_ns1 x1).
                ** exact Hvb.
    - subst t1.
      destruct (inv_cfg_locals_tau s1_ env1_ u1_ m1 Ho1) as (s1' & env1' & u1' & Hst1 & ->).
      pose proof (no_stack_det_inv_tau _ _ Ho1 Hns1) as Hns1'.
      eapply step_tau_fn_frames_l; [exact Hst1 | exact (IH s1' s2_ env1' env2_ u1' u2_ eq_refl Et2 Hns1')].
    - subst t2.
      destruct (inv_cfg_locals_tau s2_ env2_ u2_ m2 Ho2) as (s2' & env2' & u2' & Hst2 & ->).
      eapply step_tau_fn_frames_r; [exact Hst2 | exact (IH s1_ s2' env1_ env2' u1_ u2' Et1 eq_refl Hns1)]. }
  exact (Hgen _ _ Hdr s1 s2 env1 env2 u1 u2 eq_refl eq_refl Hns).
Qed.

Definition ret_deref_safe_b (s_ret t_ret : list param_attr) : bool :=
  match find_option attr_dereferenceable s_ret, find_option attr_dereferenceable t_ret with
  | None, None => true
  | Some (on1, n1), Some (on2, n2) =>
      Bool.eqb on1 on2 && int_syntax_val_eqb n1 n2 && existsb attr_is_noundef s_ret
  | _, _ => false
  end.

Definition proto_deref_safe_b (s_proto t_proto : declaration dtyp) : bool :=
  let '(s_ret, s_args) := dc_param_attrs s_proto in
  let '(t_ret, t_args) := dc_param_attrs t_proto in
  ret_deref_safe_b s_ret t_ret &&
  forallb2 (fun sa ta =>
    opt_deref_same_b (find_option attr_dereferenceable sa)
                     (find_option attr_dereferenceable ta)) s_args t_args.

Lemma fn_frames_raiseUB_bind {Pa : Params} {X R1 R2 : Type}
  (RR : R1 -> R2 -> Prop) :
  forall (s1 : @draw_strat Pa) env1 stk1 exc1 msg (k1 : X -> @CFGtop Pa R1)
         (t2 : itree (@Det_OW_E Pa) R2),
    det_ref RR
      (run_draws s1 (run_fn_frames env1 stk1 exc1 (ITree.bind (raiseUB msg) k1)))
      t2.
Proof.
  intros s1 env1 stk1 exc1 msg k1 t2.
  pstep; apply DR_Step; unfold det_step_body.
  rewrite observe_run_draws, observe_run_fn_frames, observe_bind; cbn; left; reflexivity.
Qed.

Lemma fn_frames_trigger_mem_step {Pa : Params} {R1 R2 Y : Type}
  (RR : R1 -> R2 -> Prop)
  (me : @MemoryE Pa Y)
  (s1 s2 : @draw_strat Pa)
  env1 stk1 exc1 (t1 : @CFGtop Pa R1) (k1' k1 : Y -> @CFGtop Pa R1)
  env2 stk2 exc2 (t2 : @CFGtop Pa R2) (k2' k2 : Y -> @CFGtop Pa R2) :
  observe t1 = VisF (@subevent (@MemoryE Pa) (@CFGEtop Pa) _ Y me) k1' ->
  observe t2 = VisF (@subevent (@MemoryE Pa) (@CFGEtop Pa) _ Y me) k2' ->
  (forall y : Y, observe (k1' y) = observe (k1 y)) ->
  (forall y : Y, observe (k2' y) = observe (k2 y)) ->
  (forall y : Y,
     det_ref RR
       (run_draws s1 (run_fn_frames env1 stk1 exc1 (k1 y)))
       (run_draws s2 (run_fn_frames env2 stk2 exc2 (k2 y)))) ->
  det_ref RR
    (run_draws s1 (run_fn_frames env1 stk1 exc1 t1))
    (run_draws s2 (run_fn_frames env2 stk2 exc2 t2)).
Proof.
  intros Ho1 Ho2 Hk1 Hk2 Hk.
  pstep; apply DR_Step; unfold det_step_body.
  rewrite !observe_run_draws, !observe_run_fn_frames, Ho1, Ho2; cbn.
  right; apply det_vis_both_refl; intros y; left.
  eapply det_ref_obs_eq with
    (t1 := run_draws s1 (run_fn_frames env1 stk1 exc1 (k1 y)))
    (t2 := run_draws s2 (run_fn_frames env2 stk2 exc2 (k2 y))).
  - exact (obs_eq_fn_frames_draws s1 env1 stk1 exc1 (k1 y) (k1' y) (eq_sym (Hk1 y))).
  - exact (obs_eq_fn_frames_draws s2 env2 stk2 exc2 (k2 y) (k2' y) (eq_sym (Hk2 y))).
  - exact (Hk y).
Qed.

Lemma step_assert_deref_eq {Pa : Params} {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop) :
  forall s_attrs t_attrs (v : @dvalue Pa) msg_s msg_t
         (s1 s2 : @draw_strat Pa) env1 stk1 exc1 env2 stk2 exc2
         (k1 : unit -> @CFGtop Pa R1) (k2 : unit -> @CFGtop Pa R2),
    opt_deref_same_b (find_option attr_dereferenceable s_attrs)
                     (find_option attr_dereferenceable t_attrs) = true ->
    det_ref RR
      (run_draws s1 (run_fn_frames env1 stk1 exc1 (k1 tt)))
      (run_draws s2 (run_fn_frames env2 stk2 exc2 (k2 tt))) ->
    det_ref RR
      (run_draws s1 (run_fn_frames env1 stk1 exc1
         (ITree.bind (assert_attrs_dereferenceable s_attrs v msg_s) k1)))
      (run_draws s2 (run_fn_frames env2 stk2 exc2
         (ITree.bind (assert_attrs_dereferenceable t_attrs v msg_t) k2))).
Proof.
  intros s_attrs t_attrs v msg_s msg_t s1 s2 env1 stk1 exc1 env2 stk2 exc2 k1 k2 Hsame Hk.
  unfold assert_attrs_dereferenceable.
  destruct (find_option attr_dereferenceable s_attrs) as [[on1 n1] |];
    destruct (find_option attr_dereferenceable t_attrs) as [[on2 n2] |];
    cbn [opt_deref_same_b] in Hsame; try discriminate Hsame.
  - apply andb_true_iff in Hsame as [Hon Hn].
    apply Bool.eqb_prop in Hon; subst on2.
    pose proof (int_syntax_val_eqb_denote n1 n2 Hn) as Hden; rewrite <- Hden.
    destruct v as [[p | | | | | | | ] | | ];
      try (eapply det_ref_obs_eq;
             [apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
             | apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
             | exact Hk]).
    unfold assert_dereferenceable.
    destruct ((on1 && (ptr_to_int p =? ptr_to_int null)%Z) || (Z.to_N (denote_int_syntax n1) =? 0)%N).
    + eapply det_ref_obs_eq;
        [apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
        | apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
        | exact Hk].
    + eapply fn_frames_trigger_mem_step with
        (me := Load (DTYPE_Array false (Z.to_N (denote_int_syntax n1)) (DTYPE_B 8)) (DVALUE_Base (DVALUE_Pointer p)))
        (k1 := fun _ => k1 tt) (k2 := fun _ => k2 tt);
        [unfold load, trigger; rewrite !observe_bind; reflexivity
        | unfold load, trigger; rewrite !observe_bind; reflexivity
        | intros _; rewrite !observe_bind; reflexivity
        | intros _; rewrite !observe_bind; reflexivity
        | intros _; exact Hk].
  - eapply det_ref_obs_eq;
      [apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
      | apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
      | exact Hk].
Qed.

Lemma fn_frames_bind_assoc_both {Pa : Params} {A1 B1 R1 A2 B2 R2 : Type}
  (RR : R1 -> R2 -> Prop) :
  forall (s1 s2 : @draw_strat Pa) env1 stk1 exc1 env2 stk2 exc2
         (m1 : @CFGtop Pa A1) (f1 : A1 -> @CFGtop Pa B1) (g1 : B1 -> @CFGtop Pa R1)
         (m2 : @CFGtop Pa A2) (f2 : A2 -> @CFGtop Pa B2) (g2 : B2 -> @CFGtop Pa R2),
    det_ref RR
      (run_draws s1 (run_fn_frames env1 stk1 exc1 (ITree.bind m1 (fun x => ITree.bind (f1 x) g1))))
      (run_draws s2 (run_fn_frames env2 stk2 exc2 (ITree.bind m2 (fun x => ITree.bind (f2 x) g2)))) ->
    det_ref RR
      (run_draws s1 (run_fn_frames env1 stk1 exc1 (ITree.bind (ITree.bind m1 f1) g1)))
      (run_draws s2 (run_fn_frames env2 stk2 exc2 (ITree.bind (ITree.bind m2 f2) g2))).
Proof.
  intros s1 s2 env1 stk1 exc1 env2 stk2 exc2 m1 f1 g1 m2 f2 g2 H.
  eapply det_ref_trans with (R12 := @eq R1) (R23 := RR);
    [intros ? ? ? -> Hr; exact Hr | exact (run_fn_frames_bind_assoc_lr s1 env1 stk1 exc1 m1 f1 g1) |].
  eapply det_ref_trans with (R12 := RR) (R23 := @eq R2);
    [intros ? ? ? Hr <-; exact Hr | exact H | exact (run_fn_frames_bind_assoc_rl s2 env2 stk2 exc2 m2 f2 g2)].
Qed.

Lemma step_apply_attrs_eq {Pa : Params} {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop) :
  forall s_attrs t_attrs (v : @dvalue Pa) msg_s msg_t
         (s1 s2 : @draw_strat Pa) env1 stk1 exc1 env2 stk2 exc2
         (k1 : @dvalue Pa -> @CFGtop Pa R1) (k2 : @dvalue Pa -> @CFGtop Pa R2),
    value_attrs_poison_match_b s_attrs t_attrs = true ->
    opt_deref_same_b (find_option attr_dereferenceable s_attrs)
                     (find_option attr_dereferenceable t_attrs) = true ->
    ((existsb attr_is_noundef s_attrs && negb (dvalue_well_defined (value_attrs_poison s_attrs v)) = false) ->
     det_ref RR
       (run_draws s1 (run_fn_frames env1 stk1 exc1 (k1 (value_attrs_poison s_attrs v))))
       (run_draws s2 (run_fn_frames env2 stk2 exc2 (k2 (value_attrs_poison s_attrs v))))) ->
    det_ref RR
      (run_draws s1 (run_fn_frames env1 stk1 exc1 (ITree.bind (apply_attrs s_attrs msg_s v) k1)))
      (run_draws s2 (run_fn_frames env2 stk2 exc2 (ITree.bind (apply_attrs t_attrs msg_t v) k2))).
Proof.
  intros s_attrs t_attrs v msg_s msg_t s1 s2 env1 stk1 exc1 env2 stk2 exc2 k1 k2 Hcon Hsame Hk.
  pose proof (value_attrs_poison_eq_of_match s_attrs t_attrs v Hcon) as Heqv.
  unfold value_attrs_poison_match_b in Hcon; rewrite !andb_true_iff in Hcon.
  destruct Hcon as (((((Hnu_imp & _) & _) & _) & _) & _).
  set (v' := value_attrs_poison s_attrs v) in *.
  unfold apply_attrs, apply_value_attrs; fold v'; rewrite <- Heqv.
  destruct (existsb attr_is_noundef s_attrs && negb (dvalue_well_defined v')) eqn:Eub_s.
  - eapply det_ref_obs_eq with
      (t1 := run_draws s1 (run_fn_frames env1 stk1 exc1
               (ITree.bind (raiseUB msg_s) (fun x => ITree.bind (assert_attrs_dereferenceable s_attrs x msg_s ;; ret x) k1))))
      (t2 := run_draws s2 (run_fn_frames env2 stk2 exc2 (ITree.bind (apply_attrs t_attrs msg_t v) k2))).
    + apply obs_eq_fn_frames_draws; symmetry; rewrite !observe_bind; reflexivity.
    + unfold apply_attrs, apply_value_attrs; fold v'; rewrite <- Heqv; reflexivity.
    + apply fn_frames_raiseUB_bind.
  - assert (Eub_t : existsb attr_is_noundef t_attrs && negb (dvalue_well_defined v') = false).
    { destruct (existsb attr_is_noundef t_attrs) eqn:Et; [| reflexivity].
      cbn in Hnu_imp; rewrite Hnu_imp in Eub_s; exact Eub_s. }
    rewrite Eub_t.
    eapply det_ref_obs_eq with
      (t1 := run_draws s1 (run_fn_frames env1 stk1 exc1
               (ITree.bind (assert_attrs_dereferenceable s_attrs v' msg_s) (fun _ => ITree.bind (ret v') k1))))
      (t2 := run_draws s2 (run_fn_frames env2 stk2 exc2
               (ITree.bind (assert_attrs_dereferenceable t_attrs v' msg_t) (fun _ => ITree.bind (ret v') k2)))).
    + apply obs_eq_fn_frames_draws; rewrite !observe_bind; reflexivity.
    + apply obs_eq_fn_frames_draws; rewrite !observe_bind; reflexivity.
    + eapply step_assert_deref_eq; [exact Hsame |].
      eapply det_ref_obs_eq;
        [apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
        | apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
        | exact (Hk eq_refl)].
Qed.

Fixpoint eval_args_attrs_poison {Pa : Params}
  (attrss : list (list param_attr)) (vs : list (@dvalue Pa))
  {struct vs} : list (@dvalue Pa) :=
  match vs with
  | [] => []
  | v :: vr =>
      let '(attrs, rest) := match attrss with [] => ([], []) | a :: r => (a, r) end in
      value_attrs_poison attrs v :: eval_args_attrs_poison rest vr
  end.

Fixpoint args_attrs_src_ub {Pa : Params}
  (attrss : list (list param_attr)) (vs : list (@dvalue Pa))
  {struct vs} : bool :=
  match vs with
  | [] => false
  | v :: vr =>
      let '(attrs, rest) := match attrss with [] => ([], []) | a :: r => (a, r) end in
      let v' := value_attrs_poison attrs v in
      (existsb attr_is_noundef attrs && negb (dvalue_well_defined v')) ||
      args_attrs_src_ub rest vr
  end.

Lemma eval_args_attrs_poison_wf {Pa : Params} :
  forall arg_dtys s_pattrs (vs : list (@dvalue Pa)),
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    forallb2 attr_preserves_dtyp_b arg_dtys s_pattrs = true ->
    args_attrs_src_ub s_pattrs vs = false ->
    List.length (eval_args_attrs_poison s_pattrs vs) = List.length vs /\
    Forall2 dvalue_has_dtyp (eval_args_attrs_poison s_pattrs vs) arg_dtys /\
    Forall2 (fun attrs v' => existsb attr_is_noundef attrs = true -> dvalue_well_defined v' = true)
            s_pattrs (eval_args_attrs_poison s_pattrs vs).
Proof.
  intros arg_dtys s_pattrs vs Hty.
  revert s_pattrs; induction Hty as [| v dt vr dr Hty1 Htyr IH];
    intros [| a ra] Hpres Hno_ub; cbn [forallb2] in Hpres; try discriminate Hpres.
  - repeat split; constructor.
  - cbn [eval_args_attrs_poison args_attrs_src_ub] in Hno_ub |- *.
    apply andb_true_iff in Hpres as [Hp1 Hpr].
    apply orb_false_iff in Hno_ub as [Hub1 Hubr].
    destruct (IH ra Hpr Hubr) as (Hlen & Hty_r & Hnu_r).
    split; [cbn; f_equal; exact Hlen | split].
    + constructor; [exact (value_attrs_poison_preserves_dtyp dt a v Hp1 Hty1) | exact Hty_r].
    + constructor; [| exact Hnu_r].
      intros Hnu; rewrite Hnu in Hub1; cbn in Hub1; exact (proj1 (negb_false_iff _) Hub1).
Qed.

Lemma param_attrs_refine_poison_match :
  forall sa ta, param_attrs_refine_b sa ta = true -> value_attrs_poison_match_b sa ta = true.
Proof.
  intros sa ta H; unfold param_attrs_refine_b in H; rewrite !andb_true_iff in H.
  destruct H as (_ & Hm); exact Hm.
Qed.

Lemma step_apply_args_attrs {Pa : Params} {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop) :
  forall s_pattrs t_pattrs (vs : list (@dvalue Pa)) msg_s msg_t
         (s1 s2 : @draw_strat Pa) env1 stk1 exc1 env2 stk2 exc2
         (k1 : list (@dvalue Pa) -> @CFGtop Pa R1)
         (k2 : list (@dvalue Pa) -> @CFGtop Pa R2),
    List.length s_pattrs = List.length vs ->
    forallb2 param_attrs_refine_b s_pattrs t_pattrs = true ->
    forallb2 (fun sa ta =>
      opt_deref_same_b (find_option attr_dereferenceable sa)
                       (find_option attr_dereferenceable ta)) s_pattrs t_pattrs = true ->
    (args_attrs_src_ub s_pattrs vs = false ->
     det_ref RR
       (run_draws s1 (run_fn_frames env1 stk1 exc1 (k1 (eval_args_attrs_poison s_pattrs vs))))
       (run_draws s2 (run_fn_frames env2 stk2 exc2 (k2 (eval_args_attrs_poison s_pattrs vs))))) ->
    det_ref RR
      (run_draws s1 (run_fn_frames env1 stk1 exc1 (ITree.bind (apply_args_attrs s_pattrs msg_s vs) k1)))
      (run_draws s2 (run_fn_frames env2 stk2 exc2 (ITree.bind (apply_args_attrs t_pattrs msg_t vs) k2))).
Proof.
  induction s_pattrs as [| sa rsa IH];
    intros [| ta rta] [| v rvs] msg_s msg_t s1 s2 env1 stk1 exc1 env2 stk2 exc2 k1 k2
           Hlen Hcon Hsame Hk;
    try discriminate Hlen; try discriminate Hcon.
  - eapply det_ref_obs_eq;
      [apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
      | apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
      | exact (Hk eq_refl)].
  - injection Hlen as Hlen'.
    cbn [forallb2] in Hcon, Hsame.
    apply andb_true_iff in Hcon as [Hc1 Hcr].
    apply andb_true_iff in Hsame as [Hs1 Hsr].
    cbn [apply_args_attrs eval_args_attrs_poison args_attrs_src_ub] in *.
    apply fn_frames_bind_assoc_both.
    eapply step_apply_attrs_eq; [exact (param_attrs_refine_poison_match sa ta Hc1) | exact Hs1 |].
    intros Eub1.
    apply fn_frames_bind_assoc_both.
    eapply IH; [exact Hlen' | exact Hcr | exact Hsr |].
    intros Eubr.
    eapply det_ref_obs_eq;
      [apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
      | apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
      | rewrite Eub1 in Hk; cbn [orb] in Hk; exact (Hk Eubr)].
Qed.

Lemma step_push_call_frame {Pa : Params} {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop) :
  forall (src_df tgt_df : definition dtyp (CFG.cfg dtyp))
         (vs' : list (@dvalue Pa))
         (s1 s2 : @draw_strat Pa) cenv cstk exc_slot
         (k1 : @ptr Pa -> @CFGtop Pa R1)
         (k2 : @ptr Pa -> @CFGtop Pa R2),
    List.length (df_args src_df) = List.length vs' ->
    List.length (df_args tgt_df) = List.length vs' ->
    (forall varg : @ptr Pa,
       det_ref RR
         (run_draws s1 (run_fn_frames (init_cfg_locals (df_args src_df) vs') (cenv :: cstk) exc_slot (k1 varg)))
         (run_draws s2 (run_fn_frames (init_cfg_locals (df_args tgt_df) vs') (cenv :: cstk) exc_slot (k2 varg)))) ->
    det_ref RR
      (run_draws s1 (run_fn_frames cenv cstk exc_slot (ITree.bind (push_call_frame src_df vs') k1)))
      (run_draws s2 (run_fn_frames cenv cstk exc_slot (ITree.bind (push_call_frame tgt_df vs') k2))).
Proof.
  intros src_df tgt_df vs' s1 s2 cenv cstk exc_slot k1 k2 Hlens Hlent Hk.
  unfold push_call_frame.
  rewrite (combine_lists_varargs_exact (df_args src_df) vs' Hlens).
  rewrite (combine_lists_varargs_exact (df_args tgt_df) vs' Hlent).
  set (bs_s := List.combine (df_args src_df) vs').
  set (bs_t := List.combine (df_args tgt_df) vs').
  set (dt0 := DTYPE_Struct true (@nil dtyp)).
  eapply det_ref_obs_eq with
    (t1 := run_draws s1 (run_fn_frames cenv cstk exc_slot
             (ITree.bind (mem_push ;; stack_push bs_s ;; varargs <- alloca dt0 1 None ;;
                          store dt0 varargs (DVALUE_Struct true []) ;;
                          match varargs with
                          | DVALUE_Base (DVALUE_Pointer varg) => ret varg
                          | _ => raise "Non-address returned from alloca of varargs"
                          end) k1)))
    (t2 := run_draws s2 (run_fn_frames cenv cstk exc_slot
             (ITree.bind (mem_push ;; stack_push bs_t ;; varargs <- alloca dt0 1 None ;;
                          store dt0 varargs (DVALUE_Struct true []) ;;
                          match varargs with
                          | DVALUE_Base (DVALUE_Pointer varg) => ret varg
                          | _ => raise "Non-address returned from alloca of varargs"
                          end) k2))).
  - apply obs_eq_fn_frames_draws; symmetry; rewrite !observe_bind; reflexivity.
  - apply obs_eq_fn_frames_draws; symmetry; rewrite !observe_bind; reflexivity.
  - apply fn_frames_bind_assoc_both.
    eapply fn_frames_trigger_mem_step with (me := MemPush)
      (k1 := fun _ => ITree.bind (stack_push bs_s ;; varargs <- alloca dt0 1 None ;;
                        store dt0 varargs (DVALUE_Struct true []) ;;
                        match varargs with
                        | DVALUE_Base (DVALUE_Pointer varg) => ret varg
                        | _ => raise "Non-address returned from alloca of varargs"
                        end) k1)
      (k2 := fun _ => ITree.bind (stack_push bs_t ;; varargs <- alloca dt0 1 None ;;
                        store dt0 varargs (DVALUE_Struct true []) ;;
                        match varargs with
                        | DVALUE_Base (DVALUE_Pointer varg) => ret varg
                        | _ => raise "Non-address returned from alloca of varargs"
                        end) k2);
      [unfold mem_push, trigger; rewrite !observe_bind; reflexivity
      | unfold mem_push, trigger; rewrite !observe_bind; reflexivity
      | intros _; rewrite !observe_bind; reflexivity
      | intros _; rewrite !observe_bind; reflexivity
      | intros _].
    apply fn_frames_bind_assoc_both.
    pstep; apply DR_Step; unfold det_step_body.
    unfold stack_push, trigger; rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind; cbn.
    left.
    eapply det_ref_obs_eq with
      (t1 := run_draws s1 (run_fn_frames (init_cfg_locals (df_args src_df) vs') (cenv :: cstk) exc_slot
               (ITree.bind (varargs <- alloca dt0 1 None ;;
                            store dt0 varargs (DVALUE_Struct true []) ;;
                            match varargs with
                            | DVALUE_Base (DVALUE_Pointer varg) => ret varg
                            | _ => raise "Non-address returned from alloca of varargs"
                            end) k1)))
      (t2 := run_draws s2 (run_fn_frames (init_cfg_locals (df_args tgt_df) vs') (cenv :: cstk) exc_slot
               (ITree.bind (varargs <- alloca dt0 1 None ;;
                            store dt0 varargs (DVALUE_Struct true []) ;;
                            match varargs with
                            | DVALUE_Base (DVALUE_Pointer varg) => ret varg
                            | _ => raise "Non-address returned from alloca of varargs"
                            end) k2))).
    + unfold bs_s; rewrite (push_frame_bindings_eq_init (df_args src_df) vs' Hlens).
      apply obs_eq_fn_frames_draws; symmetry; rewrite !observe_bind; reflexivity.
    + unfold bs_t; rewrite (push_frame_bindings_eq_init (df_args tgt_df) vs' Hlent).
      apply obs_eq_fn_frames_draws; symmetry; rewrite !observe_bind; reflexivity.
    + apply fn_frames_bind_assoc_both.
      eapply fn_frames_trigger_mem_step with (me := Alloca dt0 1 None)
        (k1 := fun va => ITree.bind (store dt0 va (DVALUE_Struct true []) ;;
                           match va with
                           | DVALUE_Base (DVALUE_Pointer varg) => ret varg
                           | _ => raise "Non-address returned from alloca of varargs"
                           end) k1)
        (k2 := fun va => ITree.bind (store dt0 va (DVALUE_Struct true []) ;;
                           match va with
                           | DVALUE_Base (DVALUE_Pointer varg) => ret varg
                           | _ => raise "Non-address returned from alloca of varargs"
                           end) k2);
        [unfold alloca, trigger; rewrite !observe_bind; reflexivity
        | unfold alloca, trigger; rewrite !observe_bind; reflexivity
        | intros va; rewrite !observe_bind; reflexivity
        | intros va; rewrite !observe_bind; reflexivity
        | intros va].
      apply fn_frames_bind_assoc_both.
      eapply fn_frames_trigger_mem_step with (me := Store dt0 va (DVALUE_Struct true []))
        (k1 := fun _ => ITree.bind (match va with
                          | DVALUE_Base (DVALUE_Pointer varg) => ret varg
                          | _ => raise "Non-address returned from alloca of varargs"
                          end) k1)
        (k2 := fun _ => ITree.bind (match va with
                          | DVALUE_Base (DVALUE_Pointer varg) => ret varg
                          | _ => raise "Non-address returned from alloca of varargs"
                          end) k2);
        [unfold store, trigger; rewrite !observe_bind; reflexivity
        | unfold store, trigger; rewrite !observe_bind; reflexivity
        | intros _; rewrite !observe_bind; reflexivity
        | intros _; rewrite !observe_bind; reflexivity
        | intros _].
      destruct va as [[varg | | | | | | | ] | | ];
        try (pstep; apply DR_Step; unfold det_step_body;
             rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind; cbn;
             right; apply det_vis_both_refl; intros []).
      eapply det_ref_obs_eq;
        [apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
        | apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
        | exact (Hk varg)].
Qed.

Lemma step_pop_call_frame {Pa : Params} {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop) :
  forall (s1 s2 : @draw_strat Pa) env1 env2 cenv cstk exc_slot
         (k1 : unit -> @CFGtop Pa R1) (k2 : unit -> @CFGtop Pa R2),
    det_ref RR
      (run_draws s1 (run_fn_frames cenv cstk exc_slot (k1 tt)))
      (run_draws s2 (run_fn_frames cenv cstk exc_slot (k2 tt))) ->
    det_ref RR
      (run_draws s1 (run_fn_frames env1 (cenv :: cstk) exc_slot (ITree.bind pop_call_frame k1)))
      (run_draws s2 (run_fn_frames env2 (cenv :: cstk) exc_slot (ITree.bind pop_call_frame k2))).
Proof.
  intros s1 s2 env1 env2 cenv cstk exc_slot k1 k2 Hk.
  unfold pop_call_frame.
  apply fn_frames_bind_assoc_both.
  pstep; apply DR_Step; unfold det_step_body.
  unfold stack_pop, trigger; rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind; cbn.
  left.
  eapply det_ref_obs_eq with
    (t1 := run_draws s1 (run_fn_frames cenv cstk exc_slot (ITree.bind mem_pop k1)))
    (t2 := run_draws s2 (run_fn_frames cenv cstk exc_slot (ITree.bind mem_pop k2))).
  - apply obs_eq_fn_frames_draws; symmetry; rewrite !observe_bind; reflexivity.
  - apply obs_eq_fn_frames_draws; symmetry; rewrite !observe_bind; reflexivity.
  - eapply fn_frames_trigger_mem_step with (me := MemPop) (k1 := k1) (k2 := k2);
      [unfold mem_pop, trigger; rewrite !observe_bind; reflexivity
      | unfold mem_pop, trigger; rewrite !observe_bind; reflexivity
      | intros []; rewrite !observe_bind; reflexivity
      | intros []; rewrite !observe_bind; reflexivity
      | intros []; exact Hk].
Qed.

Lemma step_check_call_return {Pa : Params} :
  forall fattrs_s fattrs_t s_ret t_ret fname_s fname_t
         (vs' : list (@dvalue Pa)) (rv1 rv2 : @exc Pa + @dvalue Pa)
         (s1 s2 : @draw_strat Pa) cenv cstk exc_slot,
    check_fn_attrs_contract fattrs_s fattrs_t = true ->
    ret_attrs_refine_b s_ret t_ret = true ->
    opt_deref_same_b (find_option attr_dereferenceable s_ret)
                     (find_option attr_dereferenceable t_ret) = true ->
    sum_exc_dvalue_refines rv1 rv2 ->
    det_ref sum_exc_dvalue_refines
      (run_draws s1 (run_fn_frames cenv cstk exc_slot
         (check_call_return fattrs_s s_ret None fname_s vs' rv1)))
      (run_draws s2 (run_fn_frames cenv cstk exc_slot
         (check_call_return fattrs_t t_ret None fname_t vs' rv2))).
Proof.
  intros fattrs_s fattrs_t s_ret t_ret fname_s fname_t vs' rv1 rv2
         s1 s2 cenv cstk exc_slot Hfattrs Hret_ref Hderef Hrv.
  destruct (check_fn_attrs_contract_inv fattrs_s fattrs_t Hfattrs)
    as (_ & _ & _ & Hnr_imp & Hnuw_imp & Hnc_imp).
  unfold ret_attrs_refine_b in Hret_ref; apply andb_true_iff in Hret_ref as [Hpar_ret Htd_imp].
  pose proof (param_attrs_refine_poison_match s_ret t_ret Hpar_ret) as Hpm_ret.
  pose proof Hpm_ret as Hpm_copy.
  unfold value_attrs_poison_match_b in Hpm_copy; rewrite !andb_true_iff in Hpm_copy.
  destruct Hpm_copy as (((((Hnu_ret_imp & _) & _) & _) & _) & _).
  destruct rv1 as [ex1 | dv1], rv2 as [ex2 | dv2];
    cbn [sum_exc_dvalue_refines] in Hrv; try contradiction Hrv.
  - subst ex2; unfold check_call_return, check_call_result.
    destruct (existsb fn_attr_is_nounwind fattrs_s) eqn:Enuw_s.
    + apply fn_frames_raiseUB_bind.
    + assert (Enuw_t : existsb fn_attr_is_nounwind fattrs_t = false).
      { destruct (existsb fn_attr_is_nounwind fattrs_t) eqn:Et; [| reflexivity].
        rewrite (Hnuw_imp Et) in Enuw_s; discriminate Enuw_s. }
      rewrite Enuw_t.
      pstep; apply DR_Step; unfold det_step_body.
      rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind; cbn; reflexivity.
  - unfold check_call_return, check_call_result.
    destruct (existsb fn_attr_is_noreturn fattrs_s) eqn:Enr_s.
    + apply fn_frames_raiseUB_bind.
    + assert (Enr_t : existsb fn_attr_is_noreturn fattrs_t = false).
      { destruct (existsb fn_attr_is_noreturn fattrs_t) eqn:Et; [| reflexivity].
        rewrite (Hnr_imp Et) in Enr_s; discriminate Enr_s. }
      rewrite Enr_t.
      destruct (existsb fn_attr_is_nocreateundeforpoison fattrs_s &&
                forallb dvalue_well_defined vs' &&
                negb (dvalue_well_defined dv1)) eqn:Enc_s.
      * apply fn_frames_raiseUB_bind.
      * assert (Enc_t :
                  existsb fn_attr_is_nocreateundeforpoison fattrs_t &&
                  forallb dvalue_well_defined vs' &&
                  negb (dvalue_well_defined dv2) = false).
        { destruct (existsb fn_attr_is_nocreateundeforpoison fattrs_t) eqn:Eft; [| reflexivity].
          rewrite (Hnc_imp Eft) in Enc_s.
          destruct (forallb dvalue_well_defined vs'); cbn in Enc_s |- *; [| reflexivity].
          destruct (dvalue_well_defined dv1) eqn:Ewd1; [| discriminate Enc_s].
          destruct (dvalue_refines_well_defined dv1 dv2 Hrv Ewd1) as [_ ->]; reflexivity. }
        rewrite Enc_t.
        eapply det_ref_obs_eq with
          (t1 := run_draws s1 (run_fn_frames cenv cstk exc_slot
                   (ITree.bind (apply_attrs s_ret (fname_s ++ " return value violates noundef.")%string dv1)
                     (fun v' => ret (inr v')))))
          (t2 := run_draws s2 (run_fn_frames cenv cstk exc_slot
                   (ITree.bind (apply_attrs t_ret (fname_t ++ " return value violates noundef.")%string dv2)
                     (fun v' => ret (inr v'))))).
        -- apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity.
        -- apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity.
        -- destruct Hrv as [Hps1 | <-].
           ++ assert (Edv1 : dv1 = DVALUE_Base DVALUE_Poison)
                by (destruct dv1 as [[| | | | | | | ] | | ]; try discriminate Hps1; reflexivity).
              subst dv1.
              destruct (existsb attr_is_noundef s_ret) eqn:Enu_sr.
              ** unfold apply_attrs, apply_value_attrs.
                 rewrite value_attrs_poison_poison, Enu_sr; cbn [dvalue_well_defined negb andb].
                 eapply det_ref_obs_eq with
                   (t1 := run_draws s1 (run_fn_frames cenv cstk exc_slot
                            (ITree.bind (raiseUB (fname_s ++ " return value violates noundef.")%string)
                              (fun x => ITree.bind (assert_attrs_dereferenceable s_ret x (fname_s ++ " return value violates noundef.")%string ;; ret x)
                                (fun v' => ret (inr v'))))))
                   (t2 := run_draws s2 (run_fn_frames cenv cstk exc_slot
                            (ITree.bind (apply_attrs t_ret (fname_t ++ " return value violates noundef.")%string dv2)
                              (fun v' => ret (inr v')))));
                   [apply obs_eq_fn_frames_draws; symmetry; rewrite !observe_bind; reflexivity
                   | reflexivity
                   | apply fn_frames_raiseUB_bind].
              ** assert (Enu_tr : existsb attr_is_noundef t_ret = false).
                 { destruct (existsb attr_is_noundef t_ret) eqn:Et; [| reflexivity].
                   cbn in Hnu_ret_imp; rewrite Enu_sr in Hnu_ret_imp; discriminate Hnu_ret_imp. }
                 assert (Edr_t : find_option attr_dereferenceable t_ret = None).
                 { destruct (find_option attr_dereferenceable t_ret); [| reflexivity].
                   cbn in Htd_imp; rewrite Enu_sr in Htd_imp; discriminate Htd_imp. }
                 assert (Edr_s : find_option attr_dereferenceable s_ret = None).
                 { rewrite Edr_t in Hderef; destruct (find_option attr_dereferenceable s_ret);
                     [discriminate Hderef | reflexivity]. }
                 unfold apply_attrs, apply_value_attrs, assert_attrs_dereferenceable.
                 rewrite value_attrs_poison_poison, Enu_sr, Enu_tr, Edr_s, Edr_t; cbn [andb].
                 pstep; apply DR_Step; unfold det_step_body.
                 rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind; cbn.
                 left; reflexivity.
           ++ eapply step_apply_attrs_eq; [exact Hpm_ret | exact Hderef | intros _].
              pstep; apply DR_Step; unfold det_step_body.
              rewrite !observe_run_draws, !observe_run_fn_frames; cbn.
              right; reflexivity.
Qed.

Definition eval_defn_open {Pa : Params}
  (df : definition dtyp (CFG.cfg dtyp))
  (caller_env : rmap (@dvalue Pa))
  (caller_stk : list (rmap (@dvalue Pa)))
  (caller_exc : option (@dvalue Pa))
  (cc : cconv) (args : list (@dvalue Pa))
  : itree (@OW_E Pa) (@exc Pa + @dvalue Pa) :=
  run_fn_frames caller_env caller_stk caller_exc (denote_function df cc args).

Definition validator_defn_refines {Pa : Params}
  (arg_dtys : list dtyp)
  (src_df tgt_df : definition dtyp (CFG.cfg dtyp)) : Prop :=
  forall caller_env caller_stk caller_exc cc (vs : list (@dvalue Pa)),
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    ow_itree_refines sum_exc_dvalue_refines
      (eval_defn_open src_df caller_env caller_stk caller_exc cc vs)
      (eval_defn_open tgt_df caller_env caller_stk caller_exc cc vs).

Definition defn_arg_dtys
  (tenv : list (ident * typ))
  (df : definition typ (CFG.cfg typ)) : list dtyp :=
  match dc_type (df_prototype df) with
  | TYPE_Function _ arg_tys _ => List.map (typ_to_dtyp tenv) arg_tys
  | _ => []
  end.

Lemma proto_cfg_to_defn_refines {Pa : Params} :
  forall (src_tenv tgt_tenv : list (ident * typ))
         (src_defn tgt_defn : definition typ (CFG.cfg typ)),
    let src_cfg := convert_typ src_tenv (df_instrs src_defn) in
    let tgt_cfg := convert_typ tgt_tenv (df_instrs tgt_defn) in
    let arg_dtys := defn_arg_dtys src_tenv src_defn in
    let s_pattrs := snd (dc_param_attrs (df_prototype src_defn)) in
    check_prototype_contract (df_prototype src_defn) (df_prototype tgt_defn) = true ->
    proto_deref_preserved_b (df_prototype src_defn) (df_prototype tgt_defn) = true ->
    forallb2 attr_preserves_dtyp_b arg_dtys s_pattrs = true ->
    df_args src_defn = args src_cfg ->
    df_args tgt_defn = args tgt_cfg ->
    List.length arg_dtys = List.length (args src_cfg) ->
    List.length (args src_cfg) = List.length (args tgt_cfg) ->
    bmap_varargs_irrel (ocfg_map (blks src_cfg)) = true ->
    bmap_varargs_irrel (ocfg_map (blks tgt_cfg)) = true ->
    (forall (vs' : list (@dvalue Pa)),
       Forall2 dvalue_has_dtyp vs' arg_dtys ->
       Forall2 (fun attrs v' => existsb attr_is_noundef attrs = true -> dvalue_well_defined v' = true)
               s_pattrs vs' ->
       forall sigma_tgt,
         wf_draw_strat sigma_tgt ->
         exists sigma_src,
           wf_draw_strat sigma_src /\
           det_ref dvalue_refines
             (run_draws sigma_src (eval_cfg_open src_cfg vs'))
             (run_draws sigma_tgt (eval_cfg_open tgt_cfg vs')) /\
           no_stack_det (run_draws sigma_src (eval_cfg_open src_cfg vs'))) ->
    @validator_defn_refines Pa arg_dtys
      (tfmap (typ_to_dtyp src_tenv) src_defn)
      (tfmap (typ_to_dtyp tgt_tenv) tgt_defn).
Proof.
  intros src_tenv tgt_tenv src_defn tgt_defn src_cfg tgt_cfg arg_dtys s_pattrs
         Hproto Hderef Hpres Hdfa_s Hdfa_t Hlen_ad Hlen_st Hbm_s Hbm_t Hcfg_ref
         cenv cstk cexc cc vs Hvs sigma_tgt Hwfsig_t.
  destruct (check_prototype_contract_inv (df_prototype src_defn) (df_prototype tgt_defn) Hproto)
    as [Hdcnm (ret_ty & arg_tys & Edct_s & _ & Hlen_sp_at & _ & Hcc & Hret_ref & _ & Hpa_ref & Hfattrs)].
  unfold arg_dtys, defn_arg_dtys in *; rewrite Edct_s in *.
  unfold proto_deref_preserved_b in Hderef.
  destruct (dc_param_attrs (df_prototype src_defn)) as [s_rattrs s_pattrs0] eqn:Edcpa_s.
  destruct (dc_param_attrs (df_prototype tgt_defn)) as [t_rattrs t_pattrs] eqn:Edcpa_t.
  unfold s_pattrs in *; cbn [fst snd] in *.
  apply andb_true_iff in Hderef as [Hderef_ret Hderef_args].
  pose proof (List.Forall2_length Hvs) as Hlen_vs.
  assert (Hlen_sp_vs : List.length s_pattrs0 = List.length vs)
    by (rewrite List.length_map in Hlen_vs; lia).
  set (src_df := tfmap (typ_to_dtyp src_tenv) src_defn).
  set (tgt_df := tfmap (typ_to_dtyp tgt_tenv) tgt_defn).
  assert (Eproto_s : df_prototype src_df = tfmap (typ_to_dtyp src_tenv) (df_prototype src_defn))
    by reflexivity.
  assert (Eproto_t : df_prototype tgt_df = tfmap (typ_to_dtyp tgt_tenv) (df_prototype tgt_defn))
    by reflexivity.
  unfold eval_defn_open, denote_function.
  rewrite Eproto_s, Eproto_t; cbn [dc_param_attrs dc_name dc_attrs dc_annotations].
  unfold endo, Endo_id; rewrite Edcpa_s, Edcpa_t.
  rewrite !anns_cconv_tfmap.
  change (df_instrs src_df) with src_cfg.
  change (df_instrs tgt_df) with tgt_cfg.
  change (df_args src_df) with (df_args src_defn).
  change (df_args tgt_df) with (df_args tgt_defn).
  set (fcc_s := anns_cconv (dc_annotations (df_prototype src_defn))) in *.
  set (fcc_t := anns_cconv (dc_annotations (df_prototype tgt_defn))) in *.
  set (fname_s := show_raw_id (dc_name (df_prototype src_defn))).
  set (fname_t := show_raw_id (dc_name (df_prototype tgt_defn))).
  destruct (cconv_eqb cc fcc_s) eqn:Ecc_s.
  - assert (Ecc_t : cconv_eqb cc fcc_t = true)
      by (rewrite <- (cconv_eqb_same_caller fcc_s fcc_t cc Hcc); exact Ecc_s).
    destruct (args_attrs_src_ub s_pattrs0 vs) eqn:Eargs_ub.
    + exists sigma_tgt; split; [exact Hwfsig_t |].
      unfold check_cconv; rewrite Ecc_s, Ecc_t.
      eapply det_ref_obs_eq;
        [apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
        | apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity |].
      eapply step_apply_args_attrs; [exact Hlen_sp_vs | exact Hpa_ref | exact Hderef_args |].
      intros Habs; discriminate Habs.
    + destruct (eval_args_attrs_poison_wf (List.map (typ_to_dtyp src_tenv) arg_tys) s_pattrs0 vs
                  Hvs Hpres Eargs_ub)
        as (Hlen_vs' & Hty_vs' & Hnu_vs').
      set (vs' := eval_args_attrs_poison s_pattrs0 vs) in *.
      destruct (Hcfg_ref vs' Hty_vs' Hnu_vs' sigma_tgt Hwfsig_t)
        as (sigma_src & Hwfsig_s & Hdr_cfg & Hns_cfg).
      exists sigma_src; split; [exact Hwfsig_s |].
      unfold check_cconv; rewrite Ecc_s, Ecc_t.
      eapply det_ref_obs_eq;
        [apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity
        | apply obs_eq_fn_frames_draws; symmetry; rewrite observe_bind; reflexivity |].
      eapply step_apply_args_attrs; [exact Hlen_sp_vs | exact Hpa_ref | exact Hderef_args |].
      intros _; fold vs'.
      assert (Hlen_dfa_s : List.length (df_args src_defn) = List.length vs')
        by (rewrite Hdfa_s; lia).
      assert (Hlen_dfa_t : List.length (df_args tgt_defn) = List.length vs')
        by (rewrite Hdfa_t; lia).
      eapply step_push_call_frame with (src_df := src_df) (tgt_df := tgt_df);
        [exact Hlen_dfa_s | exact Hlen_dfa_t | intros varg].
      change (df_args src_df) with (df_args src_defn).
      change (df_args tgt_df) with (df_args tgt_defn).
      rewrite Hdfa_s, Hdfa_t.
      eapply det_ref_cfg_to_fn_body.
      * intros s1 s2 env1 env2 rv1 rv2 Hrv.
        eapply step_pop_call_frame.
        exact (step_check_call_return (dc_attrs (df_prototype src_defn)) (dc_attrs (df_prototype tgt_defn))
                 s_rattrs t_rattrs fname_s fname_t vs' rv1 rv2 s1 s2 cenv cstk cexc
                 Hfattrs Hret_ref Hderef_ret Hrv).
      * eapply det_ref_trans with (R12 := @eq (@dvalue Pa)) (R23 := dvalue_refines);
          [intros ? ? ? -> Hr; exact Hr
          | exact (denote_cfg_varargs_det_ref src_cfg (Some varg) None sigma_src
                     (init_cfg_locals (args src_cfg) vs') Hbm_s) |].
        eapply det_ref_trans with (R12 := dvalue_refines) (R23 := @eq (@dvalue Pa));
          [intros ? ? ? Hr <-; exact Hr
          | exact Hdr_cfg
          | exact (denote_cfg_varargs_det_ref tgt_cfg None (Some varg) sigma_tgt
                     (init_cfg_locals (args tgt_cfg) vs') Hbm_t)].
      * exact (denote_cfg_varargs_no_stack_det src_cfg (Some varg) None sigma_src
                 (init_cfg_locals (args src_cfg) vs') Hbm_s Hns_cfg).
  - exists sigma_tgt; split; [exact Hwfsig_t |].
    unfold check_cconv; rewrite Ecc_s.
    apply fn_frames_raiseUB_bind.
Qed.




Lemma forallb2_raw_id_eqb_eq :
  forall xs ys,
    forallb2 raw_id_eqb xs ys = true ->
    xs = ys.
Proof.
  induction xs as [| x rx IH]; intros [| y ry] H;
    cbn [forallb2] in H; try discriminate H; [reflexivity |].
  apply andb_true_iff in H as [Hx Hr].
  apply raw_id_eqb_eq in Hx; subst y; f_equal; exact (IH ry Hr).
Qed.

Definition cert_promoted_slot_names (cert : proof_certificate) : list string :=
  List.flat_map (fun bc =>
    List.flat_map (fun mi =>
      match mi with
      | MI_AllocaPromoted ss _ _ => [ss]
      | MI_SlotRefines ss _ _ _ _ => [ss]
      end) (bc_memory_invariants bc)) (pc_blocks cert).

Definition check_ro_vars_subset
  (allowed : list (string * positive))
  (ro : return_obligation) : bool :=
  match ro with
  | RO_VoidEquiv => true
  | RO_ScalarRefines _ se te _ =>
      vars_subset_b (collect_free_vars [] se) allowed &&
      vars_subset_b (collect_free_vars [] te) allowed
  end.

Definition check_cert_cfg_with_proto_lrat
  (opt_proto : option (list dtyp * list (list param_attr)))
  (src_cfg tgt_cfg : CFG.cfg dtyp)
  (cert : proof_certificate)
  (opt_pf : option (list lrat_step)) : bool :=
  let src_pnames := List.map cert_reg_name (args src_cfg) in
  let proto_seed :=
    match opt_proto with
    | None => ([], [])
    | Some (p_dtys, s_pattrs) => seed_proto_param_ctx src_pnames p_dtys s_pattrs
    end in
  let allowed := used_src_param_vars src_cfg ++ fst proto_seed in
  let init_ctx := snd proto_seed in
  let src_uses := param_idx_uses_cfg src_cfg in
  let tgt_uses := param_idx_uses_cfg tgt_cfg in
  let src_slots := cfg_alloca_slot_names src_cfg in
  let tgt_slots := cfg_alloca_slot_names tgt_cfg in
  let known_src_slots := src_slots ++ cert_promoted_slot_names cert in
  let blk_uas := fun bid => block_uas_for bid (pc_blocks cert) in
  wf_proof_certificate cert &&
  check_validator_syntax_gates src_cfg tgt_cfg &&
  list_empty_b src_slots &&
  list_empty_b tgt_slots &&
  forallb (check_alias_witness_valid known_src_slots) (pc_alias_witnesses cert) &&
  check_ro_vars_subset allowed (pc_return_obligation cert) &&
  bmap_varargs_irrel (ocfg_map (blks src_cfg)) &&
  bmap_varargs_irrel (ocfg_map (blks tgt_cfg)) &&
  Nat.eqb (List.length (args src_cfg)) (List.length (args tgt_cfg)) &&
  no_dup_raw_ids (args src_cfg) &&
  no_dup_raw_ids (args tgt_cfg) &&
  no_dup_strings src_pnames &&
  forallb (fun u => param_use_in u src_uses) tgt_uses &&
  match pc_loop_invariants cert with
  | [] =>
      forallb (fun bc =>
        forallb (check_memory_invariant_valid allowed (bc_ub_assumptions bc ++ init_ctx))
          (bc_memory_invariants bc))
        (pc_blocks cert) &&
      match summarize_cfg_dag_with_uas blk_uas false src_cfg src_pnames,
            summarize_cfg_dag true tgt_cfg src_pnames with
      | Some d_src, Some d_tgt =>
          let fuel := S (dag_node_count d_src + dag_node_count d_tgt) in
          check_dag_refines_cert fuel allowed init_ctx (pc_return_obligation cert) opt_pf
            (spine_src_evals d_src) (spine_branch_conds d_src) d_src d_tgt
      | _, _ => false
      end
  | [lci] =>
      check_loop_cutpoint_cfg allowed init_ctx src_cfg tgt_cfg cert lci opt_pf
  | _ :: _ :: _ => false
  end.

Definition check_cert_cfg_with_lrat
  (src_cfg tgt_cfg : CFG.cfg dtyp)
  (cert : proof_certificate)
  (opt_pf : option (list lrat_step)) : bool :=
  check_cert_cfg_with_proto_lrat None src_cfg tgt_cfg cert opt_pf.

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
  let src_cfg := convert_typ src_tenv (df_instrs src_defn) in
  let tgt_cfg := convert_typ tgt_tenv (df_instrs tgt_defn) in
  let arg_dtys := defn_arg_dtys src_tenv src_defn in
  let s_pattrs := snd (dc_param_attrs (df_prototype src_defn)) in
  cert_fn_matches_raw_id (pc_function_name cert) (dc_name (df_prototype src_defn)) &&
  check_prototype_contract (df_prototype src_defn) (df_prototype tgt_defn) &&
  proto_deref_preserved_b (df_prototype src_defn) (df_prototype tgt_defn) &&
  forallb2 attr_preserves_dtyp_b arg_dtys s_pattrs &&
  forallb2 raw_id_eqb (df_args src_defn) (args src_cfg) &&
  forallb2 raw_id_eqb (df_args tgt_defn) (args tgt_cfg) &&
  Nat.eqb (List.length arg_dtys) (List.length (args src_cfg)) &&
  cfg_param_dtyp_compatible src_cfg arg_dtys &&
  check_cert_cfg_with_proto_lrat (Some (arg_dtys, s_pattrs)) src_cfg tgt_cfg cert opt_pf.

Definition check_cert_defn
  (src_tenv tgt_tenv : list (ident * typ))
  (src_defn tgt_defn : definition typ (CFG.cfg typ))
  (cert : proof_certificate) : bool :=
  check_cert_defn_with_lrat src_tenv tgt_tenv src_defn tgt_defn cert None.


(** *** 5.7 Top-Level Per-Function Translation Validator Soundness ([0 Admitted]) *)

Theorem check_cert_cfg_proto_core_sound :
  forall {Pa : Params}
         (opt_proto : option (list dtyp * list (list param_attr)))
         (src_cfg tgt_cfg : CFG.cfg dtyp)
         (cert : proof_certificate)
         (opt_pf : option (list lrat_step)),
    check_cert_cfg_with_proto_lrat opt_proto src_cfg tgt_cfg cert opt_pf = true ->
    List.length (args src_cfg) = List.length (args tgt_cfg) /\
    bmap_varargs_irrel (ocfg_map (blks src_cfg)) = true /\
    bmap_varargs_irrel (ocfg_map (blks tgt_cfg)) = true /\
    forall arg_dtys,
      List.length arg_dtys = List.length (args src_cfg) ->
      cfg_param_dtyp_compatible src_cfg arg_dtys = true ->
      cfg_param_dtyp_compatible tgt_cfg arg_dtys = true /\
      forall (vs : list (@dvalue Pa)),
        Forall2 dvalue_has_dtyp vs arg_dtys ->
        match opt_proto with
        | None => True
        | Some (p_dtys, s_pattrs) =>
            p_dtys = arg_dtys /\
            Forall2 (fun attrs v => existsb attr_is_noundef attrs = true -> dvalue_well_defined v = true)
                    s_pattrs vs
        end ->
        forall sigma_tgt,
          wf_draw_strat sigma_tgt ->
          exists sigma_src,
            wf_draw_strat sigma_src /\
            det_ref dvalue_refines
              (run_draws sigma_src (eval_cfg_open src_cfg vs))
              (run_draws sigma_tgt (eval_cfg_open tgt_cfg vs)) /\
            no_stack_det (run_draws sigma_src (eval_cfg_open src_cfg vs)).
Proof.
  intros Pa opt_proto src_cfg tgt_cfg cert opt_pf Hchk.
  unfold check_cert_cfg_with_proto_lrat in Hchk; cbn zeta in Hchk.
  set (src_pnames := List.map cert_reg_name (args src_cfg)) in *.
  set (proto_seed :=
         match opt_proto with
         | None => ([], [])
         | Some (p_dtys, s_pattrs) => seed_proto_param_ctx src_pnames p_dtys s_pattrs
         end) in *.
  set (allowed := used_src_param_vars src_cfg ++ fst proto_seed) in *.
  set (init_ctx := snd proto_seed) in *.
  set (src_uses := param_idx_uses_cfg src_cfg) in *.
  set (tgt_uses := param_idx_uses_cfg tgt_cfg) in *.
  set (blk_uas := fun bid => block_uas_for bid (pc_blocks cert)) in *.
  apply andb_true_iff in Hchk as [Hchk Hbody].
  apply andb_true_iff in Hchk as [Hchk Huses_sub].
  apply andb_true_iff in Hchk as [Hchk Hnd_sp].
  apply andb_true_iff in Hchk as [Hchk Hnd_ta].
  apply andb_true_iff in Hchk as [Hchk Hnd_sa].
  apply andb_true_iff in Hchk as [Hchk Hlen_st].
  apply andb_true_iff in Hchk as [Hchk Hbm_t].
  apply andb_true_iff in Hchk as [_ Hbm_s].
  apply Nat.eqb_eq in Hlen_st.
  apply no_dup_raw_ids_spec in Hnd_sa.
  apply no_dup_raw_ids_spec in Hnd_ta.
  apply no_dup_strings_spec in Hnd_sp.
  assert (Hpu_src : forall idx w0 pnm,
    In (idx, DTYPE_Base (DTYPE_I w0)) src_uses ->
    nth_error src_pnames idx = Some pnm ->
    In (pnm, w0) allowed).
  { intros idx w0 pnm Hin Hpnm; unfold allowed; apply in_app_iff; left.
    unfold used_src_param_vars; apply in_flat_map.
    exists (idx, DTYPE_Base (DTYPE_I w0)).
    split; [exact Hin | fold src_pnames; rewrite Hpnm; left; reflexivity]. }
  assert (Hpu_tgt : forall idx w0 pnm,
    In (idx, DTYPE_Base (DTYPE_I w0)) tgt_uses ->
    nth_error src_pnames idx = Some pnm ->
    In (pnm, w0) allowed).
  { intros idx w0 pnm Hin Hpnm.
    rewrite forallb_forall in Huses_sub.
    pose proof (Huses_sub (idx, DTYPE_Base (DTYPE_I w0)) Hin) as Hin_s.
    apply param_use_in_spec in Hin_s; exact (Hpu_src idx w0 pnm Hin_s Hpnm). }
  split; [exact Hlen_st | split; [exact Hbm_s | split; [exact Hbm_t |]]].
  intros arg_dtys Hlen_da Hcomp_s.
  assert (Hcomp_t : cfg_param_dtyp_compatible tgt_cfg arg_dtys = true).
  { unfold cfg_param_dtyp_compatible in Hcomp_s |- *.
    rewrite forallb_forall in Hcomp_s, Huses_sub |- *.
    intros u Hu; apply Hcomp_s; apply param_use_in_spec; exact (Huses_sub u Hu). }
  split; [exact Hcomp_t |].
  intros vs Hvs Hproto_vs sigma_tgt Hwfsig_t.
  pose proof (List.Forall2_length Hvs) as Hlen_vs.
  assert (Hlen_sp_s : List.length src_pnames = List.length (args src_cfg))
    by (unfold src_pnames; apply List.length_map).
  assert (Hlen_sp_t : List.length src_pnames = List.length (args tgt_cfg)) by lia.
  assert (Hlen_da_t : List.length arg_dtys = List.length (args tgt_cfg)) by lia.
  assert (Hlen_sp_vs : List.length src_pnames = List.length vs) by lia.
  set (penv := build_param_env src_pnames vs) in *.
  pose proof (used_src_param_vars_wf src_cfg arg_dtys vs Hnd_sp Hlen_da Hcomp_s Hvs) as Hpenv_used.
  fold src_pnames penv in Hpenv_used.
  assert (Hseed_wf :
    wf_param_env_for (fst proto_seed) penv /\
    (forall fo : freeze_oracle, ub_ctx_holds penv fo init_ctx)).
  { unfold proto_seed, init_ctx; clear proto_seed init_ctx allowed Hbody.
    destruct opt_proto as [[p_dtys s_pattrs] |].
    - destruct Hproto_vs as [-> Hnu].
      split.
      + exact (proj1 (seed_proto_param_ctx_sound src_pnames arg_dtys s_pattrs vs
                        dummy_freeze_oracle Hnd_sp Hlen_sp_vs Hvs Hnu)).
      + intros fo.
        exact (proj2 (seed_proto_param_ctx_sound src_pnames arg_dtys s_pattrs vs
                        fo Hnd_sp Hlen_sp_vs Hvs Hnu)).
    - split; [intros ? ? [] | intros fo; constructor]. }
  destruct Hseed_wf as [Hpenv_extra Hinit_ctx_any].
  assert (Hpenv_wf : wf_param_env_for allowed penv).
  { intros nm w Hin; unfold allowed in Hin; apply in_app_iff in Hin as [Hu | He];
      [exact (Hpenv_used nm w Hu) | exact (Hpenv_extra nm w He)]. }
  destruct (pc_loop_invariants cert) as [| lci [| ? ?]].
  - apply andb_true_iff in Hbody as [_ Hrest].
    destruct (summarize_cfg_dag_with_uas blk_uas false src_cfg src_pnames)
      as [d_src |] eqn:Esum_s; [| discriminate Hrest].
    destruct (summarize_cfg_dag true tgt_cfg src_pnames)
      as [d_tgt |] eqn:Esum_t; [| discriminate Hrest].
    pose proof (summarize_cfg_dag_with_uas_wf blk_uas false src_cfg src_pnames allowed d_src
                  Hpu_src Esum_s) as Hwfd_s.
    pose proof (summarize_cfg_dag_wf true tgt_cfg src_pnames allowed d_tgt
                  Hpu_tgt Esum_t) as Hwfd_t.
    destruct (summarize_tgt_dag_sound tgt_cfg src_pnames arg_dtys vs sigma_tgt d_tgt
                Hnd_ta Hnd_sp Hlen_sp_t Hlen_da_t Hcomp_t Hvs Hwfsig_t Esum_t)
      as [fmap_tgt Htgt_out].
    set (foracle := oracle_of_fmap fmap_tgt) in *.
    destruct (summarize_src_dag_with_uas_sound blk_uas src_cfg src_pnames arg_dtys vs foracle d_src
                Hnd_sa Hnd_sp Hlen_sp_s Hlen_da Hcomp_s Hvs Esum_s)
      as [sigma_src [Hwfsig_s Hsrc_out]].
    exists sigma_src; split; [exact Hwfsig_s |].
    destruct Hsrc_out as [[Hst_ub_s _] | (sigma_src' & env_out_s & dv_src & Hev_ds & Hst_ret_s)].
    + split.
      * exact (cfg_steps_ub_det_ref dvalue_refines sigma_src
                 (init_cfg_locals (args src_cfg) vs) (denote_cfg src_cfg None)
                 (run_draws sigma_tgt (eval_cfg_open tgt_cfg vs)) Hst_ub_s).
      * exact (cfg_steps_ub_no_stack_det sigma_src
                 (init_cfg_locals (args src_cfg) vs) (denote_cfg src_cfg None) Hst_ub_s).
    + destruct (check_dag_refines_cert_sound
                  (S (dag_node_count d_src + dag_node_count d_tgt))
                  allowed init_ctx (pc_return_obligation cert) opt_pf
                  (spine_src_evals d_src) (spine_branch_conds d_src)
                  d_src d_tgt penv foracle dv_src
                  Hwfd_s Hwfd_t Hpenv_wf (Hinit_ctx_any foracle)
                  (fun big H => spine_src_evals_wf allowed d_src big Hwfd_s H)
                  (fun big H => spine_src_evals_ret penv foracle d_src dv_src big Hev_ds H)
                  (fun c H => spine_branch_conds_ret penv foracle d_src dv_src c Hev_ds H)
                  Hrest Hev_ds)
        as [dv_tgt [Hev_dt Href_dv]].
      destruct Htgt_out as [Hev_dt_ub | (sigma_tgt' & env_out_t & dv_tgt' & Hev_dt' & Hst_ret_t)].
      * rewrite Hev_dt in Hev_dt_ub; discriminate Hev_dt_ub.
      * rewrite Hev_dt in Hev_dt'; injection Hev_dt' as <-.
        split.
        -- exact (cfg_steps_ret_det_ref dvalue_refines
                    sigma_src (init_cfg_locals (args src_cfg) vs) (denote_cfg src_cfg None)
                    sigma_src' env_out_s dv_src
                    sigma_tgt (init_cfg_locals (args tgt_cfg) vs) (denote_cfg tgt_cfg None)
                    sigma_tgt' env_out_t dv_tgt
                    Hst_ret_s Hst_ret_t Href_dv).
        -- exact (cfg_steps_ret_no_stack_det sigma_src
                    (init_cfg_locals (args src_cfg) vs) (denote_cfg src_cfg None)
                    sigma_src' env_out_s dv_src Hst_ret_s).
  - destruct (check_loop_cutpoint_cfg_open_sound
                allowed init_ctx src_cfg tgt_cfg cert lci opt_pf arg_dtys vs
                Hnd_sa Hnd_ta Hnd_sp Hlen_st Hlen_da Hcomp_s Hcomp_t Hvs
                Hpu_src Hpu_tgt Hpenv_wf (Hinit_ctx_any dummy_freeze_oracle)
                Hbody sigma_tgt Hwfsig_t)
      as [sigma_src [Hwfsig_s Hdr_loop]].
    exists sigma_src; split; [exact Hwfsig_s | split; [exact Hdr_loop |]].
    exact (check_loop_cutpoint_cfg_no_stack_det
             allowed init_ctx src_cfg tgt_cfg cert lci opt_pf arg_dtys vs
             Hnd_sa Hnd_sp Hlen_da Hcomp_s Hvs Hpu_src Hbody sigma_src).
  - discriminate Hbody.
Qed.

Theorem check_cert_cfg_with_lrat_sound :
  forall {Pa : Params} (src_cfg tgt_cfg : CFG.cfg dtyp)
         (cert : proof_certificate) (opt_pf : option (list lrat_step)),
    check_cert_cfg_with_lrat src_cfg tgt_cfg cert opt_pf = true ->
    @validator_cfg_refines Pa src_cfg tgt_cfg.
Proof.
  intros Pa src_cfg tgt_cfg cert opt_pf Hchk.
  destruct (@check_cert_cfg_proto_core_sound Pa None src_cfg tgt_cfg cert opt_pf Hchk)
    as (Hlen_st & _ & _ & Hrest).
  split; [exact Hlen_st |].
  intros arg_dtys Hlen_da Hcomp_s.
  destruct (Hrest arg_dtys Hlen_da Hcomp_s) as [Hcomp_t Hgo].
  split; [exact Hcomp_t |].
  intros vs Hvs sigma_tgt Hwfsig_t.
  destruct (Hgo vs Hvs I sigma_tgt Hwfsig_t) as (sigma_src & Hwfsig_s & Hdr & _).
  exists sigma_src; exact (conj Hwfsig_s Hdr).
Qed.

Theorem check_cert_cfg_sound :
  forall {Pa : Params} (src_cfg tgt_cfg : CFG.cfg dtyp) (cert : proof_certificate),
    check_cert_cfg src_cfg tgt_cfg cert = true ->
    @validator_cfg_refines Pa src_cfg tgt_cfg.
Proof.
  intros Pa src_cfg tgt_cfg cert Hchk.
  exact (check_cert_cfg_with_lrat_sound src_cfg tgt_cfg cert None Hchk).
Qed.

Theorem check_cert_defn_with_lrat_sound :
  forall {Pa : Params} (src_tenv tgt_tenv : list (ident * typ))
         (src_defn tgt_defn : definition typ (CFG.cfg typ))
         (cert : proof_certificate)
         (opt_pf : option (list lrat_step)),
    check_cert_defn_with_lrat src_tenv tgt_tenv src_defn tgt_defn cert opt_pf = true ->
    cert_fn_matches_raw_id (pc_function_name cert) (dc_name (df_prototype src_defn)) = true /\
    dc_name (df_prototype src_defn) = dc_name (df_prototype tgt_defn) /\
    check_prototype_contract (df_prototype src_defn) (df_prototype tgt_defn) = true /\
    @validator_defn_refines Pa
      (defn_arg_dtys src_tenv src_defn)
      (tfmap (typ_to_dtyp src_tenv) src_defn)
      (tfmap (typ_to_dtyp tgt_tenv) tgt_defn).
Proof.
  intros Pa src_tenv tgt_tenv src_defn tgt_defn cert opt_pf Hchk.
  unfold check_cert_defn_with_lrat in Hchk; cbn zeta in Hchk.
  set (src_cfg := convert_typ src_tenv (df_instrs src_defn)) in *.
  set (tgt_cfg := convert_typ tgt_tenv (df_instrs tgt_defn)) in *.
  set (arg_dtys := defn_arg_dtys src_tenv src_defn) in *.
  set (s_pattrs := snd (dc_param_attrs (df_prototype src_defn))) in *.
  apply andb_true_iff in Hchk as [Hchk Hcfg].
  apply andb_true_iff in Hchk as [Hchk Hcomp_s].
  apply andb_true_iff in Hchk as [Hchk Hlen_ad].
  apply andb_true_iff in Hchk as [Hchk Hdfa_t].
  apply andb_true_iff in Hchk as [Hchk Hdfa_s].
  apply andb_true_iff in Hchk as [Hchk Hpres].
  apply andb_true_iff in Hchk as [Hchk Hderef].
  apply andb_true_iff in Hchk as [Hfn Hproto].
  apply Nat.eqb_eq in Hlen_ad.
  apply forallb2_raw_id_eqb_eq in Hdfa_s.
  apply forallb2_raw_id_eqb_eq in Hdfa_t.
  destruct (check_prototype_contract_inv _ _ Hproto) as [Hdcnm _].
  destruct (@check_cert_cfg_proto_core_sound Pa (Some (arg_dtys, s_pattrs))
              src_cfg tgt_cfg cert opt_pf Hcfg)
    as (Hlen_st & Hbm_s & Hbm_t & Hcore).
  destruct (Hcore arg_dtys Hlen_ad Hcomp_s) as [_ Hgo].
  repeat split; [exact Hfn | exact Hdcnm | exact Hproto |].
  exact (proto_cfg_to_defn_refines src_tenv tgt_tenv src_defn tgt_defn
           Hproto Hderef Hpres Hdfa_s Hdfa_t Hlen_ad Hlen_st Hbm_s Hbm_t
           (fun vs' Hty' Hnu' => Hgo vs' Hty' (conj eq_refl Hnu'))).
Qed.

Theorem check_cert_defn_sound :
  forall {Pa : Params} (src_tenv tgt_tenv : list (ident * typ))
         (src_defn tgt_defn : definition typ (CFG.cfg typ))
         (cert : proof_certificate),
    check_cert_defn src_tenv tgt_tenv src_defn tgt_defn cert = true ->
    cert_fn_matches_raw_id (pc_function_name cert) (dc_name (df_prototype src_defn)) = true /\
    dc_name (df_prototype src_defn) = dc_name (df_prototype tgt_defn) /\
    check_prototype_contract (df_prototype src_defn) (df_prototype tgt_defn) = true /\
    @validator_defn_refines Pa
      (defn_arg_dtys src_tenv src_defn)
      (tfmap (typ_to_dtyp src_tenv) src_defn)
      (tfmap (typ_to_dtyp tgt_tenv) tgt_defn).
Proof.
  intros Pa src_tenv tgt_tenv src_defn tgt_defn cert Hchk.
  exact (check_cert_defn_with_lrat_sound src_tenv tgt_tenv src_defn tgt_defn cert None Hchk).
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
      @validator_defn_refines Pa
        (defn_arg_dtys (m_type_defs src_m) src_defn)
        (tfmap (typ_to_dtyp (m_type_defs src_m)) src_defn)
        (tfmap (typ_to_dtyp (m_type_defs tgt_m)) tgt_defn).
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
  destruct (@check_cert_defn_with_lrat_sound Pa (m_type_defs src_m) (m_type_defs tgt_m)
              src_defn tgt_defn cert opt_pf Hchk)
    as (Hfn & Hdcnm & Hproto & Href).
  exists src_defn, tgt_defn.
  repeat split; assumption.
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
      @validator_defn_refines Pa
        (defn_arg_dtys (m_type_defs src_m) src_defn)
        (tfmap (typ_to_dtyp (m_type_defs src_m)) src_defn)
        (tfmap (typ_to_dtyp (m_type_defs tgt_m)) tgt_defn).
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
      @validator_defn_refines Pa
        (defn_arg_dtys (m_type_defs src_m) src_defn)
        (tfmap (typ_to_dtyp (m_type_defs src_m)) src_defn)
        (tfmap (typ_to_dtyp (m_type_defs tgt_m)) tgt_defn).
Proof.
  intros Pa src_tle tgt_tle cert_str Hval src_m tgt_m.
  unfold validate_tle_pair_with_cert_str in Hval.
  destruct (parse_cert cert_str) as [| cert] eqn:Ep; [discriminate Hval |].
  unfold validate_tle_pair_with_cert in Hval; fold src_m tgt_m in Hval.
  pose proof (parse_cert_wf cert_str cert Ep) as Hwf_cert.
  destruct (@validate_mcfg_with_cert_sound Pa src_m tgt_m cert Hval)
    as (src_defn & tgt_defn & Hin_s & Hin_t & Hfn & Hdcnm & Hproto & Href).
  exists cert, src_defn, tgt_defn.
  repeat split; assumption.
Qed.
