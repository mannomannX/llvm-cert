(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Open-World Event Signatures, [DrawE] Refinement & Operational Stepping (Sec 1-4) *)

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
  Syntax.Traversal
  Numeric.Integers
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.LLVMEvents
  Semantics.Attributes
  Semantics.Denotation
  Semantics.IntrinsicsDefinitions
  Semantics.MemoryBytes
  Semantics.Operations.Compare
  Semantics.Operations.Conversion
  Semantics.Operations.Select
  Semantics.Operations.Freeze
  Semantics.Operations.Gep
  Theory.MemoryBytesFacts.

From CertValidator.common Require Import
  Diag.

From CertValidator Require Import
  CertFormatAst
  CertFormatGates
  AlgRulesEval.

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

Section DValueBaseProjLemmas.
  Context {Pa : Params}.

  Definition dvalue_to_int_width (v : @dvalue Pa) : option positive :=
    match v with
    | DVALUE_Base dv => @dvalue_base_int_width Pa dv
    | _ => None
    end.

  Definition dvalue_to_int_unsigned (v : @dvalue Pa) : Z :=
    match v with
    | DVALUE_Base dv => @dvalue_base_int_unsigned Pa dv
    | _ => 0%Z
    end.

  Definition eou_dvalue_int_width (x : EOU (@dvalue Pa)) : option positive :=
    match x with
    | raise_ret v => dvalue_to_int_width v
    | _ => None
    end.

  Definition eou_dvalue_int_unsigned (x : EOU (@dvalue Pa)) : Z :=
    match x with
    | raise_ret v => dvalue_to_int_unsigned v
    | _ => 0%Z
    end.

  Lemma dvalue_base_I_width_eq (sz1 sz2 : positive)
    (i1 : @Integers.bit_int sz1) (i2 : @Integers.bit_int sz2) :
    DVALUE_Base (@DVALUE_I Pa sz1 i1) = DVALUE_Base (@DVALUE_I Pa sz2 i2) ->
    sz1 = sz2.
  Proof using Type.
    intros H; pose proof (f_equal dvalue_to_int_width H) as Hw; cbn in Hw.
    inversion Hw; reflexivity.
  Qed.

  Lemma dvalue_base_I_same_sz_inj (sz : positive)
    (i1 i2 : @Integers.bit_int sz) :
    DVALUE_Base (@DVALUE_I Pa sz i1) = DVALUE_Base (@DVALUE_I Pa sz i2) ->
    i1 = i2.
  Proof using Type.
    intros H; apply alg_bit_int_unsigned_inj.
    exact (f_equal dvalue_to_int_unsigned H).
  Qed.

  Lemma eou_dvalue_I_width_eq (sz1 sz2 : positive)
    (i1 : @Integers.bit_int sz1) (i2 : @Integers.bit_int sz2) :
    raise_ret (DVALUE_Base (@DVALUE_I Pa sz1 i1)) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa sz2 i2)) ->
    sz1 = sz2.
  Proof using Type.
    intros H; pose proof (f_equal eou_dvalue_int_width H) as Hw; cbn in Hw.
    inversion Hw; reflexivity.
  Qed.

  Lemma eou_dvalue_I_same_sz_inj (sz : positive)
    (i1 i2 : @Integers.bit_int sz) :
    raise_ret (DVALUE_Base (@DVALUE_I Pa sz i1)) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa sz i2)) ->
    i1 = i2.
  Proof using Type.
    intros H; apply alg_bit_int_unsigned_inj.
    exact (f_equal eou_dvalue_int_unsigned H).
  Qed.
End DValueBaseProjLemmas.

Inductive pure_int_intrinsic_op : Set :=
| PII_SMin
| PII_SMax
| PII_UMin
| PII_UMax
| PII_UAddSat
| PII_USubSat
| PII_Abs.

Definition parse_pure_int_intrinsic_width (suf : string) : option positive :=
  if String.eqb suf "i8" then Some 8%positive
  else if String.eqb suf "i16" then Some 16%positive
  else if String.eqb suf "i32" then Some 32%positive
  else if String.eqb suf "i64" then Some 64%positive
  else None.

Definition parse_pure_int_intrinsic (fname : string) : option (pure_int_intrinsic_op * positive) :=
  if String.prefix "llvm.smin." fname then
    option_map (fun w => (PII_SMin, w))
      (parse_pure_int_intrinsic_width (String.substring 10 (String.length fname - 10) fname))
  else if String.prefix "llvm.smax." fname then
    option_map (fun w => (PII_SMax, w))
      (parse_pure_int_intrinsic_width (String.substring 10 (String.length fname - 10) fname))
  else if String.prefix "llvm.umin." fname then
    option_map (fun w => (PII_UMin, w))
      (parse_pure_int_intrinsic_width (String.substring 10 (String.length fname - 10) fname))
  else if String.prefix "llvm.umax." fname then
    option_map (fun w => (PII_UMax, w))
      (parse_pure_int_intrinsic_width (String.substring 10 (String.length fname - 10) fname))
  else if String.prefix "llvm.uadd.sat." fname then
    option_map (fun w => (PII_UAddSat, w))
      (parse_pure_int_intrinsic_width (String.substring 14 (String.length fname - 14) fname))
  else if String.prefix "llvm.usub.sat." fname then
    option_map (fun w => (PII_USubSat, w))
      (parse_pure_int_intrinsic_width (String.substring 14 (String.length fname - 14) fname))
  else if String.prefix "llvm.abs." fname then
    option_map (fun w => (PII_Abs, w))
      (parse_pure_int_intrinsic_width (String.substring 9 (String.length fname - 9) fname))
  else None.

Section OpenWorldEvents.
  Context {Pa : Params}.

  Definition pure_int_intrinsic_fn (op : pure_int_intrinsic_op) (w : positive)
    : list (@dvalue Pa) -> EOU (@exc Pa + @dvalue Pa) :=
    match op with
    | PII_SMin =>
        pure_base_to_pure (llvm_int_binop "llvm.smin got incorrect / ill-typed inputs" w (@int_smin))
    | PII_SMax =>
        pure_base_to_pure (llvm_int_binop "llvm.smax got incorrect / ill-typed inputs" w (@int_smax))
    | PII_UMin =>
        pure_base_to_pure (llvm_int_binop "llvm.umin got incorrect / ill-typed inputs" w (@int_umin))
    | PII_UMax =>
        pure_base_to_pure (llvm_int_binop "llvm.umax got incorrect / ill-typed inputs" w (@int_umax))
    | PII_UAddSat =>
        pure_base_to_pure (llvm_int_binop "llvm.uadd.sat got incorrect / ill-typed inputs" w (@int_uadd_sat))
    | PII_USubSat =>
        pure_base_to_pure (llvm_int_binop "llvm.usub.sat got incorrect / ill-typed inputs" w (@int_usub_sat))
    | PII_Abs =>
        pure_base_to_pure (llvm_int_unop_flag "llvm.abs got incorrect / ill-typed inputs" w (@int_abs))
    end.

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

  Inductive ow_event_class : Type -> Type :=
  | OWC_Draw (dt : dtyp) : ow_event_class dvalue
  | OWC_PureIntIntrinsic (op : pure_int_intrinsic_op) (w : positive) (args : list dvalue)
      : ow_event_class (exc + dvalue)
  | OWC_Det {X : Type} (de : Det_OW_E X) : ow_event_class X.

  Definition classify_ow_event {X : Type} (e : OW_E X) : ow_event_class X :=
    match e with
    | inl1 c => OWC_Det (inl1 c)
    | inr1 (inl1 ec) => OWC_Det (inr1 (inl1 ec))
    | inr1 (inr1 (inl1 ic)) =>
        match ic in IntrinsicE Y return ow_event_class Y with
        | Intrinsic dt fname args va =>
            match parse_pure_int_intrinsic fname with
            | Some (op, w) => OWC_PureIntIntrinsic op w args
            | None => OWC_Det (inr1 (inr1 (inl1 (Intrinsic dt fname args va))))
            end
        end
    | inr1 (inr1 (inr1 (inl1 ge))) => OWC_Det (inr1 (inr1 (inr1 (inl1 ge))))
    | inr1 (inr1 (inr1 (inr1 (inl1 se)))) =>
        OWC_Det (inr1 (inr1 (inr1 (inr1 (inl1 se)))))
    | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 me))))) =>
        OWC_Det (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 me))))))
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 d)))))) =>
        match d in DrawE Y return ow_event_class Y with
        | Draw dt => OWC_Draw dt
        end
    | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 rest)))))) =>
        OWC_Det (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 rest))))))
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
         inversion Hty as [dv t' Hb Hc Heqv1 Heqv2 | t' Heqv | |]; subst;
         [destruct dv; cbn in Hb, Hwd; discriminate | discriminate]).
    - exfalso; destruct Hinh as [v [Hty Hwd]];
        inversion Hty as [dv t' Hb Hc Heqv1 Heqv2 | t' Heqv | |]; subst;
        [destruct dv; cbn in Hb, Hwd; discriminate | discriminate].
    - exfalso; destruct Hinh as [v [Hty Hwd]];
        inversion Hty as [dv t' Hb Hc Heqv1 Heqv2 | t' Heqv | |]; subst;
        [destruct dv; cbn in Hb, Hwd; discriminate | discriminate].
    - exfalso; destruct Hinh as [v [Hty Hwd]];
        inversion Hty as [dv t' Hb Hc Heqv1 Heqv2 | t' Heqv | |]; subst;
        [destruct dv; cbn in Hb, Hwd; discriminate | discriminate].
    - exfalso; destruct Hinh as [v [Hty Hwd]];
        inversion Hty as [dv t' Hb Hc Heqv1 Heqv2 | t' Heqv | |]; subst;
        [destruct dv; cbn in Hb, Hwd; discriminate | discriminate].
    - exfalso; destruct Hinh as [v [Hty Hwd]];
        inversion Hty as [dv t' Hb Hc Heqv1 Heqv2 | t' Heqv | |]; subst;
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
          { clear Hwd Hnp IH Hty; revert u Hu.
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
          -- rewrite repeat_length, Esz; reflexivity.
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
    intros n dt; apply default_draw_val_wf.
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
        match classify_ow_event e in ow_event_class Y return (Y -> itree OW_E R) -> itree Det_OW_E R with
        | OWC_Draw dt => fun k' =>
            Tau (run_draws (shift_draw_strat sigma) (k' (sigma 0%nat dt)))
        | OWC_PureIntIntrinsic op w args => fun k' =>
            match pure_int_intrinsic_fn op w args with
            | raise_ret rv => Tau (run_draws sigma (k' rv))
            | raise_ub _ => Vis (@subevent UBE Det_OW_E _ void (ThrowUB tt)) void_elim
            | raise_oom _ => Vis (@subevent OOME Det_OW_E _ void (ThrowOOM tt)) void_elim
            | raise_error _ => Vis (@subevent FailureE Det_OW_E _ void (Throw tt)) void_elim
            end
        | OWC_Det _ de' => fun k' =>
            Vis de' (fun x => run_draws sigma (k' x))
        end k
    end.

  Lemma observe_run_draws {R : Type}
    (sigma : draw_strat) (t : itree OW_E R) :
    observe (run_draws sigma t) =
    match observe t with
    | RetF r => RetF r
    | TauF t' => TauF (run_draws sigma t')
    | VisF _ e k =>
        match classify_ow_event e in ow_event_class Y return (Y -> itree OW_E R) -> itree' Det_OW_E R with
        | OWC_Draw dt => fun k' =>
            TauF (run_draws (shift_draw_strat sigma) (k' (sigma 0%nat dt)))
        | OWC_PureIntIntrinsic op w args => fun k' =>
            match pure_int_intrinsic_fn op w args with
            | raise_ret rv => TauF (run_draws sigma (k' rv))
            | raise_ub _ => VisF (@subevent UBE Det_OW_E _ void (ThrowUB tt)) void_elim
            | raise_oom _ => VisF (@subevent OOME Det_OW_E _ void (ThrowOOM tt)) void_elim
            | raise_error _ => VisF (@subevent FailureE Det_OW_E _ void (Throw tt)) void_elim
            end
        | OWC_Det _ de' => fun k' =>
            VisF de' (fun x => run_draws sigma (k' x))
        end k
    end.
  Proof using Type.
    unfold observe at 1; cbn; destruct (observe t) as [r | t' | X e k]; [reflexivity | reflexivity |].
    destruct (classify_ow_event e) as [dt | op w args | X' de']; [reflexivity | destruct (pure_int_intrinsic_fn op w args); reflexivity | reflexivity].
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
    match e1 with
    | inl1 c1 =>
        match e2 with inl1 c2 => sync_call r c1 k1 c2 k2 | inr1 _ => False end
    | inr1 e1 =>
        match e2 with
        | inl1 _ => False
        | inr1 e2 =>
            match e1 with
            | inl1 ec1 =>
                match e2 with inl1 ec2 => sync_extcall r ec1 k1 ec2 k2 | inr1 _ => False end
            | inr1 e1 =>
                match e2 with
                | inl1 _ => False
                | inr1 e2 =>
                    match e1 with
                    | inl1 ic1 =>
                        match e2 with inl1 ic2 => sync_intrinsic r ic1 k1 ic2 k2 | inr1 _ => False end
                    | inr1 e1 =>
                        match e2 with
                        | inl1 _ => False
                        | inr1 e2 =>
                            match e1 with
                            | inl1 g1 =>
                                match e2 with inl1 g2 => sync_global r g1 k1 g2 k2 | inr1 _ => False end
                            | inr1 e1 =>
                                match e2 with
                                | inl1 _ => False
                                | inr1 e2 =>
                                    match e1 with
                                    | inl1 s1 =>
                                        match e2 with inl1 s2 => sync_stack r s1 k1 s2 k2 | inr1 _ => False end
                                    | inr1 e1 =>
                                        match e2 with
                                        | inl1 _ => False
                                        | inr1 e2 =>
                                            match e1 with
                                            | inl1 m1 =>
                                                match e2 with inl1 m2 => sync_memory r m1 k1 m2 k2 | inr1 _ => False end
                                            | inr1 e1 =>
                                                match e2 with
                                                | inl1 _ => False
                                                | inr1 e2 =>
                                                    match e1 with
                                                    | inl1 o1 =>
                                                        match e2 with inl1 o2 => sync_oom r o1 k1 o2 k2 | inr1 _ => False end
                                                    | inr1 e1 =>
                                                        match e2 with
                                                        | inl1 _ => False
                                                        | inr1 e2 =>
                                                            match e1 with
                                                            | inl1 x1 =>
                                                                match e2 with inl1 x2 => sync_llvmexc r x1 k1 x2 k2 | inr1 _ => False end
                                                            | inr1 e1 =>
                                                                match e2 with
                                                                | inl1 _ => False
                                                                | inr1 e2 =>
                                                                    match e1 with
                                                                    | inl1 u1 =>
                                                                        match e2 with inl1 u2 => sync_ub r u1 k1 u2 k2 | inr1 _ => False end
                                                                    | inr1 e1 =>
                                                                        match e2 with
                                                                        | inl1 _ => False
                                                                        | inr1 e2 =>
                                                                            match e1 with
                                                                            | inl1 d1 =>
                                                                                match e2 with inl1 d2 => sync_debug r d1 k1 d2 k2 | inr1 _ => False end
                                                                            | inr1 f1 =>
                                                                                match e2 with inl1 _ => False | inr1 f2 => sync_failure r f1 k1 f2 k2 end
                                                                            end
                                                                        end
                                                                    end
                                                                end
                                                            end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end
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

  Lemma det_vis_both_refl {R1 R2 : Type}
    (r : itree Det_OW_E R1 -> itree Det_OW_E R2 -> Prop)
    {X : Type} (e : Det_OW_E X)
    (k1 : X -> itree Det_OW_E R1) (k2 : X -> itree Det_OW_E R2)
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
          destruct (observe t3) as [| m3_ |]; try contradiction.
          exfalso; exact (Hnt3 m3_ eq_refl).
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
      clear Hot1; punfold H12; revert t3 H23 Hnt1.
      induction H12 as [t1_ t2_ Hs12 | t1_ m t2_ Ho1 _ _ | t1_ t2_ m2 Ho2 _ IH12];
        intros t3 H23 Hnt1.
      + destruct (observe t1_) as [y1 | m | Y1 ev kv] eqn:Ho1_;
          [| exfalso; exact (Hnt1 m eq_refl) |].
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
      clear Hot1; punfold H12; revert t3 H23 Hnt1.
      induction H12 as [t1_ t2_ Hs12 | t1_ m t2_ Ho1 _ _ | t1_ t2_ m2 Ho2 _ IH12];
        intros t3 H23 Hnt1.
      + destruct (observe t1_) as [y1 | m | Y1 ev kv] eqn:Ho1_;
          [| exfalso; exact (Hnt1 m eq_refl) |].
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
    - destruct (classify_ow_event e) as [dt | op w args | X' de'].
      + right; rewrite (Heq 0%nat dt).
        apply CIH; intros n d; exact (Heq (S n) d).
      + destruct (pure_int_intrinsic_fn op w args) as [| | | rv];
          [right; apply det_vis_both_refl; intros []
          | right; apply det_vis_both_refl; intros []
          | right; apply det_vis_both_refl; intros []
          | right; exact (CIH s1 s2 (k rv) Heq)].
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
    { rewrite observe_run_draws, observe_bind.
      assert (Ho_draw : observe (ow_draw dt) =
                        VisF (@subevent DrawE OW_E _ dvalue (Draw dt)) (fun x => Ret x))
        by reflexivity.
      rewrite Ho_draw;
        cbn [classify_ow_event subevent resum ReSum_id ReSum_sum ReSum_inl ReSum_inr cat Cat_IFun inl_ inr_ Inl_sum1 Inr_sum1 id_ Id_IFun].
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
      by (eapply det_ref_obs_eq; [exact Ho_src | | exact Hdet'];
          rewrite observe_run_draws; reflexivity).
    pose proof (det_ref_ret_ret_inv dvalue_refines _ _ Hdet'') as Hdv.
    destruct Hdv as [Hpsn | Heq]; [discriminate Hpsn |].
    unfold v1 in Heq; apply dvalue_base_I_same_sz_inj in Heq as Hi.
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
    rewrite Hi in Hu1; rewrite Hu0 in Hu1; discriminate Hu1.
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
          assert (Ho_tgt_ret :
            observe (run_draws sigma_tgt (Ret (DVALUE_Base (@DVALUE_I Pa sz (@Integers.mone sz))))) =
            RetF (DVALUE_Base (@DVALUE_I Pa sz (@Integers.mone sz))))
            by reflexivity.
          rewrite observe_run_draws_bind_ret, observe_run_draws, Ho_tgt_ret.
          unfold v0, eval_iop; rewrite eval_iop_integer_base_same_width; cbn.
          rewrite @Integers.or_mone; right; reflexivity.
    - exists sigma_tgt; split; [exact Hwft |].
      pstep; apply DR_Step; unfold det_step_body.
      rewrite !observe_run_draws, observe_bind; unfold ow_freeze; rewrite observe_freeze_i_defined; cbn iota.
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
      cfg_steps_to_ret sigma env t sigma' env' r
  | CSR_PureIntrinsic sigma env (t : CFGtop R) dt fname args va op w rv
      (k : exc + dvalue -> CFGtop R) sigma' env' r :
      observe t = VisF (@subevent IntrinsicE CFGEtop _ (exc + dvalue) (Intrinsic dt fname args va)) k ->
      parse_pure_int_intrinsic fname = Some (op, w) ->
      pure_int_intrinsic_fn op w args = raise_ret rv ->
      cfg_steps_to_ret sigma env (k rv) sigma' env' r ->
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
      cfg_steps_to_ub sigma env t
  | CSU_PureIntrinsic sigma env (t : CFGtop R) dt fname args va op w rv
      (k : exc + dvalue -> CFGtop R) :
      observe t = VisF (@subevent IntrinsicE CFGEtop _ (exc + dvalue) (Intrinsic dt fname args va)) k ->
      parse_pure_int_intrinsic fname = Some (op, w) ->
      pure_int_intrinsic_fn op w args = raise_ret rv ->
      cfg_steps_to_ub sigma env (k rv) ->
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
      [apply CSR_Ret | eapply CSR_Tau | eapply CSR_LocalRead | eapply CSR_LocalWrite | eapply CSR_Draw | eapply CSR_PureIntrinsic];
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
      [eapply CSU_UB | eapply CSU_Tau | eapply CSU_LocalRead | eapply CSU_LocalWrite | eapply CSU_Draw | eapply CSU_PureIntrinsic];
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
      | s env t dt ke s_sh s' env' r Ho Hsh _ IH
      | s env t dt fn args va op w rv ke s' env' r Ho Ep Efn _ IH ].
    - eapply cfg_steps_to_ret_obs; [symmetry; rewrite observe_bind, Ho; reflexivity | exact H2].
    - eapply CSR_Tau; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply CSR_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact (IH H2)].
    - eapply CSR_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply CSR_Draw; [rewrite observe_bind, Ho; reflexivity | exact Hsh | exact (IH H2)].
    - eapply CSR_PureIntrinsic; [rewrite observe_bind, Ho; reflexivity | exact Ep | exact Efn | exact (IH H2)].
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
      | s env t dt ke s_sh Ho Hsh _ IH
      | s env t dt fn args va op w rv ke Ho Ep Efn _ IH ].
    - eapply CSU_UB; rewrite observe_bind, Ho; reflexivity.
    - eapply CSU_Tau; [rewrite observe_bind, Ho; reflexivity | exact IH].
    - eapply CSU_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact IH].
    - eapply CSU_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact IH].
    - eapply CSU_Draw; [rewrite observe_bind, Ho; reflexivity | exact Hsh | exact IH].
    - eapply CSU_PureIntrinsic; [rewrite observe_bind, Ho; reflexivity | exact Ep | exact Efn | exact IH].
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
      | s env t dt ke s_sh s' env' r Ho Hsh _ IH
      | s env t dt fn args va op w rv ke s' env' r Ho Ep Efn _ IH ].
    - eapply cfg_steps_to_ub_obs; [symmetry; rewrite observe_bind, Ho; reflexivity | exact H2].
    - eapply CSU_Tau; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply CSU_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact (IH H2)].
    - eapply CSU_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
    - eapply CSU_Draw; [rewrite observe_bind, Ho; reflexivity | exact Hsh | exact (IH H2)].
    - eapply CSU_PureIntrinsic; [rewrite observe_bind, Ho; reflexivity | exact Ep | exact Efn | exact (IH H2)].
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
      | s env t dt ke s_sh Ho Hsh Hsub _
      | s env t dt fn args va op w rv ke Ho Ep Efn _ IH ];
      intros s2 Heq.
    - eapply CSU_UB; exact Ho.
    - eapply CSU_Tau; [exact Ho | exact (IH s2 Heq)].
    - eapply CSU_LocalRead; [exact Ho | exact Hf | exact (IH s2 Heq)].
    - eapply CSU_LocalWrite; [exact Ho | exact (IH s2 Heq)].
    - eapply CSU_Draw.
      + exact Ho.
      + intros n d; unfold shift_draw_strat in *; rewrite <- (Heq (S n) d); exact (Hsh n d).
      + rewrite <- (Heq 0%nat dt); exact Hsub.
    - eapply CSU_PureIntrinsic; [exact Ho | exact Ep | exact Efn | exact (IH s2 Heq)].
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
      | s env t dt ke s_sh Ho Hsh _ IH
      | s env t dt fn args va op w rv ke Ho Ep Efn _ IH ];
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
    - eapply det_ref_tau_l; [| exact (IH t2)].
      rewrite observe_run_draws, observe_run_cfg_locals, Ho; cbn; rewrite Ep, Efn; reflexivity.
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
      | s env t dt ke s_sh s' env' r Ho1 Hsh _ IH1
      | s env t dt fn args va op w rv ke s' env' r Ho1 Ep1 Efn1 _ IH1 ].
    - induction H2 as
        [ sb eb tb rb Ho2
        | sb eb tb tb' sb' eb' rb Ho2 _ IH2
        | sb eb tb id dv ke sb' eb' rb Ho2 Hf _ IH2
        | sb eb tb id dv ke sb' eb' rb Ho2 _ IH2
        | sb eb tb dt ke s_sh sb' eb' rb Ho2 Hsh _ IH2
        | sb eb tb dt fn args va op w rv ke sb' eb' rb Ho2 Ep2 Efn2 _ IH2 ].
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
      + eapply det_ref_tau_r; [| exact (IH2 Hrr)].
        rewrite observe_run_draws, observe_run_cfg_locals, Ho2; cbn; rewrite Ep2, Efn2; reflexivity.
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
    - eapply det_ref_tau_l; [| exact (IH1 Hrr)].
      rewrite observe_run_draws, observe_run_cfg_locals, Ho1; cbn; rewrite Ep1, Efn1; reflexivity.
  Qed.

End OpenWorldEvents.
#[export] Hint Resolve det_ref__mon : paco.

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
  - rewrite IH; split; [intros H; right; exact H | intros [-> | H]; [
      assert (Hr : raw_id_eqb r r = true) by (apply raw_id_eqb_eq; reflexivity);
      rewrite Hr in E; discriminate | exact H]].
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

Inductive pure_int_intrinsic_call_args : Set :=
| PIICA_Binop (op : pure_int_intrinsic_op) (w : positive) (a0 a1 : exp dtyp)
| PIICA_Abs (w : positive) (a0 : exp dtyp) (is_int_min_poison : bool).

Definition parse_imm_bool_arg (e : exp dtyp) : option bool :=
  match e with
  | EXP_Bool b => Some b
  | EXP_Integer z =>
      let v := denote_int_syntax z in
      if Z.eqb v 0%Z then Some false
      else if Z.eqb v 1%Z then Some true
      else None
  | _ => None
  end.

Definition match_pure_int_intrinsic_call (ins : instr dtyp)
  : option pure_int_intrinsic_call_args :=
  match ins with
  | INSTR_Call (DTYPE_Base (DTYPE_I w), EXP_Ident (ID_Global (Name fname))) args anns [] =>
      if list_empty_b (ann_fun_attributes anns) &&
         list_empty_b (ann_ret_attributes anns) then
        match parse_pure_int_intrinsic fname with
        | Some (PII_Abs, w') =>
            if Pos.eqb w w' then
              match args with
              | [((DTYPE_Base (DTYPE_I w0), a0), []); ((DTYPE_Base (DTYPE_I 1%positive), a1), [])] =>
                  if Pos.eqb w0 w then
                    match parse_imm_bool_arg a1 with
                    | Some flag => Some (PIICA_Abs w a0 flag)
                    | None => None
                    end
                  else None
              | _ => None
              end
            else None
        | Some (op, w') =>
            if Pos.eqb w w' then
              match args with
              | [((DTYPE_Base (DTYPE_I w0), a0), []); ((DTYPE_Base (DTYPE_I w1), a1), [])] =>
                  if Pos.eqb w0 w && Pos.eqb w1 w then
                    Some (PIICA_Binop op w a0 a1)
                  else None
              | _ => None
              end
            else None
        | None => None
        end
      else None
  | _ => None
  end.

Definition instr_param_uses (params defs : list raw_id) (ins : instr dtyp) : list (nat * dtyp) :=
  match ins with
  | INSTR_Op e => exp_param_uses params defs None e
  | _ =>
      match match_pure_int_intrinsic_call ins with
      | Some (PIICA_Binop _ w a0 a1) =>
          exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a0 ++
          exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a1
      | Some (PIICA_Abs w a0 _) =>
          exp_param_uses params defs (Some (DTYPE_Base (DTYPE_I w))) a0
      | None => []
      end
  end.

Definition block_param_uses (params defs : list raw_id) (b : block dtyp)
  : list (nat * dtyp) :=
  List.flat_map (fun '(_, Phi _ dt pargs, _) =>
    List.flat_map (fun '(_, e) => exp_param_uses params defs (Some dt) e) pargs)
    (blk_phis b) ++
  List.flat_map (fun '(_, ins, _) => instr_param_uses params defs ins) (blk_code b) ++
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
  intros t1 t2; unfold dtyp_eqb_dec; destruct (dtyp_eq_dec t1 t2) as [Heq | Hne];
    [split; [intros _; exact Heq | intros _; reflexivity]
    | split; [discriminate | intros Heq; contradiction (Hne Heq)]].
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
      assert (Hr : param_use_eqb u u = true) by (apply param_use_eqb_eq; reflexivity);
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


