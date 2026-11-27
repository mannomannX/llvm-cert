(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Dead Code & Dead Phi Elimination Pure Safety ([CertPasses.DCESafety])

    Purpose:
      Proves pure [EOU] safety and scalar runtime typing ([dvalue_has_dtyp]) for
      constants, arithmetic, comparisons, conversions, select, GEP, and attrs,
      plus [env_agree_on], [tenv_sound], and [left_evals_to] combinators for
      [CertPasses.DCESpec].

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml (re-exported by [CertPasses.DCE]
      for downstream simulation proofs).

    Assumptions:
      Depends on Stdlib, Paco, ITree, ExtLib, Vellvm, [CertPasses.PassCommon],
      and [CertPasses.DCESpec]; zero custom axioms (parameterized over
      [IP : IPtr] and [IPT : @IPtrTheory IP]).

    Section Outline:
      (5) Pure [EOU] safety, [dvalue_has_dtyp] inversions, & op typing;
      (6) [env_agree_on], [tenv_sound], [withCall] equations, & [left_evals_to]
      combinators. *)

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
  Structures.Monads.

From Vellvm Require Import
  Numeric
  Utils
  Syntax
  Semantics
  Semantics.VellvmIntegers
  Semantics.VellvmFloats
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
  Semantics.Implementations.Memory
  Semantics.Handlers
  Semantics.InterpretationStack
  Semantics.TopLevel
  Semantics.Libraries.

From CertPasses Require Import PassCommon.
Import Logic.
From CertPasses Require Import DCESpec.

Set Default Goal Selector "!".
Unset Implicit Arguments.

(** * 5. Pure [EOU] Safety & Scalar Runtime Typing Lemmas *)

Section DCESoundness.
  Context {IP : IPtr} {IPT : @IPtrTheory IP}.

  #[local] Notation PaV := (@ParamsV IP IPT).
  #[local] Hint Resolve cfg_local_sim__mon : paco.

  Lemma dvalue_ind_nested (P : @dvalue PaV -> Prop)
    (HBase : forall db : @dvalue_base PaV, P (DVALUE_Base db))
    (HStruct : forall (p : bool) (fs : list (@dvalue PaV)),
        Forall P fs -> P (DVALUE_Struct p fs))
    (HArray : forall (v : bool) (es : list (@dvalue PaV)),
        Forall P es -> P (DVALUE_Array v es)) :
    forall dv : @dvalue PaV, P dv.
  Proof.
    exact
      (fix IH (dv : @dvalue PaV) {struct dv} : P dv :=
         let fix go (l : list (@dvalue PaV)) {struct l} : Forall P l :=
           match l with
           | [] => Forall_nil _
           | x :: xs => @Forall_cons (@dvalue PaV) P x xs (IH x) (go xs)
           end
         in
         match dv with
         | DVALUE_Base db => HBase db
         | DVALUE_Struct p fs => HStruct p fs (go fs)
         | DVALUE_Array v es => HArray v es (go es)
         end).
  Qed.

  Lemma is_i1_dtyp_eq (dt : dtyp) :
    is_i1_dtyp dt = true -> dt = DTYPE_Base (DTYPE_I 1%positive).
  Proof.
    destruct dt as [dtb | |]; [| discriminate | discriminate].
    destruct dtb as [sz | | | | | | | | | |]; try discriminate.
    destruct sz as [p | p |]; try discriminate; reflexivity.
  Qed.

  Lemma is_ptr_dtyp_eq (dt : dtyp) :
    is_ptr_dtyp dt = true -> dt = DTYPE_Base DTYPE_Pointer.
  Proof.
    destruct dt as [dtb | |]; [| discriminate | discriminate].
    destruct dtb; try discriminate; reflexivity.
  Qed.

  Lemma is_int_dtyp_inv (dt : dtyp) :
    is_int_dtyp dt = true -> exists sz : positive, dt = DTYPE_Base (DTYPE_I sz).
  Proof.
    destruct dt as [dtb | |]; [| discriminate | discriminate].
    destruct dtb as [sz | | | | | | | | | |]; try discriminate.
    intros _; exists sz; reflexivity.
  Qed.

  Lemma is_fp_dtyp_inv (dt : dtyp) :
    is_fp_dtyp dt = true ->
    dt = DTYPE_Base (DTYPE_FP FP_float) \/ dt = DTYPE_Base (DTYPE_FP FP_double).
  Proof.
    destruct dt as [dtb | |]; [| discriminate | discriminate].
    destruct dtb as [| | | | fp | | | | | |]; try discriminate.
    destruct fp; try discriminate; intros _; [left | right]; reflexivity.
  Qed.

  Lemma check_any_guarantees_scalar (te : ty_env) (e : exp dtyp) :
    forall dt0 : dtyp,
      check_any_texp te dt0 e = true ->
      guarantees_scalar_dtyp te dt0 e = true ->
      check_scalar_texp te dt0 e = true.
  Proof.
    induction e using exp_ind_nested; intros dt0 Hany Hguar;
      cbn [check_any_texp] in Hany;
      lazymatch goal with
      | H : ?G |- ?G => exact H
      | _ => idtac
      end.
    - (* EXP_Float *)
      cbn [guarantees_scalar_dtyp] in Hguar.
      apply andb_true_iff in Hguar as [Hsc _].
      cbn [check_scalar_texp]; rewrite Hsc; exact Hany.
    - (* OP_Conversion *)
      destruct conv as [| pc | ic]; [| exact Hany | exact Hany].
      apply andb_true_iff in Hany as [Heq12 Hany1].
      cbn [guarantees_scalar_dtyp] in Hguar; rewrite Heq12 in Hguar.
      apply andb_true_iff in Hguar as [Hsc Hg].
      apply andb_true_iff in Hg as [Heq2 Hg1].
      cbn [check_scalar_texp]; rewrite Hsc, Heq2, Heq12, (IHe _ Hany1 Hg1).
      reflexivity.
    - (* OP_Select *)
      apply andb_true_iff in Hany as [Ha Hany2].
      apply andb_true_iff in Ha as [Ha Hany1].
      apply andb_true_iff in Ha as [Hi1 Hsc_c].
      cbn [guarantees_scalar_dtyp] in Hguar.
      apply andb_true_iff in Hguar as [Hsc Hg].
      apply andb_true_iff in Hg as [Hg Hg2].
      apply andb_true_iff in Hg as [Hg Hg1].
      apply andb_true_iff in Hg as [Hg _].
      apply andb_true_iff in Hg as [Hg Heq2].
      apply andb_true_iff in Hg as [_ Heq1].
      cbn [check_scalar_texp].
      rewrite Hsc, Hi1, Heq1, Heq2, Hsc_c,
              (IHe2 _ Hany1 Hg1), (IHe3 _ Hany2 Hg2).
      reflexivity.
  Qed.

  (** ** Pure [EOU] Predicates *)

  Definition eou_safe {X : Type} (P : X -> Prop) (m : EOU X) : Prop :=
    match m with
    | raise_ub _ => True
    | raise_ret x => P x
    | raise_error _ | raise_oom _ => False
    end.

  Definition eou_ret_imp {X : Type} (P : X -> Prop) (m : EOU X) : Prop :=
    match m with
    | raise_ret x => P x
    | _ => True
    end.

  Lemma fmap_EOU_ret {A B : Type} (f : A -> B) (x : A) :
    (f <$> (raise_ret x : EOU A)) = raise_ret (f x).
  Proof. reflexivity. Qed.

  Lemma bind_EOU_ret {A B : Type} (x : A) (k : A -> EOU B) :
    ExtLib.Structures.Monad.bind (raise_ret x : EOU A) k = k x.
  Proof. reflexivity. Qed.

  Lemma eou_safe_to_ret_imp {X : Type} (P : X -> Prop) (m : EOU X) :
    eou_safe P m -> eou_ret_imp P m.
  Proof.
    destruct m; cbn; intuition.
  Qed.

  Lemma eou_safe_weaken {X : Type} (P Q : X -> Prop) (m : EOU X) :
    (forall x, P x -> Q x) -> eou_safe P m -> eou_safe Q m.
  Proof.
    intros HPQ; destruct m; cbn; auto.
  Qed.

  Lemma eou_ret_imp_weaken {X : Type} (P Q : X -> Prop) (m : EOU X) :
    (forall x, P x -> Q x) -> eou_ret_imp P m -> eou_ret_imp Q m.
  Proof.
    intros HPQ; destruct m; cbn; auto.
  Qed.

  Lemma eou_safe_fmap {A B : Type} (f : A -> B) (P : B -> Prop) (m : EOU A) :
    eou_safe (fun a => P (f a)) m ->
    eou_safe P (f <$> m).
  Proof.
    destruct m; cbn; auto.
  Qed.

  Lemma eou_ret_imp_fmap {A B : Type} (f : A -> B) (P : B -> Prop) (m : EOU A) :
    eou_ret_imp (fun a => P (f a)) m ->
    eou_ret_imp P (f <$> m).
  Proof.
    destruct m; cbn; auto.
  Qed.

  Lemma eou_ret_imp_vec_poison_l
    (f : @dvalue_base PaV -> @dvalue_base PaV -> EOU (@dvalue_base PaV))
    (HF : forall y, eou_ret_imp (fun b => b = DVALUE_Poison) (f DVALUE_Poison y))
    (dt : dtyp) (elts : list (@dvalue PaV)) :
    eou_ret_imp
      (fun v => dvalue_has_dtyp v dt)
      (ExtLib.Structures.Monad.bind (map_monad (@dvalue_to_dvalue_base PaV) elts)
         (fun elts' =>
            ExtLib.Structures.Monad.bind
              (vec_loop f (List.combine (repeat (@DVALUE_Poison PaV) (Datatypes.length elts')) elts'))
              (fun ans =>
                 ExtLib.Structures.Monad.ret (@canonicalize_vector PaV (List.map (@DVALUE_Base PaV) ans))))).
  Proof.
    destruct (map_monad (@dvalue_to_dvalue_base PaV) elts) as [| | | elts'];
      [exact I | exact I | exact I | cbn [ExtLib.Structures.Monad.bind EOU_monad]].
    assert (Hloop :
      eou_ret_imp (Forall (fun b => b = @DVALUE_Poison PaV))
        (vec_loop f (List.combine (repeat (@DVALUE_Poison PaV) (Datatypes.length elts')) elts'))).
    { unfold vec_loop.
      induction elts' as [| y ys IH];
        cbn [Datatypes.length repeat List.combine monad_fold_right
             ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad].
      - cbn [eou_ret_imp]; constructor.
      - destruct (monad_fold_right _ (List.combine (repeat (@DVALUE_Poison PaV) (Datatypes.length ys)) ys) [])
          as [| | | acc];
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad eou_ret_imp] in IH |- *; try exact I.
        specialize (HF y).
        destruct (f DVALUE_Poison y) as [| | | r];
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad eou_ret_imp] in HF |- *; try exact I.
        constructor; [exact HF | exact IH]. }
    destruct (vec_loop f (List.combine (repeat (@DVALUE_Poison PaV) (Datatypes.length elts')) elts'))
      as [| | | ans];
      cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret EOU_monad eou_ret_imp] in Hloop |- *; try exact I.
    rewrite (@canonicalize_vector_all_poison_base PaV ans Hloop).
    apply DVALUE_Poison_typ_agg.
  Qed.

  (** ** [dvalue_has_dtyp] Constructors & Inversions *)

  Lemma dvalue_has_dtyp_Poison (dt : dtyp) :
    @dvalue_has_dtyp PaV (DVALUE_Base DVALUE_Poison) dt.
  Proof. apply DVALUE_Poison_typ_agg. Qed.

  Lemma dvalue_has_dtyp_I (sz : positive) (i : @bit_int sz) :
    @dvalue_has_dtyp PaV (DVALUE_Base (@DVALUE_I PaV sz i)) (DTYPE_Base (DTYPE_I sz)).
  Proof.
    apply DVALUE_Base_typ; [apply Pos.eqb_refl | reflexivity].
  Qed.

  Lemma dvalue_has_dtyp_Ptr (p : @ptr (@PROV PaV) (@PTR PaV)) :
    @dvalue_has_dtyp PaV (DVALUE_Base (DVALUE_Pointer p)) (DTYPE_Base DTYPE_Pointer).
  Proof.
    apply DVALUE_Base_typ; reflexivity.
  Qed.

  Lemma dvalue_has_dtyp_Float (f : ll_float) :
    @dvalue_has_dtyp PaV (DVALUE_Base (DVALUE_Float f)) (DTYPE_Base (DTYPE_FP FP_float)).
  Proof.
    apply DVALUE_Base_typ; reflexivity.
  Qed.

  Lemma dvalue_has_dtyp_Double (d : ll_double) :
    @dvalue_has_dtyp PaV (DVALUE_Base (DVALUE_Double d)) (DTYPE_Base (DTYPE_FP FP_double)).
  Proof.
    apply DVALUE_Base_typ; reflexivity.
  Qed.

  Lemma dvalue_has_dtyp_I_inv (v : @dvalue PaV) (sz : positive) :
    dvalue_has_dtyp v (DTYPE_Base (DTYPE_I sz)) ->
    v = DVALUE_Base DVALUE_Poison \/
    exists i : @bit_int sz, v = DVALUE_Base (@DVALUE_I PaV sz i).
  Proof.
    intros H; inversion H as [db t Hb _ | | |]; subst; [| left; reflexivity].
    destruct db as [p | sz' i | ip | d | f | | | bsz bv]; cbn in Hb; try discriminate Hb.
    - apply Pos.eqb_eq in Hb; subst sz'; right; exists i; reflexivity.
    - left; reflexivity.
  Qed.

  Lemma dvalue_has_dtyp_Ptr_inv (v : @dvalue PaV) :
    dvalue_has_dtyp v (DTYPE_Base DTYPE_Pointer) ->
    v = DVALUE_Base DVALUE_Poison \/
    exists p : @ptr (@PROV PaV) (@PTR PaV), v = DVALUE_Base (DVALUE_Pointer p).
  Proof.
    intros H; inversion H as [db t Hb _ | | |]; subst; [| left; reflexivity].
    destruct db as [p | sz' i | ip | d | f | | | bsz bv]; cbn in Hb; try discriminate Hb.
    - right; exists p; reflexivity.
    - left; reflexivity.
  Qed.

  Lemma dvalue_has_dtyp_Float_inv (v : @dvalue PaV) :
    dvalue_has_dtyp v (DTYPE_Base (DTYPE_FP FP_float)) ->
    v = DVALUE_Base DVALUE_Poison \/
    exists f : ll_float, v = DVALUE_Base (DVALUE_Float f).
  Proof.
    intros H; inversion H as [db t Hb _ | | |]; subst; [| left; reflexivity].
    destruct db as [p | sz' i | ip | d | f | | | bsz bv]; cbn in Hb; try discriminate Hb.
    - right; exists f; reflexivity.
    - left; reflexivity.
  Qed.

  Lemma dvalue_has_dtyp_Double_inv (v : @dvalue PaV) :
    dvalue_has_dtyp v (DTYPE_Base (DTYPE_FP FP_double)) ->
    v = DVALUE_Base DVALUE_Poison \/
    exists d : ll_double, v = DVALUE_Base (DVALUE_Double d).
  Proof.
    intros H; inversion H as [db t Hb _ | | |]; subst; [| left; reflexivity].
    destruct db as [p | sz' i | ip | d | f | | | bsz bv]; cbn in Hb; try discriminate Hb.
    - right; exists d; reflexivity.
    - left; reflexivity.
  Qed.

  Lemma dvalue_has_dtyp_scalar_base_inv (v : @dvalue PaV) (dt : dtyp) :
    is_scalar_dtyp dt = true ->
    dvalue_has_dtyp v dt ->
    exists db : @dvalue_base PaV,
      v = DVALUE_Base db /\
      (db = DVALUE_Poison \/
       (forall bsz bv, db <> @DVALUE_B PaV bsz bv)).
  Proof.
    intros Hsc Hty.
    destruct dt as [dtb | |]; [| discriminate Hsc | discriminate Hsc].
    cbn [is_scalar_dtyp] in Hsc.
    inversion Hty as [db t Hb _ | | |]; subst.
    - exists db; split; [reflexivity |].
      destruct db as [p | sz i | ip | d | f | | | bsz bv];
        try (right; intros ? ? Hc; discriminate Hc).
      destruct dtb as [| | | | fp | | | | | |]; try discriminate Hsc;
        try (destruct fp; try discriminate Hsc); cbn in Hb; discriminate Hb.
    - exists DVALUE_Poison; split; [reflexivity | left; reflexivity].
  Qed.

  (** ** Constants, Arithmetic, Comparisons, Conversions, Select, GEP, & Attrs *)

  Lemma denote_int_syntax_as_int_safe (dt : dtyp) (x : int_syntax) :
    is_int_dtyp dt = true ->
    exists (sz : positive) (i : @bit_int sz),
      dt = DTYPE_Base (DTYPE_I sz) /\
      @denote_int_syntax_as_int PaV dt x = raise_ret (DVALUE_Base (@DVALUE_I PaV sz i)).
  Proof.
    intros Hint.
    destruct (is_int_dtyp_inv dt Hint) as [sz ->].
    exists sz, (@Integers.repr sz (denote_int_syntax x)).
    split; [reflexivity | reflexivity].
  Qed.

  Lemma denote_float_syntax_safe (dt : dtyp) (f : float_syntax) :
    is_valid_float_lit dt f = true ->
    eou_safe (fun v => dvalue_has_dtyp v dt) (@denote_float_syntax_as_float PaV dt f).
  Proof.
    intros Hfl.
    destruct dt as [dtb | |]; [| discriminate Hfl | discriminate Hfl].
    destruct dtb as [| | | | fp | | | | | |]; try discriminate Hfl.
    destruct fp; try discriminate Hfl; cbn in Hfl |- *.
    - destruct (float32_of_float_syntax f) as [fl |]; [| discriminate Hfl].
      cbn; apply dvalue_has_dtyp_Float.
    - destruct (float_of_float_syntax f) as [db |]; [| discriminate Hfl].
      cbn; apply dvalue_has_dtyp_Double.
  Qed.

  Lemma denote_float_syntax_ret_imp (dt : dtyp) (f : float_syntax) :
    is_fp_dtyp dt = true ->
    eou_ret_imp (fun v => dvalue_has_dtyp v dt) (@denote_float_syntax_as_float PaV dt f).
  Proof.
    intros Hfp.
    destruct (is_fp_dtyp_inv dt Hfp) as [-> | ->]; cbn.
    - destruct (float32_of_float_syntax f) as [fl |]; cbn;
        [apply dvalue_has_dtyp_Float | exact I].
    - destruct (float_of_float_syntax f) as [db |]; cbn;
        [apply dvalue_has_dtyp_Double | exact I].
  Qed.

  Lemma default_dvalue_scalar_safe (dt : dtyp) :
    is_scalar_dtyp dt = true ->
    exists dv : @dvalue PaV,
      @default_dvalue_of_dtyp PaV dt = raise_ret dv /\
      dvalue_has_dtyp dv dt /\
      (is_int_dtyp dt = true -> dv <> DVALUE_Base DVALUE_Poison).
  Proof.
    intros Hsc.
    destruct dt as [dtb | |]; [| discriminate Hsc | discriminate Hsc].
    cbn [is_scalar_dtyp] in Hsc.
    destruct dtb as [sz | | | | fp | | | | | |]; try discriminate Hsc.
    - eexists; split; [reflexivity |].
      split; [apply dvalue_has_dtyp_I | intros _ Hc; discriminate Hc].
    - eexists; split; [reflexivity |].
      split; [apply dvalue_has_dtyp_Ptr | intros H; discriminate H].
    - destruct fp; try discriminate Hsc.
      + eexists; split; [reflexivity |].
        split; [apply dvalue_has_dtyp_Float | intros H; discriminate H].
      + eexists; split; [reflexivity |].
        split; [apply dvalue_has_dtyp_Double | intros H; discriminate H].
  Qed.

  Lemma eval_int_op_bit_safe (sz : positive) (iop : ibinop) (x y : @bit_int sz) :
    eou_safe
      (fun db => dvalue_has_dtyp (DVALUE_Base db) (DTYPE_Base (DTYPE_I sz)))
      (@eval_int_op PaV (@bit_int sz) _ _ iop x y).
  Proof.
    destruct iop; unfold eval_int_op, dvp;
      cbn [madd msub mmul mdivs mmods mshl mnegative mbitwidth mdtyp_of_int
           bitwidth tdb VIntVMemInt VInt_Bounded ToDvalue_Int option_pred
           ExtLib.Structures.Monad.ret ExtLib.Structures.Monad.bind EOU_monad];
      repeat (
        rewrite ?fmap_EOU_ret, ?bind_EOU_ret;
        cbv zeta;
        first [ match goal with
                | |- context [dtyp_base_eq_dec ?a ?b] =>
                    destruct (dtyp_base_eq_dec a b); [discriminate |]
                | |- context [if ?b then _ else _] => destruct b
                | |- context [match ?x with None => _ | Some _ => _ end] =>
                    destruct x
                end ]
      );
      rewrite ?fmap_EOU_ret, ?bind_EOU_ret;
      cbn [eou_safe];
      first [exact I | apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_I].
  Qed.

  Lemma eval_iop_integer_base_I_I
    (iop : ibinop) (sz1 sz2 : positive) (i1 : @bit_int sz1) (i2 : @bit_int sz2)
    (Hsz : sz1 = sz2) :
    eou_safe
      (fun db => dvalue_has_dtyp (DVALUE_Base db) (DTYPE_Base (DTYPE_I sz1)))
      (@eval_iop_integer_base PaV iop (@DVALUE_I PaV sz1 i1) (@DVALUE_I PaV sz2 i2)).
  Proof.
    unfold eval_iop_integer_base.
    destruct (Pos.eq_dec sz1 sz2) as [Heq | Hne].
    - clear Hsz; subst; cbn [eq_rect eq_rect_r eq_sym].
      apply eval_int_op_bit_safe.
    - contradiction (Hne Hsz).
  Qed.

  Lemma eval_iop_safe (iop : ibinop) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    is_int_dtyp dt = true ->
    (match iop with SDiv _ | SRem => v2 <> DVALUE_Base DVALUE_Poison | _ => True end) ->
    dvalue_has_dtyp v1 dt ->
    dvalue_has_dtyp v2 dt ->
    eou_safe (fun v => dvalue_has_dtyp v dt) (@eval_iop PaV iop v1 v2).
  Proof.
    intros Hint Hnp Hv1 Hv2.
    destruct (is_int_dtyp_inv dt Hint) as [sz ->].
    destruct (dvalue_has_dtyp_I_inv v1 sz Hv1) as [-> | [i1 ->]];
      destruct (dvalue_has_dtyp_I_inv v2 sz Hv2) as [-> | [i2 ->]];
      cbn [eval_iop]; apply eou_safe_fmap.
    - (* Poison, Poison *)
      unfold eval_iop_integer_base; destruct (iop_is_div iop) eqn:Ediv; cbn;
        [ destruct iop; try discriminate Ediv;
            try (exfalso; apply Hnp; reflexivity); exact I
        | apply dvalue_has_dtyp_Poison].
    - (* Poison, I *)
      destruct iop; cbn;
        try (destruct (Z.eq_dec (@Integers.signed sz i2) (-1)%Z); cbn;
             [exact I | apply dvalue_has_dtyp_Poison]);
        apply dvalue_has_dtyp_Poison.
    - (* I, Poison *)
      unfold eval_iop_integer_base; destruct (iop_is_div iop); cbn;
        [exact I | apply dvalue_has_dtyp_Poison].
    - (* I, I *)
      exact (eval_iop_integer_base_I_I iop sz sz i1 i2 Logic.eq_refl).
  Qed.

  Lemma eval_iop_ret_imp (iop : ibinop) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    is_int_dtyp dt = true ->
    dvalue_has_dtyp v1 dt ->
    dvalue_has_dtyp v2 dt ->
    eou_ret_imp (fun v => dvalue_has_dtyp v dt) (@eval_iop PaV iop v1 v2).
  Proof.
    intros Hint Hv1 Hv2.
    destruct (is_int_dtyp_inv dt Hint) as [sz ->].
    destruct (dvalue_has_dtyp_I_inv v1 sz Hv1) as [-> | [i1 ->]];
      destruct (dvalue_has_dtyp_I_inv v2 sz Hv2) as [-> | [i2 ->]];
      cbn [eval_iop]; apply eou_ret_imp_fmap.
    - unfold eval_iop_integer_base; destruct (iop_is_div iop); cbn;
        [exact I | apply dvalue_has_dtyp_Poison].
    - destruct iop; cbn;
        try (destruct (Z.eq_dec (@Integers.signed sz i2) (-1)%Z); cbn;
             [exact I | apply dvalue_has_dtyp_Poison]);
        apply dvalue_has_dtyp_Poison.
    - unfold eval_iop_integer_base; destruct (iop_is_div iop); cbn;
        [exact I | apply dvalue_has_dtyp_Poison].
    - apply eou_safe_to_ret_imp, (eval_iop_integer_base_I_I iop sz sz i1 i2 Logic.eq_refl).
  Qed.

  Lemma eval_int_icmp_bit_safe
    (samesign : bool) (cmp : icmp) (sz : positive) (x y : @bit_int sz) :
    eou_safe
      (fun db => dvalue_has_dtyp (DVALUE_Base db) (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_int_icmp PaV (@bit_int sz) _ samesign cmp x y).
  Proof.
    destruct cmp; unfold eval_int_icmp, dvp;
      cbn [mdtyp_of_int bitwidth VIntVMemInt VInt_Bounded
           ExtLib.Structures.Monad.ret ExtLib.Structures.Monad.bind EOU_monad];
      try (destruct (dtyp_base_eq_dec (DTYPE_I sz) DTYPE_Iptr); [discriminate |]);
      cbn [ExtLib.Structures.Monad.bind EOU_monad eou_safe];
      repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      first [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_I].
  Qed.

  Lemma eval_int_icmp_any_ret_imp
    {Int : Type} `{VMI : VMemInt Int}
    (samesign : bool) (cmp : icmp) (x y : Int) :
    eou_ret_imp
      (fun db => dvalue_has_dtyp (DVALUE_Base db) (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_int_icmp PaV Int VMI samesign cmp x y).
  Proof.
    destruct cmp; unfold eval_int_icmp, dvp;
      cbn [ExtLib.Structures.Monad.ret ExtLib.Structures.Monad.bind EOU_monad];
      try (destruct (dtyp_base_eq_dec (@mdtyp_of_int Int VMI) DTYPE_Iptr); [exact I |]);
      cbn [ExtLib.Structures.Monad.bind EOU_monad eou_ret_imp];
      repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      first [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_I].
  Qed.

  Lemma eval_int_icmp_ptr_safe
    {Int : Type} `{VMI : VMemInt Int}
    (samesign : bool) (cmp : icmp) (x y : Int) :
    is_ptr_safe_icmp cmp = true ->
    eou_safe
      (fun db => dvalue_has_dtyp (DVALUE_Base db) (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_int_icmp PaV Int VMI samesign cmp x y).
  Proof.
    intros Hsafe; destruct cmp; try discriminate Hsafe;
      unfold eval_int_icmp, dvp;
      cbn [ExtLib.Structures.Monad.ret ExtLib.Structures.Monad.bind EOU_monad eou_safe];
      repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      first [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_I].
  Qed.

  Lemma eval_icmp_base_I_I
    (samesign : bool) (cmp : icmp) (sz1 sz2 : positive)
    (i1 : @bit_int sz1) (i2 : @bit_int sz2) (Hsz : sz1 = sz2) :
    eou_safe
      (fun db => dvalue_has_dtyp (DVALUE_Base db) (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_icmp_base PaV samesign cmp (@DVALUE_I PaV sz1 i1) (@DVALUE_I PaV sz2 i2)).
  Proof.
    unfold eval_icmp_base.
    destruct (Pos.eq_dec sz1 sz2) as [Heq | Hne].
    - clear Hsz; subst; cbn [eq_rect eq_rect_r eq_sym].
      apply eval_int_icmp_bit_safe.
    - contradiction (Hne Hsz).
  Qed.

  Lemma eval_icmp_safe
    (samesign : bool) (cmp : icmp) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    is_safe_icmp_ty cmp dt = true ->
    dvalue_has_dtyp v1 dt ->
    dvalue_has_dtyp v2 dt ->
    eou_safe
      (fun v => dvalue_has_dtyp v (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_icmp PaV samesign cmp v1 v2).
  Proof.
    intros Hsafe Hv1 Hv2; unfold is_safe_icmp_ty in Hsafe.
    destruct (is_int_dtyp dt) eqn:Eint.
    - destruct (is_int_dtyp_inv dt Eint) as [sz ->].
      destruct (dvalue_has_dtyp_I_inv v1 sz Hv1) as [-> | [i1 ->]];
        destruct (dvalue_has_dtyp_I_inv v2 sz Hv2) as [-> | [i2 ->]];
        cbn [eval_icmp]; apply eou_safe_fmap.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn; apply dvalue_has_dtyp_Poison.
      + exact (eval_icmp_base_I_I samesign cmp sz sz i1 i2 Logic.eq_refl).
    - destruct (is_ptr_dtyp dt) eqn:Eptr; [| discriminate Hsafe].
      rewrite (is_ptr_dtyp_eq dt Eptr) in Hv1, Hv2.
      destruct (dvalue_has_dtyp_Ptr_inv v1 Hv1) as [-> | [p1 ->]];
        destruct (dvalue_has_dtyp_Ptr_inv v2 Hv2) as [-> | [p2 ->]];
        cbn [eval_icmp]; apply eou_safe_fmap.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn; apply dvalue_has_dtyp_Poison.
      + unfold eval_icmp_base; apply eval_int_icmp_ptr_safe, Hsafe.
  Qed.

  Lemma eval_icmp_ret_imp
    (samesign : bool) (cmp : icmp) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    (is_int_dtyp dt || is_ptr_dtyp dt) = true ->
    dvalue_has_dtyp v1 dt ->
    eou_ret_imp
      (fun v => dvalue_has_dtyp v (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_icmp PaV samesign cmp v1 v2).
  Proof.
    intros Hty Hv1.
    apply orb_true_iff in Hty as [Eint | Eptr].
    - destruct (is_int_dtyp_inv dt Eint) as [sz ->].
      destruct (dvalue_has_dtyp_I_inv v1 sz Hv1) as [-> | [i1 ->]];
        destruct v2 as [db2 | | [|] elts2]; try exact I.
      + cbn [eval_icmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          unfold eval_icmp_base; cbn [is_icmp_operand];
          try exact I; apply dvalue_has_dtyp_Poison.
      + cbn [eval_icmp]; apply eou_ret_imp_vec_poison_l.
        intros y; destruct y; unfold eval_icmp_base;
          cbn [is_icmp_operand eou_ret_imp ExtLib.Structures.Monad.ret EOU_monad];
          first [reflexivity | exact I].
      + cbn [eval_icmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          unfold eval_icmp_base; cbn [is_icmp_operand];
          try exact I; try apply dvalue_has_dtyp_Poison.
        destruct (Pos.eq_dec sz sz2) as [Heq | _]; [| exact I].
        subst sz2; cbn [eq_rect eq_rect_r eq_sym].
        apply eou_safe_to_ret_imp, eval_int_icmp_bit_safe.
    - rewrite (is_ptr_dtyp_eq dt Eptr) in Hv1.
      destruct (dvalue_has_dtyp_Ptr_inv v1 Hv1) as [-> | [p1 ->]];
        destruct v2 as [db2 | | [|] elts2]; try exact I.
      + cbn [eval_icmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          unfold eval_icmp_base; cbn [is_icmp_operand];
          try exact I; apply dvalue_has_dtyp_Poison.
      + cbn [eval_icmp]; apply eou_ret_imp_vec_poison_l.
        intros y; destruct y; unfold eval_icmp_base;
          cbn [is_icmp_operand eou_ret_imp ExtLib.Structures.Monad.ret EOU_monad];
          first [reflexivity | exact I].
      + cbn [eval_icmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          unfold eval_icmp_base; cbn [is_icmp_operand];
          try exact I; try apply dvalue_has_dtyp_Poison.
        apply eval_int_icmp_any_ret_imp.
  Qed.

  Lemma eval_fop_safe (fop : fbinop) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    is_fp_dtyp dt = true ->
    is_safe_fbinop fop = true ->
    dvalue_has_dtyp v1 dt ->
    dvalue_has_dtyp v2 dt ->
    eou_safe (fun v => dvalue_has_dtyp v dt) (@eval_fop PaV fop v1 v2).
  Proof.
    intros Hfp Hsf Hv1 Hv2.
    destruct (is_fp_dtyp_inv dt Hfp) as [-> | ->].
    - destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
        destruct (dvalue_has_dtyp_Float_inv v2 Hv2) as [-> | [f2 ->]];
        cbn [eval_fop]; apply eou_safe_fmap.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn [eval_fop_base]; destruct (fop_is_div fop); cbn;
          [exact I | apply dvalue_has_dtyp_Poison].
      + destruct fop; try discriminate Hsf; cbn; apply dvalue_has_dtyp_Float.
    - destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
        destruct (dvalue_has_dtyp_Double_inv v2 Hv2) as [-> | [d2 ->]];
        cbn [eval_fop]; apply eou_safe_fmap.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn; apply dvalue_has_dtyp_Poison.
      + cbn [eval_fop_base]; destruct (fop_is_div fop); cbn;
          [exact I | apply dvalue_has_dtyp_Poison].
      + destruct fop; try discriminate Hsf; cbn; apply dvalue_has_dtyp_Double.
  Qed.

  Lemma eval_fop_ret_imp (fop : fbinop) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    is_fp_dtyp dt = true ->
    dvalue_has_dtyp v1 dt ->
    eou_ret_imp (fun v => dvalue_has_dtyp v dt) (@eval_fop PaV fop v1 v2).
  Proof.
    intros Hfp Hv1.
    destruct (is_fp_dtyp_inv dt Hfp) as [-> | ->].
    - destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
        destruct v2 as [db2 | | [|] elts2]; try exact I.
      + cbn [eval_fop]; apply eou_ret_imp_fmap; cbn; apply dvalue_has_dtyp_Poison.
      + cbn [eval_fop]; apply eou_ret_imp_vec_poison_l;
          intros y; destruct y; cbn; reflexivity.
      + cbn [eval_fop]; apply eou_ret_imp_fmap.
        destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          cbn [eval_fop_base]; try exact I.
        * destruct fop; cbn; try exact I; apply dvalue_has_dtyp_Float.
        * destruct (fop_is_div fop); cbn; [exact I | apply dvalue_has_dtyp_Poison].
    - destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
        destruct v2 as [db2 | | [|] elts2]; try exact I.
      + cbn [eval_fop]; apply eou_ret_imp_fmap; cbn; apply dvalue_has_dtyp_Poison.
      + cbn [eval_fop]; apply eou_ret_imp_vec_poison_l;
          intros y; destruct y; cbn; reflexivity.
      + cbn [eval_fop]; apply eou_ret_imp_fmap.
        destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          cbn [eval_fop_base]; try exact I.
        * destruct fop; cbn; try exact I; apply dvalue_has_dtyp_Double.
        * destruct (fop_is_div fop); cbn; [exact I | apply dvalue_has_dtyp_Poison].
  Qed.

  Lemma eval_fneg_safe (dt : dtyp) (v1 : @dvalue PaV) :
    is_fp_dtyp dt = true ->
    dvalue_has_dtyp v1 dt ->
    eou_safe (fun v => dvalue_has_dtyp v dt) (@eval_fneg PaV v1).
  Proof.
    intros Hfp Hv1.
    destruct (is_fp_dtyp_inv dt Hfp) as [-> | ->].
    - destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
        cbn; [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_Float].
    - destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
        cbn; [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_Double].
  Qed.

  Lemma eval_fcmp_safe (cmp : fcmp) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    is_fp_dtyp dt = true ->
    dvalue_has_dtyp v1 dt ->
    dvalue_has_dtyp v2 dt ->
    eou_safe
      (fun v => dvalue_has_dtyp v (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_fcmp PaV cmp v1 v2).
  Proof.
    intros Hfp Hv1 Hv2.
    destruct (is_fp_dtyp_inv dt Hfp) as [-> | ->].
    - destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
        destruct (dvalue_has_dtyp_Float_inv v2 Hv2) as [-> | [f2 ->]];
        cbn [eval_fcmp]; apply eou_safe_fmap; cbn [eval_fcmp_base];
        try apply dvalue_has_dtyp_Poison.
      unfold float_cmp;
        repeat match goal with |- context [if ?b then _ else _] => destruct b end;
        apply dvalue_has_dtyp_I.
    - destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
        destruct (dvalue_has_dtyp_Double_inv v2 Hv2) as [-> | [d2 ->]];
        cbn [eval_fcmp]; apply eou_safe_fmap; cbn [eval_fcmp_base];
        try apply dvalue_has_dtyp_Poison.
      unfold double_cmp;
        repeat match goal with |- context [if ?b then _ else _] => destruct b end;
        apply dvalue_has_dtyp_I.
  Qed.

  Lemma eval_fcmp_ret_imp (cmp : fcmp) (dt : dtyp) (v1 v2 : @dvalue PaV) :
    is_fp_dtyp dt = true ->
    dvalue_has_dtyp v1 dt ->
    eou_ret_imp
      (fun v => dvalue_has_dtyp v (DTYPE_Base (DTYPE_I 1%positive)))
      (@eval_fcmp PaV cmp v1 v2).
  Proof.
    intros Hfp Hv1.
    destruct (is_fp_dtyp_inv dt Hfp) as [-> | ->].
    - destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
        destruct v2 as [db2 | | [|] elts2]; try exact I.
      + cbn [eval_fcmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          cbn [eval_fcmp_base]; try exact I; apply dvalue_has_dtyp_Poison.
      + cbn [eval_fcmp]; apply eou_ret_imp_vec_poison_l.
        intros y; destruct y; cbn [eval_fcmp_base eou_ret_imp ExtLib.Structures.Monad.ret EOU_monad];
          first [reflexivity | exact I].
      + cbn [eval_fcmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          cbn [eval_fcmp_base]; try exact I; try apply dvalue_has_dtyp_Poison.
        unfold float_cmp;
          repeat match goal with |- context [if ?b then _ else _] => destruct b end;
          apply dvalue_has_dtyp_I.
    - destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
        destruct v2 as [db2 | | [|] elts2]; try exact I.
      + cbn [eval_fcmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          cbn [eval_fcmp_base]; try exact I; apply dvalue_has_dtyp_Poison.
      + cbn [eval_fcmp]; apply eou_ret_imp_vec_poison_l.
        intros y; destruct y; cbn [eval_fcmp_base eou_ret_imp ExtLib.Structures.Monad.ret EOU_monad];
          first [reflexivity | exact I].
      + cbn [eval_fcmp]; apply eou_ret_imp_fmap;
          destruct db2 as [p2 | sz2 i2 | ip2 | d2 | f2 | | | bsz2 bv2];
          cbn [eval_fcmp_base]; try exact I; try apply dvalue_has_dtyp_Poison.
        unfold double_cmp;
          repeat match goal with |- context [if ?b then _ else _] => destruct b end;
          apply dvalue_has_dtyp_I.
  Qed.

  Lemma convert_pure_safe
    (pc : pure_conversion) (dt_from dt_to : dtyp) (v1 : @dvalue PaV) :
    is_safe_pure_conv pc dt_from dt_to = true ->
    dvalue_has_dtyp v1 dt_from ->
    eou_safe (fun v => dvalue_has_dtyp v dt_to) (@convert_pure PaV pc dt_from v1 dt_to).
  Proof.
    intros Hsafe Hv1.
    destruct pc as [nuw nsw | nneg | | flags | flags | nneg | | |];
      cbn [is_safe_pure_conv] in Hsafe.
    - (* Trunc *)
      destruct dt_from as [[sz1 | | | | | | | | | |] | |]; try discriminate Hsafe.
      destruct dt_to as [[sz2 | | | | | | | | | |] | |]; try discriminate Hsafe.
      destruct (dvalue_has_dtyp_I_inv v1 sz1 Hv1) as [-> | [i1 ->]];
        cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
        unfold convert_pure_base, dvp.
      + cbn; apply dvalue_has_dtyp_Poison.
      + rewrite Pos.eqb_refl, Hsafe; cbn [andb].
        destruct (_ || _); cbn; [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_I].
    - (* Zext *)
      destruct dt_from as [[sz1 | | | | | | | | | |] | |]; try discriminate Hsafe.
      destruct dt_to as [[sz2 | | | | | | | | | |] | |]; try discriminate Hsafe.
      destruct (dvalue_has_dtyp_I_inv v1 sz1 Hv1) as [-> | [i1 ->]];
        cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
        unfold convert_pure_base, dvp.
      + cbn; apply dvalue_has_dtyp_Poison.
      + rewrite Pos.eqb_refl, Hsafe; cbn [andb].
        destruct (_ && _); cbn; [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_I].
    - (* Sext *)
      destruct dt_from as [[sz1 | | | | | | | | | |] | |]; try discriminate Hsafe.
      destruct dt_to as [[sz2 | | | | | | | | | |] | |]; try discriminate Hsafe.
      destruct (dvalue_has_dtyp_I_inv v1 sz1 Hv1) as [-> | [i1 ->]];
        cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
        unfold convert_pure_base, dvp.
      + cbn; apply dvalue_has_dtyp_Poison.
      + rewrite Pos.eqb_refl, Hsafe; cbn; apply dvalue_has_dtyp_I.
    - (* Fptrunc *)
      destruct dt_from as [[| | | | fp1 | | | | | |] | |]; try discriminate Hsafe.
      destruct fp1; try discriminate Hsafe.
      destruct dt_to as [[| | | | fp2 | | | | | |] | |]; try discriminate Hsafe.
      destruct fp2; try discriminate Hsafe.
      destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
        cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
        unfold convert_pure_base, dvp; cbn;
        [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_Float].
    - (* Fpext *)
      destruct dt_from as [[| | | | fp1 | | | | | |] | |]; try discriminate Hsafe.
      destruct fp1; try discriminate Hsafe.
      destruct dt_to as [[| | | | fp2 | | | | | |] | |]; try discriminate Hsafe.
      destruct fp2; try discriminate Hsafe.
      destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
        cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
        unfold convert_pure_base, dvp; cbn;
        [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_Double].
    - (* Uitofp *)
      apply andb_true_iff in Hsafe as [Hint Hfp].
      destruct (is_int_dtyp_inv dt_from Hint) as [sz1 ->].
      destruct (is_fp_dtyp_inv dt_to Hfp) as [-> | ->];
        destruct (dvalue_has_dtyp_I_inv v1 sz1 Hv1) as [-> | [i1 ->]];
        cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
        unfold convert_pure_base, dvp; rewrite ?Pos.eqb_refl;
        repeat match goal with |- context [if ?b then _ else _] => destruct b end;
        cbn; first [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_Float | apply dvalue_has_dtyp_Double].
    - (* Sitofp *)
      apply andb_true_iff in Hsafe as [Hint Hfp].
      destruct (is_int_dtyp_inv dt_from Hint) as [sz1 ->].
      destruct (is_fp_dtyp_inv dt_to Hfp) as [-> | ->];
        destruct (dvalue_has_dtyp_I_inv v1 sz1 Hv1) as [-> | [i1 ->]];
        cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
        unfold convert_pure_base, dvp; rewrite ?Pos.eqb_refl;
        repeat match goal with |- context [if ?b then _ else _] => destruct b end;
        cbn; first [apply dvalue_has_dtyp_Poison | apply dvalue_has_dtyp_Float | apply dvalue_has_dtyp_Double].
    - (* Fptoui *)
      apply andb_true_iff in Hsafe as [Hfp Hint].
      destruct (is_int_dtyp_inv dt_to Hint) as [sz2 ->].
      destruct (is_fp_dtyp_inv dt_from Hfp) as [-> | ->].
      + destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
          cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
          unfold convert_pure_base, dvp; [cbn; apply dvalue_has_dtyp_Poison |].
        destruct (ZofB_range _ _ _ _ _); cbn;
          [apply dvalue_has_dtyp_I | apply dvalue_has_dtyp_Poison].
      + destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
          cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
          unfold convert_pure_base, dvp; [cbn; apply dvalue_has_dtyp_Poison |].
        destruct (ZofB_range _ _ _ _ _); cbn;
          [apply dvalue_has_dtyp_I | apply dvalue_has_dtyp_Poison].
    - (* Fptosi *)
      apply andb_true_iff in Hsafe as [Hfp Hint].
      destruct (is_int_dtyp_inv dt_to Hint) as [sz2 ->].
      destruct (is_fp_dtyp_inv dt_from Hfp) as [-> | ->].
      + destruct (dvalue_has_dtyp_Float_inv v1 Hv1) as [-> | [f1 ->]];
          cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
          unfold convert_pure_base, dvp; [cbn; apply dvalue_has_dtyp_Poison |].
        destruct (ZofB_range _ _ _ _ _); cbn;
          [apply dvalue_has_dtyp_I | apply dvalue_has_dtyp_Poison].
      + destruct (dvalue_has_dtyp_Double_inv v1 Hv1) as [-> | [d1 ->]];
          cbn [convert_pure get_base_conversion_type]; apply eou_safe_fmap;
          unfold convert_pure_base, dvp; [cbn; apply dvalue_has_dtyp_Poison |].
        destruct (ZofB_range _ _ _ _ _); cbn;
          [apply dvalue_has_dtyp_I | apply dvalue_has_dtyp_Poison].
  Qed.

  Lemma convert_pure_ret_imp
    (pc : pure_conversion) (dt_from dt_to : dtyp) (v1 : @dvalue PaV) :
    is_scalar_dtyp dt_to = true ->
    eou_ret_imp (fun v => dvalue_has_dtyp v dt_to) (@convert_pure PaV pc dt_from v1 dt_to).
  Proof.
    intros Hsc.
    destruct dt_to as [dtb2 | |]; [| discriminate Hsc | discriminate Hsc].
    destruct dt_from as [dtb1 | | [|] sz1 [| |]];
      try (destruct v1 as [[] | | [|] ?]; exact I).
    destruct v1 as [db1 | | [|] elts1]; try exact I.
    cbn [convert_pure get_base_conversion_type]; apply eou_ret_imp_fmap.
    destruct pc as [nuw nsw | nneg | | flags | flags | nneg | | |];
      unfold convert_pure_base, dvp;
      destruct dtb1 as [sz1 | | | | fp1 | | | | | | bsz1];
      try (destruct fp1);
      destruct db1 as [p1 | sz_from i1 | ip1 | d1 | f1 | | | bsz_v bv1];
      destruct dtb2 as [sz2 | | | | fp2 | | | | | | bsz2];
      try (destruct fp2);
      try exact I;
      try apply dvalue_has_dtyp_Poison;
      repeat match goal with
             | |- context [ZofB_range ?a ?b ?c ?d ?e] =>
                 destruct (ZofB_range a b c d e)
             | |- context [if ?b then _ else _] => destruct b
             end;
      cbn [eou_ret_imp];
      first [ exact I
            | apply dvalue_has_dtyp_Poison
            | apply dvalue_has_dtyp_I
            | apply dvalue_has_dtyp_Float
            | apply dvalue_has_dtyp_Double ].
  Qed.

  Lemma eval_select_safe_P (P : @dvalue PaV -> Prop)
    (HP_pois : P (DVALUE_Base DVALUE_Poison))
    (vc v1 v2 : @dvalue PaV) (dt1 : dtyp) :
    dvalue_has_dtyp vc (DTYPE_Base (DTYPE_I 1%positive)) ->
    P v1 ->
    P v2 ->
    eou_safe P (@eval_select PaV vc dt1 v1 v2).
  Proof.
    intros Hvc Hv1 Hv2.
    destruct (dvalue_has_dtyp_I_inv vc 1%positive Hvc) as [-> | [ic ->]];
      cbn [eval_select eval_select_base_dvalue].
    - exact HP_pois.
    - destruct (@Integers.unsigned 1%positive ic =? 1)%Z; cbn; [exact Hv1 | exact Hv2].
  Qed.

  Lemma eval_gep_ret_imp
    (flags : gep_flags) (t : dtyp) (vptr : @dvalue PaV) (vs : list (@dvalue PaV)) :
    eou_ret_imp
      (fun v => dvalue_has_dtyp v (DTYPE_Base DTYPE_Pointer))
      (@eval_gep PaV flags t vptr vs).
  Proof.
    destruct vptr as [db | |]; try exact I.
    destruct db as [p | sz i | ip | d | f | | | bsz bv]; cbn [eval_gep];
      try exact I; [| apply dvalue_has_dtyp_Poison].
    unfold catch_pois.
    destruct (handle_gep_ptr flags t p vs) as [s | s | s | [p' |]]; cbn;
      try exact I; [apply dvalue_has_dtyp_Ptr | apply dvalue_has_dtyp_Poison].
  Qed.

  Lemma value_metadata_range_scalar_typ
    (ranges : option (list (int_syntax * int_syntax)))
    (dt : dtyp) (v : @dvalue PaV) :
    is_scalar_dtyp dt = true ->
    dvalue_has_dtyp v dt ->
    dvalue_has_dtyp (@value_metadata_range PaV ranges v) dt.
  Proof.
    intros Hsc Hv.
    destruct (dvalue_has_dtyp_scalar_base_inv v dt Hsc Hv) as [db [-> _]].
    destruct ranges as [rs |]; [| exact Hv].
    cbn [value_metadata_range value_metadata_range_base].
    destruct db; try exact Hv.
    destruct (in_metadata_ranges _ _ _); [exact Hv | apply dvalue_has_dtyp_Poison].
  Qed.

  Lemma value_attrs_poison_scalar_typ
    (attrs : list param_attr) (dt : dtyp) (v : @dvalue PaV) :
    is_scalar_dtyp dt = true ->
    dvalue_has_dtyp v dt ->
    dvalue_has_dtyp (@value_attrs_poison PaV attrs v) dt.
  Proof.
    intros Hsc Hv.
    assert (Hnn : dvalue_has_dtyp (@value_attr_nonnull PaV attrs v) dt).
    { unfold value_attr_nonnull; destruct v as [db | |]; [| exact Hv | exact Hv].
      destruct db; try exact Hv.
      destruct (_ && _); [apply dvalue_has_dtyp_Poison | exact Hv]. }
    assert (Hal : dvalue_has_dtyp (@value_attr_align PaV attrs (@value_attr_nonnull PaV attrs v)) dt).
    { unfold value_attr_align.
      destruct (@value_attr_nonnull PaV attrs v) as [db | |]; try exact Hnn.
      destruct db; try exact Hnn.
      destruct (find_option attr_align attrs); [| exact Hnn].
      destruct (ptr_aligned_to _ _); [exact Hnn | apply dvalue_has_dtyp_Poison]. }
    assert (Hrg : dvalue_has_dtyp
                    (@value_attr_range PaV attrs
                       (@value_attr_align PaV attrs (@value_attr_nonnull PaV attrs v))) dt).
    { unfold value_attr_range.
      exact (value_metadata_range_scalar_typ _ dt _ Hsc Hal). }
    unfold value_attrs_poison, value_attr_nofpclass.
    set (u := @value_attr_range PaV attrs
                (@value_attr_align PaV attrs (@value_attr_nonnull PaV attrs v))) in *.
    destruct (find_option attr_nofpclass attrs) as [mask |]; [| exact Hrg].
    destruct (dvalue_has_dtyp_scalar_base_inv u dt Hsc Hrg) as [db [-> _]].
    cbn [value_nofpclass].
    destruct (fp_class db); [| exact Hrg].
    destruct (Z.land mask _ =? 0)%Z; [exact Hrg | apply dvalue_has_dtyp_Poison].
  Qed.

  Lemma apply_value_attrs_scalar_typ
    (attrs : list param_attr) (msg : string) (dt : dtyp) (v : @dvalue PaV) :
    eou_ret_imp
      (fun v' => is_scalar_dtyp dt = true -> dvalue_has_dtyp v dt -> dvalue_has_dtyp v' dt)
      (@apply_value_attrs PaV attrs msg v).
  Proof.
    unfold apply_value_attrs.
    destruct (_ && _); cbn; [exact I | apply value_attrs_poison_scalar_typ].
  Qed.

  (** * 6. Environment Relations, [withCall] Equations, & [cfg_local_sim] Combinators *)

  (** ** Live-Variable Agreement & Forward Type-Environment Soundness *)

  Definition env_agree_on
    (live : list raw_id) (env1 env2 : @local_env PaV) : Prop :=
    forall x : raw_id,
      in_raw_ids x live = true ->
      Maps.lookup x env1 = Maps.lookup x env2.

  Lemma env_agree_on_refl (live : list raw_id) (env : @local_env PaV) :
    env_agree_on live env env.
  Proof. intros x _; reflexivity. Qed.

  Lemma env_agree_on_eq (live : list raw_id) (env1 env2 : @local_env PaV) :
    env1 = env2 -> env_agree_on live env1 env2.
  Proof. intros ->; apply env_agree_on_refl. Qed.

  Lemma env_agree_on_subset
    (s1 s2 : list raw_id) (env1 env2 : @local_env PaV) :
    (forall x, in_raw_ids x s1 = true -> in_raw_ids x s2 = true) ->
    env_agree_on s2 env1 env2 ->
    env_agree_on s1 env1 env2.
  Proof.
    intros Hsub Hagree x Hx; apply Hagree, Hsub, Hx.
  Qed.

  Lemma env_agree_on_in
    (xs : list raw_id) (env1 env2 : @local_env PaV) (x : raw_id) :
    env_agree_on xs env1 env2 ->
    In x xs ->
    Maps.lookup x env1 = Maps.lookup x env2.
  Proof.
    intros Hagree Hx; apply Hagree, in_raw_ids_spec, Hx.
  Qed.

  Lemma env_agree_on_app_l
    (l1 l2 : list raw_id) (env1 env2 : @local_env PaV) :
    env_agree_on (l1 ++ l2) env1 env2 ->
    env_agree_on l1 env1 env2.
  Proof.
    apply env_agree_on_subset; intros x Hx.
    apply in_raw_ids_spec; apply in_raw_ids_spec in Hx.
    apply in_or_app; left; exact Hx.
  Qed.

  Lemma env_agree_on_app_r
    (l1 l2 : list raw_id) (env1 env2 : @local_env PaV) :
    env_agree_on (l1 ++ l2) env1 env2 ->
    env_agree_on l2 env1 env2.
  Proof.
    apply env_agree_on_subset; intros x Hx.
    apply in_raw_ids_spec; apply in_raw_ids_spec in Hx.
    apply in_or_app; right; exact Hx.
  Qed.

  Lemma env_agree_on_add_raw_ids_split
    (xs s : list raw_id) (env1 env2 : @local_env PaV) :
    env_agree_on (add_raw_ids xs s) env1 env2 ->
    env_agree_on xs env1 env2 /\ env_agree_on s env1 env2.
  Proof.
    intros H; split.
    - intros x Hx; apply H, in_add_raw_ids; left; apply in_raw_ids_spec, Hx.
    - intros x Hx; apply H, in_add_raw_ids; right; exact Hx.
  Qed.

  Lemma env_agree_on_add_both
    (live : list raw_id) (x : raw_id) (v : @dvalue PaV)
    (env1 env2 : @local_env PaV) :
    env_agree_on (remove_raw_id x live) env1 env2 ->
    env_agree_on live (Maps.add x v env1) (Maps.add x v env2).
  Proof.
    intros Hagree y Hy.
    destruct (RawIDOrd.eq_dec x y) as [<- | Hne].
    - cbn [Maps.lookup Maps.add Map_rmap]; rewrite !RMF.F.add_eq_o by reflexivity; reflexivity.
    - cbn [Maps.lookup Maps.add Map_rmap]; rewrite !RMF.F.add_neq_o by exact Hne.
      apply Hagree, in_remove_raw_id.
      split; [congruence | exact Hy].
  Qed.

  Lemma env_agree_on_add_both_same
    (live : list raw_id) (x : raw_id) (v : @dvalue PaV)
    (env1 env2 : @local_env PaV) :
    env_agree_on live env1 env2 ->
    env_agree_on live (Maps.add x v env1) (Maps.add x v env2).
  Proof.
    intros Hagree; apply env_agree_on_add_both.
    eapply env_agree_on_subset; [| exact Hagree].
    intros y Hy; apply in_remove_raw_id in Hy; exact (proj2 Hy).
  Qed.

  Lemma env_agree_on_add_dead_l
    (live : list raw_id) (x : raw_id) (v : @dvalue PaV)
    (env1 env2 : @local_env PaV) :
    in_raw_ids x live = false ->
    env_agree_on live env1 env2 ->
    env_agree_on live (Maps.add x v env1) env2.
  Proof.
    intros Hdead Hagree y Hy.
    destruct (RawIDOrd.eq_dec x y) as [<- | Hne].
    - congruence.
    - cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by exact Hne; apply Hagree, Hy.
  Qed.

  Definition val_matches_oty (oty : ty_info) (v : @dvalue PaV) : Prop :=
    match oty with
    | None => True
    | Some dt => is_scalar_dtyp dt = true /\ dvalue_has_dtyp v dt
    end.

  Lemma val_matches_normalize_oty (dt : dtyp) (v : @dvalue PaV) :
    (is_scalar_dtyp dt = true -> dvalue_has_dtyp v dt) ->
    val_matches_oty (normalize_oty (Some dt)) v.
  Proof.
    intros H; cbn [normalize_oty].
    destruct (is_scalar_dtyp dt) eqn:Esc; cbn [val_matches_oty].
    - split; [exact Esc | apply H, Logic.eq_refl].
    - exact I.
  Qed.

  Definition tenv_sound (te : ty_env) (env : @local_env PaV) : Prop :=
    forall (x : local_id) (oty : ty_info),
      lookup_ty x te = Some oty ->
      exists v : @dvalue PaV,
        Maps.lookup x env = Some v /\ val_matches_oty oty v.

  Lemma tenv_sound_nil (env : @local_env PaV) :
    tenv_sound [] env.
  Proof. intros x oty H; discriminate H. Qed.

  Lemma tenv_sound_remove_ty_same
    (x : local_id) (te : ty_env) (env : @local_env PaV) :
    tenv_sound te env ->
    tenv_sound (remove_ty x te) env.
  Proof.
    intros Hte z oty Hlk.
    destruct (RawIDOrd.eq_dec z x) as [-> | Hne].
    - rewrite lookup_remove_ty_eq in Hlk; discriminate Hlk.
    - rewrite (lookup_remove_ty_neq x z te Hne) in Hlk; apply Hte, Hlk.
  Qed.

  Lemma tenv_sound_remove_ty_add
    (x : local_id) (v : @dvalue PaV) (te : ty_env) (env : @local_env PaV) :
    tenv_sound te env ->
    tenv_sound (remove_ty x te) (Maps.add x v env).
  Proof.
    intros Hte z oty Hlk.
    destruct (RawIDOrd.eq_dec x z) as [<- | Hne].
    - rewrite lookup_remove_ty_eq in Hlk; discriminate Hlk.
    - cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by exact Hne.
      rewrite (lookup_remove_ty_neq x z te) in Hlk by congruence.
      apply Hte, Hlk.
  Qed.

  Lemma tenv_sound_set_ty
    (x : local_id) (oty : ty_info) (v : @dvalue PaV)
    (te : ty_env) (env : @local_env PaV) :
    val_matches_oty (normalize_oty oty) v ->
    tenv_sound te env ->
    tenv_sound (set_ty x oty te) (Maps.add x v env).
  Proof.
    intros Hval Hte z oty' Hlk.
    destruct (RawIDOrd.eq_dec x z) as [<- | Hne].
    - rewrite lookup_set_ty_eq in Hlk; inversion Hlk; subst oty'.
      exists v; split; [apply lookup_add_eq | exact Hval].
    - cbn [Maps.lookup Maps.add Map_rmap]; rewrite RMF.F.add_neq_o by exact Hne.
      rewrite (lookup_set_ty_neq x z oty te) in Hlk by congruence.
      apply Hte, Hlk.
  Qed.

  Lemma tenv_sound_subsumes
    (te_gen te_spec : ty_env) (env : @local_env PaV) :
    tenv_subsumes te_gen te_spec = true ->
    tenv_sound te_spec env ->
    tenv_sound te_gen env.
  Proof.
    unfold tenv_subsumes; rewrite forallb_forall.
    intros Hsub Hspec x oty_g Hlk_g.
    apply lookup_ty_in in Hlk_g.
    specialize (Hsub (x, oty_g) Hlk_g).
    apply andb_true_iff in Hsub as [Hval Hsub].
    destruct (lookup_ty x te_spec) as [oty_s |] eqn:Elk_s; [| discriminate Hsub].
    destruct (Hspec x oty_s Elk_s) as [v [Henv Hv]].
    exists v; split; [exact Henv |].
    destruct oty_g as [dt_g |]; [| exact I].
    destruct oty_s as [dt_s |]; [| discriminate Hsub].
    cbn [oty_subsumes] in Hsub.
    apply andb_true_iff in Hsub as [Hsc Heq].
    apply dtyp_eqb_eq in Heq; subst dt_s.
    exact Hv.
  Qed.

  Lemma init_tenv_sound (fargs : list local_id) (env : @local_env PaV) :
    (forall x, In x fargs -> exists v, Maps.lookup x env = Some v) ->
    tenv_sound (init_tenv fargs) env.
  Proof.
    induction fargs as [| a rest IH]; intros Henv.
    - apply tenv_sound_nil.
    - intros z oty Hlk; cbn [init_tenv] in Hlk.
      destruct (RawIDOrd.eq_dec z a) as [-> | Hne].
      + rewrite lookup_set_ty_eq in Hlk; inversion Hlk; subst oty.
        destruct (Henv a (or_introl Logic.eq_refl)) as [v Hv].
        exists v; split; [exact Hv | exact I].
      + rewrite (lookup_set_ty_neq a z None _ Hne) in Hlk.
        apply (IH (fun x Hx => Henv x (or_intror Hx)) z oty Hlk).
  Qed.

  (** ** [withCall] Equations & Left-Only Failure-Free Evaluation *)

  Lemma withCall_ret {R : Type} (x : R) :
    @withCall PaV R (Ret x) ≅ Ret x.
  Proof.
    unfold withCall; apply translate_ret.
  Qed.

  Lemma withCall_bind {R S : Type}
    (t : @MCFGtop PaV R) (k : R -> @MCFGtop PaV S) :
    @withCall PaV S (ITree.bind t k) ≅
    ITree.bind (@withCall PaV R t) (fun x => @withCall PaV S (k x)).
  Proof.
    unfold withCall; apply translate_bind.
  Qed.

  Lemma withCall_lread_bind {R : Type} (x : local_id)
    (k : @dvalue PaV -> @CFGtop PaV R) :
    ITree.bind (@withCall PaV (@dvalue PaV) (lread x)) k ≅
    ITree.bind (ITree.trigger (subevent _ (LocalRead x))) k.
  Proof.
    unfold withCall, lread, ITree.trigger.
    pstep; red; repeat (rewrite observe_bind || rewrite observe_translate); cbn.
    constructor; intros v; left.
    change (paco2 (eqit_ eq false false id) bot2
              (ITree.bind (translate inr1 (Ret v)) k) (ITree.bind (Ret v) k))
      with (ITree.bind (translate inr1 (Ret v)) k ≅ ITree.bind (Ret v) k).
    rewrite translate_ret, !Eqit.bind_ret_l; reflexivity.
  Qed.

  Lemma withCall_lread (x : local_id) :
    @withCall PaV (@dvalue PaV) (lread x) ≅
    ITree.bind (ITree.trigger (subevent _ (LocalRead x))) (fun v => Ret v).
  Proof.
    rewrite <- (Eqit.bind_ret_r (@withCall PaV (@dvalue PaV) (lread x))).
    apply withCall_lread_bind.
  Qed.

  (** [left_evals_to P env1 t1] means that [t1] executes purely via defined
      local reads in [env1] (leaving [env1] untouched) or cuts [ThrowUB], and
      if it returns [v], [P v] holds. *)
  Definition left_evals_to {R : Type}
    (P : R -> Prop) (env1 : @local_env PaV) (t1 : @CFGtop PaV R) : Prop :=
    forall env2 : @local_env PaV,
      cfg_local_sim
        (fun e1' e2' r1 _ => e1' = env1 /\ e2' = env2 /\ P r1)
        env1 env2 t1 (Ret tt).

  Lemma left_evals_to_obs_eq {R : Type}
    (P : R -> Prop) (env1 : @local_env PaV) (t1 t1' : @CFGtop PaV R) :
    t1 ≅ t1' ->
    left_evals_to P env1 t1 ->
    left_evals_to P env1 t1'.
  Proof.
    intros Heq H env2.
    eapply cfg_local_sim_obs_eq; [exact Heq | reflexivity | apply H].
  Qed.

  Lemma left_evals_to_ret {R : Type}
    (P : R -> Prop) (env1 : @local_env PaV) (x : R) :
    P x ->
    left_evals_to P env1 (Ret x).
  Proof.
    intros HP env2; apply cfg_local_sim_ret; split; [reflexivity | split; [reflexivity | exact HP]].
  Qed.

  Lemma left_evals_to_withCall_ret {R : Type}
    (P : R -> Prop) (env1 : @local_env PaV) (x : R) :
    P x ->
    left_evals_to P env1 (@withCall PaV R (Ret x)).
  Proof.
    intros HP; eapply left_evals_to_obs_eq; [symmetry; apply withCall_ret |].
    apply left_evals_to_ret, HP.
  Qed.

  Lemma left_evals_to_weaken {R : Type}
    (P Q : R -> Prop) (env1 : @local_env PaV) (t1 : @CFGtop PaV R) :
    (forall x, P x -> Q x) ->
    left_evals_to P env1 t1 ->
    left_evals_to Q env1 t1.
  Proof.
    intros HPQ H env2.
    eapply cfg_local_sim_weaken; [| apply H].
    intros ? ? r1 _ (-> & -> & Hr); split; [reflexivity | split; [reflexivity | apply HPQ, Hr]].
  Qed.

  Lemma left_evals_to_bind {R S : Type}
    (P : R -> Prop) (Q : S -> Prop) (env1 : @local_env PaV)
    (t1 : @CFGtop PaV R) (k1 : R -> @CFGtop PaV S) :
    left_evals_to P env1 t1 ->
    (forall x, P x -> left_evals_to Q env1 (k1 x)) ->
    left_evals_to Q env1 (ITree.bind t1 k1).
  Proof.
    intros Ht Hk env2.
    eapply cfg_local_sim_obs_eq;
      [reflexivity | apply (Eqit.bind_ret_l tt (fun _ : unit => Ret tt)) |].
    eapply cfg_local_sim_bind; [apply Ht |].
    intros ? ? x _ (-> & -> & Hx); apply Hk, Hx.
  Qed.

  Lemma left_evals_to_withCall_bind {R S : Type}
    (P : R -> Prop) (Q : S -> Prop) (env1 : @local_env PaV)
    (t1 : @MCFGtop PaV R) (k1 : R -> @MCFGtop PaV S) :
    left_evals_to P env1 (@withCall PaV R t1) ->
    (forall x, P x -> left_evals_to Q env1 (@withCall PaV S (k1 x))) ->
    left_evals_to Q env1 (@withCall PaV S (ITree.bind t1 k1)).
  Proof.
    intros Ht Hk.
    eapply left_evals_to_obs_eq; [symmetry; apply withCall_bind |].
    eapply left_evals_to_bind; [exact Ht | exact Hk].
  Qed.

  Lemma left_evals_to_withCall_lread
    (P : @dvalue PaV -> Prop) (env1 : @local_env PaV)
    (x : local_id) (v : @dvalue PaV) :
    Maps.lookup x env1 = Some v ->
    P v ->
    left_evals_to P env1 (@withCall PaV (@dvalue PaV) (lread x)).
  Proof.
    intros Hlk HP env2.
    pstep; eapply CLS_ReadL.
    - apply withCall_lread.
    - exact Hlk.
    - apply CLS_Step; cbn; split; [reflexivity | split; [reflexivity | exact HP]].
  Qed.

  Lemma left_evals_to_withCall_EOU {R : Type}
    (P : R -> Prop) (env1 : @local_env PaV) (m : EOU R) :
    eou_safe P m ->
    left_evals_to P env1 (@withCall PaV R (EOU_to_itree m)).
  Proof.
    intros Hm env2; destruct m as [s | s | s | x]; cbn in Hm; try contradiction; cbn [EOU_to_itree].
    - unfold withCall, raiseUB, trigger_cast, ITree.trigger.
      pstep; apply CLS_Step; unfold cls_step_body.
      repeat (rewrite observe_bind || rewrite observe_translate); cbn; left; reflexivity.
    - eapply cfg_local_sim_obs_eq; [symmetry; apply withCall_ret | reflexivity |].
      apply cfg_local_sim_ret; split; [reflexivity | split; [reflexivity | exact Hm]].
  Qed.

  Lemma left_evals_to_bind_sim {R1 S1 S2 : Type}
    (P : R1 -> Prop)
    (RS : @local_env PaV -> @local_env PaV -> S1 -> S2 -> Prop)
    (env1 env2 : @local_env PaV)
    (t1 : @CFGtop PaV R1)
    (k1 : R1 -> @CFGtop PaV S1)
    (t2 : @CFGtop PaV S2) :
    left_evals_to P env1 t1 ->
    (forall r1, P r1 -> cfg_local_sim RS env1 env2 (k1 r1) t2) ->
    cfg_local_sim RS env1 env2 (ITree.bind t1 k1) t2.
  Proof.
    intros Ht Hk.
    eapply cfg_local_sim_obs_eq;
      [reflexivity | apply (Eqit.bind_ret_l tt (fun _ : unit => t2)) |].
    eapply cfg_local_sim_bind; [apply Ht |].
    intros ? ? r1 _ (-> & -> & Hr); apply Hk, Hr.
  Qed.

End DCESoundness.
