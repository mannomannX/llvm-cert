(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Prototype Attribute Seeding & Function Refinement ([CertValidator.CertValProto])

    Purpose:
      Seeds initial [ub_ctx] assumptions from prototype parameter attributes
      ([seed_proto_param_ctx], [F-61]), models function frames ([eval_defn_open]),
      and lifts CFG refinement to [denote_function] ([proto_cfg_to_defn_refines]).

    Trust Contract & Fail-Closed Boundary:
      Fail-closed prototype and frame-refinement bridge; requires
      [check_prototype_contract], [proto_deref_preserved_b], ABI preservation,
      and [no_stack_det] guarantees before asserting [validator_defn_refines].

    Assumptions:
      Depends on Stdlib, [Paco], [ITree], [ExtLib], [Vellvm], [Diag], and
      [CertFormat]/[AigLrat]/[AlgRules]/[CfgDag]/[CertVal*]; zero custom axioms.

    Section Outline:
      5.6d [F-61] & [F-60] Prototype Attribute Seeding & [denote_function]
      Refinement ([seed_proto_param_ctx_sound], [proto_cfg_to_defn_refines]). *)

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
  CertFormat
  AigLrat
  AlgRules
  CfgDag
  CertValOpenWorld
  CertValExpReify
  CertValCfgDag
  CertValCfgSum
  CertValUbCheck
  CertValPathCheck
  CertValLoop.

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
  - unfold seed_one_param_ctx in E1; inversion E1; subst ev1; clear E1.
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
    destruct dt as [tb | |]; try apply Forall_nil.
    destruct tb as [w0 | | | | | | | | | |]; try apply Forall_nil.
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
      cbn [value_metadata_range_base in_metadata_ranges existsb]; rewrite El, Eh; reflexivity. }
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
  - inversion Hty; subst;
      [destruct (Hbase_step (DVALUE_Base dv) (ex_intro _ dv eq_refl)) as [-> | ->];
        [exact Hty | apply DVALUE_Poison_typ_agg]
      | rewrite value_attrs_poison_poison; apply DVALUE_Poison_typ_agg].
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
    + rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind, Hom;
        cbn iota; repeat rewrite observe_bind; reflexivity.
    + rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind, Hom;
        cbn iota; repeat rewrite observe_bind; reflexivity.
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
    + destruct (classify_ow_event oe) as [dt | op w args | X' de].
      * clear Hom e oe; revert k; right; exact (CIH (shift_draw_strat sigma) env stk exc_slot (k (sigma 0%nat dt))).
      * clear Hom e oe; revert k; intros k.
        destruct (pure_int_intrinsic_fn op w args) as [| | | rv];
          [right; apply det_vis_both_refl; intros []
          | right; apply det_vis_both_refl; intros []
          | right; apply det_vis_both_refl; intros []
          | right; exact (CIH sigma env stk exc_slot (k rv))].
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
    + rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind, Hom;
        cbn iota; repeat rewrite observe_bind; reflexivity.
    + rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind, Hom;
        cbn iota; repeat rewrite observe_bind; reflexivity.
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
    + destruct (classify_ow_event oe) as [dt | op w args | X' de].
      * clear Hom e oe; revert k; right; exact (CIH (shift_draw_strat sigma) env stk exc_slot (k (sigma 0%nat dt))).
      * clear Hom e oe; revert k; intros k.
        destruct (pure_int_intrinsic_fn op w args) as [| | | rv];
          [right; apply det_vis_both_refl; intros []
          | right; apply det_vis_both_refl; intros []
          | right; apply det_vis_both_refl; intros []
          | right; exact (CIH sigma env stk exc_slot (k rv))].
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
  destruct (observe t) as [x | m | X e k] eqn:Hot.
  - apply (NSD_Ret _ _ x); rewrite observe_run_draws, Hot; reflexivity.
  - destruct H as [x Ho0 | m0 Ho0 Hm0 | X0 e0 k0 Ho0 _ _];
      rewrite observe_run_draws, Hot in Ho0; try discriminate Ho0.
    injection Ho0 as <-; pclearbot.
    apply (NSD_Tau _ _ (run_draws s2 m)); [rewrite observe_run_draws, Hot; reflexivity |].
    right; exact (CIH s1 s2 m Heq Hm0).
  - destruct (classify_ow_event e) as [dt | op w args | X' de] eqn:Ecl.
    + revert e k Hot Ecl; intros e k Hot Ecl.
      destruct H as [x Ho0 | m0 Ho0 Hm0 | X0 e0 k0 Ho0 _ _];
        rewrite observe_run_draws, Hot, Ecl in Ho0; try discriminate Ho0.
      injection Ho0 as <-; pclearbot.
      apply (NSD_Tau _ _ (run_draws (shift_draw_strat s2) (k (s2 0%nat dt)))).
      * rewrite observe_run_draws, Hot, Ecl; reflexivity.
      * right; rewrite <- (Heq 0%nat dt).
        exact (CIH (shift_draw_strat s1) (shift_draw_strat s2) (k (s1 0%nat dt))
                 (fun n d => Heq (S n) d) Hm0).
    + revert e k Hot Ecl; intros e k Hot Ecl.
      destruct (pure_int_intrinsic_fn op w args) as [| | | rv] eqn:Epi.
      * apply (NSD_Vis _ _ (@subevent FailureE (@Det_OW_E Pa) _ void (Throw tt)) void_elim).
        -- rewrite observe_run_draws, Hot, Ecl, Epi; reflexivity.
        -- reflexivity.
        -- intros [].
      * apply (NSD_Vis _ _ (@subevent OOME (@Det_OW_E Pa) _ void (ThrowOOM tt)) void_elim).
        -- rewrite observe_run_draws, Hot, Ecl, Epi; reflexivity.
        -- reflexivity.
        -- intros [].
      * apply (NSD_Vis _ _ (@subevent UBE (@Det_OW_E Pa) _ void (ThrowUB tt)) void_elim).
        -- rewrite observe_run_draws, Hot, Ecl, Epi; reflexivity.
        -- reflexivity.
        -- intros [].
      * destruct H as [x Ho0 | m0 Ho0 Hm0 | X0 e0 k0 Ho0 _ _];
          rewrite observe_run_draws, Hot, Ecl, Epi in Ho0; try discriminate Ho0.
        injection Ho0 as <-; pclearbot.
        apply (NSD_Tau _ _ (run_draws s2 (k rv))).
        -- rewrite observe_run_draws, Hot, Ecl, Epi; reflexivity.
        -- right; exact (CIH s1 s2 (k rv) Heq Hm0).
    + destruct H as [x Ho0 | m0 Ho0 Hm0 | X0 e0 k0 Ho0 Hns0 Hk0];
        rewrite observe_run_draws, Hot, Ecl in Ho0; try discriminate Ho0.
      pose proof (f_equal (fun u : itree' (@Det_OW_E Pa) R =>
        match u with
        | @VisF _ _ _ X_ u_e u_k =>
            existT (fun T : Type => (@Det_OW_E Pa T * (T -> itree (@Det_OW_E Pa) R))%type) X_ (u_e, u_k)
        | _ =>
            existT (fun T : Type => (@Det_OW_E Pa T * (T -> itree (@Det_OW_E Pa) R))%type)
              X' (de, fun x : X' => run_draws s1 (k x))
        end) Ho0) as Hs.
      destruct (match Hs in (_ = z)
                return exists Hc : X' = projT1 z,
                  eq_rect X' (fun T : Type => (@Det_OW_E Pa T * (T -> itree (@Det_OW_E Pa) R))%type)
                    (de, fun x : X' => run_draws s1 (k x)) (projT1 z) Hc = projT2 z
                with
                | eq_refl => ex_intro _ eq_refl eq_refl
                end) as [Hc Hpair].
      clear Ho0 Hs; cbn [projT1 projT2] in Hc, Hpair;
        revert e0 k0 Hns0 Hk0 Hpair; destruct Hc; intros e0 k0 Hns0 Hk0 Hpair; cbn in Hpair.
      injection Hpair as <- Hk_eq.
      apply (NSD_Vis _ _ de (fun x => run_draws s2 (k x))).
      * rewrite observe_run_draws, Hot, Ecl; reflexivity.
      * exact Hns0.
      * intros x; specialize (Hk0 x); pclearbot; rewrite <- Hk_eq in Hk0.
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
    | s env t dt ke s_sh Ho Hsh _ IH
    | s env t dt fn args va op w rv ke Ho Ep Efn _ IH ].
  - pstep; eapply NSD_Vis.
    + rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity.
    + reflexivity.
    + intros [].
  - pstep; eapply NSD_Tau;
      [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | left; exact IH].
  - pstep; eapply NSD_Tau;
      [rewrite observe_run_draws, observe_run_cfg_locals, Ho; cbn; rewrite Hf; reflexivity
      | left; exact IH].
  - pstep; eapply NSD_Tau;
      [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | left; exact IH].
  - pstep; eapply NSD_Tau;
      [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | left].
    exact (run_draws_ext_no_stack_det s_sh (shift_draw_strat s) _ Hsh IH).
  - pstep; eapply NSD_Tau;
      [rewrite observe_run_draws, observe_run_cfg_locals, Ho; cbn; rewrite Ep, Efn; reflexivity
      | left; exact IH].
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
    | s env t dt ke s_sh s' env' r Ho Hsh _ IH
    | s env t dt fn args va op w rv ke s' env' r Ho Ep Efn _ IH ].
  - pstep; eapply NSD_Ret; rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity.
  - pstep; eapply NSD_Tau;
      [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | left; exact IH].
  - pstep; eapply NSD_Tau;
      [rewrite observe_run_draws, observe_run_cfg_locals, Ho; cbn; rewrite Hf; reflexivity
      | left; exact IH].
  - pstep; eapply NSD_Tau;
      [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | left; exact IH].
  - pstep; eapply NSD_Tau;
      [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | left].
    exact (run_draws_ext_no_stack_det s_sh (shift_draw_strat s) _ Hsh IH).
  - pstep; eapply NSD_Tau;
      [rewrite observe_run_draws, observe_run_cfg_locals, Ho; cbn; rewrite Ep, Efn; reflexivity
      | left; exact IH].
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
      | Some s =>
          match parse_pure_int_intrinsic s with
          | Some _ => true
          | None => false
          end
      | None => true
      end
  | _ => true
  end.

Definition cfg_varargs_irrel (G : CFG.cfg dtyp) : bool :=
  forallb (fun b => forallb (fun '(_, ins, _) => instr_varargs_irrel ins) (blk_code b)) (blks G).

Inductive va_cfg_eqF {Pa : Params} {R : Type}
  (r : @CFGtop Pa R -> @CFGtop Pa R -> Prop)
  : itree' (@CFGEtop Pa) R -> itree' (@CFGEtop Pa) R -> Prop :=
| VaRet (x : R) : va_cfg_eqF r (RetF x) (RetF x)
| VaTau (t1 t2 : @CFGtop Pa R) : r t1 t2 -> va_cfg_eqF r (TauF t1) (TauF t2)
| VaVisEq {X : Type} (e : @CFGEtop Pa X) (k1 k2 : X -> @CFGtop Pa R) :
    (forall x, r (k1 x) (k2 x)) ->
    va_cfg_eqF r (VisF e k1) (VisF e k2)
| VaVisPureIntr dt fname args va1 va2 (k1 k2 : @exc Pa + @dvalue Pa -> @CFGtop Pa R) :
    parse_pure_int_intrinsic fname <> None ->
    (forall x, r (k1 x) (k2 x)) ->
    va_cfg_eqF r
      (VisF (@subevent IntrinsicE (@CFGEtop Pa) _ (@exc Pa + @dvalue Pa) (Intrinsic dt fname args va1)) k1)
      (VisF (@subevent IntrinsicE (@CFGEtop Pa) _ (@exc Pa + @dvalue Pa) (Intrinsic dt fname args va2)) k2).

Lemma va_cfg_eqF_mon {Pa : Params} {R : Type} :
  monotone2
    (fun (r : rel2 (@CFGtop Pa R) (fun _ => @CFGtop Pa R)) (u1 u2 : @CFGtop Pa R) =>
       @va_cfg_eqF Pa R r (observe u1) (observe u2)).
Proof.
  intros u1 u2 r r' H Hle; destruct H;
    [exact (VaRet r' x)
    | exact (VaTau r' t1 t2 (Hle _ _ H))
    | exact (VaVisEq r' e k1 k2 (fun x => Hle _ _ (H x)))
    | exact (VaVisPureIntr r' dt fname args va1 va2 k1 k2 H (fun x => Hle _ _ (H0 x)))].
Qed.
#[local] Hint Resolve va_cfg_eqF_mon : paco.

Definition va_cfg_eq {Pa : Params} {R : Type} (u1 u2 : @CFGtop Pa R) : Prop :=
  paco2 (fun r a b => @va_cfg_eqF Pa R r (observe a) (observe b)) bot2 u1 u2.

Lemma va_cfg_eq_refl {Pa : Params} {R : Type} :
  forall (u : @CFGtop Pa R), va_cfg_eq u u.
Proof.
  pcofix CIH; intros u; pstep.
  destruct (observe u) as [x | u' | X e k];
    [exact (VaRet _ x)
    | apply (VaTau _ u' u'); right; exact (CIH u')
    | apply (VaVisEq _ e k k); intros x; right; exact (CIH (k x))].
Qed.

Lemma va_cfg_eq_obs_eq {Pa : Params} {R : Type} :
  forall (u1 u2 v1 v2 : @CFGtop Pa R),
    observe u1 = observe u2 ->
    observe v1 = observe v2 ->
    va_cfg_eq u1 v1 ->
    va_cfg_eq u2 v2.
Proof.
  intros u1 u2 v1 v2 H1 H2 Hva; punfold Hva; pstep.
  rewrite <- H1, <- H2; eapply va_cfg_eqF_mon; [exact Hva | intros ? ? H0; exact H0].
Qed.

Lemma va_cfg_eq_bind {Pa : Params} {A B : Type} :
  forall (t1 t2 : @CFGtop Pa A) (k1 k2 : A -> @CFGtop Pa B),
    va_cfg_eq t1 t2 ->
    (forall x, va_cfg_eq (k1 x) (k2 x)) ->
    va_cfg_eq (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  pcofix CIH; intros t1 t2 k1 k2 H1 H2; punfold H1.
  remember (observe t1) as ot1 eqn:Eo1; remember (observe t2) as ot2 eqn:Eo2.
  destruct H1 as [x | ta tb Htau | X e ka kb Hk | dt fname args va1 va2 ka kb Hp Hk].
  - eapply paco2_mon with (r := bot2); [| intros ? ? []].
    eapply va_cfg_eq_obs_eq with (u1 := k1 x) (v1 := k2 x);
      [rewrite observe_bind, <- Eo1; reflexivity | rewrite observe_bind, <- Eo2; reflexivity | exact (H2 x)].
  - pstep; rewrite !observe_bind, <- Eo1, <- Eo2; cbn [observe]; pclearbot.
    apply (VaTau _ _ _); right; exact (CIH ta tb k1 k2 Htau H2).
  - pstep; rewrite !observe_bind, <- Eo1, <- Eo2; cbn [observe].
    apply (VaVisEq _ e (fun x => ITree.bind (ka x) k1) (fun x => ITree.bind (kb x) k2)); intros x.
    right; destruct (Hk x) as [Hsub | []]; exact (CIH (ka x) (kb x) k1 k2 Hsub H2).
  - pstep; rewrite !observe_bind, <- Eo1, <- Eo2; cbn [observe].
    apply (VaVisPureIntr _ dt fname args va1 va2
             (fun x => ITree.bind (ka x) k1) (fun x => ITree.bind (kb x) k2) Hp); intros x.
    right; destruct (Hk x) as [Hsub | []]; exact (CIH (ka x) (kb x) k1 k2 Hsub H2).
Qed.

Lemma va_cfg_eq_iter {Pa : Params} {I R : Type} :
  forall (f1 f2 : I -> @CFGtop Pa (I + R)) (i : I),
    (forall p, va_cfg_eq (f1 p) (f2 p)) ->
    va_cfg_eq (ITree.iter f1 i) (ITree.iter f2 i).
Proof.
  intros f1 f2 i Hf.
  assert (Hgen : forall u1 u2 : @CFGtop Pa R,
    (exists m1 m2 : @CFGtop Pa (I + R),
       va_cfg_eq m1 m2 /\
       observe u1 =
         observe (ITree.bind m1
                    (fun lr => match lr with inl l => Tau (ITree.iter f1 l) | inr r0 => Ret r0 end)) /\
       observe u2 =
         observe (ITree.bind m2
                    (fun lr => match lr with inl l => Tau (ITree.iter f2 l) | inr r0 => Ret r0 end))) ->
    va_cfg_eq u1 u2).
  { pcofix CIH; intros u1 u2 [m1 [m2 [Hm [Ho1 Ho2]]]]; punfold Hm; pstep.
    rewrite Ho1, Ho2, !observe_bind; destruct Hm; cbn [observe].
    - destruct x as [l | r0]; [| exact (VaRet _ r0)].
      apply (VaTau _ (ITree.iter f1 l) (ITree.iter f2 l)); right.
      eapply CIH; exists (f1 l), (f2 l); split; [exact (Hf l) | split; apply observe_iter].
    - pclearbot; apply (VaTau _ _ _); right.
      exact (CIH _ _ (ex_intro _ t1 (ex_intro _ t2 (conj H (conj eq_refl eq_refl))))).
    - apply (VaVisEq _ e _ _); intros x; right.
      exact (CIH _ _ (ex_intro _ (k1 x) (ex_intro _ (k2 x)
               (conj (match H x with or_introl h => h | or_intror f => match f with end end)
                     (conj eq_refl eq_refl))))).
    - apply (VaVisPureIntr _ dt fname args va1 va2 _ _ H); intros x; right.
      exact (CIH _ _ (ex_intro _ (k1 x) (ex_intro _ (k2 x)
               (conj (match H0 x with or_introl h => h | or_intror f => match f with end end)
                     (conj eq_refl eq_refl))))). }
  eapply Hgen; exists (f1 i), (f2 i); split; [exact (Hf i) | split; apply observe_iter].
Qed.

Lemma denote_instr_varargs_eq {Pa : Params} :
  forall (i : instr_id * instr dtyp * list (metadata dtyp)) (va1 va2 : option (@ptr _ (@PTR Pa))),
    instr_varargs_irrel (snd (fst i)) = true ->
    va_cfg_eq (denote_instr i va1) (denote_instr i va2).
Proof.
  intros [[iid ins] md] va1 va2 Hirr; cbn in Hirr.
  destruct ins; try apply va_cfg_eq_refl.
  destruct fn as [dt fn_e]; unfold instr_varargs_irrel in Hirr; unfold denote_instr; cbn zeta iota beta.
  destruct (intrinsic_exp fn_e) as [s |] eqn:Eix; [| apply va_cfg_eq_refl].
  destruct (parse_pure_int_intrinsic s) as [[op w] |] eqn:Ep; [| discriminate Hirr].
  destruct iid;
    (cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
     apply va_cfg_eq_bind; [apply va_cfg_eq_refl | intros vs];
     apply va_cfg_eq_bind; [apply va_cfg_eq_refl | intros _];
     apply va_cfg_eq_bind; [| intros res; apply va_cfg_eq_refl];
     unfold intrinsic, trigger; pstep; cbn [observe]; apply VaVisPureIntr;
     [rewrite Ep; discriminate | intros x; left; apply va_cfg_eq_refl]).
Qed.

Lemma denote_code_varargs_eq {Pa : Params} :
  forall (c : code dtyp) (va1 va2 : option (@ptr _ (@PTR Pa))),
    forallb (fun '(_, ins, _) => instr_varargs_irrel ins) c = true ->
    va_cfg_eq (denote_code c va1) (denote_code c va2).
Proof.
  induction c as [| [[iid ins] md] rest IH]; intros va1 va2 H; [apply va_cfg_eq_refl |].
  cbn in H; apply andb_true_iff in H as [Hi Hr].
  unfold denote_code in *; cbn [loop_monad ExtLib.Structures.Monad.bind Monad_itree].
  apply va_cfg_eq_bind; [exact (denote_instr_varargs_eq (iid, ins, md) va1 va2 Hi) | intros _; exact (IH va1 va2 Hr)].
Qed.

Lemma denote_block_varargs_eq {Pa : Params} :
  forall (G : CFG.cfg dtyp) b bid_from (va1 va2 : option (@ptr _ (@PTR Pa))),
    cfg_varargs_irrel G = true ->
    In b (blks G) ->
    va_cfg_eq (denote_block b bid_from va1) (denote_block b bid_from va2).
Proof.
  intros G b bid_from va1 va2 Hcfg Hb.
  unfold cfg_varargs_irrel in Hcfg; rewrite forallb_forall in Hcfg.
  pose proof (Hcfg b Hb) as Hbc.
  unfold denote_block.
  apply va_cfg_eq_bind; [apply va_cfg_eq_refl | intros _].
  apply va_cfg_eq_bind; [exact (denote_code_varargs_eq (blk_code b) va1 va2 Hbc) | intros _; apply va_cfg_eq_refl].
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
  - cbn [observe].
    right; apply CIH; exists m'.
    split; reflexivity.
  - cbn [observe]; destruct (classify_cfg_event e) as [le | oe].
    + destruct le as [id dv | id].
      * right; apply CIH; exists (k tt); split; reflexivity.
      * destruct (RM.find id env) as [dv |].
        -- right; apply CIH; exists (k dv); split; reflexivity.
        -- right; apply det_vis_both_refl; intros [].
    + destruct (classify_ow_event oe) as [dt | op w args | X' de].
      * revert k; right; apply CIH.
        exists (k (sigma 0%nat dt)); split; reflexivity.
      * revert k; intros k; destruct (pure_int_intrinsic_fn op w args) as [| | | rv];
          [right; apply det_vis_both_refl; intros []
          | right; apply det_vis_both_refl; intros []
          | right; apply det_vis_both_refl; intros []
          | right; apply CIH; exists (k rv); split; reflexivity].
      * right; apply det_vis_both_refl; intros x.
        right; apply CIH; exists (k x); split; reflexivity.
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
  - pstep; eapply NSD_Tau;
      [rewrite observe_run_draws, observe_run_cfg_locals, Ho; cbn; rewrite Hf; reflexivity
      | left; exact (IH Hr)].
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
    inversion Hms as [| ? [id_sd dv_s] ? dvs_sr Hpms Hms_r]; subst.
    cbn [phi_eval_pair_matches] in Hpms; destruct Hpms as [-> [_ Hsc_s]].
    destruct (IH rs rt dvs_sr ctx opt_pf penv Hms_r Hrest) as [dvs_tr Hrel_r].
    exists ((id_t, dv_s) :: dvs_tr).
    exact (CPR_Cons id_s id_t w dv_s dv_s rp dvs_sr dvs_tr Hsup Hsc_s Hsc_s (or_intror eq_refl) Hrel_r).
Qed.

Lemma check_loop_cutpoint_cfg_no_stack_det {Pa : Params} :
  forall allowed init_ctx (src_cfg tgt_cfg : CFG.cfg dtyp)
         (cert : proof_certificate) (lci : loop_cutpoint_invariant)
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
              (block_uas_for (init src_cfg) (pc_blocks cert) (init src_cfg))) as [ctx_ent |]; [| discriminate Hchk].
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as (((_ & _) & Href_init) & Hchk).
  destruct (fold_ub_assumptions cut_allowed (nls_evals_hdr s_s) [nls_ce_cond s_s]
              (filter_param_ub_ctx src_pnames ctx_ent)
              (block_uas_for (init src_cfg) (pc_blocks cert) (nls_bid_hdr s_s)))
    as [ctx_hdr |]; [| discriminate Hchk].
  rewrite !andb_true_iff in Hchk; destruct Hchk as (_ & Hchk).
  set (latch_uas := if raw_id_eqb (nls_bid_latch_entry s_s) (nls_bid_hdr s_s) then []
                    else block_uas_for (init src_cfg) (pc_blocks cert) (nls_bid_latch_entry s_s)) in *.
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
                (fun idx dt => cfg_param_dtyp_compatible_nth src_cfg arg_dtys idx dt Hcomp_s)) as Henv0_s.
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
        { rewrite Hms_eq; clear -Hrel; induction Hrel; cbn.
          - reflexivity.
          - f_equal; assumption. }
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
  pose proof (f_equal (fun u : itree' (@Det_OW_E Pa) R =>
    match u with
    | @VisF _ _ _ X_ u_e u_k =>
        existT (fun T : Type => (@Det_OW_E Pa T * (T -> itree (@Det_OW_E Pa) R))%type) X_ (u_e, u_k)
    | _ =>
        existT (fun T : Type => (@Det_OW_E Pa T * (T -> itree (@Det_OW_E Pa) R))%type) X (e, k)
    end) Ho') as Hs.
  destruct (match Hs in (_ = z)
            return exists Hc : X = projT1 z,
              eq_rect X (fun T : Type => (@Det_OW_E Pa T * (T -> itree (@Det_OW_E Pa) R))%type)
                (e, k) (projT1 z) Hc = projT2 z
            with
            | eq_refl => ex_intro _ eq_refl eq_refl
            end) as [Hc Hpair].
  clear Ho' Hs; cbn [projT1 projT2] in Hc, Hpair;
    revert e0 k0 Hns Hk Hpair; destruct Hc; intros e0 k0 Hns Hk Hpair; cbn in Hpair.
  injection Hpair as <- <-.
  split; [exact Hns | intros x; specialize (Hk x); pclearbot; exact Hk].
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
    + symmetry; exact (obs_eq_cfg_locals_draws sigma env u1 u2 Ho).
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
      * symmetry; exact (obs_eq_cfg_locals_draws sigma env u1 u2 Ho_eq).
      * reflexivity.
      * eapply paco2_mon; [apply det_ref_refl; intros; reflexivity | intros ? ? []].
    + pstep; apply DR_Step; unfold det_step_body.
      rewrite !observe_run_draws, !observe_run_cfg_locals, Ho1, Ho2, !observe_bind, Hom; cbn [observe].
      right; apply CIH; right.
      exists m'; split; reflexivity.
    + pstep; apply DR_Step; unfold det_step_body.
      rewrite !observe_run_draws, !observe_run_cfg_locals, Ho1, Ho2, !observe_bind, Hom; cbn [observe].
      destruct (classify_cfg_event e) as [le | oe].
      * destruct le as [id dv | id].
        -- right; apply CIH; right.
           exists (k tt); split; reflexivity.
        -- destruct (RM.find id env) as [dv |].
           ++ right; apply CIH; right.
              exists (k dv); split; reflexivity.
           ++ right; apply det_vis_both_refl; intros [].
      * destruct (classify_ow_event oe) as [dt | op w args | X' de].
        -- clear Hom e oe; revert k; right; apply CIH; right.
           exists (k (sigma 0%nat dt)); split; reflexivity.
        -- clear Hom e oe; revert k; intros k.
           destruct (pure_int_intrinsic_fn op w args) as [| | | rv];
             [right; apply det_vis_both_refl; intros []
             | right; apply det_vis_both_refl; intros []
             | right; apply det_vis_both_refl; intros []
             | right; apply CIH; right;
               exists (k rv); split; reflexivity].
        -- right; apply det_vis_both_refl; intros x.
           right; apply CIH; right.
           exists (k x); split; reflexivity.
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
                        (ITree.bind (ITree.bind m'
                           (fun lr => match lr with inl l => Tau (ITree.iter f2 l) | inr r0 => Ret r0 end)) g))))
        by (rewrite observe_run_draws, observe_run_cfg_locals, Ho2, !observe_bind, Hom; reflexivity).
      pose proof (no_stack_det_inv_tau _ _ Ho_t2 Hns2) as Hns2'.
      pstep; eapply NSD_Tau;
        [rewrite observe_run_draws, observe_run_cfg_locals, Ho1, !observe_bind, Hom; reflexivity | right].
      eapply CIH; [right; exists m'; split; reflexivity | exact Hns2'].
    + destruct (classify_cfg_event e) as [le | oe] eqn:Ece.
      * destruct le as [id dv | id].
        -- assert (Ho_t2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                           TauF (run_draws sigma (run_cfg_locals (RM.add id dv env)
                             (ITree.bind (ITree.bind (k tt)
                                (fun lr => match lr with inl l => Tau (ITree.iter f2 l) | inr r0 => Ret r0 end)) g))))
             by (rewrite observe_run_draws, observe_run_cfg_locals, Ho2, !observe_bind, Hom;
                 cbn [observe]; rewrite Ece; reflexivity).
           pose proof (no_stack_det_inv_tau _ _ Ho_t2 Hns2) as Hns2'.
           pstep; eapply NSD_Tau;
             [rewrite observe_run_draws, observe_run_cfg_locals, Ho1, !observe_bind, Hom;
              cbn [observe]; rewrite Ece; reflexivity | right].
           eapply CIH; [right; exists (k tt); split; reflexivity | exact Hns2'].
        -- destruct (RM.find id env) as [dv |] eqn:Ef.
           ++ assert (Ho_t2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                              TauF (run_draws sigma (run_cfg_locals env
                                (ITree.bind (ITree.bind (k dv)
                                   (fun lr =>
                                      match lr with inl l => Tau (ITree.iter f2 l) | inr r0 => Ret r0 end)) g))))
                by (rewrite observe_run_draws, observe_run_cfg_locals, Ho2, !observe_bind, Hom;
                    cbn [observe]; rewrite Ece, Ef; reflexivity).
              pose proof (no_stack_det_inv_tau _ _ Ho_t2 Hns2) as Hns2'.
              pstep; eapply NSD_Tau;
                [rewrite observe_run_draws, observe_run_cfg_locals, Ho1, !observe_bind, Hom;
                 cbn [observe]; rewrite Ece, Ef; reflexivity | right].
              eapply CIH; [right; exists (k dv); split; reflexivity | exact Hns2'].
           ++ assert (Ho_v : observe (run_draws sigma (run_cfg_locals env u2)) =
                             observe (run_draws sigma (run_cfg_locals env u1)))
                by (rewrite !observe_run_draws, !observe_run_cfg_locals, Ho1, Ho2, !observe_bind, Hom;
                    cbn [observe]; rewrite Ece, Ef; reflexivity).
              eapply paco1_mon; [exact (no_stack_det_obs_eq _ _ Ho_v Hns2) | intros ? []].
      * destruct (classify_ow_event oe) as [dt | op w args | X' de] eqn:Eoe.
        -- assert (Ho_t2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                           TauF (run_draws (shift_draw_strat sigma) (run_cfg_locals env
                             (ITree.bind (ITree.bind (k (sigma 0%nat dt))
                                (fun lr => match lr with inl l => Tau (ITree.iter f2 l) | inr r0 => Ret r0 end)) g))))
             by (rewrite observe_run_draws, observe_run_cfg_locals, Ho2, !observe_bind, Hom;
                 cbn [observe]; rewrite Ece, Eoe; reflexivity).
           pose proof (no_stack_det_inv_tau _ _ Ho_t2 Hns2) as Hns2'.
           pstep; eapply NSD_Tau;
             [rewrite observe_run_draws, observe_run_cfg_locals, Ho1, !observe_bind, Hom;
              cbn [observe]; rewrite Ece, Eoe; reflexivity | right].
           eapply CIH; [right; exists (k (sigma 0%nat dt)); split; reflexivity | exact Hns2'].
        -- destruct (pure_int_intrinsic_fn op w args) as [| | | rv] eqn:Epi.
           ++ assert (Ho_v : observe (run_draws sigma (run_cfg_locals env u2)) =
                             observe (run_draws sigma (run_cfg_locals env u1)))
                by (rewrite !observe_run_draws, !observe_run_cfg_locals, Ho1, Ho2, !observe_bind, Hom;
                    cbn [observe]; rewrite Ece, Eoe, Epi; reflexivity).
              eapply paco1_mon; [exact (no_stack_det_obs_eq _ _ Ho_v Hns2) | intros ? []].
           ++ assert (Ho_v : observe (run_draws sigma (run_cfg_locals env u2)) =
                             observe (run_draws sigma (run_cfg_locals env u1)))
                by (rewrite !observe_run_draws, !observe_run_cfg_locals, Ho1, Ho2, !observe_bind, Hom;
                    cbn [observe]; rewrite Ece, Eoe, Epi; reflexivity).
              eapply paco1_mon; [exact (no_stack_det_obs_eq _ _ Ho_v Hns2) | intros ? []].
           ++ assert (Ho_v : observe (run_draws sigma (run_cfg_locals env u2)) =
                             observe (run_draws sigma (run_cfg_locals env u1)))
                by (rewrite !observe_run_draws, !observe_run_cfg_locals, Ho1, Ho2, !observe_bind, Hom;
                    cbn [observe]; rewrite Ece, Eoe, Epi; reflexivity).
              eapply paco1_mon; [exact (no_stack_det_obs_eq _ _ Ho_v Hns2) | intros ? []].
           ++ assert (Ho_t2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                              TauF (run_draws sigma (run_cfg_locals env
                                (ITree.bind (ITree.bind (k rv)
                                   (fun lr =>
                                      match lr with inl l => Tau (ITree.iter f2 l) | inr r0 => Ret r0 end)) g))))
                by (rewrite observe_run_draws, observe_run_cfg_locals, Ho2, !observe_bind, Hom;
                    cbn [observe]; rewrite Ece, Eoe, Epi; reflexivity).
              pose proof (no_stack_det_inv_tau _ _ Ho_t2 Hns2) as Hns2'.
              pstep; eapply NSD_Tau;
                [rewrite observe_run_draws, observe_run_cfg_locals, Ho1, !observe_bind, Hom;
                 cbn [observe]; rewrite Ece, Eoe, Epi; reflexivity | right].
              eapply CIH; [right; exists (k rv); split; reflexivity | exact Hns2'].
        -- assert (Ho_v2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                           VisF de (fun x => run_draws sigma (run_cfg_locals env
                             (ITree.bind (ITree.bind (k x)
                                (fun lr => match lr with inl l => Tau (ITree.iter f2 l) | inr r0 => Ret r0 end)) g))))
             by (rewrite observe_run_draws, observe_run_cfg_locals, Ho2, !observe_bind, Hom;
                 cbn [observe]; rewrite Ece, Eoe; reflexivity).
           destruct (no_stack_det_inv_vis _ _ _ Ho_v2 Hns2) as [Hns_de Hk_ns].
           pstep; eapply NSD_Vis;
             [rewrite observe_run_draws, observe_run_cfg_locals, Ho1, !observe_bind, Hom;
              cbn [observe]; rewrite Ece, Eoe; reflexivity
             | exact Hns_de
             | intros x; right; eapply CIH;
               [right; exists (k x); split; reflexivity | exact (Hk_ns x)]].
Qed.

Definition ocfg_step_va_rel {Pa : Params}
  (bmap : rmap (block dtyp)) (va : option (@ptr _ (@PTR Pa)))
  (p : block_id * block_id)
  : @CFGtop Pa ((block_id * block_id) + ((block_id * block_id) + @dvalue Pa)) :=
  let '(bid_from, bid_src) := p in
  match RM.find bid_src bmap with
  | None => ret (inr (inl (bid_from, bid_src)))
  | Some block_src =>
      bd <- denote_block block_src bid_from va ;;
      match bd with
      | inr dv => ret (inr (inr dv))
      | inl bid_target => ret (inl (bid_src, bid_target))
      end
  end.

Lemma ocfg_step_varargs_eq {Pa : Params} :
  forall (bmap : rmap (block dtyp)) (va1 va2 : option (@ptr _ (@PTR Pa))),
    bmap_varargs_irrel bmap = true ->
    forall (p : block_id * block_id),
      va_cfg_eq (ocfg_step_va_rel bmap va1 p) (ocfg_step_va_rel bmap va2 p).
Proof.
  intros bmap va1 va2 Hbm [bid_from bid_src]; unfold ocfg_step_va_rel.
  destruct (RM.find bid_src bmap) as [b |] eqn:Hf; [| apply va_cfg_eq_refl].
  destruct (rmap_find_in_elements bmap bid_src b Hf) as [k' Hin].
  unfold bmap_varargs_irrel in Hbm; rewrite forallb_forall in Hbm.
  pose proof (Hbm (k', b) Hin) as Hbc; cbn in Hbc.
  apply va_cfg_eq_bind; [| intros [bt | dv]; apply va_cfg_eq_refl].
  unfold denote_block; apply va_cfg_eq_bind; [apply va_cfg_eq_refl | intros _].
  apply va_cfg_eq_bind; [exact (denote_code_varargs_eq (blk_code b) va1 va2 Hbc) | intros _; apply va_cfg_eq_refl].
Qed.

Lemma va_cfg_eq_det_ref {Pa : Params} {R : Type} :
  forall (sigma : @draw_strat Pa) env (u1 u2 : @CFGtop Pa R),
    va_cfg_eq u1 u2 ->
    det_ref eq
      (run_draws sigma (run_cfg_locals env u1))
      (run_draws sigma (run_cfg_locals env u2)).
Proof.
  pcofix CIH; intros sigma env u1 u2 Hva; punfold Hva; pstep.
  apply DR_Step; unfold det_step_body.
  rewrite !observe_run_draws, !observe_run_cfg_locals.
  destruct Hva.
  - reflexivity.
  - pclearbot; right; apply CIH; exact H.
  - destruct (classify_cfg_event e) as [le | oe].
    + destruct le as [id dv | id].
      * pclearbot; right; apply CIH; exact (H tt).
      * destruct (RM.find id env) as [dv |].
        -- pclearbot; right; apply CIH; exact (H dv).
        -- right; apply det_vis_both_refl; intros [].
    + destruct (classify_ow_event oe) as [dt | op w args | X' de].
      * pclearbot; right; apply CIH; exact (H (sigma 0%nat dt)).
      * destruct (pure_int_intrinsic_fn op w args) as [| | | rv].
        -- right; apply det_vis_both_refl; intros [].
        -- right; apply det_vis_both_refl; intros [].
        -- right; apply det_vis_both_refl; intros [].
        -- pclearbot; right; apply CIH; exact (H rv).
      * right; apply det_vis_both_refl; intros x.
        pclearbot; right; apply CIH; exact (H x).
  - cbn - [parse_pure_int_intrinsic pure_int_intrinsic_fn run_draws run_cfg_locals].
    destruct (parse_pure_int_intrinsic fname) as [[op w] |] eqn:Ep; [| exfalso; exact (H eq_refl)].
    destruct (pure_int_intrinsic_fn op w args) as [| | | rv].
    + right; apply det_vis_both_refl; intros [].
    + right; apply det_vis_both_refl; intros [].
    + right; apply det_vis_both_refl; intros [].
    + pclearbot; right; apply CIH; exact (H0 rv).
Qed.

Lemma va_cfg_eq_no_stack_det {Pa : Params} {R : Type} :
  forall (sigma : @draw_strat Pa) env (u1 u2 : @CFGtop Pa R),
    va_cfg_eq u1 u2 ->
    no_stack_det (run_draws sigma (run_cfg_locals env u2)) ->
    no_stack_det (run_draws sigma (run_cfg_locals env u1)).
Proof.
  pcofix CIH; intros sigma env u1 u2 Hva Hns2; punfold Hva; punfold Hns2; pstep.
  remember (observe u1) as o1 eqn:Ho_u1; remember (observe u2) as o2 eqn:Ho_u2.
  destruct Hva as [x | ta tb Htau | X e ka kb Hk | dt fname args va1 va2 ka kb Hp Hk].
  - destruct Hns2 as [x' Ho2 | m2 Ho2 _ | X2 e2 k2 Ho2 _ _];
      rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u2 in Ho2; try discriminate Ho2.
    injection Ho2 as <-; eapply NSD_Ret; rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u1; reflexivity.
  - pclearbot.
    assert (Ho2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                  TauF (run_draws sigma (run_cfg_locals env tb)))
      by (rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u2; reflexivity).
    destruct Hns2 as [x' Ho2' | m2 Ho2' Hm2 | X2 e2 k2 Ho2' _ _]; rewrite Ho2 in Ho2'; try discriminate Ho2'.
    injection Ho2' as <-; pclearbot; eapply NSD_Tau;
      [rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u1; reflexivity
      | right; exact (CIH sigma env ta tb Htau Hm2)].
  - destruct (classify_cfg_event e) as [le | oe] eqn:Ece.
    + destruct le as [id dv | id].
      * assert (Ho2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                      TauF (run_draws sigma (run_cfg_locals (RM.add id dv env) (kb tt))))
          by (rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u2; cbn; rewrite Ece; reflexivity).
        destruct Hns2 as [x' Ho2' | m2 Ho2' Hm2 | X2 e2 k2 Ho2' _ _]; rewrite Ho2 in Ho2'; try discriminate Ho2'.
        injection Ho2' as <-; pclearbot.
        eapply NSD_Tau;
          [rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u1; cbn; rewrite Ece; reflexivity
          | right; exact (CIH sigma (RM.add id dv env) (ka tt) (kb tt) (Hk tt) Hm2)].
      * destruct (RM.find id env) as [dv |] eqn:Ef.
        -- assert (Ho2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                         TauF (run_draws sigma (run_cfg_locals env (kb dv))))
             by (rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u2; cbn; rewrite Ece, Ef; reflexivity).
           destruct Hns2 as [x' Ho2' | m2 Ho2' Hm2 | X2 e2 k2 Ho2' _ _]; rewrite Ho2 in Ho2'; try discriminate Ho2'.
           injection Ho2' as <-; pclearbot.
           eapply NSD_Tau;
             [rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u1; cbn; rewrite Ece, Ef; reflexivity
             | right; exact (CIH sigma env (ka dv) (kb dv) (Hk dv) Hm2)].
        -- eapply NSD_Vis;
             [rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u1; cbn; rewrite Ece, Ef; reflexivity
             | reflexivity | intros []].
    + destruct (classify_ow_event oe) as [dt | op w args | X' de] eqn:Eoe.
      * assert (Ho2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                      TauF (run_draws (shift_draw_strat sigma) (run_cfg_locals env (kb (sigma 0%nat dt)))))
          by (rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u2; cbn; rewrite Ece, Eoe; reflexivity).
        destruct Hns2 as [x' Ho2' | m2 Ho2' Hm2 | X2 e2 k2 Ho2' _ _]; rewrite Ho2 in Ho2'; try discriminate Ho2'.
        injection Ho2' as <-; pclearbot.
        eapply NSD_Tau;
          [rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u1; cbn; rewrite Ece, Eoe; reflexivity
          | right; exact (CIH _ env _ _ (Hk _) Hm2)].
      * destruct (pure_int_intrinsic_fn op w args) as [| | | rv] eqn:Epi;
          [ eapply NSD_Vis;
              [rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u1;
               cbn; rewrite Ece, Eoe, Epi; reflexivity
              | reflexivity | intros []]
          | eapply NSD_Vis;
              [rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u1;
               cbn; rewrite Ece, Eoe, Epi; reflexivity
              | reflexivity | intros []]
          | eapply NSD_Vis;
              [rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u1;
               cbn; rewrite Ece, Eoe, Epi; reflexivity
              | reflexivity | intros []]
          |].
        assert (Ho2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                      TauF (run_draws sigma (run_cfg_locals env (kb rv))))
          by (rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u2; cbn; rewrite Ece, Eoe, Epi; reflexivity).
        destruct Hns2 as [x' Ho2' | m2 Ho2' Hm2 | X2 e2 k2 Ho2' _ _]; rewrite Ho2 in Ho2'; try discriminate Ho2'.
        injection Ho2' as <-; pclearbot.
        eapply NSD_Tau;
          [rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u1; cbn; rewrite Ece, Eoe, Epi; reflexivity
          | right; exact (CIH sigma env (ka rv) (kb rv) (Hk rv) Hm2)].
      * assert (Ho2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                      VisF de (fun x => run_draws sigma (run_cfg_locals env (kb x))))
          by (rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u2; cbn; rewrite Ece, Eoe; reflexivity).
        destruct (no_stack_det_inv_vis _ _ _ Ho2 (ltac:(pstep; exact Hns2))) as [Hns_de Hk_ns].
        eapply NSD_Vis;
          [rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u1; cbn; rewrite Ece, Eoe; reflexivity
          | exact Hns_de |].
        intros x; pclearbot; right; exact (CIH sigma env (ka x) (kb x) (Hk x) (Hk_ns x)).
  - destruct (parse_pure_int_intrinsic fname) as [[op w] |] eqn:Ep; [| exfalso; exact (Hp eq_refl)].
    destruct (pure_int_intrinsic_fn op w args) as [| | | rv] eqn:Epi;
      [ eapply NSD_Vis;
          [rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u1; cbn; rewrite Ep, Epi; reflexivity
          | reflexivity | intros []]
      | eapply NSD_Vis;
          [rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u1; cbn; rewrite Ep, Epi; reflexivity
          | reflexivity | intros []]
      | eapply NSD_Vis;
          [rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u1; cbn; rewrite Ep, Epi; reflexivity
          | reflexivity | intros []]
      |].
    assert (Ho2 : observe (run_draws sigma (run_cfg_locals env u2)) =
                  TauF (run_draws sigma (run_cfg_locals env (kb rv))))
      by (rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u2; cbn; rewrite Ep, Epi; reflexivity).
    destruct Hns2 as [x' Ho2' | m2 Ho2' Hm2 | X2 e2 k2 Ho2' _ _]; rewrite Ho2 in Ho2'; try discriminate Ho2'.
    injection Ho2' as <-; pclearbot.
    eapply NSD_Tau;
      [rewrite observe_run_draws, observe_run_cfg_locals, <- Ho_u1; cbn; rewrite Ep, Epi; reflexivity
      | right; exact (CIH sigma env (ka rv) (kb rv) (Hk rv) Hm2)].
Qed.

Lemma denote_cfg_varargs_det_ref {Pa : Params} :
  forall (G : CFG.cfg dtyp) (va1 va2 : option (@ptr _ (@PTR Pa))) (sigma : @draw_strat Pa) env,
    bmap_varargs_irrel (ocfg_map (blks G)) = true ->
    det_ref eq
      (run_draws sigma (run_cfg_locals env (denote_cfg_map (ocfg_map (blks G)) G va1)))
      (run_draws sigma (run_cfg_locals env (denote_cfg_map (ocfg_map (blks G)) G va2))).
Proof.
  intros G va1 va2 sigma env Hbm.
  apply va_cfg_eq_det_ref.
  unfold denote_cfg_map; cbn [ExtLib.Structures.Monad.bind Monad_itree]; unfold denote_ocfg_map.
  apply va_cfg_eq_bind; [| intros [? | ?]; apply va_cfg_eq_refl].
  apply va_cfg_eq_iter; exact (ocfg_step_varargs_eq (ocfg_map (blks G)) va1 va2 Hbm).
Qed.

Lemma denote_cfg_varargs_no_stack_det {Pa : Params} :
  forall (G : CFG.cfg dtyp) (va1 va2 : option (@ptr _ (@PTR Pa))) (sigma : @draw_strat Pa) env,
    bmap_varargs_irrel (ocfg_map (blks G)) = true ->
    no_stack_det (run_draws sigma (run_cfg_locals env (denote_cfg_map (ocfg_map (blks G)) G va2))) ->
    no_stack_det (run_draws sigma (run_cfg_locals env (denote_cfg_map (ocfg_map (blks G)) G va1))).
Proof.
  intros G va1 va2 sigma env Hbm Hns.
  eapply va_cfg_eq_no_stack_det; [| exact Hns].
  unfold denote_cfg_map; cbn [ExtLib.Structures.Monad.bind Monad_itree]; unfold denote_ocfg_map.
  apply va_cfg_eq_bind; [| intros [? | ?]; apply va_cfg_eq_refl].
  apply va_cfg_eq_iter; exact (ocfg_step_varargs_eq (ocfg_map (blks G)) va1 va2 Hbm).
Qed.

Lemma visf_eq_inv {E : Type -> Type} {R X1 X2 : Type}
  (e1 : E X1) (k1 : X1 -> itree E R)
  (e2 : E X2) (k2 : X2 -> itree E R) :
  (VisF e1 k1 : itree' E R) = VisF e2 k2 ->
  exists Hc : X1 = X2,
    eq_rect X1 E e1 X2 Hc = e2 /\
    (forall x : X1, k1 x = k2 (eq_rect X1 (fun T => T) x X2 Hc)).
Proof.
  intros H.
  pose proof (f_equal (fun u : itree' E R =>
    match u with
    | @VisF _ _ _ X_ u_e u_k =>
        existT (fun T : Type => (E T * (T -> itree E R))%type) X_ (u_e, u_k)
    | _ =>
        existT (fun T : Type => (E T * (T -> itree E R))%type) X1 (e1, k1)
    end) H) as Hs.
  destruct (match Hs in (_ = z)
            return exists Hc : X1 = projT1 z,
              eq_rect X1 (fun T : Type => (E T * (T -> itree E R))%type) (e1, k1) (projT1 z) Hc = projT2 z
            with
            | eq_refl => ex_intro _ eq_refl eq_refl
            end) as [Hc Hpair].
  clear H Hs; cbn [projT1 projT2] in Hc, Hpair;
    revert e2 k2 Hpair; destruct Hc; intros e2 k2 Hpair; cbn in Hpair.
  injection Hpair as <- <-.
  exists eq_refl; split; reflexivity.
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
    cfg_locals_tau_step s env u (shift_draw_strat s) env (k (s 0%nat dt))
| CLTS_PureIntIntrinsic s env u dt fname args va op w rv (k : @exc Pa + @dvalue Pa -> @CFGtop Pa A) :
    observe u = VisF (inr1 (inr1 (inl1 (Intrinsic dt fname args va)))) k ->
    parse_pure_int_intrinsic fname = Some (op, w) ->
    pure_int_intrinsic_fn op w args = raise_ret rv ->
    cfg_locals_tau_step s env u s env (k rv).

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
    + destruct ic as [dt fname args va]; cbn in Ho.
      destruct (parse_pure_int_intrinsic fname) as [[op w] |] eqn:Hpi; [| discriminate Ho].
      destruct (pure_int_intrinsic_fn op w args) as [| | | rv] eqn:Hfn; try discriminate Ho.
      injection Ho as <-; exists s, env, (k rv).
      split; [exact (CLTS_PureIntIntrinsic s env u dt fname args va op w rv k Hou Hpi Hfn) | reflexivity].
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
    | s env u dt k Hou
    | s env u dt fname args va op w rv k Hou Hpi Hfn ].
  - left; unfold src, dst.
    rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - right; exists (run_draws s (run_fn_frames (RM.add id dv env) stk exc_slot (ITree.bind (run_exc_k (k tt)) kf))).
    split;
      [unfold src; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity
      | unfold dst; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc_k; reflexivity].
  - right; exists (run_draws s (run_fn_frames env stk exc_slot (ITree.bind (run_exc_k (k dv)) kf))).
    split;
      [unfold src; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou;
       cbn; rewrite Ef; reflexivity
      | unfold dst; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc_k; reflexivity].
  - right;
      exists (run_draws (shift_draw_strat s)
                (run_fn_frames env stk exc_slot (ITree.bind (run_exc_k (k (s 0%nat dt))) kf))).
    split;
      [unfold src; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity
      | unfold dst; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc_k; reflexivity].
  - right; exists (run_draws s (run_fn_frames env stk exc_slot (ITree.bind (run_exc_k (k rv)) kf))).
    split;
      [unfold src; rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou;
       cbn; rewrite Hpi, Hfn; reflexivity
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
  - eapply DR_TauL;
      [exact Ho1a
      | eapply DR_TauR; [exact Ho2a | apply DR_Step; unfold det_step_body; rewrite Ho1b, Ho2b; exact Hself]].
Qed.

Definition opt_llvmexc_det_event {Pa : Params} {X : Type} (e : @Det_OW_E Pa X) : option (@exc Pa) :=
  match e with
  | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 (LLVMExc x)))))))) => Some x
  | _ => None
  end.

Definition is_oom_det_event {Pa : Params} {X : Type} (e : @Det_OW_E Pa X) : bool :=
  match e with
  | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 _)))))) => true
  | _ => false
  end.

Definition is_failure_det_event {Pa : Params} {X : Type} (e : @Det_OW_E Pa X) : bool :=
  match e with
  | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 _))))))))) => true
  | _ => false
  end.

Lemma det_vis_both_is_oom {Pa : Params} {R1 R2 X1 X2 : Type}
  (r : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop)
  (e1 : @Det_OW_E Pa X1) (k1 : X1 -> itree (@Det_OW_E Pa) R1)
  (e2 : @Det_OW_E Pa X2) (k2 : X2 -> itree (@Det_OW_E Pa) R2) :
  det_vis_both r e1 k1 e2 k2 ->
  is_oom_det_event e1 = is_oom_det_event e2.
Proof.
  unfold Det_OW_E in e1, e2.
  repeat match type of e1 with
         | (_ +' _) _ =>
             destruct e1 as [x1 | e1]; destruct e2 as [x2 | e2];
             try (cbn; intros; contradiction)
         end;
    intros _; reflexivity.
Qed.

Lemma det_vis_both_oom {Pa : Params} {R1 R2 : Type}
  (r : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop)
  {X1 X2 : Type}
  (e1 : @Det_OW_E Pa X1) (k1 : X1 -> itree (@Det_OW_E Pa) R1)
  (e2 : @Det_OW_E Pa X2) (k2 : X2 -> itree (@Det_OW_E Pa) R2) :
  is_oom_det_event e1 = true ->
  is_oom_det_event e2 = true ->
  det_vis_both r e1 k1 e2 k2.
Proof.
  unfold Det_OW_E in e1, e2.
  repeat match type of e1 with
         | (_ +' _) _ =>
             destruct e1 as [x1 | e1];
             [destruct e2 as [x2 | e2];
              [first
                 [ cbn; intros H1 _; discriminate H1
                 | destruct x1 as [u1], x2 as [u2]; destruct u1, u2; cbn;
                   intros _ _; split; [reflexivity | intros []] ]
              | intros H1 H2; cbn in H1, H2; first [discriminate H1 | discriminate H2]]
             | destruct e2 as [x2 | e2]; [intros H1 H2; cbn in H1, H2; first [discriminate H1 | discriminate H2] |]]
         end.
  cbn; intros H1 _; discriminate H1.
Qed.

Lemma det_vis_both_is_ub {Pa : Params} {R1 R2 X1 X2 : Type}
  (r : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop)
  (e1 : @Det_OW_E Pa X1) (k1 : X1 -> itree (@Det_OW_E Pa) R1)
  (e2 : @Det_OW_E Pa X2) (k2 : X2 -> itree (@Det_OW_E Pa) R2) :
  det_vis_both r e1 k1 e2 k2 ->
  det_is_ub e1 = det_is_ub e2.
Proof.
  unfold Det_OW_E in e1, e2.
  repeat match type of e1 with
         | (_ +' _) _ =>
             destruct e1 as [x1 | e1]; destruct e2 as [x2 | e2];
             try (cbn; intros; contradiction)
         end;
    intros _; first [reflexivity | destruct x1, x2; reflexivity].
Qed.

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

Lemma det_vis_both_failure {Pa : Params} {R1 R2 : Type}
  (r : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop)
  {X1 X2 : Type}
  (e1 : @Det_OW_E Pa X1) (k1 : X1 -> itree (@Det_OW_E Pa) R1)
  (e2 : @Det_OW_E Pa X2) (k2 : X2 -> itree (@Det_OW_E Pa) R2) :
  is_failure_det_event e1 = true ->
  is_failure_det_event e2 = true ->
  det_vis_both r e1 k1 e2 k2.
Proof.
  unfold Det_OW_E in e1, e2.
  repeat match type of e1 with
         | (_ +' _) _ =>
             destruct e1 as [? | e1]; [cbn; intros H; discriminate H |];
             destruct e2 as [? | e2]; [cbn; intros _ H; discriminate H |]
         end.
  intros _ _; destruct e1 as [u1], e2 as [u2]; destruct u1, u2; cbn.
  split; [reflexivity | intros []].
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
         intros H;
         intuition (try apply Hfg; try apply HP1; rewrite <- ?Hk1, <- ?Hk2; auto));
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
| CLVC_OOM :
    is_oom_det_event de = true ->
    det_is_ub de = false ->
    is_failure_det_event de = false ->
    opt_llvmexc_det_event de = None ->
    (forall B stk exc_slot (kf : @exc Pa + A -> @CFGtop Pa B),
       exists k_void : void -> itree (@Det_OW_E Pa) B,
         observe (run_draws s (run_fn_frames env stk exc_slot (ITree.bind (run_exc u) kf))) =
         VisF (@subevent OOME (@Det_OW_E Pa) _ void (ThrowOOM tt)) k_void) ->
    cfg_locals_vis_case s env u de kd
| CLVC_UB :
    det_is_ub de = true ->
    is_failure_det_event de = false ->
    is_oom_det_event de = false ->
    opt_llvmexc_det_event de = None ->
    (forall B stk exc_slot (kf : @exc Pa + A -> @CFGtop Pa B),
       exists k_void : void -> itree (@Det_OW_E Pa) B,
         observe (run_draws s (run_fn_frames env stk exc_slot (ITree.bind (run_exc u) kf))) =
         VisF (@subevent UBE (@Det_OW_E Pa) _ void (ThrowUB tt)) k_void) ->
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
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [Hc [Hde Hk]]; destruct Hc; cbn in Hde, Hk; subst de.
    apply CLVC_Other with (ku := ku); [reflexivity | intros x; exact (eq_sym (Hk x)) |].
    intros B stk exc_slot kf;
      rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [Hc [Hde Hk]]; destruct Hc; cbn in Hde, Hk; subst de.
    apply CLVC_Other with (ku := ku); [reflexivity | intros x; exact (eq_sym (Hk x)) |].
    intros B stk exc_slot kf;
      rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - destruct ic as [dt fname args va]; cbn in Ho.
    destruct (parse_pure_int_intrinsic fname) as [[op w] |] eqn:Hpi.
    + destruct (pure_int_intrinsic_fn op w args) as [err_s | oom_s | ub_s | rv] eqn:Hfn; try discriminate Ho.
      * destruct (visf_eq_inv _ _ _ _ Ho) as [Hc [Hde _]]; destruct Hc; cbn in Hde; subst de.
        apply CLVC_ReadFail; [reflexivity | reflexivity | reflexivity |].
        intros B stk exc_slot kf; eexists.
        rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou;
          cbn; rewrite Hpi, Hfn; reflexivity.
      * destruct (visf_eq_inv _ _ _ _ Ho) as [Hc [Hde _]]; destruct Hc; cbn in Hde; subst de.
        apply CLVC_OOM; [reflexivity | reflexivity | reflexivity | reflexivity |].
        intros B stk exc_slot kf; eexists.
        rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou;
          cbn; rewrite Hpi, Hfn; reflexivity.
      * destruct (visf_eq_inv _ _ _ _ Ho) as [Hc [Hde _]]; destruct Hc; cbn in Hde; subst de.
        apply CLVC_UB; [reflexivity | reflexivity | reflexivity | reflexivity |].
        intros B stk exc_slot kf; eexists.
        rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou;
          cbn; rewrite Hpi, Hfn; reflexivity.
    + destruct (visf_eq_inv _ _ _ _ Ho) as [Hc [Hde Hk]]; destruct Hc; cbn in Hde, Hk; subst de.
      apply CLVC_Other with (ku := ku); [reflexivity | intros x; exact (eq_sym (Hk x)) |].
      intros B stk exc_slot kf;
        rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou;
        cbn; rewrite Hpi; reflexivity.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [Hc [Hde Hk]]; destruct Hc; cbn in Hde, Hk; subst de.
    apply CLVC_Other with (ku := ku); [reflexivity | intros x; exact (eq_sym (Hk x)) |].
    intros B stk exc_slot kf;
      rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - destruct le as [id dv | id]; cbn in Ho; [discriminate Ho |].
    destruct (RM.find id env) as [dv |] eqn:Ef; [discriminate Ho |].
    destruct (visf_eq_inv _ _ _ _ Ho) as [Hc [Hde _]]; destruct Hc; cbn in Hde; subst de.
    apply CLVC_ReadFail; [reflexivity | reflexivity | reflexivity |].
    intros B stk exc_slot kf; eexists.
    rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou;
      cbn; rewrite Ef; cbn; reflexivity.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [Hc [Hde _]]; destruct Hc; cbn in Hde; subst de.
    apply CLVC_Stack; reflexivity.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [Hc [Hde Hk]]; destruct Hc; cbn in Hde, Hk; subst de.
    apply CLVC_Other with (ku := ku); [reflexivity | intros x; exact (eq_sym (Hk x)) |].
    intros B stk exc_slot kf;
      rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - destruct de_dr; cbn in Ho; discriminate Ho.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [Hc [Hde Hk]]; destruct Hc; cbn in Hde, Hk; subst de.
    apply CLVC_Other with (ku := ku); [reflexivity | intros x; exact (eq_sym (Hk x)) |].
    intros B stk exc_slot kf;
      rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - destruct xe as [ex]; cbn in Ho;
      destruct (visf_eq_inv _ _ _ _ Ho) as [Hc [Hde _]]; destruct Hc; cbn in Hde; subst de.
    apply (CLVC_Exc s env u _ kd ex); [reflexivity | reflexivity | reflexivity |].
    rewrite observe_run_exc, Hou; reflexivity.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [Hc [Hde Hk]]; destruct Hc; cbn in Hde, Hk; subst de.
    apply CLVC_Other with (ku := ku); [reflexivity | intros x; exact (eq_sym (Hk x)) |].
    intros B stk exc_slot kf;
      rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [Hc [Hde Hk]]; destruct Hc; cbn in Hde, Hk; subst de.
    apply CLVC_Other with (ku := ku); [reflexivity | intros x; exact (eq_sym (Hk x)) |].
    intros B stk exc_slot kf;
      rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
  - cbn in Ho; destruct (visf_eq_inv _ _ _ _ Ho) as [Hc [Hde Hk]]; destruct Hc; cbn in Hde, Hk; subst de.
    apply CLVC_Other with (ku := ku); [reflexivity | intros x; exact (eq_sym (Hk x)) |].
    intros B stk exc_slot kf;
      rewrite observe_run_draws, observe_run_fn_frames, observe_bind, observe_run_exc, Hou; reflexivity.
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
  - destruct ic as [dt fname args va]; cbn in Ho.
    destruct (parse_pure_int_intrinsic fname) as [[op w] |];
      [destruct (pure_int_intrinsic_fn op w args) |]; discriminate Ho.
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
        * eapply det_ref__mon;
            [exact Hk_ref | intros a b [Hab | []]; left; eapply paco2_mon; [exact Hab | intros ? ? []]].
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
        * destruct Hvc1 as [_ Hub_f _ _ | _ Hub_f | ex1 _ Hub_f _ _ | _ Hub_f _ _ _ | _ _ _ _ Hofub | ku1 _ _ Hofn1];
            try (rewrite Hub1 in Hub_f; discriminate Hub_f).
          -- destruct (Hofub R1 stk exc_slot kf1) as [kv1 Ho_fn1].
             apply DR_Step; unfold det_step_body; rewrite Ho_fn1; left; reflexivity.
          -- apply DR_Step; unfold det_step_body; rewrite (Hofn1 R1 stk exc_slot kf1); left; exact Hub1.
        * destruct (observe (run_draws s2_ (run_cfg_locals env2_ u2_))) as [| | X2 de2 kd2] eqn:Ho2; try contradiction.
          pose proof (det_vis_both_is_stack _ de1 kd1 de2 kd2 Hvb) as Hst_eq.
          rewrite Hns_de1 in Hst_eq; symmetry in Hst_eq.
          pose proof (det_vis_both_opt_llvmexc _ de1 kd1 de2 kd2 Hvb) as Hexc_eq.
          pose proof (det_vis_both_is_failure _ de1 kd1 de2 kd2 Hvb) as Hfl_eq.
          pose proof (det_vis_both_is_oom _ de1 kd1 de2 kd2 Hvb) as Hoom_eq.
          pose proof (det_vis_both_is_ub _ de1 kd1 de2 kd2 Hvb) as Hub_eq.
          pose proof (inv_cfg_locals_vis s2_ env2_ u2_ de2 kd2 Ho2) as Hvc2.
          destruct Hvc1 as
            [Hfl1 _ Hne1 Hof1 | Hst1 _ | ex1 Hex1 Hub1_f Hfl1_f Hou1_exc
            | Hoom1 _ Hfl1_f Hne1 Hof1 | Hub1_ub _ _ _ Hofub1 | ku1 Hne1 Hkd1 Hofn1].
          -- rewrite Hfl1 in Hfl_eq; symmetry in Hfl_eq.
             destruct (Hof1 R1 stk exc_slot kf1) as [kv1 Ho_fn1].
             destruct Hvc2 as
               [_ _ _ Hof2 | Hst2 _ | ex2 _ _ Hfl2_f _
               | _ _ Hfl2_f _ _ | _ Hfl2_f _ _ _ | ku2 _ _ Hofn2];
               try (rewrite Hst2 in Hst_eq; discriminate Hst_eq);
               try (rewrite Hfl2_f in Hfl_eq; discriminate Hfl_eq).
             ++ destruct (Hof2 R2 stk exc_slot kf2) as [kv2 Ho_fn2].
                apply DR_Step; unfold det_step_body; rewrite Ho_fn1, Ho_fn2;
                  right; apply det_vis_both_refl; intros [].
             ++ apply DR_Step; unfold det_step_body; rewrite Ho_fn1, (Hofn2 R2 stk exc_slot kf2).
                right; apply det_vis_both_failure; [reflexivity | exact Hfl_eq].
          -- rewrite Hst1 in Hns_de1; discriminate Hns_de1.
          -- rewrite Hex1 in Hexc_eq; symmetry in Hexc_eq.
             destruct Hvc2 as
               [_ _ Hne2 _ | Hst2 _ | ex2 Hex2 _ _ Hou2_exc
               | _ _ _ Hne2 _ | _ _ _ Hne2 _ | ku2 Hne2 _ _];
               try (rewrite Hne2 in Hexc_eq; discriminate Hexc_eq);
               try (rewrite Hst2 in Hst_eq; discriminate Hst_eq).
             rewrite Hex2 in Hexc_eq; injection Hexc_eq as ->.
             pose proof (Hkf s1_ s2_ env1_ env2_ (inl ex1) (inl ex1) eq_refl) as Hk_ref.
             punfold Hk_ref.
             eapply det_ref__obs_eq with
               (t1 := run_draws s1_ (run_fn_frames env1_ stk exc_slot (kf1 (inl ex1))))
               (t2 := run_draws s2_ (run_fn_frames env2_ stk exc_slot (kf2 (inl ex1)))).
             ++ apply obs_eq_fn_frames_draws; rewrite observe_bind, Hou1_exc; reflexivity.
             ++ apply obs_eq_fn_frames_draws; rewrite observe_bind, Hou2_exc; reflexivity.
             ++ eapply det_ref__mon;
                  [exact Hk_ref | intros a b [Hab | []]; left; eapply paco2_mon; [exact Hab | intros ? ? []]].
          -- rewrite Hoom1 in Hoom_eq; symmetry in Hoom_eq.
             destruct Hvc2 as
               [Hfl2 _ _ _ | Hst2 _ | ex2 Hex2 _ _ _
               | Hoom2 _ _ _ Hof2 | _ _ Hoom2_f _ _ | ku2 _ _ Hofn2];
               try (rewrite Hst2 in Hst_eq; discriminate Hst_eq);
               try (rewrite Hoom2_f in Hoom_eq; discriminate Hoom_eq).
             ++ rewrite Hfl1_f, Hfl2 in Hfl_eq; discriminate Hfl_eq.
             ++ rewrite Hex2 in Hexc_eq; rewrite Hne1 in Hexc_eq; discriminate Hexc_eq.
             ++ destruct (Hof1 R1 stk exc_slot kf1) as [kv1 Ho_fn1];
                  destruct (Hof2 R2 stk exc_slot kf2) as [kv2 Ho_fn2].
                apply DR_Step; unfold det_step_body; rewrite Ho_fn1, Ho_fn2;
                  right; apply det_vis_both_refl; intros [].
             ++ destruct (Hof1 R1 stk exc_slot kf1) as [kv1 Ho_fn1].
                apply DR_Step; unfold det_step_body; rewrite Ho_fn1, (Hofn2 R2 stk exc_slot kf2).
                right; apply det_vis_both_oom; [reflexivity | exact Hoom_eq].
          -- destruct (Hofub1 R1 stk exc_slot kf1) as [kv1 Ho_fn1].
             apply DR_Step; unfold det_step_body; rewrite Ho_fn1; left; reflexivity.
          -- rewrite Hne1 in Hexc_eq; symmetry in Hexc_eq.
             destruct Hvc2 as
               [Hfl2 _ _ Hof2 | Hst2 _ | ex2 Hex2 _ _ _
               | Hoom2 _ _ _ Hof2 | Hub2_ub _ _ _ _ | ku2 _ Hkd2 Hofn2].
             ++ rewrite Hfl2 in Hfl_eq.
                destruct (Hof2 R2 stk exc_slot kf2) as [kv2 Ho_fn2].
                apply DR_Step; unfold det_step_body; rewrite (Hofn1 R1 stk exc_slot kf1), Ho_fn2.
                right; apply det_vis_both_failure; [exact Hfl_eq | reflexivity].
             ++ rewrite Hst2 in Hst_eq; discriminate Hst_eq.
             ++ rewrite Hex2 in Hexc_eq; discriminate Hexc_eq.
             ++ rewrite Hoom2 in Hoom_eq.
                destruct (Hof2 R2 stk exc_slot kf2) as [kv2 Ho_fn2].
                apply DR_Step; unfold det_step_body; rewrite (Hofn1 R1 stk exc_slot kf1), Ho_fn2.
                right; apply det_vis_both_oom; [exact Hoom_eq | reflexivity].
             ++ rewrite Hub2_ub in Hub_eq.
                apply DR_Step; unfold det_step_body; rewrite (Hofn1 R1 stk exc_slot kf1); left; exact Hub_eq.
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
  rewrite !observe_run_draws, !observe_run_fn_frames, Ho1, Ho2; cbn - [det_vis_both].
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
        [unfold load, trigger;
         cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
         rewrite !observe_bind; reflexivity
        | unfold load, trigger;
          cbn [ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
          rewrite !observe_bind; reflexivity
        | intros dv; rewrite ?observe_bind; reflexivity
        | intros dv; rewrite ?observe_bind; reflexivity
        | intros dv; exact Hk].
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
  unfold apply_attrs, apply_value_attrs; cbn zeta; fold v'; rewrite <- Heqv.
  destruct (existsb attr_is_noundef s_attrs && negb (dvalue_well_defined v')) eqn:Eub_s.
  - pstep; apply DR_Step; unfold det_step_body.
    rewrite observe_run_draws, observe_run_fn_frames;
      cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
      rewrite !observe_bind; cbn; left; reflexivity.
  - assert (Eub_t : existsb attr_is_noundef t_attrs && negb (dvalue_well_defined v') = false).
    { destruct (existsb attr_is_noundef t_attrs) eqn:Et; [| reflexivity].
      cbn in Hnu_imp; rewrite Hnu_imp in Eub_s; exact Eub_s. }
    rewrite Eub_t.
    eapply det_ref_obs_eq with
      (t1 := run_draws s1 (run_fn_frames env1 stk1 exc1
               (ITree.bind (ITree.bind (assert_attrs_dereferenceable s_attrs v' msg_s) (fun _ => ret v')) k1)))
      (t2 := run_draws s2 (run_fn_frames env2 stk2 exc2
               (ITree.bind (ITree.bind (assert_attrs_dereferenceable t_attrs v' msg_t) (fun _ => ret v')) k2))).
    + apply obs_eq_fn_frames_draws;
        cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite !observe_bind; cbn - [assert_attrs_dereferenceable ITree.bind];
        repeat rewrite observe_bind; reflexivity.
    + apply obs_eq_fn_frames_draws;
        cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
        rewrite !observe_bind; cbn - [assert_attrs_dereferenceable ITree.bind];
        repeat rewrite observe_bind; reflexivity.
    + eapply fn_frames_bind_assoc_both.
      eapply step_assert_deref_eq; [exact Hsame |].
      eapply det_ref_obs_eq;
        [apply obs_eq_fn_frames_draws; symmetry;
         cbn [ExtLib.Structures.Monad.ret Monad_itree]; rewrite observe_bind; reflexivity
        | apply obs_eq_fn_frames_draws; symmetry;
          cbn [ExtLib.Structures.Monad.ret Monad_itree]; rewrite observe_bind; reflexivity
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

Lemma step_fn_frames_raise_both {Pa : Params} {X R1 R2 : Type}
  (RR : R1 -> R2 -> Prop) :
  forall (s1 s2 : @draw_strat Pa) e1 cstk1 exc1 e2 cstk2 exc2
         msg (k1 : X -> @CFGtop Pa R1) (k2 : X -> @CFGtop Pa R2),
    det_ref RR
      (run_draws s1 (run_fn_frames e1 cstk1 exc1 (ITree.bind (raise msg) k1)))
      (run_draws s2 (run_fn_frames e2 cstk2 exc2 (ITree.bind (raise msg) k2))).
Proof.
  intros s1 s2 e1 cstk1 exc1 e2 cstk2 exc2 msg k1 k2.
  pstep; apply DR_Step; unfold det_step_body.
  rewrite !observe_run_draws, !observe_run_fn_frames, !observe_bind; cbn.
  right; split; [reflexivity | intros []].
Qed.

Lemma step_push_call_frame {Pa : Params} {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop) :
  forall (src_df tgt_df : definition dtyp (CFG.cfg dtyp))
         (vs' : list (@dvalue Pa))
         (s1 s2 : @draw_strat Pa) cenv cstk exc_slot
         (k1 : @ptr _ (@PTR Pa) -> @CFGtop Pa R1)
         (k2 : @ptr _ (@PTR Pa) -> @CFGtop Pa R2),
    List.length (df_args src_df) = List.length vs' ->
    List.length (df_args tgt_df) = List.length vs' ->
    (forall varg : @ptr _ (@PTR Pa),
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
             (ITree.bind (mem_push ;;
                          stack_push bs_s ;;
                          varargs <- alloca dt0 1 None ;;
                          store dt0 varargs (DVALUE_Struct true []) ;;
                          match varargs with
                          | DVALUE_Base (DVALUE_Pointer varg) => ret varg
                          | _ => raise "Non-address returned from alloca of varargs"
                          end) k1)))
    (t2 := run_draws s2 (run_fn_frames cenv cstk exc_slot
             (ITree.bind (mem_push ;;
                          stack_push bs_t ;;
                          varargs <- alloca dt0 1 None ;;
                          store dt0 varargs (DVALUE_Struct true []) ;;
                          match varargs with
                          | DVALUE_Base (DVALUE_Pointer varg) => ret varg
                          | _ => raise "Non-address returned from alloca of varargs"
                          end) k2))).
  - apply obs_eq_fn_frames_draws; symmetry;
      cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
      rewrite observe_bind; rewrite observe_bind at 1;
      cbn [observe EOU_to_itree map_monad EOU_monad ExtLib.Structures.Monad.ret];
      cbn iota beta;
      rewrite observe_bind at 1;
      cbn [observe]; cbn iota beta; reflexivity.
  - apply obs_eq_fn_frames_draws; symmetry;
      cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
      rewrite observe_bind; rewrite observe_bind at 1;
      cbn [observe EOU_to_itree map_monad EOU_monad ExtLib.Structures.Monad.ret];
      cbn iota beta;
      rewrite observe_bind at 1;
      cbn [observe]; cbn iota beta; reflexivity.
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
      | intros []; rewrite !observe_bind; reflexivity
      | intros []; rewrite !observe_bind; reflexivity
      | intros []].
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
    + replace (push_frame_bindings bs_s) with (init_cfg_locals (df_args src_df) vs')
        by (unfold bs_s; symmetry; exact (push_frame_bindings_eq_init (df_args src_df) vs' Hlens)).
      apply obs_eq_fn_frames_draws; symmetry; rewrite !observe_bind; reflexivity.
    + replace (push_frame_bindings bs_t) with (init_cfg_locals (df_args tgt_df) vs')
        by (unfold bs_t; symmetry; exact (push_frame_bindings_eq_init (df_args tgt_df) vs' Hlent)).
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
        | intros []; rewrite !observe_bind; reflexivity
        | intros []; rewrite !observe_bind; reflexivity
        | intros []].
      destruct va as [[varg | | | | | | | ] | | ];
        [| apply step_fn_frames_raise_both ..].
      eapply det_ref_obs_eq;
        [apply obs_eq_fn_frames_draws; symmetry;
         cbn [ExtLib.Structures.Monad.ret Monad_itree];
         rewrite observe_bind; cbn [observe]; cbn iota beta; reflexivity
        | apply obs_eq_fn_frames_draws; symmetry;
          cbn [ExtLib.Structures.Monad.ret Monad_itree];
          rewrite observe_bind; cbn [observe]; cbn iota beta; reflexivity
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
        discriminate (Hnuw_imp eq_refl). }
      rewrite Enuw_t.
      pstep; apply DR_Step; unfold det_step_body.
      rewrite !observe_run_draws, !observe_run_fn_frames;
        cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree EOU_monad];
        rewrite !observe_bind; cbn; reflexivity.
  - unfold check_call_return, check_call_result.
    destruct (existsb fn_attr_is_noreturn fattrs_s) eqn:Enr_s.
    + apply fn_frames_raiseUB_bind.
    + assert (Enr_t : existsb fn_attr_is_noreturn fattrs_t = false).
      { destruct (existsb fn_attr_is_noreturn fattrs_t) eqn:Et; [| reflexivity].
        discriminate (Hnr_imp eq_refl). }
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
          rewrite (Hnc_imp eq_refl) in Enc_s.
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
        -- apply obs_eq_fn_frames_draws; symmetry;
             cbn [EOU_to_itree value_metadata_range ExtLib.Structures.Monad.bind
                  ExtLib.Structures.Monad.ret Monad_itree EOU_monad];
             rewrite !observe_bind; cbn [observe]; cbn iota beta; reflexivity.
        -- apply obs_eq_fn_frames_draws; symmetry;
             cbn [EOU_to_itree value_metadata_range ExtLib.Structures.Monad.bind
                  ExtLib.Structures.Monad.ret Monad_itree EOU_monad];
             rewrite !observe_bind; cbn [observe]; cbn iota beta; reflexivity.
        -- destruct Hrv as [Hps1 | <-].
           ++ assert (Edv1 : dv1 = DVALUE_Base DVALUE_Poison)
                by (destruct dv1 as [[| | | | | | | ] | | ]; try discriminate Hps1; reflexivity).
              subst dv1.
              destruct (existsb attr_is_noundef s_ret) eqn:Enu_sr.
              ** unfold apply_attrs, apply_value_attrs.
                 rewrite value_attrs_poison_poison, Enu_sr; cbn [dvalue_well_defined negb andb].
                 pstep; apply DR_Step; unfold det_step_body.
                 rewrite observe_run_draws, observe_run_fn_frames;
                   cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
                   rewrite !observe_bind; cbn; left; reflexivity.
              ** assert (Enu_tr : existsb attr_is_noundef t_ret = false).
                 { destruct (existsb attr_is_noundef t_ret) eqn:Et; [| reflexivity].
                   rewrite ?Et, ?Enu_sr in Hnu_ret_imp; cbn in Hnu_ret_imp; discriminate Hnu_ret_imp. }
                 assert (Edr_t : find_option attr_dereferenceable t_ret = None).
                 { destruct (find_option attr_dereferenceable t_ret); [| reflexivity].
                   rewrite ?Enu_sr in Htd_imp; cbn in Htd_imp; discriminate Htd_imp. }
                 assert (Edr_s : find_option attr_dereferenceable s_ret = None).
                 { rewrite Edr_t in Hderef; destruct (find_option attr_dereferenceable s_ret) as [[b_dr n_dr] |];
                     [cbn [opt_deref_same_b] in Hderef; discriminate Hderef | reflexivity]. }
                 unfold apply_attrs, apply_value_attrs, assert_attrs_dereferenceable.
                 rewrite value_attrs_poison_poison, Enu_sr, Enu_tr, Edr_s, Edr_t; cbn [andb].
                 pstep; apply DR_Step; unfold det_step_body.
                 rewrite !observe_run_draws, !observe_run_fn_frames;
                   cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree];
                   repeat (rewrite observe_bind; cbn [observe]; cbn iota beta);
                   left; reflexivity.
           ++ eapply step_apply_attrs_eq; [exact Hpm_ret | exact Hderef | intros _Eub].
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

Lemma dc_name_tfmap (f : typ -> dtyp) (d : declaration typ) :
  dc_name (tfmap f d) = dc_name d.
Proof.
  cbn [dc_name tfmap TFunctor_declaration endo Endo_id]; reflexivity.
Qed.

Lemma dc_param_attrs_tfmap (f : typ -> dtyp) (d : declaration typ) :
  dc_param_attrs (tfmap f d) = dc_param_attrs d.
Proof.
  destruct d as [nm ty [r ps] ats ans].
  cbn [dc_param_attrs tfmap TFunctor_declaration endo Endo_prod Endo_list Endo_id].
  f_equal.
  - unfold endo, Endo_list, Endo_id.
    induction r as [| a ra IH]; [reflexivity | cbn [List.map]; cbn beta; f_equal; exact IH].
  - unfold endo, Endo_list, Endo_id.
    induction ps as [| p rp IH]; [reflexivity | cbn [List.map]; cbn beta; f_equal; [| exact IH]].
    induction p as [| x rx IHx]; [reflexivity | cbn [endo Endo_list Endo_id List.map]; cbn beta; f_equal; exact IHx].
Qed.

Lemma dc_attrs_tfmap (f : typ -> dtyp) (d : declaration typ) :
  dc_attrs (tfmap f d) = dc_attrs d.
Proof.
  destruct d as [nm ty pa ats ans].
  cbn [dc_attrs tfmap TFunctor_declaration endo Endo_list Endo_id].
  unfold endo, Endo_list, Endo_id.
  induction ats as [| a ra IH]; [reflexivity | cbn [List.map]; cbn beta; f_equal; exact IH].
Qed.

Lemma dc_annotations_tfmap (f : typ -> dtyp) (d : declaration typ) :
  dc_annotations (tfmap f d) = tfmap f (dc_annotations d).
Proof.
  cbn [dc_annotations tfmap TFunctor_declaration]; reflexivity.
Qed.

Lemma df_args_tfmap (f : typ -> dtyp) (d : definition typ (CFG.cfg typ)) :
  df_args (tfmap f d) = df_args d.
Proof.
  destruct d as [proto args body].
  cbn [df_args tfmap TFunctor_definition endo Endo_list Endo_id].
  unfold endo, Endo_list, Endo_id.
  induction args as [| a ra IH]; [reflexivity | cbn [List.map]; cbn beta; f_equal; exact IH].
Qed.

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
  rewrite Eproto_s, Eproto_t.
  rewrite !dc_param_attrs_tfmap, !dc_name_tfmap, !dc_attrs_tfmap, !dc_annotations_tfmap.
  rewrite Edcpa_s, Edcpa_t.
  rewrite !anns_cconv_tfmap.
  change (df_instrs src_df) with src_cfg.
  change (df_instrs tgt_df) with tgt_cfg.
  cbn [fst snd].
  set (fcc_s := anns_cconv (dc_annotations (df_prototype src_defn))) in *.
  set (fcc_t := anns_cconv (dc_annotations (df_prototype tgt_defn))) in *.
  set (fname_s := ShowAST.show_raw_id (dc_name (df_prototype src_defn))).
  set (fname_t := ShowAST.show_raw_id (dc_name (df_prototype tgt_defn))).
  destruct (cconv_eqb cc fcc_s) eqn:Ecc_s.
  - assert (Ecc_t : cconv_eqb cc fcc_t = true)
      by (rewrite <- (cconv_eqb_same_caller fcc_s fcc_t cc Hcc); exact Ecc_s).
    destruct (args_attrs_src_ub s_pattrs0 vs) eqn:Eargs_ub.
    + exists sigma_tgt; split; [exact Hwfsig_t |].
      unfold check_cconv; rewrite Ecc_s, Ecc_t.
      eapply det_ref_obs_eq;
        [apply obs_eq_fn_frames_draws; symmetry;
         cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree EOU_monad];
         rewrite observe_bind; cbn [observe]; cbn iota beta; reflexivity
        | apply obs_eq_fn_frames_draws; symmetry;
          cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree EOU_monad];
          rewrite observe_bind; cbn [observe]; cbn iota beta; reflexivity
        |].
      eapply step_apply_args_attrs; [exact Hlen_sp_vs | exact Hpa_ref | exact Hderef_args |].
      intros Habs; rewrite Eargs_ub in Habs; discriminate Habs.
    + destruct (eval_args_attrs_poison_wf (List.map (typ_to_dtyp src_tenv) arg_tys) s_pattrs0 vs
                  Hvs Hpres Eargs_ub)
        as (Hlen_vs' & Hty_vs' & Hnu_vs').
      set (vs' := eval_args_attrs_poison s_pattrs0 vs) in *.
      destruct (Hcfg_ref vs' Hty_vs' Hnu_vs' sigma_tgt Hwfsig_t)
        as (sigma_src & Hwfsig_s & Hdr_cfg & Hns_cfg).
      exists sigma_src; split; [exact Hwfsig_s |].
      unfold check_cconv; rewrite Ecc_s, Ecc_t.
      eapply det_ref_obs_eq;
        [apply obs_eq_fn_frames_draws; symmetry;
         cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree EOU_monad];
         rewrite observe_bind; cbn [observe]; cbn iota beta; reflexivity
        | apply obs_eq_fn_frames_draws; symmetry;
          cbn [EOU_to_itree ExtLib.Structures.Monad.bind ExtLib.Structures.Monad.ret Monad_itree EOU_monad];
          rewrite observe_bind; cbn [observe]; cbn iota beta; reflexivity
        |].
      eapply step_apply_args_attrs; [exact Hlen_sp_vs | exact Hpa_ref | exact Hderef_args |].
      intros _Eub; fold vs'.
      assert (Hlen_dfa_s : List.length (df_args src_df) = List.length vs')
        by (unfold src_df; rewrite df_args_tfmap, Hdfa_s;
            exact (eq_trans (eq_sym Hlen_ad)
                     (eq_trans (eq_sym Hlen_vs) (eq_sym Hlen_vs')))).
      assert (Hlen_dfa_t : List.length (df_args tgt_df) = List.length vs')
        by (unfold tgt_df; rewrite df_args_tfmap, Hdfa_t;
            exact (eq_trans (eq_sym Hlen_st)
                     (eq_trans (eq_sym Hlen_ad)
                        (eq_trans (eq_sym Hlen_vs) (eq_sym Hlen_vs'))))).
      eapply step_push_call_frame with (src_df := src_df) (tgt_df := tgt_df);
        [exact Hlen_dfa_s | exact Hlen_dfa_t | intros varg].
      unfold src_df, tgt_df; rewrite !df_args_tfmap, Hdfa_s, Hdfa_t.
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
    unfold check_cconv; rewrite Ecc_s;
      cbn [EOU_to_itree ExtLib.Structures.Monad.bind Monad_itree];
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

