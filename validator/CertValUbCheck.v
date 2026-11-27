(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Source UB Discharge & Target UB-Safety Checking ([CertValidator.CertValUbCheck])

    Purpose:
      Defines structural justification checks for source [ub_assumption]s
      ([check_ub_assumption_justified], [check_ub_assumptions_list]), target
      scalar/void UB-safety checking, and [check_scalar_dag_via_ro].

    Trust Contract & Fail-Closed Boundary:
      Fail-closed UB assumption and target safety verifier
      ([check_ub_assumptions_list_sound], [check_scalar_dag_via_ro_sound]);
      unjustified source UBs or potentially-UB target terms are rejected ([false]).

    Assumptions:
      Depends on Stdlib, [Paco], [ITree], [ExtLib], [Vellvm], [Diag], and
      [CertFormat]/[AigLrat]/[AlgRules]/[CfgDag]/[CertVal*]; zero custom axioms.

    Section Outline:
      5.6 Source UB Assumption Discharge, Target UB-Safety & Certificate
      Obligation Checker ([check_ub_assumptions_list], [check_scalar_dag_via_ro]). *)

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
  CertValCfgDag.

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

(** *** 5.6 Source UB Assumption Discharge, Target UB-Safety & Certificate Obligation Checker *)

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
    destruct Hin as [<- | Hin]; [exists dv0; exact Es | exact (IH v e Hev Hin)].
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
      exists op, w, fl, lhs; split;
        [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
    + destruct (IHr Hr) as (op & w & fl & lhs & Hop & Hdef & Hsub).
      exists op, w, fl, lhs; split;
        [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
  - apply orb_true_iff in H as [Hl | Hr].
    + destruct (IHl Hl) as (op & w & fl & lhs & Hop & Hdef & Hsub).
      exists op, w, fl, lhs; split;
        [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
    + destruct (IHr Hr) as (op & w & fl & lhs & Hop & Hdef & Hsub).
      exists op, w, fl, lhs; split;
        [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
  - destruct (IHo H) as (op & w & fl & lhs & Hop & Hdef & Hsub).
    exists op, w, fl, lhs; split;
      [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
  - rewrite !orb_true_iff in H; destruct H as [[Hc | Ht] | Hf].
    + destruct (IHc Hc) as (op & w & fl & lhs & Hop & Hdef & Hsub).
      exists op, w, fl, lhs; split;
        [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
    + destruct (IHt Ht) as (op & w & fl & lhs & Hop & Hdef & Hsub).
      exists op, w, fl, lhs; split;
        [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
    + destruct (IHf Hf) as (op & w & fl & lhs & Hop & Hdef & Hsub).
      exists op, w, fl, lhs; split;
        [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
  - destruct (IHo H) as (op & w & fl & lhs & Hop & Hdef & Hsub).
    exists op, w, fl, lhs; split;
      [exact Hop | split; [exact Hdef | cbn [is_syntactic_subexpr]; rewrite !orb_true_iff; auto]].
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
  pose proof (dvalue_base_I_width_eq _ _ _ _ Heq0) as Hweq; subst w0; clear il0 Heq0.
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
      rewrite Er in Eer'.
      pose proof (eou_dvalue_I_width_eq _ _ _ _ Eer') as Hweq; subst w'.
      pose proof (eou_dvalue_I_same_sz_inj _ _ _ Eer') as <-.
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
      destruct (eval_cert_expr penv [] foracle l) as [| | sl | vl] eqn:El;
        cbn [eou_bind] in Hev; try discriminate Hev.
      * inversion Hev; subst sl; exact (IHl ctx src_evals penv foracle msg Hsl Hwtl Hpl Hctx Hsrc El).
      * destruct (eval_cert_expr penv [] foracle r) as [| | sr | vr] eqn:Er;
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
                unfold eval_closed_cert_expr in Er'; rewrite Er in Er'; injection Er' as ->.
                destruct Hwfr as [Hps | [ir0 Heq0]]; [discriminate Hps |].
                pose proof (dvalue_base_I_width_eq _ _ _ _ Heq0) as Hweq; subst w'.
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
                     unfold eval_closed_cert_expr in Er'; rewrite Er in Er'; injection Er' as ->.
                     destruct Hwfr as [Hps | [ir0 Heq0]]; [discriminate Hps |].
                     pose proof (dvalue_base_I_width_eq _ _ _ _ Heq0) as ->.
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
                     destruct (Hextract_nz Hnz_or) as [ir [-> Hnz]].
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
                     unfold eval_closed_cert_expr in Er'; rewrite Er in Er'; injection Er' as ->.
                     destruct Hwfr as [Hps | [ir0 Heq0]]; [discriminate Hps |].
                     pose proof (dvalue_base_I_width_eq _ _ _ _ Heq0) as ->.
                     destruct Hwfl as [-> | [il ->]].
                     +++ cbn in Hev; destruct (Z.eq_dec (@Integers.signed w ir') (-1)%Z) as [Hm1 | _];
                           [exact (Hnsm Hm1) | cbn in Hev; discriminate Hev].
                     +++ unfold eval_iop in Hev; rewrite eval_iop_integer_base_same_width in Hev.
                         unfold cert_to_ibinop, eval_int_op in Hev; cbn in Hev.
                         rewrite (proj2 (Z.eqb_neq (@Integers.signed w ir') 0%Z) Hnsz) in Hev.
                         rewrite (proj2 (Z.eqb_neq (@Integers.signed w ir') (-1)%Z) Hnsm), Bool.andb_false_r in Hev.
                         cbn in Hev; discriminate Hev.
                 --- rewrite !andb_true_iff in Hguarded; destruct Hguarded as ([Hnz_or Hdefl] & Hnovf).
                     destruct (Hextract_nz Hnz_or) as [ir [-> Hnz]].
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
      destruct (eval_cert_expr penv [] foracle l) as [| | sl | vl] eqn:El;
        cbn [eou_bind] in Hev; try discriminate Hev.
      * inversion Hev; subst sl; exact (IHl ctx src_evals penv foracle msg Hsl Hwtl Hpl Hctx Hsrc El).
      * destruct (eval_cert_expr penv [] foracle r) as [| | sr | vr] eqn:Er;
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
      destruct (eval_cert_expr penv [] foracle o) as [| | so | vo] eqn:Eo;
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
        by (intros x wx Hx; apply Hpenv, in_app_iff; right;
            apply in_app_iff; left; exact Hx).
      assert (Hpf : wf_param_env_for (collect_free_vars [] f) penv)
        by (intros x wx Hx; apply Hpenv, in_app_iff; right;
            apply in_app_iff; right; exact Hx).
      unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev.
      destruct (eval_cert_expr penv [] foracle c) as [| | sc | vc] eqn:Ec;
        cbn [eou_bind] in Hev; try discriminate Hev.
      * inversion Hev; subst sc; exact (IHc ctx src_evals penv foracle msg Hsc Hwtc Hpc Hctx Hsrc Ec).
      * destruct (eval_cert_expr penv [] foracle t) as [| | st | vt] eqn:Et;
          cbn [eou_bind] in Hev; try discriminate Hev.
        -- inversion Hev; subst st; exact (IHt ctx src_evals penv foracle msg Hst Hwtt Hpt Hctx Hsrc Et).
        -- destruct (eval_cert_expr penv [] foracle f) as [| | sf | vf] eqn:Ef;
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
      destruct (eval_cert_expr penv [] foracle o) as [| | so | vo] eqn:Eo;
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
    destruct (IHt et Hwft eq_refl) as (Hwtt & Hbwt & Hlft & Hfvt).
    destruct (IHf ef Hwff eq_refl) as (Hwtf & Hbwf & Hlff & Hfvf).
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
        -- pose proof (IHt et penv foracle dv_src Hwft Hpenv eq_refl Hevd) as Het.
           destruct (ub_free_expr_eval_ret ef [] penv [] foracle Hubf Hwtf wf_let_val_env_nil Hpf)
             as [vf [Hef _]].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ec, Het, Hef; cbn.
           rewrite Ecbit; reflexivity.
        -- pose proof (IHf ef penv foracle dv_src Hwff Hpenv eq_refl Hevd) as Hef.
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
    destruct (IHt et Hwft eq_refl) as (Hwtt & Hbwt & Hlft & Hfvt).
    destruct (IHf ef Hwff eq_refl) as (Hwtf & Hbwf & Hlff & Hfvf).
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
    destruct (IHt et penv foracle Hwft Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret eq_refl) as [dvt [Het Hevt]].
    destruct (IHf ef penv foracle Hwff Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret eq_refl) as [dvf [Hef Hevf]].
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

