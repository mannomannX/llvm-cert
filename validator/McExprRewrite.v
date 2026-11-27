(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Machine-Code Expression Lowering & Rewrite Verification ([CertValidator.McExprRewrite])

    Purpose:
      Implements pure MC DAG flattening ([flatten_mc_dag_to_expr]), verified power-of-2
      [CB_SDiv] lowering ([lower_sdiv_pow2]), shared-multiplier congruence abstraction
      ([abstract_shared_muls]), and unified refinement checks ([check_mc_expr_refines_diag]).

    Trust Contract & Fail-Closed Boundary:
      Proof-only helper module (re-exported by [McValidator]). [check_mc_expr_refines_diag]
      fails closed ([inl err]) whenever normalized/abstracted expressions fail
      [check_expr_refines_with_lrat_diag]; [inr tt] implies [check_mc_expr_refines ... = true].

    Assumptions:
      [Stdlib], [Vellvm], [CertValidator.common.Diag], and [CertValidator.{AigLrat,CertFormat,
      AlgRules,CertValidator}]; zero custom axioms.

    Section Outline:
      1. DAG flattening; 2. Power-of-2 [CB_SDiv] lowering; 3. Shared-multiplier congruence
      abstraction; 4. Unified MC expression refinement checks. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.Ascii
  Strings.String
  List
  Bool
  Lia.
Import ListNotations.

From Vellvm Require Import
  Utils
  Utils.ITreeUtil
  Utils.Assoc
  Utils.ListUtil
  Numeric.Zbits
  Numeric.Integers
  Syntax.LLVMAst
  Syntax.AstLib
  Syntax.CFG
  Syntax.ModuleRefs
  Syntax.DynamicTypes
  Syntax.TypToDtyp
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.Attributes
  Semantics.Denotation
  Semantics.Operations.Compare
  Semantics.Operations.Conversion
  Semantics.Operations.Select
  Semantics.Operations.Freeze
  Semantics.LLVMEvents.

From CertValidator.common Require Import
  Diag.

From CertValidator Require Import
  AigLrat
  CertFormat
  AlgRules
  CertValidator.

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
#[local] Arguments Nat.eqb _ _ : simpl nomatch.
#[local] Arguments Nat.leb _ _ : simpl nomatch.
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
#[local] Arguments Integers.add : simpl never.
#[local] Arguments Integers.sub : simpl never.
#[local] Arguments Integers.mul : simpl never.
#[local] Arguments Integers.divs : simpl never.
#[local] Arguments Integers.shru : simpl never.
#[local] Arguments Integers.shr : simpl never.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** 1. Pure Machine-Code DAG Flattening ([flatten_mc_dag_to_expr]) *)

Fixpoint flatten_mc_dag_to_expr (ret_w : positive) (d : cfg_dag) {struct d}
  : string + cert_expr :=
  match d with
  | CD_RetScalar w e =>
      if negb (Pos.eqb w ret_w) then
        inl (diag "mc-dag-flatten"
          ("MC DAG return width " ++ diag_pos_dec w ++ " does not match expected " ++ diag_pos_dec ret_w))
      else if negb (ub_free_expr e) then
        inl (diag "mc-dag-flatten" "MC DAG return expression failed UB-freedom check")
      else inr e
  | CD_Branch cond dt df =>
      match flatten_mc_dag_to_expr ret_w dt with
      | inl err => inl err
      | inr et =>
          match flatten_mc_dag_to_expr ret_w df with
          | inl err => inl err
          | inr ef =>
              if ub_free_expr cond
              then inr (CE_Select ret_w cond et ef)
              else inl (diag "mc-dag-flatten" "MC DAG branch condition failed UB-freedom check")
          end
      end
  | _ => inl (diag "mc-dag-flatten" "unsupported non-scalar or side-effecting node in MC DAG")
  end.

Lemma flatten_mc_dag_to_expr_typing :
  forall allowed ret_w d e,
    wf_cfg_dag allowed d = true ->
    flatten_mc_dag_to_expr ret_w d = inr e ->
    wt_cert_expr [] e = true /\
    cert_expr_bit_width e = ret_w /\
    is_let_free_expr e = true /\
    ub_free_expr e = true /\
    incl (collect_free_vars [] e) allowed.
Proof.
  intros allowed ret_w d.
  induction d as [| | w' ret_e | ws step_e next IH | uas next IH | cond dt IHt df IHf];
    intros e Hwf Hf; cbn [wf_cfg_dag flatten_mc_dag_to_expr] in Hwf, Hf;
    try discriminate Hf.
  - destruct (Pos.eqb w' ret_w) eqn:Ebw; cbn [negb] in Hf; [| discriminate Hf].
    destruct (ub_free_expr ret_e) eqn:Eub; cbn [negb] in Hf; [| discriminate Hf].
    apply Pos.eqb_eq in Ebw; subst w'.
    inversion Hf; subst e; clear Hf.
    rewrite !andb_true_iff in Hwf; destruct Hwf as (((Hwt & Hbw) & Hlf) & Hfv).
    apply Pos.eqb_eq in Hbw.
    repeat split; try assumption; exact (vars_subset_b_incl _ _ Hfv).
  - destruct (flatten_mc_dag_to_expr ret_w dt) as [| et] eqn:Ert; [discriminate Hf |].
    destruct (flatten_mc_dag_to_expr ret_w df) as [| ef] eqn:Erf; [discriminate Hf |].
    destruct (ub_free_expr cond) eqn:Hubc; [| discriminate Hf].
    inversion Hf; subst e; clear Hf.
    rewrite !andb_true_iff in Hwf.
    destruct Hwf as (((((Hwtc & Hbwc) & Hlfc) & Hfvc) & Hwft) & Hwff).
    destruct (IHt et Hwft eq_refl) as (Hwtt & Hbwt & Hlft & Hubt & Hfvt).
    destruct (IHf ef Hwff eq_refl) as (Hwtf & Hbwf & Hlff & Hubf & Hfvf).
    cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr ub_free_expr collect_free_vars].
    rewrite Hwtc, Hwtt, Hwtf, Hbwc, Hbwt, Hbwf, !Pos.eqb_refl,
            Hlfc, Hlft, Hlff, Hubc, Hubt, Hubf.
    repeat split; try reflexivity.
    intros u Hu; apply in_app_iff in Hu as [Huc | Hutf];
      [exact (vars_subset_b_incl _ _ Hfvc u Huc) |].
    apply in_app_iff in Hutf as [Hut | Huf]; [exact (Hfvt u Hut) | exact (Hfvf u Huf)].
Qed.

Lemma flatten_mc_dag_to_expr_sound {Pa : Params} :
  forall allowed ret_w d e (penv : param_env Pa) foracle dv,
    wf_cfg_dag allowed d = true ->
    wf_param_env_for allowed penv ->
    flatten_mc_dag_to_expr ret_w d = inr e ->
    eval_cfg_dag penv foracle d = DO_Ret dv ->
    eval_closed_cert_expr penv foracle e = raise_ret dv.
Proof.
  intros allowed ret_w d.
  induction d as [| | w' ret_e | ws step_e next IH | uas next IH | cond dt IHt df IHf];
    intros e penv foracle dv Hwf Hpenv Hf Hevd;
    cbn [wf_cfg_dag flatten_mc_dag_to_expr eval_cfg_dag] in Hwf, Hf, Hevd;
    try discriminate Hf; try discriminate Hevd.
  - destruct (Pos.eqb w' ret_w), (ub_free_expr ret_e); cbn [negb] in Hf; try discriminate Hf.
    inversion Hf; subst e; clear Hf.
    destruct (eval_closed_cert_expr penv foracle ret_e) as [| | | dv0]; try discriminate Hevd.
    inversion Hevd; subst dv0; reflexivity.
  - rewrite !andb_true_iff in Hwf; destruct Hwf as (((((_ & _) & _) & _) & Hwft) & Hwff).
    destruct (flatten_mc_dag_to_expr ret_w dt) as [| et] eqn:Ert; [discriminate Hf |].
    destruct (flatten_mc_dag_to_expr ret_w df) as [| ef] eqn:Erf; [discriminate Hf |].
    destruct (ub_free_expr cond) eqn:Hubc; [| discriminate Hf].
    inversion Hf; subst e; clear Hf.
    destruct (eval_closed_cert_expr penv foracle cond) as [| | | dvc] eqn:Ec;
      try discriminate Hevd.
    destruct dvc as [dbc | |]; try discriminate Hevd.
    destruct dbc as [| wc cbit | | | | | |]; try discriminate Hevd.
    destruct wc as [| |]; try discriminate Hevd.
    destruct (flatten_mc_dag_to_expr_typing allowed ret_w dt et Hwft Ert)
      as (Hwtt & _ & _ & Hubt & Hfvt).
    destruct (flatten_mc_dag_to_expr_typing allowed ret_w df ef Hwff Erf)
      as (Hwtf & _ & _ & Hubf & Hfvf).
    assert (Hpt : wf_param_env_for (collect_free_vars [] et) penv)
      by (intros x wx Hx; exact (Hpenv x wx (Hfvt (x, wx) Hx))).
    assert (Hpf : wf_param_env_for (collect_free_vars [] ef) penv)
      by (intros x wx Hx; exact (Hpenv x wx (Hfvf (x, wx) Hx))).
    destruct (@Integers.unsigned 1%positive cbit =? 1)%Z eqn:Ecbit.
    + pose proof (IHt et penv foracle dv Hwft Hpenv eq_refl Hevd) as Het.
      destruct (ub_free_expr_eval_ret ef [] penv [] foracle Hubf Hwtf wf_let_val_env_nil Hpf)
        as [vf [Hef _]].
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ec, Het, Hef; cbn.
      rewrite Ecbit; reflexivity.
    + pose proof (IHf ef penv foracle dv Hwff Hpenv eq_refl Hevd) as Hef.
      destruct (ub_free_expr_eval_ret et [] penv [] foracle Hubt Hwtt wf_let_val_env_nil Hpt)
        as [vt [Het _]].
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ec, Het, Hef; cbn.
      rewrite Ecbit; reflexivity.
Qed.

(** ** 2. Verified Power-of-2 [CB_SDiv] Strength-Reduction Lowering *)

Definition find_sdiv_pow2_shift (w : positive) (c : N) : option N :=
  if (3 <=? w)%positive then
    let ic := @Integers.repr w (Z.of_N c) in
    match @Integers.is_power2 w ic with
    | Some logn =>
        let k := @Integers.unsigned w logn in
        if (1 <=? k)%Z && (k <=? Z.pos w - 2)%Z
        then Some (Z.to_N k)
        else None
    | None => None
    end
  else None.

Definition sdiv_pow2_bias_expr (w : positive) (l : cert_expr) (k : N) : cert_expr :=
  let wm1 := CE_BvConst w (N.pos w - 1)%N in
  let wmk := CE_BvConst w (N.pos w - k)%N in
  let k_e := CE_BvConst w k in
  let sgn := CE_BinOp CB_AShr w no_binop_flags l wm1 in
  let bias := CE_BinOp CB_LShr w no_binop_flags sgn wmk in
  CE_BinOp CB_AShr w no_binop_flags (CE_BinOp CB_Add w no_binop_flags l bias) k_e.

Fixpoint lower_sdiv_pow2 (e : cert_expr) {struct e} : cert_expr :=
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ => e
  | CE_BinOp CB_SDiv w fl l (CE_BvConst w' c) =>
      let l' := lower_sdiv_pow2 l in
      if Pos.eqb w w' && negb (cbf_exact fl) then
        match find_sdiv_pow2_shift w c with
        | Some k => sdiv_pow2_bias_expr w l' k
        | None => CE_BinOp CB_SDiv w fl l' (CE_BvConst w' c)
        end
      else CE_BinOp CB_SDiv w fl l' (CE_BvConst w' c)
  | CE_BinOp op w fl l r =>
      CE_BinOp op w fl (lower_sdiv_pow2 l) (lower_sdiv_pow2 r)
  | CE_ICmp pr ss w l r =>
      CE_ICmp pr ss w (lower_sdiv_pow2 l) (lower_sdiv_pow2 r)
  | CE_Cast k fw tw fl o =>
      CE_Cast k fw tw fl (lower_sdiv_pow2 o)
  | CE_Select w c t f =>
      CE_Select w (lower_sdiv_pow2 c) (lower_sdiv_pow2 t) (lower_sdiv_pow2 f)
  | CE_Freeze w o =>
      CE_Freeze w o
  | CE_Let bs body => CE_Let bs body
  end.

Lemma sdiv_pow2_bias_typing :
  forall w l k,
    wt_cert_expr [] l = true ->
    cert_expr_bit_width l = w ->
    is_let_free_expr l = true ->
    wt_cert_expr [] (sdiv_pow2_bias_expr w l k) = true /\
    cert_expr_bit_width (sdiv_pow2_bias_expr w l k) = w /\
    is_let_free_expr (sdiv_pow2_bias_expr w l k) = true /\
    incl (collect_free_vars [] (sdiv_pow2_bias_expr w l k)) (collect_free_vars [] l).
Proof.
  intros w l k Hwt Hbw Hlf.
  unfold sdiv_pow2_bias_expr.
  cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars
       wf_binop_flags_for cbf_nuw cbf_nsw cbf_exact cbf_disjoint no_binop_flags].
  rewrite Hwt, Hbw, Hlf, !Pos.eqb_refl, !andb_true_r.
  repeat split; try reflexivity.
  intros x Hx; rewrite !app_nil_r, !in_app_iff in Hx; destruct Hx as [Hx | Hx]; exact Hx.
Qed.

Lemma lower_sdiv_pow2_typing :
  forall e,
    wt_cert_expr [] e = true ->
    is_let_free_expr e = true ->
    wt_cert_expr [] (lower_sdiv_pow2 e) = true /\
    cert_expr_bit_width (lower_sdiv_pow2 e) = cert_expr_bit_width e /\
    is_let_free_expr (lower_sdiv_pow2 e) = true /\
    incl (collect_free_vars [] (lower_sdiv_pow2 e)) (collect_free_vars [] e).
Proof.
  intros e; induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hwt Hlf; try discriminate Hlf.
  - repeat split; try assumption; apply incl_refl.
  - repeat split; try assumption; apply incl_refl.
  - repeat split; try assumption; apply incl_refl.
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
    destruct Hwt as ((((Hfl & Hwtl) & Hwtr) & Hwl) & Hwr);
      destruct Hlf as [Hlfl Hlfr].
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    destruct (IHl Hwtl Hlfl) as (Hwt_l & Hbw_l & Hlf_l & Hfv_l).
    destruct (IHr Hwtr Hlfr) as (Hwt_r & Hbw_r & Hlf_r & Hfv_r).
    assert (Hdef :
      wt_cert_expr [] (CE_BinOp op w fl (lower_sdiv_pow2 l) (lower_sdiv_pow2 r)) = true /\
      cert_expr_bit_width (CE_BinOp op w fl (lower_sdiv_pow2 l) (lower_sdiv_pow2 r)) = w /\
      is_let_free_expr (CE_BinOp op w fl (lower_sdiv_pow2 l) (lower_sdiv_pow2 r)) = true /\
      incl (collect_free_vars [] (CE_BinOp op w fl (lower_sdiv_pow2 l) (lower_sdiv_pow2 r)))
           (collect_free_vars [] l ++ collect_free_vars [] r)).
    { cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars].
      rewrite Hfl, Hwt_l, Hwt_r, Hbw_l, Hbw_r, Hwl, Hwr, !Pos.eqb_refl, Hlf_l, Hlf_r.
      repeat split; try reflexivity.
      intros x Hx; apply in_app_iff in Hx as [Hx | Hx]; apply in_app_iff;
        [left; exact (Hfv_l x Hx) | right; exact (Hfv_r x Hx)]. }
    cbn [lower_sdiv_pow2 cert_expr_bit_width collect_free_vars].
    destruct op; try exact Hdef.
    destruct r as [w' c | | | | | | | |]; try exact Hdef.
    destruct (Pos.eqb w w' && negb (cbf_exact fl)); try exact Hdef.
    destruct (find_sdiv_pow2_shift w c) as [kN |]; try exact Hdef.
    destruct (sdiv_pow2_bias_typing w (lower_sdiv_pow2 l) kN Hwt_l (eq_trans Hbw_l Hwl) Hlf_l)
      as (Hwt_b & Hbw_b & Hlf_b & Hfv_b).
    repeat split; try assumption.
    intros x Hx; apply in_app_iff; left; exact (Hfv_l x (Hfv_b x Hx)).
  - cbn [lower_sdiv_pow2 wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars] in *.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
    destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr); destruct Hlf as [Hlfl Hlfr].
    destruct (IHl Hwtl Hlfl) as (Hwt_l & Hbw_l & Hlf_l & Hfv_l).
    destruct (IHr Hwtr Hlfr) as (Hwt_r & Hbw_r & Hlf_r & Hfv_r).
    rewrite Hwt_l, Hwt_r, Hbw_l, Hbw_r, Hwl, Hwr, Hlf_l, Hlf_r.
    repeat split; try reflexivity.
    intros x Hx; apply in_app_iff in Hx as [Hx | Hx]; apply in_app_iff;
      [left; exact (Hfv_l x Hx) | right; exact (Hfv_r x Hx)].
  - cbn [lower_sdiv_pow2 wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars] in *.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((Hk & Hwto) & Hwo).
    destruct (IHo Hwto Hlf) as (Hwt_o & Hbw_o & Hlf_o & Hfv_o).
    rewrite Hk, Hwt_o, Hbw_o, Hwo, Hlf_o; repeat split; try reflexivity; exact Hfv_o.
  - cbn [lower_sdiv_pow2 wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars] in *.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hwc) & Hwtt0) & Hwtf0).
    destruct Hlf as ([Hlfc Hlft] & Hlff).
    destruct (IHc Hwtc Hlfc) as (Hwt_c & Hbw_c & Hlf_c & Hfv_c).
    destruct (IHt Hwtt Hlft) as (Hwt_t & Hbw_t & Hlf_t & Hfv_t).
    destruct (IHf Hwtf Hlff) as (Hwt_f & Hbw_f & Hlf_f & Hfv_f).
    rewrite Hwt_c, Hwt_t, Hwt_f, Hbw_c, Hbw_t, Hbw_f, Hwc, Hwtt0, Hwtf0, Hlf_c, Hlf_t, Hlf_f.
    repeat split; try reflexivity.
    intros x Hx; apply in_app_iff in Hx as [Hx | Hx]; apply in_app_iff;
      [left; exact (Hfv_c x Hx) |].
    right; apply in_app_iff in Hx as [Hx | Hx]; apply in_app_iff;
      [left; exact (Hfv_t x Hx) | right; exact (Hfv_f x Hx)].
  - cbn [lower_sdiv_pow2 cert_expr_bit_width]; repeat split; try assumption; apply incl_refl.
Qed.

Lemma Z_pow_gt_lin_strict : forall w : positive,
  (Z.pos w < 2 ^ Z.pos w)%Z.
Proof.
  intros w; induction w as [| w' IH] using Pos.peano_ind.
  - lia.
  - rewrite Pos2Z.inj_succ, Z.pow_succ_r by lia; lia.
Qed.

Lemma modulus_pow_eq : forall w : positive,
  @Integers.modulus w = (2 ^ Z.pos w)%Z.
Proof.
  intros w; rewrite (@Integers.modulus_power w); unfold Integers.zwordsize; apply alg_two_p_pow; lia.
Qed.

Lemma half_modulus_pow_eq : forall w : positive,
  @Integers.half_modulus w = (2 ^ (Z.pos w - 1))%Z.
Proof.
  intros w.
  assert (Hhm : (@Integers.modulus w = 2 * @Integers.half_modulus w)%Z)
    by exact (@Integers.half_modulus_modulus w).
  rewrite modulus_pow_eq in Hhm.
  replace (2 ^ Z.pos w)%Z with (2 * 2 ^ (Z.pos w - 1))%Z in Hhm
    by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  lia.
Qed.

Lemma Z_add_bias_div_quot_neg : forall a k : Z,
  (a < 0)%Z -> (1 <= k)%Z ->
  ((a + 2 ^ k - 1) / 2 ^ k = Z.quot a (2 ^ k))%Z.
Proof.
  intros a k Ha Hk.
  set (m := (-a)%Z).
  set (b := (2 ^ k)%Z).
  assert (Hb : (2 <= b)%Z) by (unfold b; change 2%Z with (2 ^ 1)%Z; apply Z.pow_le_mono_r; lia).
  assert (Hm : (0 < m)%Z) by (unfold m; lia).
  replace a with (-m)%Z by (unfold m; lia).
  rewrite Z.quot_opp_l by lia.
  rewrite Z.quot_div_nonneg by lia.
  set (q := (m / b)%Z).
  set (r := (m mod b)%Z).
  pose proof (Z.div_mod m b ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound m b ltac:(lia)) as Hrb.
  fold q r in Hdm, Hrb.
  assert (Heq : (- m + b - 1 = b * (-q) + (b - 1 - r))%Z) by lia.
  rewrite Heq, Z.add_comm, Z.mul_comm, Z.div_add, Z.div_small; lia.
Qed.

Lemma sdiv_pow2_bias_exact :
  forall w (x : @Integers.bit_int w) (k : Z),
    (3 <= w)%positive ->
    (1 <= k <= Z.pos w - 2)%Z ->
    @Integers.divs w x (@Integers.repr w (2 ^ k)) =
    @Integers.shr w
      (@Integers.add w x
        (@Integers.shru w
          (@Integers.shr w x (@Integers.repr w (Z.pos w - 1)))
          (@Integers.repr w (Z.pos w - k))))
      (@Integers.repr w k).
Proof.
  intros w x k Hw Hk.
  pose proof (Z_pow_gt_lin_strict w) as Hlin.
  pose proof (modulus_pow_eq w) as Hmod.
  pose proof (half_modulus_pow_eq w) as Hhm.
  pose proof (@Integers.signed_range w x) as Hsr.
  unfold Integers.min_signed, Integers.max_signed in Hsr; rewrite Hhm in Hsr.
  assert (Hmod_u : @Integers.max_unsigned w = (2 ^ Z.pos w - 1)%Z)
    by (unfold Integers.max_unsigned; rewrite Hmod; reflexivity).
  assert (Hwm1_u : @Integers.unsigned w (@Integers.repr w (Z.pos w - 1)) = (Z.pos w - 1)%Z)
    by (apply @Integers.unsigned_repr; lia).
  assert (Hwmk_u : @Integers.unsigned w (@Integers.repr w (Z.pos w - k)) = (Z.pos w - k)%Z)
    by (apply @Integers.unsigned_repr; lia).
  assert (Hk_u : @Integers.unsigned w (@Integers.repr w k) = k)
    by (apply @Integers.unsigned_repr; lia).
  assert (Hpow_k : (2 <= 2 ^ k <= 2 ^ (Z.pos w - 2))%Z).
  { split; [change 2%Z with (2 ^ 1)%Z |]; apply Z.pow_le_mono_r; lia. }
  assert (Hpow_wm2 : (2 * 2 ^ (Z.pos w - 2) = 2 ^ (Z.pos w - 1))%Z)
    by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (Hpow_wm1 : (2 * 2 ^ (Z.pos w - 1) = 2 ^ Z.pos w)%Z)
    by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (Hs_div : @Integers.signed w (@Integers.repr w (2 ^ k)) = (2 ^ k)%Z).
  { apply @Integers.signed_repr.
    unfold Integers.min_signed, Integers.max_signed; rewrite Hhm; lia. }
  unfold Integers.divs; rewrite Hs_div.
  destruct (Z.ltb (@Integers.signed w x) 0%Z) eqn:Esgn.
  - apply Z.ltb_lt in Esgn.
    assert (Hsgn : @Integers.shr w x (@Integers.repr w (Z.pos w - 1)) = @Integers.mone w).
    { rewrite Integers.shr_div_two_p, Hwm1_u, alg_two_p_pow by lia.
      replace (@Integers.signed w x)
        with (2 ^ (Z.pos w - 1) * (-1) + (@Integers.signed w x + 2 ^ (Z.pos w - 1)))%Z by lia.
      rewrite Z.add_comm, Z.mul_comm, Z.div_add, Z.div_small by lia.
      rewrite Z.add_0_l; reflexivity. }
    assert (Hbias : @Integers.shru w (@Integers.mone w) (@Integers.repr w (Z.pos w - k)) =
                    @Integers.repr w (2 ^ k - 1)).
    { rewrite Integers.shru_div_two_p, Hwmk_u, alg_two_p_pow by lia.
      rewrite (@Integers.unsigned_mone w), Hmod.
      assert (Hpow_w : (2 ^ (Z.pos w - k) * 2 ^ k = 2 ^ Z.pos w)%Z)
        by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (Hrem : (4 <= 2 ^ (Z.pos w - k))%Z)
        by (change 4%Z with (2 ^ 2)%Z; apply Z.pow_le_mono_r; lia).
      replace (2 ^ Z.pos w - 1)%Z with (2 ^ (Z.pos w - k) * (2 ^ k - 1) + (2 ^ (Z.pos w - k) - 1))%Z by lia.
      rewrite Z.add_comm, Z.mul_comm, Z.div_add, Z.div_small by lia; reflexivity. }
    rewrite Hsgn, Hbias.
    assert (Hsb : @Integers.signed w (@Integers.repr w (2 ^ k - 1)) = (2 ^ k - 1)%Z)
      by (apply @Integers.signed_repr; unfold Integers.min_signed, Integers.max_signed; rewrite Hhm; lia).
    assert (Hsum_s : @Integers.signed w (@Integers.add w x (@Integers.repr w (2 ^ k - 1))) =
                     (@Integers.signed w x + (2 ^ k - 1))%Z).
    { unfold Integers.add.
      replace (@Integers.repr w (@Integers.unsigned w x + @Integers.unsigned w (@Integers.repr w (2 ^ k - 1))))
        with (@Integers.repr w (@Integers.signed w x + (2 ^ k - 1))).
      - apply @Integers.signed_repr; unfold Integers.min_signed, Integers.max_signed; rewrite Hhm; lia.
      - apply Integers.eqm_samerepr, Integers.eqm_add;
          [apply Integers.eqm_signed_unsigned
          | rewrite (@Integers.unsigned_repr w (2 ^ k - 1)) by (unfold Integers.max_unsigned; rewrite Hmod; lia);
            apply Integers.eqm_refl]. }
    rewrite Integers.shr_div_two_p, Hk_u, Hsum_s, alg_two_p_pow by lia.
    f_equal; symmetry; replace (@Integers.signed w x + (2 ^ k - 1))%Z with (@Integers.signed w x + 2 ^ k - 1)%Z by lia.
    apply Z_add_bias_div_quot_neg; lia.
  - apply Z.ltb_ge in Esgn.
    assert (Hsgn : @Integers.shr w x (@Integers.repr w (Z.pos w - 1)) = @Integers.zero w).
    { rewrite Integers.shr_div_two_p, Hwm1_u, alg_two_p_pow by lia.
      rewrite Z.div_small by lia; reflexivity. }
    assert (Hbias : @Integers.shru w (@Integers.zero w) (@Integers.repr w (Z.pos w - k)) = @Integers.zero w).
    { rewrite Integers.shru_div_two_p, (@Integers.unsigned_zero w), alg_two_p_pow by lia.
      rewrite Z.div_0_l; [reflexivity | apply Z.pow_nonzero; lia]. }
    rewrite Hsgn, Hbias, (@Integers.add_zero w).
    rewrite Integers.shr_div_two_p, Hk_u, alg_two_p_pow by lia.
    rewrite Z.quot_div_nonneg by lia; reflexivity.
Qed.

Lemma find_sdiv_pow2_shift_spec :
  forall w c kN,
    find_sdiv_pow2_shift w c = Some kN ->
    (3 <= w)%positive /\
    (1 <= Z.of_N kN <= Z.pos w - 2)%Z /\
    @Integers.repr w (Z.of_N c) = @Integers.repr w (2 ^ Z.of_N kN).
Proof.
  intros w c kN H; unfold find_sdiv_pow2_shift in H.
  destruct (3 <=? w)%positive eqn:Hw; [| discriminate H].
  apply Pos.leb_le in Hw.
  destruct (@Integers.is_power2 w (@Integers.repr w (Z.of_N c))) as [logn |] eqn:Ep2;
    [| discriminate H].
  set (k := @Integers.unsigned w logn) in *.
  destruct ((1 <=? k)%Z && (k <=? Z.pos w - 2)%Z) eqn:Hkb; [| discriminate H].
  apply andb_true_iff in Hkb as [Hk1 Hk2]; apply Z.leb_le in Hk1, Hk2.
  inversion H; subst kN; clear H.
  rewrite Z2N.id by lia.
  repeat split; try assumption.
  rewrite <- (@Integers.repr_unsigned w (@Integers.repr w (Z.of_N c))).
  rewrite (Integers.is_power2_correct _ _ Ep2), alg_two_p_pow by lia; reflexivity.
Qed.

Lemma eval_iop_sdiv_ok :
  forall {Pa : Params} fl w x y k,
    cbf_exact fl = false ->
    @Integers.signed w y = k ->
    (k =? 0)%Z = false ->
    (k =? -1)%Z = false ->
    @eval_iop Pa (cert_to_ibinop CB_SDiv fl)
      (DVALUE_Base (@DVALUE_I Pa w x)) (DVALUE_Base (@DVALUE_I Pa w y)) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.divs w x y))).
Proof.
  intros Pa fl w x y k Hex Hsy H0 Hm1; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  unfold cert_to_ibinop, eval_int_op; cbn [cbf_exact]; rewrite Hex; cbn.
  rewrite Hsy, H0, Hm1, andb_false_r; cbn; reflexivity.
Qed.

Lemma eval_iop_ashr_ok :
  forall {Pa : Params} w x s,
    (@Integers.unsigned w s >=? Z.pos w)%Z = false ->
    @eval_iop Pa (cert_to_ibinop CB_AShr no_binop_flags)
      (DVALUE_Base (@DVALUE_I Pa w x)) (DVALUE_Base (@DVALUE_I Pa w s)) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.shr w x s))).
Proof.
  intros Pa w x s Hge; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  unfold cert_to_ibinop, eval_int_op; cbn; rewrite Hge; reflexivity.
Qed.

Lemma eval_iop_lshr_ok :
  forall {Pa : Params} w x s,
    (@Integers.unsigned w s >=? Z.pos w)%Z = false ->
    @eval_iop Pa (cert_to_ibinop CB_LShr no_binop_flags)
      (DVALUE_Base (@DVALUE_I Pa w x)) (DVALUE_Base (@DVALUE_I Pa w s)) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.shru w x s))).
Proof.
  intros Pa w x s Hge; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  unfold cert_to_ibinop, eval_int_op; cbn; rewrite Hge; reflexivity.
Qed.

Lemma eval_iop_add_ok :
  forall {Pa : Params} w x y,
    @eval_iop Pa (cert_to_ibinop CB_Add no_binop_flags)
      (DVALUE_Base (@DVALUE_I Pa w x)) (DVALUE_Base (@DVALUE_I Pa w y)) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.add w x y))).
Proof.
  intros Pa w x y; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  unfold cert_to_ibinop, eval_int_op; cbn; reflexivity.
Qed.

Lemma lower_sdiv_pow2_sound {Pa : Params} :
  forall e (penv : param_env Pa) foracle,
    wt_cert_expr [] e = true ->
    is_let_free_expr e = true ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle e)
      (eval_closed_cert_expr penv foracle (lower_sdiv_pow2 e)).
Proof.
  intros e penv foracle; induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hwt Hlf; try discriminate Hlf;
    try apply equiv_eou_dvalue_refl.
  - cbn [wt_cert_expr is_let_free_expr] in Hwt, Hlf.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
    destruct Hwt as ((((Hfl & Hwtl) & Hwtr) & Hwl) & Hwr); destruct Hlf as [Hlfl Hlfr].
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    pose proof (IHl Hwtl Hlfl) as El.
    pose proof (IHr Hwtr Hlfr) as Er.
    assert (Hdef :
      equiv_eou_dvalue
        (eval_closed_cert_expr penv foracle (CE_BinOp op w fl l r))
        (eval_closed_cert_expr penv foracle (CE_BinOp op w fl (lower_sdiv_pow2 l) (lower_sdiv_pow2 r)))).
    { unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
      apply cert_eou_bind_equiv; [exact El | intros vl].
      apply cert_eou_bind_equiv; [exact Er | intros vr].
      apply equiv_eou_dvalue_refl. }
    cbn [lower_sdiv_pow2].
    destruct op; try exact Hdef.
    destruct r as [w' c | | | | | | | |]; try exact Hdef.
    destruct (Pos.eqb w w' && negb (cbf_exact fl)) eqn:Eex; try exact Hdef.
    destruct (find_sdiv_pow2_shift w c) as [kN |] eqn:Efnd; try exact Hdef.
    apply andb_true_iff in Eex as [Eww Hex].
    apply Pos.eqb_eq in Eww; apply negb_true_iff in Hex; subst w'.
    destruct (find_sdiv_pow2_shift_spec w c kN Efnd) as (Hw3 & Hkrng & Hcrep).
    pose proof (Z_pow_gt_lin_strict w) as Hlin.
    pose proof (modulus_pow_eq w) as Hmod.
    pose proof (half_modulus_pow_eq w) as Hhm.
    assert (Hpow_k : (2 <= 2 ^ Z.of_N kN <= 2 ^ (Z.pos w - 2))%Z)
      by (split; [change 2%Z with (2 ^ 1)%Z |]; apply Z.pow_le_mono_r; lia).
    assert (Hpow_wm2 : (2 * 2 ^ (Z.pos w - 2) = 2 ^ (Z.pos w - 1))%Z)
      by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (Hpow_wm1 : (2 * 2 ^ (Z.pos w - 1) = 2 ^ Z.pos w)%Z)
      by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    assert (Hic_s : @Integers.signed w (@Integers.repr w (Z.of_N c)) = (2 ^ Z.of_N kN)%Z).
    { rewrite Hcrep; apply @Integers.signed_repr; unfold Integers.min_signed, Integers.max_signed;
        rewrite Hhm; lia. }
    eapply equiv_eou_dvalue_trans; [exact Hdef |].
    cbn [lower_sdiv_pow2] in *.
    unfold eval_closed_cert_expr, sdiv_pow2_bias_expr in *.
    cbn [eval_cert_expr].
    destruct (eval_cert_expr penv [] foracle (lower_sdiv_pow2 l)) as [| | | vl'] eqn:El';
      cbn [eou_bind]; try reflexivity.
    destruct (lower_sdiv_pow2_typing l Hwtl Hlfl) as (Hwt_l' & Hbw_l' & _).
    pose proof (eval_cert_expr_ret_wf_scalar (lower_sdiv_pow2 l) [] penv [] foracle vl' Hwt_l' El') as Hwfl'.
    rewrite Hbw_l', Hwl in Hwfl'.
    assert (Hwm1_u : @Integers.unsigned w (@Integers.repr w (Z.of_N (N.pos w - 1))) = (Z.pos w - 1)%Z)
      by (replace (Z.of_N (N.pos w - 1)) with (Z.pos w - 1)%Z by lia;
          apply @Integers.unsigned_repr; unfold Integers.max_unsigned; rewrite Hmod; lia).
    assert (Hwmk_u : @Integers.unsigned w (@Integers.repr w (Z.of_N (N.pos w - kN))) = (Z.pos w - Z.of_N kN)%Z)
      by (replace (Z.of_N (N.pos w - kN)) with (Z.pos w - Z.of_N kN)%Z by lia;
          apply @Integers.unsigned_repr; unfold Integers.max_unsigned; rewrite Hmod; lia).
    assert (Hk_u : @Integers.unsigned w (@Integers.repr w (Z.of_N kN)) = Z.of_N kN)
      by (apply @Integers.unsigned_repr; unfold Integers.max_unsigned; rewrite Hmod; lia).
    assert (Hge1 : (@Integers.unsigned w (@Integers.repr w (Z.of_N (N.pos w - 1))) >=? Z.pos w)%Z = false)
      by (rewrite Hwm1_u, Z.geb_leb; apply Z.leb_gt; lia).
    assert (Hge2 : (@Integers.unsigned w (@Integers.repr w (Z.of_N (N.pos w - kN))) >=? Z.pos w)%Z = false)
      by (rewrite Hwmk_u, Z.geb_leb; apply Z.leb_gt; lia).
    assert (Hge3 : (@Integers.unsigned w (@Integers.repr w (Z.of_N kN)) >=? Z.pos w)%Z = false)
      by (rewrite Hk_u, Z.geb_leb; apply Z.leb_gt; lia).
    replace (Z.of_N (N.pos w - 1)) with (Z.pos w - 1)%Z in * by lia.
    replace (Z.of_N (N.pos w - kN)) with (Z.pos w - Z.of_N kN)%Z in * by lia.
    destruct Hwfl' as [-> | [il ->]].
    + cbn [cert_to_ibinop]; rewrite Hex, eval_iop_sdiv_poison_l.
      destruct (Z.eq_dec (@Integers.signed w (@Integers.repr w (Z.of_N c))) (-1)%Z); [lia |].
      rewrite (eval_iop_no_flags_poison_any CB_AShr w)
        by (first [reflexivity | left; reflexivity | right; eexists; reflexivity]).
      cbn [eou_bind].
      rewrite (eval_iop_no_flags_poison_any CB_LShr w)
        by (first [reflexivity | left; reflexivity | right; eexists; reflexivity]).
      cbn [eou_bind].
      rewrite (eval_iop_no_flags_poison_any CB_Add w)
        by (first [reflexivity | left; reflexivity | right; eexists; reflexivity]).
      cbn [eou_bind].
      rewrite (eval_iop_no_flags_poison_any CB_AShr w)
        by (first [reflexivity | left; reflexivity | right; eexists; reflexivity]).
      reflexivity.
    + assert (Hs0 : (2 ^ Z.of_N kN =? 0)%Z = false) by (apply Z.eqb_neq; lia).
      assert (Hsm1 : (2 ^ Z.of_N kN =? -1)%Z = false) by (apply Z.eqb_neq; lia).
      rewrite (eval_iop_sdiv_ok fl w il _ (2 ^ Z.of_N kN)%Z Hex Hic_s Hs0 Hsm1).
      rewrite (eval_iop_ashr_ok w il _ Hge1); cbn [eou_bind].
      rewrite (eval_iop_lshr_ok w _ _ Hge2); cbn [eou_bind].
      rewrite eval_iop_add_ok; cbn [eou_bind].
      rewrite (eval_iop_ashr_ok w _ _ Hge3); cbn [eou_bind equiv_eou_dvalue].
      do 2 f_equal; rewrite Hcrep.
      exact (sdiv_pow2_bias_exact w il (Z.of_N kN) Hw3 Hkrng).
  - cbn [wt_cert_expr is_let_free_expr] in Hwt, Hlf.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf;
      destruct Hwt as (((Hwtl & Hwtr) & _) & _); destruct Hlf as [Hlfl Hlfr].
    unfold eval_closed_cert_expr in *; cbn [lower_sdiv_pow2 eval_cert_expr].
    apply cert_eou_bind_equiv; [exact (IHl Hwtl Hlfl) | intros vl].
    apply cert_eou_bind_equiv; [exact (IHr Hwtr Hlfr) | intros vr].
    apply equiv_eou_dvalue_refl.
  - cbn [wt_cert_expr is_let_free_expr] in Hwt.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((_ & Hwto) & _).
    unfold eval_closed_cert_expr in *; cbn [lower_sdiv_pow2 eval_cert_expr].
    apply cert_eou_bind_equiv; [exact (IHo Hwto Hlf) | intros vo].
    apply equiv_eou_dvalue_refl.
  - cbn [wt_cert_expr is_let_free_expr] in Hwt, Hlf.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & _) & _) & _); destruct Hlf as ([Hlfc Hlft] & Hlff).
    unfold eval_closed_cert_expr in *; cbn [lower_sdiv_pow2 eval_cert_expr].
    apply cert_eou_bind_equiv; [exact (IHc Hwtc Hlfc) | intros vc].
    apply cert_eou_bind_equiv; [exact (IHt Hwtt Hlft) | intros vt].
    apply cert_eou_bind_equiv; [exact (IHf Hwtf Hlff) | intros vf].
    apply equiv_eou_dvalue_refl.
Qed.

(** ** 3. Verified Shared-Multiplier Congruence Abstraction *)

Definition set_param_env {Pa : Params}
  (penv : param_env Pa) (nm : string) (v : @dvalue Pa) : param_env Pa :=
  fun x => if String.eqb nm x then Some v else penv x.

Fixpoint freeze_free_expr (e : cert_expr) {struct e} : bool :=
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ => true
  | CE_BinOp _ _ _ l r | CE_ICmp _ _ _ l r =>
      freeze_free_expr l && freeze_free_expr r
  | CE_Cast _ _ _ _ o => freeze_free_expr o
  | CE_Select _ c t f =>
      freeze_free_expr c && freeze_free_expr t && freeze_free_expr f
  | CE_Freeze _ _ | CE_Let _ _ => false
  end.

Definition is_const_cert_expr (e : cert_expr) : bool :=
  match e with
  | CE_BvConst _ _ => true
  | _ => false
  end.

Definition is_nonblastable_mul (e : cert_expr) : bool :=
  match e with
  | CE_BinOp CB_Mul w _ l r =>
      (12 <? w)%positive && negb (is_const_cert_expr l) && negb (is_const_cert_expr r)
  | _ => false
  end.

Fixpoint collect_nonblastable_muls_acc
  (acc : list (positive * cert_expr)) (e : cert_expr) {struct e}
  : list (positive * cert_expr) :=
  let acc1 := if is_nonblastable_mul e then (cert_expr_bit_width e, e) :: acc else acc in
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ | CE_Let _ _ => acc1
  | CE_BinOp _ _ _ l r | CE_ICmp _ _ _ l r =>
      collect_nonblastable_muls_acc (collect_nonblastable_muls_acc acc1 l) r
  | CE_Cast _ _ _ _ o | CE_Freeze _ o => collect_nonblastable_muls_acc acc1 o
  | CE_Select _ c t f =>
      collect_nonblastable_muls_acc
        (collect_nonblastable_muls_acc (collect_nonblastable_muls_acc acc1 c) t) f
  end.

Definition collect_nonblastable_muls (e : cert_expr)
  : list (positive * cert_expr) :=
  collect_nonblastable_muls_acc [] e.

Fixpoint subst_subexpr (target repl e : cert_expr) {struct e} : cert_expr :=
  if cert_expr_eqb e target then repl
  else
    match e with
    | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ | CE_Let _ _ => e
    | CE_BinOp op w fl l r =>
        CE_BinOp op w fl (subst_subexpr target repl l) (subst_subexpr target repl r)
    | CE_ICmp pr ss w l r =>
        CE_ICmp pr ss w (subst_subexpr target repl l) (subst_subexpr target repl r)
    | CE_Cast k fw tw fl o =>
        CE_Cast k fw tw fl (subst_subexpr target repl o)
    | CE_Select w c t f =>
        CE_Select w (subst_subexpr target repl c)
                    (subst_subexpr target repl t)
                    (subst_subexpr target repl f)
    | CE_Freeze w o => CE_Freeze w (subst_subexpr target repl o)
    end.

Lemma subst_subexpr_typing_full :
  forall target nm w e,
    negb (starts_with_dollar nm) = true ->
    cert_expr_bit_width target = w ->
    ~ In nm (List.map fst (collect_free_vars [] e)) ->
    wt_cert_expr [] e = true ->
    is_let_free_expr e = true ->
    wt_cert_expr [] (subst_subexpr target (CE_Var nm w) e) = true /\
    cert_expr_bit_width (subst_subexpr target (CE_Var nm w) e) = cert_expr_bit_width e /\
    is_let_free_expr (subst_subexpr target (CE_Var nm w) e) = true /\
    incl (collect_free_vars [] (subst_subexpr target (CE_Var nm w) e))
         ((nm, w) :: collect_free_vars [] e) /\
    Forall (fun '(x, wx) => x = nm -> wx = w)
           (collect_free_vars [] (subst_subexpr target (CE_Var nm w) e)).
Proof.
  intros target nm w e Hnd Htw.
  induction e as
    [ w0 val0 | w0 | nm0 w0
    | op w0 fl l IHl r IHr
    | pr ss w0 l IHl r IHr
    | k fw tw fl o IHo
    | w0 c IHc t IHt f IHf
    | w0 o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hni Hwt Hlf; try discriminate Hlf;
    cbn [subst_subexpr].
  - destruct (cert_expr_eqb (CE_BvConst w0 val0) target) eqn:Heq.
    + apply cert_expr_eqb_eq in Heq; subst target; rewrite Htw.
      cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars lookup_let_width].
      rewrite Hnd; repeat split; try reflexivity;
        [intros x [Hx | []]; left; exact Hx | constructor; auto].
    + cbn [cert_expr_bit_width]; repeat split; try assumption;
        [intros x Hx; right; exact Hx | constructor].
  - destruct (cert_expr_eqb (CE_Poison w0) target) eqn:Heq.
    + apply cert_expr_eqb_eq in Heq; subst target; rewrite Htw.
      cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars lookup_let_width].
      rewrite Hnd; repeat split; try reflexivity;
        [intros x [Hx | []]; left; exact Hx | constructor; auto].
    + cbn [cert_expr_bit_width]; repeat split; try assumption;
        [intros x Hx; right; exact Hx | constructor].
  - destruct (cert_expr_eqb (CE_Var nm0 w0) target) eqn:Heq.
    + apply cert_expr_eqb_eq in Heq; subst target; rewrite Htw.
      cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars lookup_let_width].
      rewrite Hnd; repeat split; try reflexivity;
        [intros x [Hx | []]; left; exact Hx | constructor; auto].
    + cbn [cert_expr_bit_width]; repeat split; try assumption;
        [intros x Hx; right; exact Hx |].
      cbn [collect_free_vars string_in_list List.map] in Hni |- *; constructor;
        [intros ->; exfalso; apply Hni; left; reflexivity | constructor].
  - destruct (cert_expr_eqb (CE_BinOp op w0 fl l r) target) eqn:Heq.
    + apply cert_expr_eqb_eq in Heq; subst target; rewrite Htw.
      cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars lookup_let_width].
      rewrite Hnd; repeat split; try reflexivity;
        [intros x [Hx | []]; left; exact Hx | constructor; auto].
    + cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars] in Hni, Hwt, Hlf |- *.
      rewrite map_app in Hni.
      rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
      destruct Hwt as ((((Hfl & Hwtl) & Hwtr) & Hwl) & Hwr);
        destruct Hlf as [Hlfl Hlfr].
      destruct (IHl (fun H => Hni (proj2 (in_app_iff _ _ _) (or_introl H))) Hwtl Hlfl)
        as (Hwt_l & Hbw_l & Hlf_l & Hfv_l & Hfa_l).
      destruct (IHr (fun H => Hni (proj2 (in_app_iff _ _ _) (or_intror H))) Hwtr Hlfr)
        as (Hwt_r & Hbw_r & Hlf_r & Hfv_r & Hfa_r).
      rewrite Hfl, Hwt_l, Hwt_r, Hbw_l, Hbw_r, Hwl, Hwr, Hlf_l, Hlf_r.
      repeat split; try reflexivity.
      * intros x Hx; apply in_app_iff in Hx as [Hx | Hx].
        -- destruct (Hfv_l x Hx) as [-> | Hx'];
             [left; reflexivity | right; apply in_app_iff; left; exact Hx'].
        -- destruct (Hfv_r x Hx) as [-> | Hx'];
             [left; reflexivity | right; apply in_app_iff; right; exact Hx'].
      * apply Forall_app; split; assumption.
  - destruct (cert_expr_eqb (CE_ICmp pr ss w0 l r) target) eqn:Heq.
    + apply cert_expr_eqb_eq in Heq; subst target; rewrite Htw.
      cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars lookup_let_width].
      rewrite Hnd; repeat split; try reflexivity;
        [intros x [Hx | []]; left; exact Hx | constructor; auto].
    + cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars] in Hni, Hwt, Hlf |- *.
      rewrite map_app in Hni.
      rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
      destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr);
        destruct Hlf as [Hlfl Hlfr].
      destruct (IHl (fun H => Hni (proj2 (in_app_iff _ _ _) (or_introl H))) Hwtl Hlfl)
        as (Hwt_l & Hbw_l & Hlf_l & Hfv_l & Hfa_l).
      destruct (IHr (fun H => Hni (proj2 (in_app_iff _ _ _) (or_intror H))) Hwtr Hlfr)
        as (Hwt_r & Hbw_r & Hlf_r & Hfv_r & Hfa_r).
      rewrite Hwt_l, Hwt_r, Hbw_l, Hbw_r, Hwl, Hwr, Hlf_l, Hlf_r.
      repeat split; try reflexivity.
      * intros x Hx; apply in_app_iff in Hx as [Hx | Hx].
        -- destruct (Hfv_l x Hx) as [-> | Hx'];
             [left; reflexivity | right; apply in_app_iff; left; exact Hx'].
        -- destruct (Hfv_r x Hx) as [-> | Hx'];
             [left; reflexivity | right; apply in_app_iff; right; exact Hx'].
      * apply Forall_app; split; assumption.
  - destruct (cert_expr_eqb (CE_Cast k fw tw fl o) target) eqn:Heq.
    + apply cert_expr_eqb_eq in Heq; subst target; rewrite Htw.
      cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars lookup_let_width].
      rewrite Hnd; repeat split; try reflexivity;
        [intros x [Hx | []]; left; exact Hx | constructor; auto].
    + cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars] in Hni, Hwt, Hlf |- *.
      rewrite !andb_true_iff in Hwt; destruct Hwt as ((Hk & Hwto) & Hwo).
      destruct (IHo Hni Hwto Hlf) as (Hwt_o & Hbw_o & Hlf_o & Hfv_o & Hfa_o).
      rewrite Hk, Hwt_o, Hbw_o, Hwo, Hlf_o; repeat split; try reflexivity; assumption.
  - destruct (cert_expr_eqb (CE_Select w0 c t f) target) eqn:Heq.
    + apply cert_expr_eqb_eq in Heq; subst target; rewrite Htw.
      cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars lookup_let_width].
      rewrite Hnd; repeat split; try reflexivity;
        [intros x [Hx | []]; left; exact Hx | constructor; auto].
    + cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars] in Hni, Hwt, Hlf |- *.
      rewrite !map_app in Hni.
      rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
      destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hwc) & Hwt0) & Hwf0);
        destruct Hlf as ([Hlfc Hlft] & Hlff).
      destruct (IHc (fun H => Hni (proj2 (in_app_iff _ _ _) (or_introl H))) Hwtc Hlfc)
        as (Hwt_c & Hbw_c & Hlf_c & Hfv_c & Hfa_c).
      destruct (IHt (fun H => Hni (proj2 (in_app_iff _ _ _)
                  (or_intror (proj2 (in_app_iff _ _ _) (or_introl H))))) Hwtt Hlft)
        as (Hwt_t & Hbw_t & Hlf_t & Hfv_t & Hfa_t).
      destruct (IHf (fun H => Hni (proj2 (in_app_iff _ _ _)
                  (or_intror (proj2 (in_app_iff _ _ _) (or_intror H))))) Hwtf Hlff)
        as (Hwt_f & Hbw_f & Hlf_f & Hfv_f & Hfa_f).
      rewrite Hwt_c, Hwt_t, Hwt_f, Hbw_c, Hbw_t, Hbw_f, Hwc, Hwt0, Hwf0, Hlf_c, Hlf_t, Hlf_f.
      repeat split; try reflexivity.
      * intros x Hx; apply in_app_iff in Hx as [Hx | Hx].
        -- destruct (Hfv_c x Hx) as [-> | Hx'];
             [left; reflexivity | right; apply in_app_iff; left; exact Hx'].
        -- apply in_app_iff in Hx as [Hx | Hx].
           ++ destruct (Hfv_t x Hx) as [-> | Hx'];
                [left; reflexivity
                | right; apply in_app_iff; right;
                  apply in_app_iff; left; exact Hx'].
           ++ destruct (Hfv_f x Hx) as [-> | Hx'];
                [left; reflexivity
                | right; apply in_app_iff; right;
                  apply in_app_iff; right; exact Hx'].
      * apply Forall_app; split; [exact Hfa_c | apply Forall_app; split; assumption].
  - destruct (cert_expr_eqb (CE_Freeze w0 o) target) eqn:Heq.
    + apply cert_expr_eqb_eq in Heq; subst target; rewrite Htw.
      cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars lookup_let_width].
      rewrite Hnd; repeat split; try reflexivity;
        [intros x [Hx | []]; left; exact Hx | constructor; auto].
    + cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars] in Hni, Hwt, Hlf |- *.
      apply andb_true_iff in Hwt as [Hwto Hwo].
      destruct (IHo Hni Hwto Hlf) as (Hwt_o & Hbw_o & Hlf_o & Hfv_o & Hfa_o).
      rewrite Hwt_o, Hbw_o, Hwo, Hlf_o; repeat split; try reflexivity; assumption.
Qed.

Lemma subst_subexpr_preserves_ub_freeze :
  forall target nm w e,
    ub_free_expr e = true ->
    freeze_free_expr e = true ->
    ub_free_expr (subst_subexpr target (CE_Var nm w) e) = true /\
    freeze_free_expr (subst_subexpr target (CE_Var nm w) e) = true.
Proof.
  intros target nm w e; induction e as
    [ w0 val0 | w0 | nm0 w0
    | op w0 fl l IHl r IHr
    | pr ss w0 l IHl r IHr
    | k fw tw fl o IHo
    | w0 c IHc t IHt f IHf
    | w0 o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hub Hfr; try discriminate Hfr;
    cbn [subst_subexpr];
    destruct (cert_expr_eqb _ target); try exact (conj eq_refl eq_refl);
    cbn [ub_free_expr freeze_free_expr] in Hub, Hfr |- *;
    try exact (conj eq_refl eq_refl).
  - rewrite !andb_true_iff in Hub; rewrite !andb_true_iff in Hfr.
    destruct Hub as ([Hop Hubl] & Hubr); destruct Hfr as [Hfrl Hfrr].
    destruct (IHl Hubl Hfrl) as [Hul Hfl]; destruct (IHr Hubr Hfrr) as [Hur Hfr'].
    rewrite Hop, Hul, Hur, Hfl, Hfr'; split; reflexivity.
  - rewrite !andb_true_iff in Hub; rewrite !andb_true_iff in Hfr.
    destruct Hub as [Hubl Hubr]; destruct Hfr as [Hfrl Hfrr].
    destruct (IHl Hubl Hfrl) as [Hul Hfl]; destruct (IHr Hubr Hfrr) as [Hur Hfr'].
    rewrite Hul, Hur, Hfl, Hfr'; split; reflexivity.
  - exact (IHo Hub Hfr).
  - rewrite !andb_true_iff in Hub; rewrite !andb_true_iff in Hfr.
    destruct Hub as ([Hubc Hubt] & Hubf); destruct Hfr as ([Hfrc Hfrt] & Hfrf).
    destruct (IHc Hubc Hfrc) as [Huc Hfc]; destruct (IHt Hubt Hfrt) as [Hut Hft]; destruct (IHf Hubf Hfrf) as [Huf Hff].
    rewrite Huc, Hut, Huf, Hfc, Hft, Hff; split; reflexivity.
Qed.

Lemma eval_cert_expr_set_unused_lf {Pa : Params} :
  forall e (penv : param_env Pa) foracle nm vt,
    is_let_free_expr e = true ->
    ~ In nm (List.map fst (collect_free_vars [] e)) ->
    eval_closed_cert_expr (set_param_env penv nm vt) foracle e =
    eval_closed_cert_expr penv foracle e.
Proof.
  intros e penv foracle nm vt; induction e as
    [ w0 val0 | w0 | nm0 w0
    | op w0 fl l IHl r IHr
    | pr ss w0 l IHl r IHr
    | k fw tw fl o IHo
    | w0 c IHc t IHt f IHf
    | w0 o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hlf Hni; try discriminate Hlf;
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
  - reflexivity.
  - reflexivity.
  - cbn [collect_free_vars] in Hni; cbn [lookup_let_val].
    unfold set_param_env; destruct (String.eqb nm nm0) eqn:Eeq; [| reflexivity].
    apply String.eqb_eq in Eeq; subst nm0;
      exfalso; apply Hni; left; reflexivity.
  - cbn [is_let_free_expr collect_free_vars] in Hlf, Hni; apply andb_true_iff in Hlf as [Hl Hr]; rewrite map_app in Hni.
    rewrite (IHl Hl (fun H => Hni (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHr Hr (fun H => Hni (proj2 (in_app_iff _ _ _) (or_intror H)))).
    reflexivity.
  - cbn [is_let_free_expr collect_free_vars] in Hlf, Hni; apply andb_true_iff in Hlf as [Hl Hr]; rewrite map_app in Hni.
    rewrite (IHl Hl (fun H => Hni (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHr Hr (fun H => Hni (proj2 (in_app_iff _ _ _) (or_intror H)))).
    reflexivity.
  - rewrite (IHo Hlf Hni); reflexivity.
  - cbn [is_let_free_expr collect_free_vars] in Hlf, Hni; rewrite !andb_true_iff in Hlf; rewrite !map_app in Hni.
    destruct Hlf as ([Hc Ht] & Hf).
    rewrite (IHc Hc (fun H => Hni (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHt Ht (fun H => Hni (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl H)))))).
    rewrite (IHf Hf (fun H => Hni (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_intror H)))))).
    reflexivity.
  - rewrite (IHo Hlf Hni); reflexivity.
Qed.

Lemma eval_cert_expr_subst_eq {Pa : Params} :
  forall target nm w (vt : @dvalue Pa) e penv foracle,
    freeze_free_expr e = true ->
    ~ In nm (List.map fst (collect_free_vars [] e)) ->
    eval_closed_cert_expr penv foracle target = raise_ret vt ->
    wf_scalar_dvalue w vt ->
    eval_closed_cert_expr (set_param_env penv nm vt) foracle (subst_subexpr target (CE_Var nm w) e) =
    eval_closed_cert_expr penv foracle e.
Proof.
  intros target nm w vt e penv foracle Hfr Hni Hevt Hwfv; revert Hfr Hni.
  induction e as
    [ w0 val0 | w0 | nm0 w0
    | op w0 fl l IHl r IHr
    | pr ss w0 l IHl r IHr
    | k fw tw fl o IHo
    | w0 c IHc t IHt f IHf
    | w0 o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hfr Hni; try discriminate Hfr;
    cbn [subst_subexpr];
    destruct (cert_expr_eqb _ target) eqn:Heq;
    try (apply cert_expr_eqb_eq in Heq; subst target;
         unfold eval_closed_cert_expr in *; cbn [eval_cert_expr lookup_let_val];
         unfold set_param_env; rewrite String.eqb_refl, (check_scalar_width_ok w vt Hwfv);
         symmetry; exact Hevt).
  - reflexivity.
  - reflexivity.
  - unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; cbn [collect_free_vars] in Hni.
    unfold set_param_env; destruct (String.eqb nm nm0) eqn:Eeq; [| reflexivity].
    apply String.eqb_eq in Eeq; subst nm0;
      exfalso; apply Hni; left; reflexivity.
  - cbn [freeze_free_expr collect_free_vars] in Hfr, Hni;
      apply andb_true_iff in Hfr as [Hfl Hfr]; rewrite map_app in Hni.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    rewrite (IHl Hfl (fun H => Hni (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHr Hfr (fun H => Hni (proj2 (in_app_iff _ _ _) (or_intror H)))).
    reflexivity.
  - cbn [freeze_free_expr collect_free_vars] in Hfr, Hni;
      apply andb_true_iff in Hfr as [Hfl Hfr]; rewrite map_app in Hni.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    rewrite (IHl Hfl (fun H => Hni (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHr Hfr (fun H => Hni (proj2 (in_app_iff _ _ _) (or_intror H)))).
    reflexivity.
  - unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite (IHo Hfr Hni); reflexivity.
  - cbn [freeze_free_expr collect_free_vars] in Hfr, Hni; rewrite !andb_true_iff in Hfr; rewrite !map_app in Hni.
    destruct Hfr as ([Hfc Hft] & Hff).
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    rewrite (IHc Hfc (fun H => Hni (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHt Hft (fun H => Hni (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl H)))))).
    rewrite (IHf Hff (fun H => Hni (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_intror H)))))).
    reflexivity.
Qed.

Lemma binop_flags_weaken_refl : forall fl,
  binop_flags_weaken fl fl = true.
Proof.
  intros [nuw nsw ex dj]; unfold binop_flags_weaken; cbn;
    destruct nuw, nsw, ex, dj; reflexivity.
Qed.

Lemma cast_flags_weaken_refl : forall fl,
  cast_flags_weaken fl fl = true.
Proof.
  intros [nn nuw nsw]; unfold cast_flags_weaken; cbn;
    destruct nn, nuw, nsw; reflexivity.
Qed.

Lemma eval_cert_expr_mono_var {Pa : Params} :
  forall e nm w (vs vt : @dvalue Pa) penv foracle,
    wt_cert_expr [] e = true ->
    is_let_free_expr e = true ->
    ub_free_expr e = true ->
    freeze_free_expr e = true ->
    dvalue_refines vs vt ->
    wf_scalar_dvalue w vs ->
    wf_scalar_dvalue w vt ->
    Forall (fun '(x, wx) => x = nm -> wx = w) (collect_free_vars [] e) ->
    wf_param_env_for (collect_free_vars [] e) (set_param_env penv nm vs) ->
    refine_eou_dvalue
      (eval_closed_cert_expr (set_param_env penv nm vs) foracle e)
      (eval_closed_cert_expr (set_param_env penv nm vt) foracle e).
Proof.
  intros e nm w vs vt penv foracle Hwt Hlf Hub Hfr Href Hwvs Hwvt Hfa Hpenv; revert Hwt Hlf Hub Hfr Hfa Hpenv.
  induction e as
    [ w0 val0 | w0 | nm0 w0
    | op w0 fl l IHl r IHr
    | pr ss w0 l IHl r IHr
    | k fw tw fl o IHo
    | w0 c IHc t IHt f IHf
    | w0 o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hwt Hlf Hub Hfr Hfa Hpenv; try discriminate Hfr.
  - apply refine_eou_dvalue_refl.
  - apply refine_eou_dvalue_refl.
  - unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val].
    unfold set_param_env; destruct (String.eqb nm nm0) eqn:Eeq.
    + apply String.eqb_eq in Eeq; subst nm0.
      inversion Hfa as [| ? ? Hwx _]; subst; specialize (Hwx eq_refl); subst w0.
      rewrite (check_scalar_width_ok w vs Hwvs), (check_scalar_width_ok w vt Hwvt); exact Href.
    + destruct (penv nm0) as [dv |]; [| cbn; exact I].
      destruct (check_scalar_width w0 dv); cbn; [exact I.. | apply dvalue_refines_refl].
  - cbn [wt_cert_expr is_let_free_expr ub_free_expr freeze_free_expr collect_free_vars] in *.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf;
      rewrite !andb_true_iff in Hub; rewrite !andb_true_iff in Hfr.
    destruct Hwt as ((((Hfl & Hwtl) & Hwtr) & Hwl) & Hwr).
    destruct Hlf as [Hlfl Hlfr]; destruct Hub as ([Hop Hubl] & Hubr); destruct Hfr as [Hfrl Hfrr].
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr; apply negb_true_iff in Hop.
    apply Forall_app in Hfa as [Hfal Hfar].
    assert (Hpl : wf_param_env_for (collect_free_vars [] l) (set_param_env penv nm vs))
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars [] r) (set_param_env penv nm vs))
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
    assert (Hpl_t : wf_param_env_for (collect_free_vars [] l) (set_param_env penv nm vt)).
    { intros x wx Hx; unfold set_param_env; destruct (String.eqb nm x) eqn:Enm.
      - apply String.eqb_eq in Enm; subst x.
        rewrite Forall_forall in Hfal; pose proof (Hfal (nm, wx) Hx eq_refl) as ->.
        exists vt; split; [reflexivity | exact Hwvt].
      - destruct (Hpl x wx Hx) as [dv [Hdv Hwfdv]]; unfold set_param_env in Hdv; rewrite Enm in Hdv.
        exists dv; split; assumption. }
    assert (Hpr_t : wf_param_env_for (collect_free_vars [] r) (set_param_env penv nm vt)).
    { intros x wx Hx; unfold set_param_env; destruct (String.eqb nm x) eqn:Enm.
      - apply String.eqb_eq in Enm; subst x.
        rewrite Forall_forall in Hfar; pose proof (Hfar (nm, wx) Hx eq_refl) as ->.
        exists vt; split; [reflexivity | exact Hwvt].
      - destruct (Hpr x wx Hx) as [dv [Hdv Hwfdv]]; unfold set_param_env in Hdv; rewrite Enm in Hdv.
        exists dv; split; assumption. }
    destruct (ub_free_expr_eval_ret l [] _ [] foracle Hubl Hwtl wf_let_val_env_nil Hpl) as [vl1 [El1 Hwfl1]].
    destruct (ub_free_expr_eval_ret r [] _ [] foracle Hubr Hwtr wf_let_val_env_nil Hpr) as [vr1 [Er1 Hwfr1]].
    destruct (ub_free_expr_eval_ret l [] _ [] foracle Hubl Hwtl wf_let_val_env_nil Hpl_t) as [vl2 [El2 Hwfl2]].
    destruct (ub_free_expr_eval_ret r [] _ [] foracle Hubr Hwtr wf_let_val_env_nil Hpr_t) as [vr2 [Er2 Hwfr2]].
    pose proof (IHl Hwtl Hlfl Hubl Hfrl Hfal Hpl) as Rl.
    pose proof (IHr Hwtr Hlfr Hubr Hfrr Hfar Hpr) as Rr.
    unfold eval_closed_cert_expr in *; rewrite El1, El2 in Rl; rewrite Er1, Er2 in Rr; cbn in Rl, Rr.
    cbn [eval_cert_expr]; rewrite El1, Er1, El2, Er2; cbn [eou_bind].
    rewrite Hwl in Hwfl1, Hwfl2; rewrite Hwr in Hwfr1, Hwfr2.
    exact (eval_iop_non_div_rem_monotone op fl fl w0 vl1 vl2 vr1 vr2
             Hop (binop_flags_weaken_refl fl) Hwfl1 Hwfl2 Hwfr1 Hwfr2 Rl Rr).
  - cbn [wt_cert_expr is_let_free_expr ub_free_expr freeze_free_expr collect_free_vars] in *.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf;
      rewrite !andb_true_iff in Hub; rewrite !andb_true_iff in Hfr.
    destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr);
      destruct Hlf as [Hlfl Hlfr]; destruct Hub as [Hubl Hubr]; destruct Hfr as [Hfrl Hfrr].
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    apply Forall_app in Hfa as [Hfal Hfar].
    assert (Hpl : wf_param_env_for (collect_free_vars [] l) (set_param_env penv nm vs))
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars [] r) (set_param_env penv nm vs))
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
    assert (Hpl_t : wf_param_env_for (collect_free_vars [] l) (set_param_env penv nm vt)).
    { intros x wx Hx; unfold set_param_env; destruct (String.eqb nm x) eqn:Enm.
      - apply String.eqb_eq in Enm; subst x; rewrite Forall_forall in Hfal;
          rewrite (Hfal (nm, wx) Hx eq_refl); exists vt; split; auto.
      - destruct (Hpl x wx Hx) as [dv [Hdv Hwfdv]]; unfold set_param_env in Hdv;
          rewrite Enm in Hdv; exists dv; split; assumption. }
    assert (Hpr_t : wf_param_env_for (collect_free_vars [] r) (set_param_env penv nm vt)).
    { intros x wx Hx; unfold set_param_env; destruct (String.eqb nm x) eqn:Enm.
      - apply String.eqb_eq in Enm; subst x; rewrite Forall_forall in Hfar;
          rewrite (Hfar (nm, wx) Hx eq_refl); exists vt; split; auto.
      - destruct (Hpr x wx Hx) as [dv [Hdv Hwfdv]]; unfold set_param_env in Hdv;
          rewrite Enm in Hdv; exists dv; split; assumption. }
    destruct (ub_free_expr_eval_ret l [] _ [] foracle Hubl Hwtl wf_let_val_env_nil Hpl) as [vl1 [El1 Hwfl1]].
    destruct (ub_free_expr_eval_ret r [] _ [] foracle Hubr Hwtr wf_let_val_env_nil Hpr) as [vr1 [Er1 Hwfr1]].
    destruct (ub_free_expr_eval_ret l [] _ [] foracle Hubl Hwtl wf_let_val_env_nil Hpl_t) as [vl2 [El2 Hwfl2]].
    destruct (ub_free_expr_eval_ret r [] _ [] foracle Hubr Hwtr wf_let_val_env_nil Hpr_t) as [vr2 [Er2 Hwfr2]].
    pose proof (IHl Hwtl Hlfl Hubl Hfrl Hfal Hpl) as Rl.
    pose proof (IHr Hwtr Hlfr Hubr Hfrr Hfar Hpr) as Rr.
    unfold eval_closed_cert_expr in *; rewrite El1, El2 in Rl; rewrite Er1, Er2 in Rr; cbn in Rl, Rr.
    cbn [eval_cert_expr]; rewrite El1, Er1, El2, Er2; cbn [eou_bind].
    rewrite Hwl in Hwfl1, Hwfl2; rewrite Hwr in Hwfr1, Hwfr2.
    exact (eval_icmp_monotone ss ss pr w0 vl1 vl2 vr1 vr2
             (Bool.implb_same ss) Hwfl1 Hwfl2 Hwfr1 Hwfr2 Rl Rr).
  - cbn [wt_cert_expr is_let_free_expr ub_free_expr freeze_free_expr collect_free_vars] in *.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((Hk & Hwto) & Hwo); apply Pos.eqb_eq in Hwo.
    assert (Hpo_t : wf_param_env_for (collect_free_vars [] o) (set_param_env penv nm vt)).
    { intros x wx Hx; unfold set_param_env; destruct (String.eqb nm x) eqn:Enm.
      - apply String.eqb_eq in Enm; subst x; rewrite Forall_forall in Hfa;
          rewrite (Hfa (nm, wx) Hx eq_refl); exists vt; split; auto.
      - destruct (Hpenv x wx Hx) as [dv [Hdv Hwfdv]]; unfold set_param_env in Hdv;
          rewrite Enm in Hdv; exists dv; split; assumption. }
    destruct (ub_free_expr_eval_ret o [] _ [] foracle Hub Hwto wf_let_val_env_nil Hpenv) as [vo1 [Eo1 Hwfo1]].
    destruct (ub_free_expr_eval_ret o [] _ [] foracle Hub Hwto wf_let_val_env_nil Hpo_t) as [vo2 [Eo2 Hwfo2]].
    pose proof (IHo Hwto Hlf Hub Hfr Hfa Hpenv) as Ro.
    unfold eval_closed_cert_expr in *; rewrite Eo1, Eo2 in Ro; cbn in Ro.
    cbn [eval_cert_expr]; rewrite Eo1, Eo2; cbn [eou_bind].
    rewrite Hwo in Hwfo1, Hwfo2.
    exact (eval_cast_monotone k fw tw fl fl vo1 vo2 Hk Hk (cast_flags_weaken_refl fl) Hwfo1 Hwfo2 Ro).
  - cbn [wt_cert_expr is_let_free_expr ub_free_expr freeze_free_expr collect_free_vars] in *.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf;
      rewrite !andb_true_iff in Hub; rewrite !andb_true_iff in Hfr.
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hwc) & Hwt0) & Hwf0).
    destruct Hlf as ([Hlfc Hlft] & Hlff); destruct Hub as ([Hubc Hubt] & Hubf); destruct Hfr as ([Hfrc Hfrt] & Hfrf).
    apply Pos.eqb_eq in Hwc; apply Pos.eqb_eq in Hwt0; apply Pos.eqb_eq in Hwf0.
    apply Forall_app in Hfa as [Hfac Hfatf]; apply Forall_app in Hfatf as [Hfat Hfaf].
    assert (Hpc : wf_param_env_for (collect_free_vars [] c) (set_param_env penv nm vs))
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpt : wf_param_env_for (collect_free_vars [] t) (set_param_env penv nm vs))
      by (intros x wx Hx; apply Hpenv, in_app_iff;
          right; apply in_app_iff; left; exact Hx).
    assert (Hpf : wf_param_env_for (collect_free_vars [] f) (set_param_env penv nm vs))
      by (intros x wx Hx; apply Hpenv, in_app_iff;
          right; apply in_app_iff; right; exact Hx).
    assert (Hpc_t : wf_param_env_for (collect_free_vars [] c) (set_param_env penv nm vt)).
    { intros x wx Hx; unfold set_param_env; destruct (String.eqb nm x) eqn:Enm.
      - apply String.eqb_eq in Enm; subst x; rewrite Forall_forall in Hfac;
          rewrite (Hfac (nm, wx) Hx eq_refl); exists vt; split; auto.
      - destruct (Hpc x wx Hx) as [dv [Hdv Hwfdv]]; unfold set_param_env in Hdv;
          rewrite Enm in Hdv; exists dv; split; assumption. }
    assert (Hpt_t : wf_param_env_for (collect_free_vars [] t) (set_param_env penv nm vt)).
    { intros x wx Hx; unfold set_param_env; destruct (String.eqb nm x) eqn:Enm.
      - apply String.eqb_eq in Enm; subst x; rewrite Forall_forall in Hfat;
          rewrite (Hfat (nm, wx) Hx eq_refl); exists vt; split; auto.
      - destruct (Hpt x wx Hx) as [dv [Hdv Hwfdv]]; unfold set_param_env in Hdv;
          rewrite Enm in Hdv; exists dv; split; assumption. }
    assert (Hpf_t : wf_param_env_for (collect_free_vars [] f) (set_param_env penv nm vt)).
    { intros x wx Hx; unfold set_param_env; destruct (String.eqb nm x) eqn:Enm.
      - apply String.eqb_eq in Enm; subst x; rewrite Forall_forall in Hfaf;
          rewrite (Hfaf (nm, wx) Hx eq_refl); exists vt; split; auto.
      - destruct (Hpf x wx Hx) as [dv [Hdv Hwfdv]]; unfold set_param_env in Hdv;
          rewrite Enm in Hdv; exists dv; split; assumption. }
    destruct (ub_free_expr_eval_ret c [] _ [] foracle Hubc Hwtc wf_let_val_env_nil Hpc) as [vc1 [Ec1 Hwfc1]].
    destruct (ub_free_expr_eval_ret t [] _ [] foracle Hubt Hwtt wf_let_val_env_nil Hpt) as [vt1 [Et1 Hwft1]].
    destruct (ub_free_expr_eval_ret f [] _ [] foracle Hubf Hwtf wf_let_val_env_nil Hpf) as [vf1 [Ef1 Hwff1]].
    destruct (ub_free_expr_eval_ret c [] _ [] foracle Hubc Hwtc wf_let_val_env_nil Hpc_t) as [vc2 [Ec2 Hwfc2]].
    destruct (ub_free_expr_eval_ret t [] _ [] foracle Hubt Hwtt wf_let_val_env_nil Hpt_t) as [vt2 [Et2 Hwft2]].
    destruct (ub_free_expr_eval_ret f [] _ [] foracle Hubf Hwtf wf_let_val_env_nil Hpf_t) as [vf2 [Ef2 Hwff2]].
    pose proof (IHc Hwtc Hlfc Hubc Hfrc Hfac Hpc) as Rc.
    pose proof (IHt Hwtt Hlft Hubt Hfrt Hfat Hpt) as Rt.
    pose proof (IHf Hwtf Hlff Hubf Hfrf Hfaf Hpf) as Rf.
    unfold eval_closed_cert_expr in *; rewrite Ec1, Ec2 in Rc; rewrite Et1, Et2 in Rt; rewrite Ef1, Ef2 in Rf;
      cbn in Rc, Rt, Rf.
    cbn [eval_cert_expr]; rewrite Ec1, Et1, Ef1, Ec2, Et2, Ef2; cbn [eou_bind].
    rewrite Hwc in Hwfc1, Hwfc2; rewrite Hwt0 in Hwft1, Hwft2; rewrite Hwf0 in Hwff1, Hwff2.
    exact (eval_select_monotone w0 vc1 vc2 vt1 vt2 vf1 vf2 Hwfc1 Hwfc2 Hwft1 Hwft2 Hwff1 Hwff2 Rc Rt Rf).
Qed.

Definition ub_assumption_bad_or_mentions (nm : string) (ua : ub_assumption) : bool :=
  match ua with
  | UBA_ParamNoUndef p _ | UBA_PtrNonNull p | UBA_PtrAligned p _
  | UBA_PtrDereferenceable p _ | UBA_LoadNoUndef p _ => String.eqb p nm
  | UBA_DivisorNonZero e | UBA_BranchCondDefined e =>
      let ee := expand_lets e in
      negb (is_let_free_expr ee) || string_in_list nm (List.map fst (collect_free_vars [] ee))
  | UBA_SignedDivNoOverflow l r =>
      let el := expand_lets l in
      let er := expand_lets r in
      negb (is_let_free_expr el && is_let_free_expr er) ||
      string_in_list nm (List.map fst (collect_free_vars [] el ++ collect_free_vars [] er))
  | UBA_UnreachableEliminated => false
  end.

Definition var_in_ub_ctx (nm : string) (ctx : ub_ctx) : bool :=
  existsb (ub_assumption_bad_or_mentions nm) ctx.

Lemma ub_ctx_holds_set_fresh {Pa : Params} :
  forall (penv : param_env Pa) foracle ctx nm vt,
    var_in_ub_ctx nm ctx = false ->
    ub_ctx_holds penv foracle ctx ->
    ub_ctx_holds (set_param_env penv nm vt) foracle ctx.
Proof.
  intros penv foracle ctx nm vt Hvar Hctx.
  induction Hctx as [| ua rest Hua Hrest IH]; [constructor |].
  unfold var_in_ub_ctx in Hvar; cbn [existsb] in Hvar; apply orb_false_iff in Hvar as [Hu Hvr].
  constructor; [| exact (IH Hvr)].
  destruct ua; cbn [ub_assumption_bad_or_mentions] in Hu; cbn [ub_assumption_holds] in Hua |- *.
  - intros dv Hdv; unfold set_param_env in Hdv; rewrite (String.eqb_sym nm param), Hu in Hdv; exact (Hua dv Hdv).
  - intros dv Hdv; unfold set_param_env in Hdv; rewrite (String.eqb_sym nm param), Hu in Hdv; exact (Hua dv Hdv).
  - intros dv Hdv; unfold set_param_env in Hdv; rewrite (String.eqb_sym nm param), Hu in Hdv; exact (Hua dv Hdv).
  - intros dv Hdv; unfold set_param_env in Hdv; rewrite (String.eqb_sym nm param), Hu in Hdv; exact (Hua dv Hdv).
  - intros dv Hdv; unfold set_param_env in Hdv; rewrite (String.eqb_sym nm slot), Hu in Hdv; exact (Hua dv Hdv).
  - apply orb_false_iff in Hu as [Hlf Hnin]; apply negb_false_iff in Hlf.
    rewrite eval_cert_expr_set_unused_lf; [exact Hua | exact Hlf |].
    intros Hin; apply string_in_list_spec in Hin; congruence.
  - apply orb_false_iff in Hu as [Hlf Hnin]; apply negb_false_iff, andb_true_iff in Hlf as [Hlfl Hlfr].
    intros w il ir Hl Hr.
    rewrite eval_cert_expr_set_unused_lf in Hl;
      [| exact Hlfl
      | intros Hin;
        assert (Hin' : In nm (List.map fst
          (collect_free_vars [] (expand_lets lhs) ++ collect_free_vars [] (expand_lets rhs))))
          by (rewrite map_app; apply in_app_iff; left; exact Hin);
        apply string_in_list_spec in Hin'; congruence].
    rewrite eval_cert_expr_set_unused_lf in Hr;
      [| exact Hlfr
      | intros Hin;
        assert (Hin' : In nm (List.map fst
          (collect_free_vars [] (expand_lets lhs) ++ collect_free_vars [] (expand_lets rhs))))
          by (rewrite map_app; apply in_app_iff; right; exact Hin);
        apply string_in_list_spec in Hin'; congruence].
    exact (Hua w il ir Hl Hr).
  - apply orb_false_iff in Hu as [Hlf Hnin]; apply negb_false_iff in Hlf.
    intros v Hv; rewrite eval_cert_expr_set_unused_lf in Hv;
      [exact (Hua v Hv) | exact Hlf | intros Hin; apply string_in_list_spec in Hin; congruence].
  - exact Hua.
Qed.

Fixpoint mk_fresh_abs_loop (fuel : nat) (cand : string) (avoid : list string) (ctx : ub_ctx)
  : option string :=
  match fuel with
  | O => None
  | S fuel' =>
      if negb (starts_with_dollar cand) &&
         negb (string_in_list cand avoid) &&
         negb (var_in_ub_ctx cand ctx)
      then Some cand
      else mk_fresh_abs_loop fuel' (String.append cand "_") avoid ctx
  end.

Definition fresh_abs_name (idx : nat) (avoid : list string) (ctx : ub_ctx) : option string :=
  let base := String.append "mc_abs_" (show_Z_dec (Z.of_nat idx)) in
  mk_fresh_abs_loop (S (List.length avoid + List.length ctx)) base avoid ctx.

Lemma fresh_abs_name_ok : forall idx avoid ctx nm,
  fresh_abs_name idx avoid ctx = Some nm ->
  negb (starts_with_dollar nm) = true /\
  negb (string_in_list nm avoid) = true /\
  var_in_ub_ctx nm ctx = false.
Proof.
  intros idx avoid ctx nm H; unfold fresh_abs_name in H.
  set (fuel := S (List.length avoid + List.length ctx)) in *.
  set (cand := String.append "mc_abs_" (show_Z_dec (Z.of_nat idx))) in *.
  clearbody fuel cand; revert cand H; induction fuel as [| fuel' IH];
    intros cand H; cbn in H; [discriminate H |].
  destruct (negb (starts_with_dollar cand) && negb (string_in_list cand avoid) && negb (var_in_ub_ctx cand ctx))
    eqn:Eok; [| exact (IH _ H)].
  inversion H; subst cand; clear H.
  rewrite !andb_true_iff in Eok; destruct Eok as ([H1 H2] & H3).
  apply negb_true_iff in H3; repeat split; assumption.
Qed.

Fixpoint find_matching_mul_tgt
  (ctx : ub_ctx) (w_s : positive) (ms : cert_expr) (cands : list (positive * cert_expr))
  {struct cands} : option cert_expr :=
  match cands with
  | [] => None
  | (w_t, mt) :: rest =>
      if Pos.eqb w_s w_t &&
         wt_cert_expr [] mt && is_let_free_expr mt && ub_free_expr mt &&
         check_expr_refines ctx ms mt
      then Some mt
      else find_matching_mul_tgt ctx w_s ms rest
  end.

Fixpoint find_matching_mul_pair
  (ctx : ub_ctx) (s_cands t_cands : list (positive * cert_expr))
  {struct s_cands} : option (positive * cert_expr * cert_expr) :=
  match s_cands with
  | [] => None
  | (w_s, ms) :: rest =>
      if wt_cert_expr [] ms && is_let_free_expr ms && ub_free_expr ms then
        match find_matching_mul_tgt ctx w_s ms t_cands with
        | Some mt => Some (w_s, ms, mt)
        | None => find_matching_mul_pair ctx rest t_cands
        end
      else find_matching_mul_pair ctx rest t_cands
  end.

Definition abstract_one_mul
  (ctx : ub_ctx) (avoid : list string) (idx : nat) (es et : cert_expr)
  : option (string * positive * cert_expr * cert_expr * cert_expr * cert_expr) :=
  if wt_cert_expr [] es && wt_cert_expr [] et &&
     is_let_free_expr es && is_let_free_expr et &&
     ub_free_expr es && ub_free_expr et &&
     freeze_free_expr es && freeze_free_expr et then
    match find_matching_mul_pair ctx (collect_nonblastable_muls es) (collect_nonblastable_muls et) with
    | None => None
    | Some (w, ms, mt) =>
        if Pos.eqb (cert_expr_bit_width ms) w && Pos.eqb (cert_expr_bit_width mt) w then
          match fresh_abs_name idx avoid ctx with
          | None => None
          | Some nm =>
              let es' := subst_subexpr ms (CE_Var nm w) es in
              let et' := subst_subexpr mt (CE_Var nm w) et in
              Some (nm, w, ms, mt, es', et')
          end
        else None
    end
  else None.

Fixpoint abstract_shared_muls
  (fuel : nat) (ctx : ub_ctx) (avoid : list string) (idx : nat) (es et : cert_expr)
  {struct fuel} : cert_expr * cert_expr :=
  match fuel with
  | O => (es, et)
  | S fuel' =>
      match abstract_one_mul ctx avoid idx es et with
      | None => (es, et)
      | Some (nm, _, _, _, es', et') =>
          abstract_shared_muls fuel' ctx (nm :: avoid) (S idx) es' et'
      end
  end.

Lemma collect_nonblastable_muls_acc_vars :
  forall e acc w m,
    In (w, m) (collect_nonblastable_muls_acc acc e) ->
    In (w, m) acc \/ incl (collect_free_vars [] m) (collect_free_vars [] e).
Proof.
  intros e acc w m; revert acc.
  induction e as
    [ w0 val0 | w0 | nm0 w0
    | op w0 fl l IHl r IHr
    | pr ss w0 l IHl r IHr
    | k fw tw fl o IHo
    | w0 c IHc t IHt f IHf
    | w0 o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros acc Hin; cbn [collect_nonblastable_muls_acc] in Hin;
    try match type of Hin with
        | context [if is_nonblastable_mul ?ee then _ else _] =>
            assert (Hacc1 :
              In (w, m) (if is_nonblastable_mul ee then (cert_expr_bit_width ee, ee) :: acc else acc) ->
              In (w, m) acc \/ incl (collect_free_vars [] m) (collect_free_vars [] ee))
              by (destruct (is_nonblastable_mul ee);
                  [intros [Heq | Ha]; [inversion Heq; right; apply incl_refl | left; exact Ha]
                  | intro Ha; left; exact Ha])
        end.
  - left; exact Hin.
  - left; exact Hin.
  - left; exact Hin.
  - destruct (IHr _ Hin) as [Hl | Hr].
    + destruct (IHl _ Hl) as [Ha1 | Hl0];
        [first [exact (Hacc1 Ha1) | left; exact Ha1] |].
      right; cbn [collect_free_vars];
        intros x Hx; apply in_app_iff; left; exact (Hl0 x Hx).
    + right; cbn [collect_free_vars];
        intros x Hx; apply in_app_iff; right; exact (Hr x Hx).
  - destruct (IHr _ Hin) as [Hl | Hr].
    + destruct (IHl _ Hl) as [Ha1 | Hl0];
        [first [exact (Hacc1 Ha1) | left; exact Ha1] |].
      right; cbn [collect_free_vars];
        intros x Hx; apply in_app_iff; left; exact (Hl0 x Hx).
    + right; cbn [collect_free_vars];
        intros x Hx; apply in_app_iff; right; exact (Hr x Hx).
  - destruct (IHo _ Hin) as [Ha1 | Ho];
      [first [exact (Hacc1 Ha1) | left; exact Ha1] | right; exact Ho].
  - destruct (IHf _ Hin) as [Ht | Hf].
    + destruct (IHt _ Ht) as [Hc | Ht0].
      * destruct (IHc _ Hc) as [Ha1 | Hc0];
          [first [exact (Hacc1 Ha1) | left; exact Ha1] |].
        right; cbn [collect_free_vars];
          intros x Hx; apply in_app_iff; left; exact (Hc0 x Hx).
      * right; cbn [collect_free_vars]; intros x Hx;
          apply in_app_iff; right; apply in_app_iff; left; exact (Ht0 x Hx).
    + right; cbn [collect_free_vars]; intros x Hx;
        apply in_app_iff; right; apply in_app_iff; right; exact (Hf x Hx).
  - destruct (IHo _ Hin) as [Ha1 | Ho];
      [first [exact (Hacc1 Ha1) | left; exact Ha1] | right; exact Ho].
  - left; exact Hin.
Qed.

Lemma collect_nonblastable_muls_vars :
  forall e w m,
    In (w, m) (collect_nonblastable_muls e) ->
    incl (collect_free_vars [] m) (collect_free_vars [] e).
Proof.
  intros e w m Hin.
  destruct (collect_nonblastable_muls_acc_vars e [] w m Hin) as [[] | H]; exact H.
Qed.

Lemma find_matching_mul_tgt_spec :
  forall ctx w_s ms t_cands mt,
    find_matching_mul_tgt ctx w_s ms t_cands = Some mt ->
    In (w_s, mt) t_cands /\
    wt_cert_expr [] mt = true /\
    is_let_free_expr mt = true /\
    ub_free_expr mt = true /\
    check_expr_refines ctx ms mt = true.
Proof.
  intros ctx w_s ms t_cands mt; induction t_cands as [| [w_t mt0] rest IH]; cbn; [discriminate |].
  destruct (Pos.eqb w_s w_t && wt_cert_expr [] mt0 && is_let_free_expr mt0 &&
            ub_free_expr mt0 && check_expr_refines ctx ms mt0) eqn:Eok.
  - rewrite !andb_true_iff in Eok; destruct Eok as ((((Hw & Hwt) & Hlf) & Hub) & Href).
    apply Pos.eqb_eq in Hw; subst w_t; intros H; inversion H; subst mt0.
    repeat split; try assumption; left; reflexivity.
  - intros H; destruct (IH H) as (Hin & ? & ? & ? & ?);
      repeat split; try assumption; right; exact Hin.
Qed.

Lemma find_matching_mul_pair_spec :
  forall ctx s_cands t_cands w ms mt,
    find_matching_mul_pair ctx s_cands t_cands = Some (w, ms, mt) ->
    In (w, ms) s_cands /\
    In (w, mt) t_cands /\
    wt_cert_expr [] ms = true /\ is_let_free_expr ms = true /\ ub_free_expr ms = true /\
    wt_cert_expr [] mt = true /\ is_let_free_expr mt = true /\ ub_free_expr mt = true /\
    check_expr_refines ctx ms mt = true.
Proof.
  intros ctx s_cands t_cands w ms mt; induction s_cands as [| [w_s ms0] rest IH]; cbn; [discriminate |].
  destruct (wt_cert_expr [] ms0 && is_let_free_expr ms0 && ub_free_expr ms0) eqn:Ems.
  - rewrite !andb_true_iff in Ems; destruct Ems as ([Hwts Hlfs] & Hubs).
    destruct (find_matching_mul_tgt ctx w_s ms0 t_cands) as [mt0 |] eqn:Etgt.
    + intros H; inversion H; subst w_s ms0 mt0.
      destruct (find_matching_mul_tgt_spec _ _ _ _ _ Etgt) as (Hint & Hwtt & Hlft & Hubt & Href).
      repeat split; try assumption; left; reflexivity.
    + intros H; destruct (IH H) as (Hins & ? & ? & ? & ? & ? & ? & ? & ?);
        repeat split; try assumption; right; exact Hins.
  - intros H; destruct (IH H) as (Hins & ? & ? & ? & ? & ? & ? & ? & ?);
      repeat split; try assumption; right; exact Hins.
Qed.

Lemma abstract_shared_muls_sound {Pa : Params} :
  forall fuel ctx avoid idx es et es_out et_out opt_pf (penv : param_env Pa) foracle,
    Forall (fun x => string_in_list x avoid = true) (List.map fst (collect_free_vars [] es)) ->
    Forall (fun x => string_in_list x avoid = true) (List.map fst (collect_free_vars [] et)) ->
    wf_param_env_for (collect_free_vars [] es) penv ->
    wf_param_env_for (collect_free_vars [] et) penv ->
    ub_ctx_holds penv foracle ctx ->
    abstract_shared_muls fuel ctx avoid idx es et = (es_out, et_out) ->
    check_expr_refines_with_lrat ctx es_out et_out opt_pf = true ->
    refine_eou_dvalue
      (eval_closed_cert_expr penv foracle es)
      (eval_closed_cert_expr penv foracle et).
Proof.
  induction fuel as [| fuel' IH];
    intros ctx avoid idx es et es_out et_out opt_pf penv foracle
           Havs Havt Hps Hpt Hctx Habs Hchk;
    cbn [abstract_shared_muls] in Habs.
  - inversion Habs; subst es_out et_out.
    exact (check_expr_refines_with_lrat_sound ctx es et opt_pf penv foracle Hchk Hps Hpt Hctx).
  - destruct (abstract_one_mul ctx avoid idx es et)
      as [[[[[[nm w] ms] mt] es'] et'] |] eqn:Eone.
    + unfold abstract_one_mul in Eone.
      destruct (wt_cert_expr [] es && wt_cert_expr [] et &&
                is_let_free_expr es && is_let_free_expr et &&
                ub_free_expr es && ub_free_expr et &&
                freeze_free_expr es && freeze_free_expr et) eqn:Ewf; [| discriminate Eone].
      rewrite !andb_true_iff in Ewf.
      destruct Ewf as (((((((Hwts & Hwtt) & Hlfs) & Hlft) & Hubs) & Hubt) & Hfrs) & Hfrt).
      destruct (find_matching_mul_pair ctx (collect_nonblastable_muls es) (collect_nonblastable_muls et))
        as [[[w0 ms0] mt0] |] eqn:Epair; [| discriminate Eone].
      destruct (Pos.eqb (cert_expr_bit_width ms0) w0 && Pos.eqb (cert_expr_bit_width mt0) w0) eqn:Ebw;
        [| discriminate Eone].
      destruct (fresh_abs_name idx avoid ctx) as [nm0 |] eqn:Efr; [| discriminate Eone].
      inversion Eone; subst nm0 w0 ms0 mt0 es' et'; clear Eone.
      apply andb_true_iff in Ebw as [Ebws Ebwt]; apply Pos.eqb_eq in Ebws; apply Pos.eqb_eq in Ebwt.
      destruct (find_matching_mul_pair_spec _ _ _ _ _ _ Epair)
        as (Hins & Hint & Hwt_ms & Hlf_ms & Hub_ms & Hwt_mt & Hlf_mt & Hub_mt & Href_m).
      destruct (fresh_abs_name_ok _ _ _ _ Efr) as (Hnd & Hnin_av & Hnin_ctx).
      assert (Hnin_es : ~ In nm (List.map fst (collect_free_vars [] es))).
      { intros Hin; rewrite Forall_forall in Havs;
          pose proof (Havs nm Hin) as Hs; rewrite Hs in Hnin_av; discriminate. }
      assert (Hnin_et : ~ In nm (List.map fst (collect_free_vars [] et))).
      { intros Hin; rewrite Forall_forall in Havt;
          pose proof (Havt nm Hin) as Hs; rewrite Hs in Hnin_av; discriminate. }
      pose proof (collect_nonblastable_muls_vars _ _ _ Hins) as Hinc_ms.
      pose proof (collect_nonblastable_muls_vars _ _ _ Hint) as Hinc_mt.
      assert (Hp_ms : wf_param_env_for (collect_free_vars [] ms) penv)
        by (intros x wx Hx; exact (Hps x wx (Hinc_ms (x, wx) Hx))).
      assert (Hp_mt : wf_param_env_for (collect_free_vars [] mt) penv)
        by (intros x wx Hx; exact (Hpt x wx (Hinc_mt (x, wx) Hx))).
      destruct (ub_free_expr_eval_ret ms [] penv [] foracle Hub_ms Hwt_ms wf_let_val_env_nil Hp_ms)
        as [vs [Evs Hwfvs]].
      destruct (ub_free_expr_eval_ret mt [] penv [] foracle Hub_mt Hwt_mt wf_let_val_env_nil Hp_mt)
        as [vt [Evt Hwfvt]].
      rewrite Ebws in Hwfvs; rewrite Ebwt in Hwfvt.
      pose proof (check_expr_refines_sound ctx ms mt penv foracle Href_m Hp_ms Hp_mt Hctx) as Href_v.
      unfold eval_closed_cert_expr in Href_v; rewrite Evs, Evt in Href_v; cbn [refine_eou_dvalue] in Href_v.
      destruct (subst_subexpr_typing_full ms nm w es Hnd Ebws Hnin_es Hwts Hlfs)
        as (Hwt_s' & _ & Hlf_s' & Hinc_s' & Hfa_s').
      destruct (subst_subexpr_typing_full mt nm w et Hnd Ebwt Hnin_et Hwtt Hlft)
        as (Hwt_t' & _ & Hlf_t' & Hinc_t' & _).
      destruct (subst_subexpr_preserves_ub_freeze ms nm w es Hubs Hfrs) as [Hub_s' Hfr_s'].
      assert (Havs' : Forall (fun x => string_in_list x (nm :: avoid) = true)
                        (List.map fst (collect_free_vars [] (subst_subexpr ms (CE_Var nm w) es)))).
      { rewrite Forall_forall; intros x Hx; apply in_map_iff in Hx as [[x0 wx0] [Heqx Hinx]].
        cbn [fst] in Heqx; subst x0; apply Hinc_s' in Hinx; destruct Hinx as [Heqp | Hinx].
        - inversion Heqp; subst; cbn [string_in_list]; rewrite String.eqb_refl; reflexivity.
        - assert (Hinx_f : In x (List.map fst (collect_free_vars [] es)))
            by (apply in_map_iff; exists (x, wx0); auto).
          rewrite Forall_forall in Havs; cbn [string_in_list];
            rewrite (Havs x Hinx_f); destruct (String.eqb _ _); reflexivity. }
      assert (Havt' : Forall (fun x => string_in_list x (nm :: avoid) = true)
                        (List.map fst (collect_free_vars [] (subst_subexpr mt (CE_Var nm w) et)))).
      { rewrite Forall_forall; intros x Hx; apply in_map_iff in Hx as [[x0 wx0] [Heqx Hinx]].
        cbn [fst] in Heqx; subst x0; apply Hinc_t' in Hinx; destruct Hinx as [Heqp | Hinx].
        - inversion Heqp; subst; cbn [string_in_list]; rewrite String.eqb_refl; reflexivity.
        - assert (Hinx_f : In x (List.map fst (collect_free_vars [] et)))
            by (apply in_map_iff; exists (x, wx0); auto).
          rewrite Forall_forall in Havt; cbn [string_in_list];
            rewrite (Havt x Hinx_f); destruct (String.eqb _ _); reflexivity. }
      assert (Hp_s_vs : wf_param_env_for (collect_free_vars [] (subst_subexpr ms (CE_Var nm w) es))
                          (set_param_env penv nm vs)).
      { intros x wx Hx; apply Hinc_s' in Hx; destruct Hx as [Heq | Hx].
        - inversion Heq; subst; unfold set_param_env;
            rewrite String.eqb_refl; exists vs; split; auto.
        - assert (Hneq : nm <> x) by (intros ->; apply Hnin_es, in_map_iff; exists (x, wx); auto).
          unfold set_param_env; apply String.eqb_neq in Hneq; rewrite Hneq; exact (Hps x wx Hx). }
      assert (Hp_s_vt : wf_param_env_for (collect_free_vars [] (subst_subexpr ms (CE_Var nm w) es))
                          (set_param_env penv nm vt)).
      { intros x wx Hx; apply Hinc_s' in Hx; destruct Hx as [Heq | Hx].
        - inversion Heq; subst; unfold set_param_env;
            rewrite String.eqb_refl; exists vt; split; auto.
        - assert (Hneq : nm <> x) by (intros ->; apply Hnin_es, in_map_iff; exists (x, wx); auto).
          unfold set_param_env; apply String.eqb_neq in Hneq; rewrite Hneq; exact (Hps x wx Hx). }
      assert (Hp_t_vt : wf_param_env_for (collect_free_vars [] (subst_subexpr mt (CE_Var nm w) et))
                          (set_param_env penv nm vt)).
      { intros x wx Hx; apply Hinc_t' in Hx; destruct Hx as [Heq | Hx].
        - inversion Heq; subst; unfold set_param_env;
            rewrite String.eqb_refl; exists vt; split; auto.
        - assert (Hneq : nm <> x) by (intros ->; apply Hnin_et, in_map_iff; exists (x, wx); auto).
          unfold set_param_env; apply String.eqb_neq in Hneq; rewrite Hneq; exact (Hpt x wx Hx). }
      pose proof (ub_ctx_holds_set_fresh penv foracle ctx nm vt Hnin_ctx Hctx) as Hctx'.
      pose proof (IH ctx (nm :: avoid) (S idx)
                    (subst_subexpr ms (CE_Var nm w) es)
                    (subst_subexpr mt (CE_Var nm w) et)
                    es_out et_out opt_pf (set_param_env penv nm vt) foracle
                    Havs' Havt' Hp_s_vt Hp_t_vt Hctx' Habs Hchk) as Hrec.
      pose proof (eval_cert_expr_subst_eq ms nm w vs es penv foracle Hfrs Hnin_es Evs Hwfvs) as Hs_eq.
      pose proof (eval_cert_expr_subst_eq mt nm w vt et penv foracle Hfrt Hnin_et Evt Hwfvt) as Ht_eq.
      pose proof (eval_cert_expr_mono_var (subst_subexpr ms (CE_Var nm w) es)
                    nm w vs vt penv foracle Hwt_s' Hlf_s' Hub_s' Hfr_s'
                    Href_v Hwfvs Hwfvt Hfa_s' Hp_s_vs) as Hmono.
      rewrite <- Hs_eq, <- Ht_eq.
      eapply refine_eou_dvalue_trans; [exact Hmono | exact Hrec].
    + inversion Habs; subst es_out et_out.
      exact (check_expr_refines_with_lrat_sound ctx es et opt_pf penv foracle Hchk Hps Hpt Hctx).
Qed.

(** ** 4. Unified MC Expression Refinement & Verification *)

Definition prepare_mc_expr_pair
  (ctx : ub_ctx) (allowed : list (string * positive)) (e_ir e_mc : cert_expr)
  : cert_expr * cert_expr :=
  let e_ir1 := lower_sdiv_pow2 e_ir in
  let avoid :=
    List.map fst allowed ++
    List.map fst (collect_free_vars [] e_ir1) ++
    List.map fst (collect_free_vars [] e_mc) in
  abstract_shared_muls 4%nat ctx avoid 0%nat e_ir1 e_mc.

Definition check_blast_pair_diag
  (phase : string) (ctx : ub_ctx) (s t : cert_expr) (opt_pf : option (list lrat_step))
  : string + unit :=
  let sz := cert_expr_bit_width s in
  let known_vars := collect_free_vars [] s ++ collect_free_vars [] t in
  let env0 := blast_ub_ctx ctx known_vars ctx (mk_blast_env (init_blast_state 2%positive) [] []) in
  let ms_s := if expr_has_freeze s then Some ([], default_let_expand_budget) else None in
  let ms_t := if expr_has_freeze t then Some ([], default_let_expand_budget) else None in
  match blast_cert_expr ctx [] ms_s s env0 with
  | None =>
      inl (diag "mc-refine"
        (phase ++ ": failed to bit-blast source IR expression (width " ++ diag_pos_dec sz ++ ")"))
  | Some (src_r, env1) =>
      match blast_cert_expr ctx [] ms_t t env1 with
      | None =>
          inl (diag "mc-refine"
            (phase ++ ": failed to bit-blast target MC expression (width " ++ diag_pos_dec sz ++ ")"))
      | Some (tgt_r, env2) =>
          let cex := blast_refinement_cex_opt sz lit_true src_r tgt_r (be_st env2) in
          if check_cex_unsat cex opt_pf then inr tt
          else
            match opt_pf with
            | Some pf =>
                inl (diag "lrat-check"
                  (phase ++ ": LRAT proof (" ++ diag_nat_dec (length_tr pf) ++
                   " step(s)) failed to refute bit-blasted MC-to-IR refinement counterexample"))
            | None =>
                inl (diag "mc-refine"
                  (phase ++ ": bounded SAT solver failed to discharge bit-blasted MC-to-IR refinement " ++
                   "obligation (no LRAT proof provided)"))
            end
      end
  end.

Lemma check_blast_pair_diag_sound :
  forall phase ctx s t opt_pf,
    check_blast_pair_diag phase ctx s t opt_pf = inr tt ->
    check_blast_pair ctx s t opt_pf = true.
Proof.
  intros phase ctx s t opt_pf H.
  unfold check_blast_pair_diag in H; unfold check_blast_pair.
  destruct (blast_cert_expr _ [] _ s _) as [[src_r env1] |]; [| discriminate H].
  destruct (blast_cert_expr _ [] _ t _) as [[tgt_r env2] |]; [| discriminate H].
  destruct (check_cex_unsat _ opt_pf); [reflexivity | destruct opt_pf; discriminate H].
Qed.

Definition check_expr_refines_with_lrat_diag
  (ctx : ub_ctx) (src tgt : cert_expr) (opt_pf : option (list lrat_step)) : string + unit :=
  if check_expr_refines ctx src tgt then inr tt
  else
    let ws := cert_expr_bit_width src in
    let wt := cert_expr_bit_width tgt in
    if negb (Pos.eqb ws wt) then
      inl (diag "mc-refine"
        ("bit-width mismatch between IR expression (" ++ diag_pos_dec ws ++
         ") and MC expression (" ++ diag_pos_dec wt ++ ")"))
    else if negb (wt_cert_expr [] src) then
      inl (diag "mc-refine" "source IR expression failed well-typedness check")
    else if negb (wt_cert_expr [] tgt) then
      inl (diag "mc-refine" "target MC expression failed well-typedness check")
    else
      match check_blast_pair_diag "direct" ctx src tgt opt_pf with
      | inr tt => inr tt
      | inl direct_err =>
          if check_wf_let_dag_fast norm_let_expand_budget src &&
             check_wf_let_dag_fast norm_let_expand_budget tgt
          then
            match expand_lets_fueled norm_let_expand_budget src,
                  expand_lets_fueled norm_let_expand_budget tgt with
            | Some es, Some et =>
                let ns := normalize_cert_expr ctx es in
                let nt := normalize_cert_expr ctx et in
                if cert_expr_eqb src ns && cert_expr_eqb tgt nt then inl direct_err
                else check_blast_pair_diag "normalized" ctx ns nt opt_pf
            | _, _ => inl direct_err
            end
          else inl direct_err
      end.

Lemma check_expr_refines_with_lrat_diag_sound :
  forall ctx src tgt opt_pf,
    check_expr_refines_with_lrat_diag ctx src tgt opt_pf = inr tt ->
    check_expr_refines_with_lrat ctx src tgt opt_pf = true.
Proof.
  intros ctx src tgt opt_pf H.
  unfold check_expr_refines_with_lrat_diag in H; cbn zeta in H.
  unfold check_expr_refines_with_lrat; cbn zeta.
  destruct (check_expr_refines ctx src tgt); [reflexivity |].
  destruct (Pos.eqb (cert_expr_bit_width src) (cert_expr_bit_width tgt));
    cbn [negb] in H; [| discriminate H].
  destruct (wt_cert_expr [] src); cbn [negb] in H; [| discriminate H].
  destruct (wt_cert_expr [] tgt); cbn [negb] in H; [| discriminate H].
  change (negb (true && true && true)) with false; cbv iota.
  destruct (check_blast_pair_diag "direct" ctx src tgt opt_pf) as [direct_err | []] eqn:Ebd.
  - destruct (check_blast_pair ctx src tgt opt_pf); [reflexivity |].
    destruct (check_wf_let_dag_fast norm_let_expand_budget src &&
              check_wf_let_dag_fast norm_let_expand_budget tgt); [| discriminate H].
    cbv iota.
    destruct (expand_lets_fueled norm_let_expand_budget src) as [es |]; [| discriminate H].
    destruct (expand_lets_fueled norm_let_expand_budget tgt) as [et |]; [| discriminate H].
    destruct (cert_expr_eqb src (normalize_cert_expr ctx es) &&
              cert_expr_eqb tgt (normalize_cert_expr ctx et)); [discriminate H |].
    cbv iota.
    exact (check_blast_pair_diag_sound _ _ _ _ _ H).
  - rewrite (check_blast_pair_diag_sound _ _ _ _ _ Ebd); reflexivity.
Qed.

Definition check_mc_expr_refines
  (ctx : ub_ctx) (allowed : list (string * positive)) (e_ir e_mc : cert_expr)
  (opt_pf : option (list lrat_step)) : bool :=
  let '(es', et') := prepare_mc_expr_pair ctx allowed e_ir e_mc in
  check_expr_refines_with_lrat ctx es' et' opt_pf.

Definition check_mc_expr_refines_diag
  (ctx : ub_ctx) (allowed : list (string * positive)) (e_ir e_mc : cert_expr)
  (opt_pf : option (list lrat_step)) : string + unit :=
  let '(es', et') := prepare_mc_expr_pair ctx allowed e_ir e_mc in
  check_expr_refines_with_lrat_diag ctx es' et' opt_pf.

Lemma check_mc_expr_refines_diag_sound :
  forall ctx allowed e_ir e_mc opt_pf,
    check_mc_expr_refines_diag ctx allowed e_ir e_mc opt_pf = inr tt ->
    check_mc_expr_refines ctx allowed e_ir e_mc opt_pf = true.
Proof.
  intros ctx allowed e_ir e_mc opt_pf H.
  unfold check_mc_expr_refines_diag in H; unfold check_mc_expr_refines.
  destruct (prepare_mc_expr_pair ctx allowed e_ir e_mc) as [es' et'].
  exact (check_expr_refines_with_lrat_diag_sound _ _ _ _ H).
Qed.

Lemma prepare_mc_expr_pair_sound {Pa : Params} :
  forall ctx allowed e_ir e_mc opt_pf (penv : param_env Pa) foracle,
    wt_cert_expr [] e_ir = true ->
    is_let_free_expr e_ir = true ->
    wf_param_env_for (collect_free_vars [] e_ir) penv ->
    wf_param_env_for (collect_free_vars [] e_mc) penv ->
    ub_ctx_holds penv foracle ctx ->
    check_mc_expr_refines ctx allowed e_ir e_mc opt_pf = true ->
    refine_eou_dvalue
      (eval_closed_cert_expr penv foracle e_ir)
      (eval_closed_cert_expr penv foracle e_mc).
Proof.
  intros ctx allowed e_ir e_mc opt_pf penv foracle Hwt Hlf Hps Hpt Hctx Hchk.
  unfold check_mc_expr_refines, prepare_mc_expr_pair in Hchk.
  set (e_ir1 := lower_sdiv_pow2 e_ir) in *.
  set (avoid := List.map fst allowed ++
                List.map fst (collect_free_vars [] e_ir1) ++
                List.map fst (collect_free_vars [] e_mc)) in *.
  destruct (abstract_shared_muls 4%nat ctx avoid 0%nat e_ir1 e_mc) as [es' et'] eqn:Habs.
  destruct (lower_sdiv_pow2_typing e_ir Hwt Hlf) as (_ & _ & _ & Hinc1).
  assert (Hp1 : wf_param_env_for (collect_free_vars [] e_ir1) penv)
    by (intros x wx Hx; exact (Hps x wx (Hinc1 (x, wx) Hx))).
  assert (Havs : Forall (fun x => string_in_list x avoid = true) (List.map fst (collect_free_vars [] e_ir1))).
  { rewrite Forall_forall; intros x Hx; apply string_in_list_spec; unfold avoid.
    apply in_app_iff; right; apply in_app_iff; left; exact Hx. }
  assert (Havt : Forall (fun x => string_in_list x avoid = true) (List.map fst (collect_free_vars [] e_mc))).
  { rewrite Forall_forall; intros x Hx; apply string_in_list_spec; unfold avoid.
    apply in_app_iff; right; apply in_app_iff; right; exact Hx. }
  pose proof (abstract_shared_muls_sound 4%nat ctx avoid 0%nat e_ir1 e_mc es' et' opt_pf penv foracle
                Havs Havt Hp1 Hpt Hctx Habs Hchk) as Href1.
  pose proof (lower_sdiv_pow2_sound e_ir penv foracle Hwt Hlf) as Heq1.
  fold e_ir1 in Heq1.
  destruct (eval_closed_cert_expr penv foracle e_ir) as [s | s | s | v_ir],
           (eval_closed_cert_expr penv foracle e_ir1) as [s1 | s1 | s1 | v_ir1];
    cbn in Heq1, Href1 |- *; try contradiction Heq1; subst; try exact Href1.
Qed.

