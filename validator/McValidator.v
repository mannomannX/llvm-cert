(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified ELF64-to-IR Backend Translation Validator ([CertValidator.McValidator])

    Implements for Milestone M1 of Phase [8.3a]:
    1. Pure MC DAG flattening ([flatten_mc_dag_to_expr]) reducing [Rv64Sem]'s
       symbolic execution tree into a single total, UB-free [CE_Select] term.
    2. Verified power-of-2 signed-division lowering ([lower_sdiv_pow2], exact
       semantic equivalence [lower_sdiv_pow2_sound]) matching LLVM's
       [srai; srli; add; srai] strength reduction across all bitwidths [w >= 3].
    3. Verified congruence-closure / uninterpreted-multiplier abstraction
       ([abstract_shared_muls], [abstract_shared_muls_sound]) discharging shared
       wide multiplications without 64x64 bit-blasting.
    4. Strict IR-to-MC prototype, LP64 [signext]/[zeroext] ABI, syntax, and
       relocation gates integrated into [validate_mc_tle_with_cert_str], backed
       by [validate_mc_tle_with_cert_str_sound] ([0 Admitted], zero custom axioms).
    5. Diagnostic DIMACS CNF emitter ([emit_mc_dimacs_cnf_str]) blasting the
       exact normalized/abstracted pair for offline LRAT proof generation. *)

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

From CertValidator Require Import
  AigLrat
  CertFormat
  AlgRules
  CertValidator
  Elf64Spec
  Rv64Sem
  A64CoreSem
  McFormat.

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
  : option cert_expr :=
  match d with
  | CD_RetScalar w e =>
      if Pos.eqb w ret_w && ub_free_expr e then Some e else None
  | CD_Branch cond dt df =>
      match flatten_mc_dag_to_expr ret_w dt, flatten_mc_dag_to_expr ret_w df with
      | Some et, Some ef =>
          if ub_free_expr cond && ub_free_expr et && ub_free_expr ef
          then Some (CE_Select ret_w cond et ef)
          else None
      | _, _ => None
      end
  | _ => None
  end.

Lemma flatten_mc_dag_to_expr_typing :
  forall allowed ret_w d e,
    wf_cfg_dag allowed d = true ->
    flatten_mc_dag_to_expr ret_w d = Some e ->
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
  - destruct (Pos.eqb w' ret_w && ub_free_expr ret_e) eqn:Eok; [| discriminate Hf].
    apply andb_true_iff in Eok as [Ebw Eub].
    apply Pos.eqb_eq in Ebw; subst w'.
    inversion Hf; subst e; clear Hf.
    rewrite !andb_true_iff in Hwf; destruct Hwf as (((Hwt & Hbw) & Hlf) & Hfv).
    apply Pos.eqb_eq in Hbw.
    repeat split; try assumption; exact (vars_subset_b_incl _ _ Hfv).
  - destruct (flatten_mc_dag_to_expr ret_w dt) as [et |] eqn:Ert; [| discriminate Hf].
    destruct (flatten_mc_dag_to_expr ret_w df) as [ef |] eqn:Erf; [| discriminate Hf].
    destruct (ub_free_expr cond && ub_free_expr et && ub_free_expr ef) eqn:Eub;
      [| discriminate Hf].
    rewrite !andb_true_iff in Eub; destruct Eub as ([Hubc Hubt] & Hubf).
    inversion Hf; subst e; clear Hf.
    rewrite !andb_true_iff in Hwf.
    destruct Hwf as (((((Hwtc & Hbwc) & Hlfc) & Hfvc) & Hwft) & Hwff).
    destruct (IHt et Hwft eq_refl) as (Hwtt & Hbwt & Hlft & _ & Hfvt).
    destruct (IHf ef Hwff eq_refl) as (Hwtf & Hbwf & Hlff & _ & Hfvf).
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
    flatten_mc_dag_to_expr ret_w d = Some e ->
    eval_cfg_dag penv foracle d = DO_Ret dv ->
    eval_closed_cert_expr penv foracle e = raise_ret dv.
Proof.
  intros allowed ret_w d.
  induction d as [| | w' ret_e | ws step_e next IH | uas next IH | cond dt IHt df IHf];
    intros e penv foracle dv Hwf Hpenv Hf Hevd;
    cbn [wf_cfg_dag flatten_mc_dag_to_expr eval_cfg_dag] in Hwf, Hf, Hevd;
    try discriminate Hf; try discriminate Hevd.
  - destruct (Pos.eqb w' ret_w && ub_free_expr ret_e); [| discriminate Hf].
    inversion Hf; subst e; clear Hf.
    destruct (eval_closed_cert_expr penv foracle ret_e) as [| | | dv0]; try discriminate Hevd.
    inversion Hevd; subst dv0; reflexivity.
  - rewrite !andb_true_iff in Hwf; destruct Hwf as (((((_ & _) & _) & _) & Hwft) & Hwff).
    destruct (flatten_mc_dag_to_expr ret_w dt) as [et |] eqn:Ert; [| discriminate Hf].
    destruct (flatten_mc_dag_to_expr ret_w df) as [ef |] eqn:Erf; [| discriminate Hf].
    destruct (ub_free_expr cond && ub_free_expr et && ub_free_expr ef) eqn:Eub;
      [| discriminate Hf].
    rewrite !andb_true_iff in Eub; destruct Eub as ([_ Hubt] & Hubf).
    inversion Hf; subst e; clear Hf.
    destruct (eval_closed_cert_expr penv foracle cond) as [| | | dvc] eqn:Ec;
      try discriminate Hevd.
    destruct dvc as [dbc | |]; try discriminate Hevd.
    destruct dbc as [| wc cbit | | | | | |]; try discriminate Hevd.
    destruct wc as [| |]; try discriminate Hevd.
    destruct (flatten_mc_dag_to_expr_typing allowed ret_w dt et Hwft Ert)
      as (Hwtt & _ & _ & _ & Hfvt).
    destruct (flatten_mc_dag_to_expr_typing allowed ret_w df ef Hwff Erf)
      as (Hwtf & _ & _ & _ & Hfvf).
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
      replace (@Integers.signed w x) with (2 ^ (Z.pos w - 1) * (-1) + (@Integers.signed w x + 2 ^ (Z.pos w - 1)))%Z by lia.
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
      by (replace (Z.of_N (N.pos w - 1)) with (Z.pos w - 1)%Z by lia; apply @Integers.unsigned_repr; unfold Integers.max_unsigned; rewrite Hmod; lia).
    assert (Hwmk_u : @Integers.unsigned w (@Integers.repr w (Z.of_N (N.pos w - kN))) = (Z.pos w - Z.of_N kN)%Z)
      by (replace (Z.of_N (N.pos w - kN)) with (Z.pos w - Z.of_N kN)%Z by lia; apply @Integers.unsigned_repr; unfold Integers.max_unsigned; rewrite Hmod; lia).
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
      rewrite (eval_iop_no_flags_poison_any CB_AShr w) by (first [reflexivity | left; reflexivity | right; eexists; reflexivity]).
      cbn [eou_bind].
      rewrite (eval_iop_no_flags_poison_any CB_LShr w) by (first [reflexivity | left; reflexivity | right; eexists; reflexivity]).
      cbn [eou_bind].
      rewrite (eval_iop_no_flags_poison_any CB_Add w) by (first [reflexivity | left; reflexivity | right; eexists; reflexivity]).
      cbn [eou_bind].
      rewrite (eval_iop_no_flags_poison_any CB_AShr w) by (first [reflexivity | left; reflexivity | right; eexists; reflexivity]).
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
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf; destruct Hwt as (((Hwtl & Hwtr) & _) & _); destruct Hlf as [Hlfl Hlfr].
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

Fixpoint collect_nonblastable_muls (e : cert_expr) {struct e}
  : list (positive * cert_expr) :=
  let here := if is_nonblastable_mul e then [(cert_expr_bit_width e, e)] else [] in
  here ++
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ | CE_Let _ _ => []
  | CE_BinOp _ _ _ l r | CE_ICmp _ _ _ l r =>
      collect_nonblastable_muls l ++ collect_nonblastable_muls r
  | CE_Cast _ _ _ _ o | CE_Freeze _ o => collect_nonblastable_muls o
  | CE_Select _ c t f =>
      collect_nonblastable_muls c ++
      collect_nonblastable_muls t ++
      collect_nonblastable_muls f
  end.

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
      rewrite Hnd; repeat split; try reflexivity; [intros x [Hx | []]; left; exact Hx | constructor; auto].
    + cbn [cert_expr_bit_width]; repeat split; try assumption; [intros x Hx; right; exact Hx | constructor].
  - destruct (cert_expr_eqb (CE_Poison w0) target) eqn:Heq.
    + apply cert_expr_eqb_eq in Heq; subst target; rewrite Htw.
      cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars lookup_let_width].
      rewrite Hnd; repeat split; try reflexivity; [intros x [Hx | []]; left; exact Hx | constructor; auto].
    + cbn [cert_expr_bit_width]; repeat split; try assumption; [intros x Hx; right; exact Hx | constructor].
  - destruct (cert_expr_eqb (CE_Var nm0 w0) target) eqn:Heq.
    + apply cert_expr_eqb_eq in Heq; subst target; rewrite Htw.
      cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars lookup_let_width].
      rewrite Hnd; repeat split; try reflexivity; [intros x [Hx | []]; left; exact Hx | constructor; auto].
    + cbn [cert_expr_bit_width]; repeat split; try assumption; [intros x Hx; right; exact Hx |].
      cbn [collect_free_vars string_in_list List.map] in Hni |- *; constructor; [intros ->; exfalso; apply Hni; left; reflexivity | constructor].
  - destruct (cert_expr_eqb (CE_BinOp op w0 fl l r) target) eqn:Heq.
    + apply cert_expr_eqb_eq in Heq; subst target; rewrite Htw.
      cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars lookup_let_width].
      rewrite Hnd; repeat split; try reflexivity; [intros x [Hx | []]; left; exact Hx | constructor; auto].
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
        -- destruct (Hfv_l x Hx) as [-> | Hx']; [left; reflexivity | right; apply in_app_iff; left; exact Hx'].
        -- destruct (Hfv_r x Hx) as [-> | Hx']; [left; reflexivity | right; apply in_app_iff; right; exact Hx'].
      * apply Forall_app; split; assumption.
  - destruct (cert_expr_eqb (CE_ICmp pr ss w0 l r) target) eqn:Heq.
    + apply cert_expr_eqb_eq in Heq; subst target; rewrite Htw.
      cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars lookup_let_width].
      rewrite Hnd; repeat split; try reflexivity; [intros x [Hx | []]; left; exact Hx | constructor; auto].
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
        -- destruct (Hfv_l x Hx) as [-> | Hx']; [left; reflexivity | right; apply in_app_iff; left; exact Hx'].
        -- destruct (Hfv_r x Hx) as [-> | Hx']; [left; reflexivity | right; apply in_app_iff; right; exact Hx'].
      * apply Forall_app; split; assumption.
  - destruct (cert_expr_eqb (CE_Cast k fw tw fl o) target) eqn:Heq.
    + apply cert_expr_eqb_eq in Heq; subst target; rewrite Htw.
      cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars lookup_let_width].
      rewrite Hnd; repeat split; try reflexivity; [intros x [Hx | []]; left; exact Hx | constructor; auto].
    + cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars] in Hni, Hwt, Hlf |- *.
      rewrite !andb_true_iff in Hwt; destruct Hwt as ((Hk & Hwto) & Hwo).
      destruct (IHo Hni Hwto Hlf) as (Hwt_o & Hbw_o & Hlf_o & Hfv_o & Hfa_o).
      rewrite Hk, Hwt_o, Hbw_o, Hwo, Hlf_o; repeat split; try reflexivity; assumption.
  - destruct (cert_expr_eqb (CE_Select w0 c t f) target) eqn:Heq.
    + apply cert_expr_eqb_eq in Heq; subst target; rewrite Htw.
      cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars lookup_let_width].
      rewrite Hnd; repeat split; try reflexivity; [intros x [Hx | []]; left; exact Hx | constructor; auto].
    + cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars] in Hni, Hwt, Hlf |- *.
      rewrite !map_app in Hni.
      rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
      destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hwc) & Hwt0) & Hwf0);
        destruct Hlf as ([Hlfc Hlft] & Hlff).
      destruct (IHc (fun H => Hni (proj2 (in_app_iff _ _ _) (or_introl H))) Hwtc Hlfc)
        as (Hwt_c & Hbw_c & Hlf_c & Hfv_c & Hfa_c).
      destruct (IHt (fun H => Hni (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl H))))) Hwtt Hlft)
        as (Hwt_t & Hbw_t & Hlf_t & Hfv_t & Hfa_t).
      destruct (IHf (fun H => Hni (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_intror H))))) Hwtf Hlff)
        as (Hwt_f & Hbw_f & Hlf_f & Hfv_f & Hfa_f).
      rewrite Hwt_c, Hwt_t, Hwt_f, Hbw_c, Hbw_t, Hbw_f, Hwc, Hwt0, Hwf0, Hlf_c, Hlf_t, Hlf_f.
      repeat split; try reflexivity.
      * intros x Hx; apply in_app_iff in Hx as [Hx | Hx].
        -- destruct (Hfv_c x Hx) as [-> | Hx']; [left; reflexivity | right; apply in_app_iff; left; exact Hx'].
        -- apply in_app_iff in Hx as [Hx | Hx].
           ++ destruct (Hfv_t x Hx) as [-> | Hx']; [left; reflexivity | right; apply in_app_iff; right; apply in_app_iff; left; exact Hx'].
           ++ destruct (Hfv_f x Hx) as [-> | Hx']; [left; reflexivity | right; apply in_app_iff; right; apply in_app_iff; right; exact Hx'].
      * apply Forall_app; split; [exact Hfa_c | apply Forall_app; split; assumption].
  - destruct (cert_expr_eqb (CE_Freeze w0 o) target) eqn:Heq.
    + apply cert_expr_eqb_eq in Heq; subst target; rewrite Htw.
      cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars lookup_let_width].
      rewrite Hnd; repeat split; try reflexivity; [intros x [Hx | []]; left; exact Hx | constructor; auto].
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
    apply String.eqb_eq in Eeq; subst nm0; exfalso; apply Hni; left; reflexivity.
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
    apply String.eqb_eq in Eeq; subst nm0; exfalso; apply Hni; left; reflexivity.
  - cbn [freeze_free_expr collect_free_vars] in Hfr, Hni; apply andb_true_iff in Hfr as [Hfl Hfr]; rewrite map_app in Hni.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    rewrite (IHl Hfl (fun H => Hni (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHr Hfr (fun H => Hni (proj2 (in_app_iff _ _ _) (or_intror H)))).
    reflexivity.
  - cbn [freeze_free_expr collect_free_vars] in Hfr, Hni; apply andb_true_iff in Hfr as [Hfl Hfr]; rewrite map_app in Hni.
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
      - apply String.eqb_eq in Enm; subst x; rewrite Forall_forall in Hfal; rewrite (Hfal (nm, wx) Hx eq_refl); exists vt; split; auto.
      - destruct (Hpl x wx Hx) as [dv [Hdv Hwfdv]]; unfold set_param_env in Hdv; rewrite Enm in Hdv; exists dv; split; assumption. }
    assert (Hpr_t : wf_param_env_for (collect_free_vars [] r) (set_param_env penv nm vt)).
    { intros x wx Hx; unfold set_param_env; destruct (String.eqb nm x) eqn:Enm.
      - apply String.eqb_eq in Enm; subst x; rewrite Forall_forall in Hfar; rewrite (Hfar (nm, wx) Hx eq_refl); exists vt; split; auto.
      - destruct (Hpr x wx Hx) as [dv [Hdv Hwfdv]]; unfold set_param_env in Hdv; rewrite Enm in Hdv; exists dv; split; assumption. }
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
      - apply String.eqb_eq in Enm; subst x; rewrite Forall_forall in Hfa; rewrite (Hfa (nm, wx) Hx eq_refl); exists vt; split; auto.
      - destruct (Hpenv x wx Hx) as [dv [Hdv Hwfdv]]; unfold set_param_env in Hdv; rewrite Enm in Hdv; exists dv; split; assumption. }
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
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; left; exact Hx).
    assert (Hpf : wf_param_env_for (collect_free_vars [] f) (set_param_env penv nm vs))
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; right; exact Hx).
    assert (Hpc_t : wf_param_env_for (collect_free_vars [] c) (set_param_env penv nm vt)).
    { intros x wx Hx; unfold set_param_env; destruct (String.eqb nm x) eqn:Enm.
      - apply String.eqb_eq in Enm; subst x; rewrite Forall_forall in Hfac; rewrite (Hfac (nm, wx) Hx eq_refl); exists vt; split; auto.
      - destruct (Hpc x wx Hx) as [dv [Hdv Hwfdv]]; unfold set_param_env in Hdv; rewrite Enm in Hdv; exists dv; split; assumption. }
    assert (Hpt_t : wf_param_env_for (collect_free_vars [] t) (set_param_env penv nm vt)).
    { intros x wx Hx; unfold set_param_env; destruct (String.eqb nm x) eqn:Enm.
      - apply String.eqb_eq in Enm; subst x; rewrite Forall_forall in Hfat; rewrite (Hfat (nm, wx) Hx eq_refl); exists vt; split; auto.
      - destruct (Hpt x wx Hx) as [dv [Hdv Hwfdv]]; unfold set_param_env in Hdv; rewrite Enm in Hdv; exists dv; split; assumption. }
    assert (Hpf_t : wf_param_env_for (collect_free_vars [] f) (set_param_env penv nm vt)).
    { intros x wx Hx; unfold set_param_env; destruct (String.eqb nm x) eqn:Enm.
      - apply String.eqb_eq in Enm; subst x; rewrite Forall_forall in Hfaf; rewrite (Hfaf (nm, wx) Hx eq_refl); exists vt; split; auto.
      - destruct (Hpf x wx Hx) as [dv [Hdv Hwfdv]]; unfold set_param_env in Hdv; rewrite Enm in Hdv; exists dv; split; assumption. }
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
      [| exact Hlfl | intros Hin; assert (Hin' : In nm (List.map fst (collect_free_vars [] (expand_lets lhs) ++ collect_free_vars [] (expand_lets rhs)))) by (rewrite map_app; apply in_app_iff; left; exact Hin); apply string_in_list_spec in Hin'; congruence].
    rewrite eval_cert_expr_set_unused_lf in Hr;
      [| exact Hlfr | intros Hin; assert (Hin' : In nm (List.map fst (collect_free_vars [] (expand_lets lhs) ++ collect_free_vars [] (expand_lets rhs)))) by (rewrite map_app; apply in_app_iff; right; exact Hin); apply string_in_list_spec in Hin'; congruence].
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
  clearbody fuel cand; revert cand H; induction fuel as [| fuel' IH]; intros cand H; cbn in H; [discriminate H |].
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

Lemma collect_nonblastable_muls_vars :
  forall e w m,
    In (w, m) (collect_nonblastable_muls e) ->
    incl (collect_free_vars [] m) (collect_free_vars [] e).
Proof.
  intros e w m.
  induction e as
    [ w0 val0 | w0 | nm0 w0
    | op w0 fl l IHl r IHr
    | pr ss w0 l IHl r IHr
    | k fw tw fl o IHo
    | w0 c IHc t IHt f IHf
    | w0 o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hin; cbn [collect_nonblastable_muls] in Hin;
    destruct (is_nonblastable_mul _) eqn:Em; cbn [app] in Hin;
    try (destruct Hin as [Heq | Hin]; [inversion Heq; subst m; apply incl_refl |]);
    try contradiction Hin.
  - apply in_app_iff in Hin as [Hl | Hr]; cbn [collect_free_vars];
      [intros x Hx; apply in_app_iff; left; exact (IHl Hl x Hx)
      | intros x Hx; apply in_app_iff; right; exact (IHr Hr x Hx)].
  - apply in_app_iff in Hin as [Hl | Hr]; cbn [collect_free_vars];
      [intros x Hx; apply in_app_iff; left; exact (IHl Hl x Hx)
      | intros x Hx; apply in_app_iff; right; exact (IHr Hr x Hx)].
  - apply in_app_iff in Hin as [Hl | Hr]; cbn [collect_free_vars];
      [intros x Hx; apply in_app_iff; left; exact (IHl Hl x Hx)
      | intros x Hx; apply in_app_iff; right; exact (IHr Hr x Hx)].
  - apply in_app_iff in Hin as [Hl | Hr]; cbn [collect_free_vars];
      [intros x Hx; apply in_app_iff; left; exact (IHl Hl x Hx)
      | intros x Hx; apply in_app_iff; right; exact (IHr Hr x Hx)].
  - exact (IHo Hin).
  - exact (IHo Hin).
  - apply in_app_iff in Hin as [Hc | Htf]; cbn [collect_free_vars];
      [intros x Hx; apply in_app_iff; left; exact (IHc Hc x Hx) |].
    apply in_app_iff in Htf as [Ht | Hf]; intros x Hx; apply in_app_iff; right; apply in_app_iff;
      [left; exact (IHt Ht x Hx) | right; exact (IHf Hf x Hx)].
  - apply in_app_iff in Hin as [Hc | Htf]; cbn [collect_free_vars];
      [intros x Hx; apply in_app_iff; left; exact (IHc Hc x Hx) |].
    apply in_app_iff in Htf as [Ht | Hf]; intros x Hx; apply in_app_iff; right; apply in_app_iff;
      [left; exact (IHt Ht x Hx) | right; exact (IHf Hf x Hx)].
  - exact (IHo Hin).
  - exact (IHo Hin).
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
  - intros H; destruct (IH H) as (Hin & ? & ? & ? & ?); repeat split; try assumption; right; exact Hin.
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
    + intros H; destruct (IH H) as (Hins & ? & ? & ? & ? & ? & ? & ? & ?); repeat split; try assumption; right; exact Hins.
  - intros H; destruct (IH H) as (Hins & ? & ? & ? & ? & ? & ? & ? & ?); repeat split; try assumption; right; exact Hins.
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
      { intros Hin; rewrite Forall_forall in Havs; pose proof (Havs nm Hin) as Hs; rewrite Hs in Hnin_av; discriminate. }
      assert (Hnin_et : ~ In nm (List.map fst (collect_free_vars [] et))).
      { intros Hin; rewrite Forall_forall in Havt; pose proof (Havt nm Hin) as Hs; rewrite Hs in Hnin_av; discriminate. }
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
          rewrite Forall_forall in Havs; cbn [string_in_list]; rewrite (Havs x Hinx_f); destruct (String.eqb _ _); reflexivity. }
      assert (Havt' : Forall (fun x => string_in_list x (nm :: avoid) = true)
                        (List.map fst (collect_free_vars [] (subst_subexpr mt (CE_Var nm w) et)))).
      { rewrite Forall_forall; intros x Hx; apply in_map_iff in Hx as [[x0 wx0] [Heqx Hinx]].
        cbn [fst] in Heqx; subst x0; apply Hinc_t' in Hinx; destruct Hinx as [Heqp | Hinx].
        - inversion Heqp; subst; cbn [string_in_list]; rewrite String.eqb_refl; reflexivity.
        - assert (Hinx_f : In x (List.map fst (collect_free_vars [] et)))
            by (apply in_map_iff; exists (x, wx0); auto).
          rewrite Forall_forall in Havt; cbn [string_in_list]; rewrite (Havt x Hinx_f); destruct (String.eqb _ _); reflexivity. }
      assert (Hp_s_vs : wf_param_env_for (collect_free_vars [] (subst_subexpr ms (CE_Var nm w) es))
                          (set_param_env penv nm vs)).
      { intros x wx Hx; apply Hinc_s' in Hx; destruct Hx as [Heq | Hx].
        - inversion Heq; subst; unfold set_param_env; rewrite String.eqb_refl; exists vs; split; auto.
        - assert (Hneq : nm <> x) by (intros ->; apply Hnin_es, in_map_iff; exists (x, wx); auto).
          unfold set_param_env; apply String.eqb_neq in Hneq; rewrite Hneq; exact (Hps x wx Hx). }
      assert (Hp_s_vt : wf_param_env_for (collect_free_vars [] (subst_subexpr ms (CE_Var nm w) es))
                          (set_param_env penv nm vt)).
      { intros x wx Hx; apply Hinc_s' in Hx; destruct Hx as [Heq | Hx].
        - inversion Heq; subst; unfold set_param_env; rewrite String.eqb_refl; exists vt; split; auto.
        - assert (Hneq : nm <> x) by (intros ->; apply Hnin_es, in_map_iff; exists (x, wx); auto).
          unfold set_param_env; apply String.eqb_neq in Hneq; rewrite Hneq; exact (Hps x wx Hx). }
      assert (Hp_t_vt : wf_param_env_for (collect_free_vars [] (subst_subexpr mt (CE_Var nm w) et))
                          (set_param_env penv nm vt)).
      { intros x wx Hx; apply Hinc_t' in Hx; destruct Hx as [Heq | Hx].
        - inversion Heq; subst; unfold set_param_env; rewrite String.eqb_refl; exists vt; split; auto.
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

Definition check_mc_expr_refines
  (ctx : ub_ctx) (allowed : list (string * positive)) (e_ir e_mc : cert_expr)
  (opt_pf : option (list lrat_step)) : bool :=
  let '(es', et') := prepare_mc_expr_pair ctx allowed e_ir e_mc in
  check_expr_refines_with_lrat ctx es' et' opt_pf.

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

(** ** 5. IR Prototype, ABI Extension, Syntax Gates & End-to-End Validator *)

Definition attr_is_signext (a : param_attr) : bool :=
  match a with
  | PARAMATTR_Signext => true
  | _ => false
  end.

Definition attr_is_zeroext (a : param_attr) : bool :=
  match a with
  | PARAMATTR_Zeroext => true
  | _ => false
  end.

Definition check_one_mc_arg
  (arch : elf_arch) (pnm : string) (dt : dtyp) (attrs : list param_attr) (sp : rv_arg_spec) : bool :=
  String.eqb (ras_name sp) pnm &&
  rv_valid_arg_spec sp &&
  dtyp_eqb dt (DTYPE_Base (DTYPE_I (ras_width sp))) &&
  match arch with
  | EA_Riscv64 =>
      if Pos.eqb (ras_width sp) 64%positive then
        match ras_ext sp with
        | RAE_None => true
        | _ => false
        end
      else
        match ras_ext sp with
        | RAE_SignExt => existsb attr_is_signext attrs
        | RAE_ZeroExt => existsb attr_is_zeroext attrs
        | RAE_None => false
        end
  | EA_AArch64 =>
      if Pos.eqb (ras_width sp) 64%positive then
        match ras_ext sp with
        | RAE_None => true
        | _ => false
        end
      else if Pos.eqb (ras_width sp) 32%positive then
        match ras_ext sp with
        | RAE_None => true
        | _ => false
        end
      else
        match ras_ext sp with
        | RAE_SignExt => existsb attr_is_signext attrs
        | RAE_ZeroExt => existsb attr_is_zeroext attrs
        | RAE_None => true
        end
  end.

Fixpoint check_mc_arg_specs
  (arch : elf_arch) (pnms : list string) (dts : list dtyp) (pattrs : list (list param_attr))
  (specs : list rv_arg_spec) {struct pnms} : bool :=
  match pnms, dts, pattrs, specs with
  | [], [], [], [] => true
  | p :: rp, d :: rd, a :: ra, s :: rs =>
      check_one_mc_arg arch p d a s && check_mc_arg_specs arch rp rd ra rs
  | _, _, _, _ => false
  end.

Lemma check_mc_arg_specs_len : forall arch pnms dts pattrs specs,
  check_mc_arg_specs arch pnms dts pattrs specs = true ->
  List.length pnms = List.length dts /\
  List.length dts = List.length pattrs /\
  List.length pattrs = List.length specs.
Proof.
  intros arch; induction pnms as [| p rp IH]; intros [| d rd] [| a ra] [| s rs] H;
    cbn in H; try discriminate H; [repeat split |].
  apply andb_true_iff in H as [_ Hr].
  destruct (IH _ _ _ Hr) as (H1 & H2 & H3); repeat split; cbn; lia.
Qed.

Lemma check_mc_arg_specs_nth : forall arch pnms dts pattrs specs idx p d a s,
  check_mc_arg_specs arch pnms dts pattrs specs = true ->
  nth_error pnms idx = Some p ->
  nth_error dts idx = Some d ->
  nth_error pattrs idx = Some a ->
  nth_error specs idx = Some s ->
  check_one_mc_arg arch p d a s = true.
Proof.
  intros arch; induction pnms as [| p0 rp IH]; intros [| d0 rd] [| a0 ra] [| s0 rs] [| idx'] p d a s H Hp Hd Ha Hs;
    cbn in H, Hp, Hd, Ha, Hs; try discriminate;
    apply andb_true_iff in H as [H1 Hr].
  - inversion Hp; inversion Hd; inversion Ha; inversion Hs; subst; exact H1.
  - exact (IH _ _ _ _ _ _ _ _ Hr Hp Hd Ha Hs).
Qed.

Lemma check_one_mc_arg_inv : forall arch pnm dt attrs sp,
  check_one_mc_arg arch pnm dt attrs sp = true ->
  ras_name sp = pnm /\
  rv_valid_arg_spec sp = true /\
  dt = DTYPE_Base (DTYPE_I (ras_width sp)).
Proof.
  intros arch pnm dt attrs sp H; unfold check_one_mc_arg in H.
  rewrite !andb_true_iff in H; destruct H as (((Hn & Hv) & Hdt) & _).
  apply String.eqb_eq in Hn.
  unfold dtyp_eqb in Hdt; destruct (dtyp_eq_dec dt (DTYPE_Base (DTYPE_I (ras_width sp))));
    [| discriminate Hdt].
  repeat split; assumption.
Qed.

Lemma check_mc_arg_specs_names : forall arch pnms dts pattrs specs,
  check_mc_arg_specs arch pnms dts pattrs specs = true ->
  List.map ras_name specs = pnms.
Proof.
  intros arch; induction pnms as [| p rp IH]; intros [| d rd] [| a ra] [| s rs] H;
    cbn in H; try discriminate H; [reflexivity |].
  apply andb_true_iff in H as [H1 Hr].
  destruct (check_one_mc_arg_inv _ _ _ _ _ H1) as [Hnm _].
  cbn; rewrite Hnm, (IH _ _ _ Hr); reflexivity.
Qed.

Definition check_mc_ir_syntax_gates (G : CFG.cfg dtyp) : bool :=
  cfg_no_fast_math G &&
  cfg_no_concurrency G &&
  cfg_supported_abi G &&
  cfg_intrinsics_allowlisted G &&
  cfg_no_vaarg G &&
  cfg_no_exceptions G &&
  list_empty_b (cfg_alloca_slot_names G) &&
  bmap_varargs_irrel (ocfg_map (blks G)).

Definition check_mc_ir_proto_contract
  (tenv : list (ident * typ)) (defn : definition typ (CFG.cfg typ)) (mcert : mc_certificate)
  : bool :=
  let proto := df_prototype defn in
  let ir_cfg := convert_typ tenv (df_instrs defn) in
  let ir_pnames := List.map cert_reg_name (args ir_cfg) in
  let '(s_rattrs, s_pattrs) := dc_param_attrs proto in
  cert_fn_matches_raw_id (mc_fn_name mcert) (dc_name proto) &&
  match dc_type proto with
  | TYPE_Function ret_ty arg_tys false =>
      let arg_dtys := List.map (typ_to_dtyp tenv) arg_tys in
      dtyp_eqb (typ_to_dtyp tenv ret_ty) (DTYPE_Base (DTYPE_I (mc_ret_width mcert))) &&
      rv_supported_arg_width (mc_ret_width mcert) &&
      forallb decl_ann_supported (dc_annotations proto) &&
      forallb (fun a => negb (is_unmodeled_fn_attr a))
              (dc_attrs proto ++ ann_fun_attributes (dc_annotations proto)) &&
      forallb (fun a => negb (is_unmodeled_param_attr a)) s_rattrs &&
      forallb (forallb (fun a => negb (is_unmodeled_param_attr a))) s_pattrs &&
      forallb2 attr_preserves_dtyp_b arg_dtys s_pattrs &&
      forallb2 raw_id_eqb (df_args defn) (args ir_cfg) &&
      no_dup_raw_ids (args ir_cfg) &&
      no_dup_strings ir_pnames &&
      check_mc_arg_specs (mc_arch mcert) ir_pnames arg_dtys s_pattrs (mc_args mcert) &&
      match mc_arch mcert with
      | EA_Riscv64 => true
      | EA_AArch64 =>
          forallb (fun sp => negb (existsb (String.eqb (a64_hi_var_name (ras_name sp))) ir_pnames))
                  (mc_args mcert)
      end &&
      cfg_param_dtyp_compatible ir_cfg arg_dtys &&
      check_mc_ir_syntax_gates ir_cfg
  | _ => false
  end.

Definition mc_build_init_ctx
  (arch : elf_arch) (ir_pnames : list string) (arg_dtys : list dtyp)
  (s_pattrs : list (list param_attr)) (specs : list rv_arg_spec)
  : list (string * positive) * ub_ctx :=
  let '(proto_vars, proto_ctx) := seed_proto_param_ctx ir_pnames arg_dtys s_pattrs in
  let arg_vars := List.map (fun sp => (ras_name sp, ras_width sp)) specs in
  let extra_vars :=
    match arch with
    | EA_Riscv64 => []
    | EA_AArch64 => a64_hi_vars specs
    end in
  let mc_ctx := List.map (fun sp => UBA_ParamNoUndef (ras_name sp) (ras_width sp)) specs in
  let extra_ctx :=
    match arch with
    | EA_Riscv64 => []
    | EA_AArch64 => List.map (fun nv => UBA_ParamNoUndef (fst nv) (snd nv)) (a64_hi_vars specs)
    end in
  (proto_vars ++ arg_vars ++ extra_vars, proto_ctx ++ mc_ctx ++ extra_ctx).

Definition mc_decode_and_summarize
  (arch : elf_arch) (rvc : bool) (bytes : list N)
  (arg_specs : list rv_arg_spec) (ret_w : positive) : string + cfg_dag :=
  match arch with
  | EA_Riscv64 =>
      match decode_rv64_bytes rvc bytes with
      | inl err => inl err
      | inr insts =>
          let rv_fuel := S (2 * List.length insts) in
          match summarize_rv64_dag rv_fuel insts arg_specs ret_w with
          | None => inl "RV64 machine-code symbolic summarization failed"
          | Some d_mc => inr d_mc
          end
      end
  | EA_AArch64 =>
      if rvc then inl "compressed mode not supported for AArch64"
      else
        match decode_a64_bytes bytes with
        | inl err => inl err
        | inr insts =>
            let a64_fuel := S (2 * List.length insts) in
            match summarize_a64_dag a64_fuel insts arg_specs ret_w with
            | None => inl "AArch64 machine-code symbolic summarization failed"
            | Some d_mc => inr d_mc
            end
        end
  end.

Definition validate_mc_mcfg_with_cert
  (ir_m : CFG.mcfg typ) (raw_elf : list N) (mcert : mc_certificate) : string + unit :=
  if negb (wf_mc_cert mcert) then inl "malformed mc-cert-v1 certificate"
  else if negb (mcfg_identified_typs_defined ir_m) then
    inl "undefined identified type in IR module"
  else
    match find_unique_defn_by_name (mc_fn_name mcert) (m_definitions ir_m) with
    | None => inl "function definition not found or ambiguous in IR module"
    | Some ir_defn =>
        if negb (check_mc_ir_proto_contract (m_type_defs ir_m) ir_defn mcert) then
          inl "IR prototype, ABI extension, or syntax contract check failed"
        else
          let fn_bare := strip_leading_at (mc_fn_name mcert) in
          match elf64_extract_func raw_elf (mc_arch mcert) (mc_elf_kind mcert) fn_bare with
          | inl err => inl err
          | inr sl =>
              if negb (Bool.eqb (mc_rvc mcert) (efs_rvc sl)) then
                inl "ELF64 RVC flag mismatch with mc-cert-v1 rvc mode"
              else
                match mc_decode_and_summarize (mc_arch mcert) (mc_rvc mcert) (efs_bytes sl) (mc_args mcert) (mc_ret_width mcert) with
                | inl err => inl err
                | inr d_mc =>
                    match flatten_mc_dag_to_expr (mc_ret_width mcert) d_mc with
                    | None => inl "MC DAG flattening failed"
                    | Some e_mc =>
                        let tenv := m_type_defs ir_m in
                        let ir_cfg := convert_typ tenv (df_instrs ir_defn) in
                        let ir_pnames := List.map cert_reg_name (args ir_cfg) in
                        let arg_dtys := defn_arg_dtys tenv ir_defn in
                        let s_pattrs := snd (dc_param_attrs (df_prototype ir_defn)) in
                        let '(seed_vars, mc_init_ctx) :=
                            mc_build_init_ctx (mc_arch mcert) ir_pnames arg_dtys s_pattrs (mc_args mcert) in
                        let allowed := used_src_param_vars ir_cfg ++ seed_vars in
                        match summarize_cfg_dag_with_uas (fun _ => []) false ir_cfg ir_pnames with
                        | None => inl "IR CFG symbolic summarization failed"
                        | Some d_ir =>
                            match src_dag_to_expr (mc_ret_width mcert) d_ir with
                            | Some e_ir =>
                                if check_mc_expr_refines mc_init_ctx allowed e_ir e_mc (mc_lrat_proof mcert)
                                then inr tt
                                else inl "MC-to-IR scalar refinement obligation failed"
                            | None =>
                                let dag_fuel := S (dag_node_count d_ir + 1) in
                                let ro :=
                                  RO_ScalarRefines (mc_ret_width mcert)
                                    (CE_BvConst (mc_ret_width mcert) 0%N)
                                    (CE_BvConst (mc_ret_width mcert) 0%N) false in
                                if check_dag_refines_cert dag_fuel allowed mc_init_ctx ro
                                     (mc_lrat_proof mcert)
                                     (spine_src_evals d_ir) (spine_branch_conds d_ir)
                                     d_ir (CD_RetScalar (mc_ret_width mcert) e_mc)
                                then inr tt
                                else inl "MC-to-IR DAG refinement obligation failed"
                            end
                        end
                    end
                end
          end
    end.

Definition validate_mc_tle_with_cert_str
  (ir_tle : toplevel_entities typ (block typ * list (block typ)))
  (elf_str cert_str : string) : string + unit :=
  match parse_mc_cert cert_str with
  | inl err => inl err
  | inr mcert =>
      validate_mc_mcfg_with_cert
        (mcfg_of_tle (resolve_module_refs ir_tle))
        (mc_string_to_bytes elf_str)
        mcert
  end.

Lemma mc_args_noundef_ctx_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle specs rf0,
    rv_rf_matches_args penv specs rf0 ->
    ub_ctx_holds penv foracle (List.map (fun sp => UBA_ParamNoUndef (ras_name sp) (ras_width sp)) specs).
Proof.
  intros penv foracle specs rf0 Hm.
  apply Forall_forall; intros ua Hin.
  apply in_map_iff in Hin as [sp [Heq Hsp]]; subst ua.
  destruct (In_nth_error specs sp Hsp) as [k Hnth].
  destruct (nth_error_Some specs k) as [Hs1 _].
  assert (Hlt : (k < List.length specs)%nat) by (apply Hs1; congruence).
  destruct (Hm k sp Hlt Hnth) as [v [Hp _]].
  cbn [ub_assumption_holds]; intros dv Hdv; rewrite Hp in Hdv; injection Hdv as <-; discriminate.
Qed.

Lemma a64_args_noundef_ctx_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle specs rf0,
    a64_rf_matches_args penv specs rf0 ->
    ub_ctx_holds penv foracle (List.map (fun sp => UBA_ParamNoUndef (ras_name sp) (ras_width sp)) specs).
Proof.
  intros penv foracle specs rf0 Hm.
  apply Forall_forall; intros ua Hin.
  apply in_map_iff in Hin as [sp [Heq Hsp]]; subst ua.
  destruct (In_nth_error specs sp Hsp) as [k Hnth].
  destruct (nth_error_Some specs k) as [Hs1 _].
  assert (Hlt : (k < List.length specs)%nat) by (apply Hs1; congruence).
  destruct (Hm k sp Hlt Hnth) as [v [Hp _]].
  cbn [ub_assumption_holds]; intros dv Hdv; rewrite Hp in Hdv; injection Hdv as <-; discriminate.
Qed.

Lemma a64_hi_vars_wf_and_ctx {Pa : Params} :
  forall (penv : param_env Pa) foracle specs rf0,
    NoDup (List.map ras_name specs) ->
    let penv' := a64_extend_penv_with_hi penv specs rf0 in
    wf_param_env_for (a64_hi_vars specs) penv' /\
    ub_ctx_holds penv' foracle (List.map (fun nv => UBA_ParamNoUndef (fst nv) (snd nv)) (a64_hi_vars specs)).
Proof.
  intros penv foracle specs rf0 Hnd penv'.
  assert (Hlookup : forall nm w, In (nm, w) (a64_hi_vars specs) ->
    exists k sp, nth_error specs k = Some sp /\
      nm = a64_hi_var_name (ras_name sp) /\ w = 64%positive /\ (ras_width sp =? 64)%positive = false).
  { intros nm w Hin; unfold a64_hi_vars in Hin; apply in_flat_map in Hin as [sp [Hsp Hhere]].
    destruct (Pos.eqb (ras_width sp) 64%positive) eqn:E64; [contradiction Hhere |].
    destruct Hhere as [Heq | []]; inversion Heq; subst nm w.
    destruct (In_nth_error specs sp Hsp) as [k Hnth].
    exists k, sp; repeat split; assumption. }
  split.
  - intros nm w Hin; destruct (Hlookup nm w Hin) as (k & sp & Hnth & -> & -> & Hw64).
    pose proof (a64_extend_penv_at_hi 0%nat k specs sp rf0 penv Hnd Hnth Hw64) as Hp.
    change (a64_extend_penv_with_hi_at 0%nat specs rf0 penv) with penv' in Hp.
    exists (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (N.of_nat (0 + k)) rf0))).
    split; [exact Hp | right; eexists; reflexivity].
  - apply Forall_forall; intros ua Hin; apply in_map_iff in Hin as [[nm w] [<- Hnv]]; cbn [fst snd].
    destruct (Hlookup nm w Hnv) as (k & sp & Hnth & -> & -> & Hw64).
    pose proof (a64_extend_penv_at_hi 0%nat k specs sp rf0 penv Hnd Hnth Hw64) as Hp.
    change (a64_extend_penv_with_hi_at 0%nat specs rf0 penv) with penv' in Hp.
    cbn [ub_assumption_holds]; intros dv Hdv; rewrite Hp in Hdv; injection Hdv as <-; discriminate.
Qed.

Lemma wf_cfg_dag_mono : forall vars1 vars2 d,
  incl vars1 vars2 ->
  wf_cfg_dag vars1 d = true ->
  wf_cfg_dag vars2 d = true.
Proof.
  intros vars1 vars2 d Hinc; induction d as [| | w ret_e | w step_e next IH | uas next IH | cond on_t IHt on_f IHf];
    intro Hwf; cbn [wf_cfg_dag] in *; try exact Hwf.
  - rewrite !andb_true_iff in *; destruct Hwf as (((? & ?) & ?) & Hsub); repeat split; try assumption.
    apply incl_vars_subset_b; eapply incl_tran; [exact (vars_subset_b_incl _ _ Hsub) | exact Hinc].
  - rewrite !andb_true_iff in *; destruct Hwf as ((((? & ?) & ?) & Hsub) & Hn); repeat split; try assumption;
      [apply incl_vars_subset_b; eapply incl_tran; [exact (vars_subset_b_incl _ _ Hsub) | exact Hinc] | exact (IH Hn)].
  - exact (IH Hwf).
  - rewrite !andb_true_iff in *; destruct Hwf as (((((? & ?) & ?) & Hsub) & Ht) & Hf); repeat split; try assumption;
      [apply incl_vars_subset_b; eapply incl_tran; [exact (vars_subset_b_incl _ _ Hsub) | exact Hinc] | exact (IHt Ht) | exact (IHf Hf)].
Qed.

Lemma eval_cert_expr_penv_agree {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) foracle e,
    is_let_free_expr e = true ->
    (forall nm w, In (nm, w) (collect_free_vars [] e) -> penv1 nm = penv2 nm) ->
    eval_cert_expr penv1 [] foracle e = eval_cert_expr penv2 [] foracle e.
Proof.
  intros penv1 penv2 foracle e.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hlf Hag; cbn [is_let_free_expr collect_free_vars eval_cert_expr lookup_let_val] in *.
  - reflexivity.
  - reflexivity.
  - rewrite (Hag nm w ltac:(left; reflexivity)); reflexivity.
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    rewrite (IHl Hlfl (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_introl Hx)))),
            (IHr Hlfr (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror Hx)))); reflexivity.
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    rewrite (IHl Hlfl (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_introl Hx)))),
            (IHr Hlfr (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror Hx)))); reflexivity.
  - rewrite (IHo Hlf Hag); reflexivity.
  - rewrite !andb_true_iff in Hlf; destruct Hlf as [[Hlfc Hlft] Hlff].
    rewrite (IHc Hlfc (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_introl Hx)))),
            (IHt Hlft (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hx)))))),
            (IHf Hlff (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hx)))))); reflexivity.
  - rewrite (IHo Hlf Hag); reflexivity.
  - discriminate Hlf.
Qed.

Lemma eval_cfg_dag_penv_agree {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) foracle allowed d,
    wf_cfg_dag allowed d = true ->
    (forall nm w, In (nm, w) allowed -> penv1 nm = penv2 nm) ->
    eval_cfg_dag penv1 foracle d = eval_cfg_dag penv2 foracle d.
Proof.
  intros penv1 penv2 foracle allowed d;
    induction d as [| | w ret_e | w step_e next IH | uas next IH | cond on_t IHt on_f IHf];
    intros Hwf Hag; cbn [wf_cfg_dag eval_cfg_dag] in *; try reflexivity.
  - rewrite !andb_true_iff in Hwf; destruct Hwf as (((_ & _) & Hlf) & Hsub).
    unfold eval_closed_cert_expr.
    erewrite eval_cert_expr_penv_agree; [reflexivity | exact Hlf |].
    intros nm w0 Hin; apply (Hag nm w0 ((vars_subset_b_incl _ _ Hsub) _ Hin)).
  - rewrite !andb_true_iff in Hwf; destruct Hwf as ((((_ & _) & Hlf) & Hsub) & Hn).
    unfold eval_closed_cert_expr.
    erewrite (eval_cert_expr_penv_agree penv1 penv2);
      [| exact Hlf | intros nm w0 Hin; apply (Hag nm w0 ((vars_subset_b_incl _ _ Hsub) _ Hin))].
    destruct (eval_cert_expr penv2 [] foracle step_e); try reflexivity; exact (IH Hn Hag).
  - exact (IH Hwf Hag).
  - rewrite !andb_true_iff in Hwf; destruct Hwf as (((((_ & _) & Hlf) & Hsub) & Ht) & Hf).
    unfold eval_closed_cert_expr.
    erewrite (eval_cert_expr_penv_agree penv1 penv2);
      [| exact Hlf | intros nm w0 Hin; apply (Hag nm w0 ((vars_subset_b_incl _ _ Hsub) _ Hin))].
    destruct (eval_cert_expr penv2 [] foracle cond) as [| | | dvc]; try reflexivity.
    destruct dvc as [dbc | |]; try reflexivity.
    destruct dbc as [| wc cbit | | | | | |]; try reflexivity.
    destruct wc as [| |]; try reflexivity.
    destruct (@Integers.unsigned 1 cbit =? 1)%Z; [exact (IHt Ht Hag) | exact (IHf Hf Hag)].
Qed.

Lemma validate_mc_core_refine_sound {Pa : Params} :
  forall allowed mc_init_ctx ret_w lrat_pf d_ir d_mc e_mc penv dv_ir dv_mc,
    flatten_mc_dag_to_expr ret_w d_mc = Some e_mc ->
    (match src_dag_to_expr ret_w d_ir with
     | Some e_ir => check_mc_expr_refines mc_init_ctx allowed e_ir e_mc lrat_pf
     | None =>
         check_dag_refines_cert (S (dag_node_count d_ir + 1)) allowed mc_init_ctx
           (RO_ScalarRefines ret_w (CE_BvConst ret_w 0%N) (CE_BvConst ret_w 0%N) false)
           lrat_pf (spine_src_evals d_ir) (spine_branch_conds d_ir) d_ir (CD_RetScalar ret_w e_mc)
     end) = true ->
    wf_cfg_dag allowed d_ir = true ->
    wf_cfg_dag allowed d_mc = true ->
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv dummy_freeze_oracle mc_init_ctx ->
    eval_cfg_dag penv dummy_freeze_oracle d_mc = DO_Ret dv_mc ->
    eval_cfg_dag penv dummy_freeze_oracle d_ir = DO_Ret dv_ir ->
    dvalue_refines dv_ir dv_mc.
Proof.
  intros allowed mc_init_ctx ret_w lrat_pf d_ir d_mc e_mc penv dv_ir dv_mc
         Eflat Hchk Hwfd_ir Hwfd_mc Hpenv_all Hctx_all Hevd_mc Hevd_ir.
  destruct (flatten_mc_dag_to_expr_typing allowed ret_w d_mc e_mc Hwfd_mc Eflat)
    as (Hwt_mc & Hbw_mc & Hlf_mc & Hub_mc & Hfv_mc).
  assert (Hp_mc : wf_param_env_for (collect_free_vars [] e_mc) penv)
    by (intros x wx Hx; exact (Hpenv_all x wx (Hfv_mc (x, wx) Hx))).
  pose proof (flatten_mc_dag_to_expr_sound allowed ret_w d_mc e_mc
                penv dummy_freeze_oracle dv_mc Hwfd_mc Hpenv_all Eflat Hevd_mc) as Heve_mc.
  destruct (src_dag_to_expr ret_w d_ir) as [e_ir |] eqn:Esd.
  - destruct (src_dag_to_expr_typing allowed ret_w d_ir e_ir Hwfd_ir Esd)
      as (Hwt_ir & _ & Hlf_ir & Hfv_ir).
    assert (Hp_ir : wf_param_env_for (collect_free_vars [] e_ir) penv)
      by (intros x wx Hx; exact (Hpenv_all x wx (Hfv_ir (x, wx) Hx))).
    pose proof (src_dag_to_expr_sound allowed ret_w d_ir e_ir
                  penv dummy_freeze_oracle dv_ir Hwfd_ir Hpenv_all Esd Hevd_ir) as Heve_ir.
    pose proof (prepare_mc_expr_pair_sound _ allowed e_ir e_mc lrat_pf
                  penv dummy_freeze_oracle Hwt_ir Hlf_ir Hp_ir Hp_mc Hctx_all Hchk) as Href_e.
    rewrite Heve_ir, Heve_mc in Href_e; exact Href_e.
  - assert (Hwfd_flat : wf_cfg_dag allowed (CD_RetScalar ret_w e_mc) = true).
    { cbn [wf_cfg_dag]; rewrite Hwt_mc, Hbw_mc, Pos.eqb_refl, Hlf_mc, (incl_vars_subset_b _ _ Hfv_mc); reflexivity. }
    destruct (check_dag_refines_cert_sound
                (S (dag_node_count d_ir + 1)) allowed mc_init_ctx
                (RO_ScalarRefines ret_w (CE_BvConst ret_w 0%N) (CE_BvConst ret_w 0%N) false)
                lrat_pf (spine_src_evals d_ir) (spine_branch_conds d_ir)
                d_ir (CD_RetScalar ret_w e_mc) penv dummy_freeze_oracle dv_ir
                Hwfd_ir Hwfd_flat Hpenv_all Hctx_all
                (fun big H => spine_src_evals_wf allowed d_ir big Hwfd_ir H)
                (fun big H => spine_src_evals_ret penv dummy_freeze_oracle d_ir dv_ir big Hevd_ir H)
                (fun c H => spine_branch_conds_ret penv dummy_freeze_oracle d_ir dv_ir c Hevd_ir H)
                Hchk Hevd_ir) as (dv_tgt & Hevt_flat & Href_dv).
    cbn [eval_cfg_dag] in Hevt_flat; rewrite Heve_mc in Hevt_flat; inversion Hevt_flat; subst dv_tgt; exact Href_dv.
Qed.

Theorem validate_mc_tle_with_cert_str_sound :
  forall {Pa : Params}
         (ir_tle : toplevel_entities typ (block typ * list (block typ)))
         (elf_str cert_str : string),
    validate_mc_tle_with_cert_str ir_tle elf_str cert_str = inr tt ->
    let ir_m := mcfg_of_tle (resolve_module_refs ir_tle) in
    let raw_elf := mc_string_to_bytes elf_str in
    exists mcert ir_defn sl,
      parse_mc_cert cert_str = inr mcert /\
      wf_mc_cert mcert = true /\
      In ir_defn (m_definitions ir_m) /\
      cert_fn_matches_raw_id (mc_fn_name mcert) (dc_name (df_prototype ir_defn)) = true /\
      elf64_extract_func raw_elf (mc_arch mcert) (mc_elf_kind mcert) (strip_leading_at (mc_fn_name mcert)) = inr sl /\
      efs_rvc sl = mc_rvc mcert /\
      let tenv := m_type_defs ir_m in
      let ir_cfg := convert_typ tenv (df_instrs ir_defn) in
      let ir_pnames := List.map cert_reg_name (args ir_cfg) in
      let arg_dtys := defn_arg_dtys tenv ir_defn in
      let s_pattrs := snd (dc_param_attrs (df_prototype ir_defn)) in
      match mc_arch mcert with
      | EA_Riscv64 =>
          exists insts,
            decode_rv64_bytes (mc_rvc mcert) (efs_bytes sl) = inr insts /\
            let rv_fuel := S (2 * List.length insts) in
            forall (vs : list (@dvalue Pa)) rf0,
              Forall2 dvalue_has_dtyp vs arg_dtys ->
              Forall2 (fun attrs v => existsb attr_is_noundef attrs = true -> dvalue_well_defined v = true)
                      s_pattrs vs ->
              rv_rf_matches_args (build_param_env ir_pnames vs) (mc_args mcert) rf0 ->
              exists sigma_ir rf_end,
                wf_draw_strat sigma_ir /\
                rv_exec rv_fuel insts 0%N rf0 = Some rf_end /\
                rv_callee_saved_preserved rf0 rf_end /\
                (cfg_steps_to_ub sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
                 exists sigma_ir' env_out dv_ir,
                   cfg_steps_to_ret sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)
                     sigma_ir' env_out dv_ir /\
                   dvalue_refines dv_ir
                     (DVALUE_Base (@DVALUE_I Pa (mc_ret_width mcert)
                        (rv_trunc_ret_val (mc_ret_width mcert) (rv_read_reg 10%N rf_end)))))
      | EA_AArch64 =>
          mc_rvc mcert = false /\
          exists insts,
            decode_a64_bytes (efs_bytes sl) = inr insts /\
            let a64_fuel := S (2 * List.length insts) in
            forall (vs : list (@dvalue Pa)) rf0 fl0,
              Forall2 dvalue_has_dtyp vs arg_dtys ->
              Forall2 (fun attrs v => existsb attr_is_noundef attrs = true -> dvalue_well_defined v = true)
                      s_pattrs vs ->
              a64_rf_matches_args (build_param_env ir_pnames vs) (mc_args mcert) rf0 ->
              exists sigma_ir rf_end fl_end,
                wf_draw_strat sigma_ir /\
                a64_exec a64_fuel insts 0%N rf0 fl0 = Some (rf_end, fl_end) /\
                a64_callee_saved_preserved rf0 rf_end /\
                (cfg_steps_to_ub sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
                 exists sigma_ir' env_out dv_ir,
                   cfg_steps_to_ret sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)
                     sigma_ir' env_out dv_ir /\
                   dvalue_refines dv_ir
                     (DVALUE_Base (@DVALUE_I Pa (mc_ret_width mcert)
                        (rv_trunc_ret_val (mc_ret_width mcert) (a64_read_reg 0%N rf_end)))))
      end.
Proof.
  intros Pa ir_tle elf_str cert_str Hval ir_m raw_elf.
  unfold validate_mc_tle_with_cert_str in Hval; fold ir_m raw_elf in Hval.
  destruct (parse_mc_cert cert_str) as [| mcert] eqn:Ecert; [discriminate Hval |].
  pose proof (parse_mc_cert_wf cert_str mcert Ecert) as Hwf_cert.
  unfold validate_mc_mcfg_with_cert in Hval.
  rewrite Hwf_cert in Hval; cbn [negb] in Hval.
  destruct (mcfg_identified_typs_defined ir_m); cbn [negb] in Hval; [| discriminate Hval].
  destruct (find_unique_defn_by_name (mc_fn_name mcert) (m_definitions ir_m)) as [ir_defn |] eqn:Efnd;
    [| discriminate Hval].
  destruct (find_unique_defn_by_name_in _ _ _ Efnd) as [Hin_defn _].
  destruct (check_mc_ir_proto_contract (m_type_defs ir_m) ir_defn mcert) eqn:Hproto;
    cbn [negb] in Hval; [| discriminate Hval].
  destruct (elf64_extract_func raw_elf (mc_arch mcert) (mc_elf_kind mcert) (strip_leading_at (mc_fn_name mcert)))
    as [| sl] eqn:Eelf; [discriminate Hval |].
  destruct (Bool.eqb (mc_rvc mcert) (efs_rvc sl)) eqn:Ervc; cbn [negb] in Hval; [| discriminate Hval].
  apply Bool.eqb_prop in Ervc.
  destruct (mc_decode_and_summarize (mc_arch mcert) (mc_rvc mcert) (efs_bytes sl) (mc_args mcert) (mc_ret_width mcert))
    as [| d_mc] eqn:Edec_s; [discriminate Hval |].
  destruct (flatten_mc_dag_to_expr (mc_ret_width mcert) d_mc) as [e_mc |] eqn:Eflat;
    [| discriminate Hval].
  set (tenv := m_type_defs ir_m) in *.
  set (ir_cfg := convert_typ tenv (df_instrs ir_defn)) in *.
  set (ir_pnames := List.map cert_reg_name (args ir_cfg)) in *.
  set (arg_dtys := defn_arg_dtys tenv ir_defn) in *.
  set (s_pattrs := snd (dc_param_attrs (df_prototype ir_defn))) in *.
  destruct (mc_build_init_ctx (mc_arch mcert) ir_pnames arg_dtys s_pattrs (mc_args mcert))
    as [seed_vars mc_init_ctx] eqn:Ectx_b.
  set (allowed := used_src_param_vars ir_cfg ++ seed_vars) in *.
  destruct (summarize_cfg_dag_with_uas (fun _ => []) false ir_cfg ir_pnames)
    as [d_ir |] eqn:Esum_ir; [| discriminate Hval].
  assert (Hfn_m : cert_fn_matches_raw_id (mc_fn_name mcert) (dc_name (df_prototype ir_defn)) = true).
  { unfold check_mc_ir_proto_contract in Hproto; cbn zeta in Hproto.
    destruct (dc_param_attrs (df_prototype ir_defn)).
    apply andb_true_iff in Hproto as [Hfn _]; exact Hfn. }
  exists mcert, ir_defn, sl.
  repeat split; try assumption; [symmetry; exact Ervc |].
  (* Unpack prototype invariants *)
  unfold check_mc_ir_proto_contract in Hproto; cbn zeta in Hproto; fold tenv ir_cfg ir_pnames in Hproto.
  destruct (dc_param_attrs (df_prototype ir_defn)) as [s_rattrs s_pattrs0] eqn:Edcpa.
  apply andb_true_iff in Hproto as [_ Hbody].
  destruct (dc_type (df_prototype ir_defn)) as [| | | | | | | | | | | ret_ty arg_tys [|] | | | | |] eqn:Edct;
    try discriminate Hbody.
  rewrite !andb_true_iff in Hbody.
  destruct Hbody as (((((((((((((_ & _) & _) & _) & _) & _) & _) & _) & Hnd_raw) & Hnd_sp) & Hmc_args) & Hhi_dis) & Hcomp) & _).
  apply no_dup_raw_ids_spec in Hnd_raw.
  apply no_dup_strings_spec in Hnd_sp.
  assert (Hlen_sp_s : List.length ir_pnames = List.length (args ir_cfg))
    by (unfold ir_pnames; apply List.length_map).
  assert (Hlen_ad : List.length arg_dtys = List.length (args ir_cfg)).
  { unfold arg_dtys, defn_arg_dtys; rewrite Edct; cbn match.
    destruct (check_mc_arg_specs_len _ _ _ _ _ Hmc_args) as [Hlp _].
    rewrite <- Hlp, Hlen_sp_s; reflexivity. }
  assert (Harg_dtys_eq : arg_dtys = List.map (typ_to_dtyp tenv) arg_tys)
    by (unfold arg_dtys, defn_arg_dtys; rewrite Edct; reflexivity).
  rewrite <- Harg_dtys_eq in Hcomp.
  assert (Hpu_ir : forall idx w0 pnm,
    In (idx, DTYPE_Base (DTYPE_I w0)) (param_idx_uses_cfg ir_cfg) ->
    nth_error ir_pnames idx = Some pnm ->
    In (pnm, w0) (used_src_param_vars ir_cfg)).
  { intros idx w0 pnm Hin Hpnm; unfold used_src_param_vars; apply in_flat_map.
    exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin | fold ir_pnames; rewrite Hpnm; left; reflexivity]. }
  pose proof (summarize_cfg_dag_with_uas_wf (fun _ => []) false ir_cfg ir_pnames (used_src_param_vars ir_cfg) d_ir Hpu_ir Esum_ir)
    as Hwfd_ir0.
  assert (Hwfd_ir : wf_cfg_dag allowed d_ir = true)
    by (eapply wf_cfg_dag_mono; [intros u Hu; unfold allowed; apply in_app_iff; left; exact Hu | exact Hwfd_ir0]).
  assert (Hnames_eq : List.map ras_name (mc_args mcert) = ir_pnames)
    by exact (check_mc_arg_specs_names _ _ _ _ _ Hmc_args).
  assert (Hnd_mc : NoDup (List.map ras_name (mc_args mcert)))
    by (rewrite Hnames_eq; exact Hnd_sp).
  assert (Hchk :
    (match src_dag_to_expr (mc_ret_width mcert) d_ir with
     | Some e_ir => check_mc_expr_refines mc_init_ctx allowed e_ir e_mc (mc_lrat_proof mcert)
     | None =>
         check_dag_refines_cert (S (dag_node_count d_ir + 1)) allowed mc_init_ctx
           (RO_ScalarRefines (mc_ret_width mcert) (CE_BvConst (mc_ret_width mcert) 0%N) (CE_BvConst (mc_ret_width mcert) 0%N) false)
           (mc_lrat_proof mcert) (spine_src_evals d_ir) (spine_branch_conds d_ir) d_ir (CD_RetScalar (mc_ret_width mcert) e_mc)
     end) = true).
  { destruct (src_dag_to_expr (mc_ret_width mcert) d_ir) as [e_ir |];
      [destruct (check_mc_expr_refines mc_init_ctx allowed e_ir e_mc (mc_lrat_proof mcert))
      | destruct (check_dag_refines_cert (S (dag_node_count d_ir + 1)) allowed mc_init_ctx
                    (RO_ScalarRefines (mc_ret_width mcert) (CE_BvConst (mc_ret_width mcert) 0%N) (CE_BvConst (mc_ret_width mcert) 0%N) false)
                    (mc_lrat_proof mcert) (spine_src_evals d_ir) (spine_branch_conds d_ir) d_ir (CD_RetScalar (mc_ret_width mcert) e_mc))];
      [reflexivity | discriminate Hval | reflexivity | discriminate Hval]. }
  cbn zeta.
  destruct (mc_arch mcert) eqn:Earch; unfold mc_decode_and_summarize in Edec_s.
  - (* EA_Riscv64 *)
    destruct (decode_rv64_bytes (mc_rvc mcert) (efs_bytes sl)) as [| insts] eqn:Edec;
      [discriminate Edec_s |].
    set (rv_fuel := S (2 * List.length insts)) in *.
    destruct (summarize_rv64_dag rv_fuel insts (mc_args mcert) (mc_ret_width mcert))
      as [d_mc0 |] eqn:Esum_mc; [| discriminate Edec_s].
    inversion Edec_s; subst d_mc0; clear Edec_s.
    exists insts; split; [reflexivity |].
    intros vs rf0 Hty Hnu Hm.
    change (m_type_defs ir_m) with tenv in Hty, Hnu, Hm.
    change (convert_typ tenv (df_instrs ir_defn)) with ir_cfg in Hty, Hnu, Hm.
    change (List.map cert_reg_name (args ir_cfg)) with ir_pnames in Hty, Hnu, Hm.
    change (defn_arg_dtys tenv ir_defn) with arg_dtys in Hty, Hnu, Hm.
    change (snd (dc_param_attrs (df_prototype ir_defn))) with s_pattrs in Hty, Hnu, Hm.
    set (penv := build_param_env ir_pnames vs) in *.
    pose proof (used_src_param_vars_wf ir_cfg arg_dtys vs Hnd_sp Hlen_ad Hcomp Hty) as Hpenv_used.
    fold ir_pnames penv in Hpenv_used.
    assert (Hlen_sp_vs : List.length ir_pnames = List.length vs)
      by (pose proof (Forall2_length Hty); lia).
    unfold s_pattrs in *; cbn [snd] in *.
    unfold mc_build_init_ctx in Ectx_b.
    destruct (seed_proto_param_ctx ir_pnames arg_dtys s_pattrs0) as [proto_vars proto_ctx] eqn:Eseed.
    inversion Ectx_b; subst seed_vars mc_init_ctx; clear Ectx_b.
    pose proof (seed_proto_param_ctx_sound ir_pnames arg_dtys s_pattrs0 vs dummy_freeze_oracle
                  Hnd_sp Hlen_sp_vs Hty Hnu) as [Hpenv_proto Hctx_proto].
    rewrite Eseed in Hpenv_proto, Hctx_proto; cbn [fst snd] in Hpenv_proto, Hctx_proto.
    pose proof (mc_args_noundef_ctx_sound penv dummy_freeze_oracle (mc_args mcert) rf0 Hm) as Hctx_mc.
    assert (Hctx_all : ub_ctx_holds penv dummy_freeze_oracle
                         (proto_ctx ++ List.map (fun sp => UBA_ParamNoUndef (ras_name sp) (ras_width sp)) (mc_args mcert) ++ []))
      by (rewrite app_nil_r; apply Forall_app; split; assumption).
    assert (Hmc_vars_all :
      forall sp, In sp (mc_args mcert) -> In (ras_name sp, ras_width sp) allowed).
    { intros sp Hsp; unfold allowed; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left.
      apply in_map_iff; exists sp; split; [reflexivity | exact Hsp]. }
    assert (Hmc_vars_wf :
      wf_param_env_for (List.map (fun sp => (ras_name sp, ras_width sp)) (mc_args mcert) ++ []) penv).
    { intros nm w Hin; rewrite app_nil_r in Hin; apply in_map_iff in Hin as [sp [Heq Hsp]]; inversion Heq; subst nm w.
      destruct (In_nth_error (mc_args mcert) sp Hsp) as [k Hnth].
      destruct (nth_error_Some (mc_args mcert) k) as [Hs1 _].
      destruct (Hm k sp ltac:(apply Hs1; congruence) Hnth) as [v [Hp _]].
      exists (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)); split; [exact Hp | right; exists v; reflexivity]. }
    assert (Hpenv_all : wf_param_env_for allowed penv).
    { intros nm w Hin; unfold allowed in Hin; apply in_app_iff in Hin as [Hu | Hs].
      - exact (Hpenv_used nm w Hu).
      - apply in_app_iff in Hs as [Hp | Hm_v]; [exact (Hpenv_proto nm w Hp) | exact (Hmc_vars_wf nm w Hm_v)]. }
    pose proof (decode_rv64_bytes_no_word_mulh (mc_rvc mcert) (efs_bytes sl) insts Edec) as Hnmul.
    pose proof (summarize_rv64_dag_wf rv_fuel insts (mc_args mcert) (mc_ret_width mcert) d_mc Hnmul Esum_mc)
      as Hwfd_mc0.
    assert (Hwfd_mc : wf_cfg_dag allowed d_mc = true).
    { eapply wf_cfg_dag_mono; [| exact Hwfd_mc0].
      intros u Hu; apply in_map_iff in Hu as [sp [<- Hsp]]; exact (Hmc_vars_all sp Hsp). }
    destruct (summarize_rv64_dag_sound rv_fuel (mc_rvc mcert) (efs_bytes sl) insts
                (mc_args mcert) (mc_ret_width mcert) d_mc penv dummy_freeze_oracle rf0
                Edec Esum_mc Hm)
      as (rf_end & Hexec & Hcs & Hevd_mc).
    destruct (summarize_src_dag_with_uas_sound (fun _ => []) ir_cfg ir_pnames arg_dtys vs
                dummy_freeze_oracle d_ir Hnd_raw Hnd_sp Hlen_sp_s Hlen_ad Hcomp Hty Esum_ir)
      as (sigma_ir & Hwfsig & Hsrc_out).
    exists sigma_ir, rf_end; split; [exact Hwfsig | split; [exact Hexec | split; [exact Hcs |]]].
    destruct Hsrc_out as [[Hub_s _] | (sigma_ir' & env_out & dv_ir & Hevd_ir & Hst_ret)].
    + left; exact Hub_s.
    + right; exists sigma_ir', env_out, dv_ir; split; [exact Hst_ret |].
      eapply validate_mc_core_refine_sound;
        [exact Eflat | exact Hchk | exact Hwfd_ir | exact Hwfd_mc | exact Hpenv_all | exact Hctx_all | exact Hevd_mc | exact Hevd_ir].
  - (* EA_AArch64 *)
    destruct (mc_rvc mcert) eqn:Emrvc; [discriminate Edec_s |].
    split; [reflexivity |].
    destruct (decode_a64_bytes (efs_bytes sl)) as [| insts] eqn:Edec;
      [discriminate Edec_s |].
    set (a64_fuel := S (2 * List.length insts)) in *.
    destruct (summarize_a64_dag a64_fuel insts (mc_args mcert) (mc_ret_width mcert))
      as [d_mc0 |] eqn:Esum_mc; [| discriminate Edec_s].
    inversion Edec_s; subst d_mc0; clear Edec_s.
    exists insts; split; [reflexivity |].
    intros vs rf0 fl0 Hty Hnu Hm.
    change (m_type_defs ir_m) with tenv in Hty, Hnu, Hm.
    change (convert_typ tenv (df_instrs ir_defn)) with ir_cfg in Hty, Hnu, Hm.
    change (List.map cert_reg_name (args ir_cfg)) with ir_pnames in Hty, Hnu, Hm.
    change (defn_arg_dtys tenv ir_defn) with arg_dtys in Hty, Hnu, Hm.
    change (snd (dc_param_attrs (df_prototype ir_defn))) with s_pattrs in Hty, Hnu, Hm.
    set (penv := build_param_env ir_pnames vs) in *.
    set (penv' := a64_extend_penv_with_hi penv (mc_args mcert) rf0) in *.
    assert (Hdis_orig : forall nm, In nm ir_pnames -> penv' nm = penv nm).
    { intros nm Hinnm; unfold penv', a64_extend_penv_with_hi; apply a64_extend_penv_at_orig.
      intros sp Hsp Heq; rewrite forallb_forall in Hhi_dis.
      pose proof (Hhi_dis sp Hsp) as Hneg; apply negb_true_iff in Hneg.
      assert (Hex : existsb (String.eqb (a64_hi_var_name (ras_name sp))) ir_pnames = true)
        by (apply existsb_exists; exists nm; split; [exact Hinnm | rewrite <- Heq; apply String.eqb_refl]).
      rewrite Hex in Hneg; discriminate Hneg. }
    assert (Hdis_args : forall sp, In sp (mc_args mcert) -> ~ In (a64_hi_var_name (ras_name sp)) (List.map ras_name (mc_args mcert))).
    { intros sp Hsp Hin; rewrite Hnames_eq in Hin; rewrite forallb_forall in Hhi_dis.
      pose proof (Hhi_dis sp Hsp) as Hneg; apply negb_true_iff in Hneg.
      assert (Hex : existsb (String.eqb (a64_hi_var_name (ras_name sp))) ir_pnames = true)
        by (apply existsb_exists; exists (a64_hi_var_name (ras_name sp)); split; [exact Hin | apply String.eqb_refl]).
      rewrite Hex in Hneg; discriminate Hneg. }
    pose proof (used_src_param_vars_wf ir_cfg arg_dtys vs Hnd_sp Hlen_ad Hcomp Hty) as Hpenv_used0.
    fold ir_pnames penv in Hpenv_used0.
    assert (Hpenv_used : wf_param_env_for (used_src_param_vars ir_cfg) penv').
    { intros nm w Hin; destruct (Hpenv_used0 nm w Hin) as [dv [Hp Hwf_dv]].
      assert (Hinnm : In nm ir_pnames).
      { unfold used_src_param_vars in Hin; apply in_flat_map in Hin as [[idx dt] [_ Hhere]].
        destruct dt as [[w0 | | | | | | | | | |] | |]; try contradiction Hhere.
        destruct (nth_error (List.map cert_reg_name (args ir_cfg)) idx) as [nm0 |] eqn:Hnth; [| contradiction Hhere].
        destruct Hhere as [Heq | []]; inversion Heq; subst nm0; fold ir_pnames in Hnth; exact (nth_error_In _ _ Hnth). }
      rewrite (Hdis_orig nm Hinnm); exists dv; split; assumption. }
    assert (Hlen_sp_vs : List.length ir_pnames = List.length vs)
      by (pose proof (Forall2_length Hty); lia).
    unfold s_pattrs in *; cbn [snd] in *.
    unfold mc_build_init_ctx in Ectx_b.
    destruct (seed_proto_param_ctx ir_pnames arg_dtys s_pattrs0) as [proto_vars proto_ctx] eqn:Eseed.
    inversion Ectx_b; subst seed_vars mc_init_ctx; clear Ectx_b.
    assert (Hlookup' : forall idx pnm v,
      nth_error ir_pnames idx = Some pnm -> nth_error vs idx = Some v -> penv' pnm = Some v).
    { intros idx pnm v Hnp Hnv.
      rewrite (Hdis_orig pnm (nth_error_In _ _ Hnp)).
      destruct (build_param_env_nth ir_pnames vs idx pnm Hnd_sp Hlen_sp_vs Hnp) as [dv [Hdv Hbp]].
      rewrite Hnv in Hdv; inversion Hdv; subst dv; exact Hbp. }
    pose proof (seed_proto_param_ctx_sound_aux ir_pnames arg_dtys s_pattrs0 vs penv' dummy_freeze_oracle Hty Hnu Hlookup')
      as [Hpenv_proto Hctx_proto].
    rewrite Eseed in Hpenv_proto, Hctx_proto; cbn [fst snd] in Hpenv_proto, Hctx_proto.
    assert (Hm' : a64_rf_matches_args penv' (mc_args mcert) rf0).
    { intros k sp Hlt Hnth; destruct (Hm k sp Hlt Hnth) as [v [Hp Hmt]].
      assert (Hinnm : In (ras_name sp) ir_pnames)
        by (rewrite <- Hnames_eq; apply in_map_iff; exists sp; split; [reflexivity | exact (nth_error_In _ _ Hnth)]).
      exists v; split; [rewrite (Hdis_orig _ Hinnm); exact Hp | exact Hmt]. }
    pose proof (a64_args_noundef_ctx_sound penv' dummy_freeze_oracle (mc_args mcert) rf0 Hm') as Hctx_mc.
    destruct (a64_hi_vars_wf_and_ctx penv dummy_freeze_oracle (mc_args mcert) rf0 Hnd_mc) as [Hpenv_hi Hctx_hi].
    fold penv' in Hpenv_hi, Hctx_hi.
    assert (Hctx_all : ub_ctx_holds penv' dummy_freeze_oracle
                         (proto_ctx ++ List.map (fun sp => UBA_ParamNoUndef (ras_name sp) (ras_width sp)) (mc_args mcert)
                                    ++ List.map (fun nv => UBA_ParamNoUndef (fst nv) (snd nv)) (a64_hi_vars (mc_args mcert))))
      by (apply Forall_app; split; [exact Hctx_proto | apply Forall_app; split; assumption]).
    assert (Hmc_vars_wf :
      wf_param_env_for (List.map (fun sp => (ras_name sp, ras_width sp)) (mc_args mcert)) penv').
    { intros nm w Hin; apply in_map_iff in Hin as [sp [Heq Hsp]]; inversion Heq; subst nm w.
      destruct (In_nth_error (mc_args mcert) sp Hsp) as [k Hnth].
      destruct (nth_error_Some (mc_args mcert) k) as [Hs1 _].
      destruct (Hm' k sp ltac:(apply Hs1; congruence) Hnth) as [v [Hp _]].
      exists (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)); split; [exact Hp | right; exists v; reflexivity]. }
    assert (Hpenv_all : wf_param_env_for allowed penv').
    { intros nm w Hin; unfold allowed in Hin; apply in_app_iff in Hin as [Hu | Hs].
      - exact (Hpenv_used nm w Hu).
      - apply in_app_iff in Hs as [Hp | Hrest]; [exact (Hpenv_proto nm w Hp) |].
        apply in_app_iff in Hrest as [Hmv | Hhi]; [exact (Hmc_vars_wf nm w Hmv) | exact (Hpenv_hi nm w Hhi)]. }
    pose proof (decode_a64_bytes_valid (efs_bytes sl) insts Edec) as Hval_a64.
    pose proof (summarize_a64_dag_wf a64_fuel insts (mc_args mcert) (mc_ret_width mcert) d_mc Hval_a64 Esum_mc)
      as Hwfd_mc0.
    assert (Hwfd_mc : wf_cfg_dag allowed d_mc = true).
    { eapply wf_cfg_dag_mono; [| exact Hwfd_mc0].
      intros u Hu; apply in_app_iff in Hu as [Hu1 | Hu2];
        unfold allowed; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff;
        [left; exact Hu1 | right; exact Hu2]. }
    destruct (summarize_a64_dag_sound a64_fuel (efs_bytes sl) insts (mc_args mcert) (mc_ret_width mcert)
                d_mc penv dummy_freeze_oracle rf0 fl0 Edec Hnd_mc Hdis_args Esum_mc Hm)
      as (rf_end & fl_end & Hexec & Hcs & Hevd_mc).
    fold penv' in Hevd_mc.
    destruct (summarize_src_dag_with_uas_sound (fun _ => []) ir_cfg ir_pnames arg_dtys vs
                dummy_freeze_oracle d_ir Hnd_raw Hnd_sp Hlen_sp_s Hlen_ad Hcomp Hty Esum_ir)
      as (sigma_ir & Hwfsig & Hsrc_out).
    exists sigma_ir, rf_end, fl_end; split; [exact Hwfsig | split; [exact Hexec | split; [exact Hcs |]]].
    destruct Hsrc_out as [[Hub_s _] | (sigma_ir' & env_out & dv_ir & Hevd_ir & Hst_ret)].
    + left; exact Hub_s.
    + right; exists sigma_ir', env_out, dv_ir; split; [exact Hst_ret |].
      assert (Hevd_ir' : eval_cfg_dag penv' dummy_freeze_oracle d_ir = DO_Ret dv_ir).
      { rewrite <- Hevd_ir; eapply eval_cfg_dag_penv_agree; [exact Hwfd_ir0 |].
        intros nm w Hin; unfold used_src_param_vars in Hin; apply in_flat_map in Hin as [[idx dt] [_ Hhere]].
        destruct dt as [[w0 | | | | | | | | | |] | |]; try contradiction Hhere.
        destruct (nth_error (List.map cert_reg_name (args ir_cfg)) idx) as [nm0 |] eqn:Hnth; [| contradiction Hhere].
        destruct Hhere as [Heq | []]; inversion Heq; subst nm0; fold ir_pnames in Hnth.
        exact (Hdis_orig nm (nth_error_In _ _ Hnth)). }
      eapply validate_mc_core_refine_sound;
        [exact Eflat | exact Hchk | exact Hwfd_ir | exact Hwfd_mc | exact Hpenv_all | exact Hctx_all | exact Hevd_mc | exact Hevd_ir'].
Qed.

(** ** 6. Diagnostic Tail-Recursive DIMACS CNF Emitter *)

Definition push_str_rev_chars (acc : list ascii) (s : string) : list ascii :=
  str_to_chars_rev_acc acc s.

Fixpoint format_clause_rev_chars (acc : list ascii) (cl : clause) {struct cl} : list ascii :=
  match cl with
  | [] => push_str_rev_chars acc "0" ++ [ascii_of_nat 10]
  | l :: rest =>
      let acc1 := push_str_rev_chars acc (show_Z_dec l) in
      format_clause_rev_chars (ascii_of_nat 32 :: acc1) rest
  end.

Fixpoint format_cnf_clauses_rev (acc : list ascii) (f : cnf) {struct f} : list ascii :=
  match f with
  | [] => acc
  | (_, cl) :: rest =>
      let acc1 :=
        match cl with
        | [] => ascii_of_nat 10 :: ascii_of_nat 48 :: acc
        | _ :: _ =>
            let fix go (a : list ascii) (ls : list lit) {struct ls} : list ascii :=
                match ls with
                | [] => ascii_of_nat 10 :: ascii_of_nat 48 :: a
                | l :: rs => go (ascii_of_nat 32 :: push_str_rev_chars a (show_Z_dec l)) rs
                end in
            go acc cl
        end in
      format_cnf_clauses_rev acc1 rest
  end.

Definition format_dimacs_cnf (num_vars : positive) (f : cnf) : string :=
  let hdr := ("p cnf " ++ show_Z_dec (Z.pos num_vars) ++ " " ++ show_Z_dec (Z.of_nat (List.length f)) ++ String (ascii_of_nat 10) "")%string in
  let rev_all := format_cnf_clauses_rev (push_str_rev_chars [] hdr) f in
  rev_chars_to_str_acc EmptyString rev_all.

Definition emit_mc_dimacs_cnf_str
  (ir_tle : toplevel_entities typ (block typ * list (block typ)))
  (elf_str cert_str : string) : string + string :=
  match parse_mc_cert cert_str with
  | inl err => inl err
  | inr mcert =>
      let ir_m := mcfg_of_tle (resolve_module_refs ir_tle) in
      let raw_elf := mc_string_to_bytes elf_str in
      if negb (wf_mc_cert mcert) then inl "malformed mc-cert-v1 certificate"
      else if negb (mcfg_identified_typs_defined ir_m) then
        inl "undefined identified type in IR module"
      else
        match find_unique_defn_by_name (mc_fn_name mcert) (m_definitions ir_m) with
        | None => inl "function definition not found or ambiguous in IR module"
        | Some ir_defn =>
            if negb (check_mc_ir_proto_contract (m_type_defs ir_m) ir_defn mcert) then
              inl "IR prototype, ABI extension, or syntax contract check failed"
            else
              let fn_bare := strip_leading_at (mc_fn_name mcert) in
              match elf64_extract_func raw_elf (mc_arch mcert) (mc_elf_kind mcert) fn_bare with
              | inl err => inl err
              | inr sl =>
                  if negb (Bool.eqb (mc_rvc mcert) (efs_rvc sl)) then
                    inl "ELF64 RVC flag mismatch with mc-cert-v1 rvc mode"
                  else
                    match mc_decode_and_summarize (mc_arch mcert) (mc_rvc mcert) (efs_bytes sl) (mc_args mcert) (mc_ret_width mcert) with
                    | inl err => inl err
                    | inr d_mc =>
                        match flatten_mc_dag_to_expr (mc_ret_width mcert) d_mc with
                        | None => inl "MC DAG flattening failed"
                        | Some e_mc =>
                            let tenv := m_type_defs ir_m in
                            let ir_cfg := convert_typ tenv (df_instrs ir_defn) in
                            let ir_pnames := List.map cert_reg_name (args ir_cfg) in
                            let arg_dtys := defn_arg_dtys tenv ir_defn in
                            let s_pattrs := snd (dc_param_attrs (df_prototype ir_defn)) in
                            let '(seed_vars, mc_init_ctx) :=
                                mc_build_init_ctx (mc_arch mcert) ir_pnames arg_dtys s_pattrs (mc_args mcert) in
                            let allowed := used_src_param_vars ir_cfg ++ seed_vars in
                            match summarize_cfg_dag_with_uas (fun _ => []) false ir_cfg ir_pnames with
                            | None => inl "IR CFG symbolic summarization failed"
                            | Some d_ir =>
                                match src_dag_to_expr (mc_ret_width mcert) d_ir with
                                | None => inl "IR DAG could not be flattened to scalar select tree for CNF emission"
                                | Some e_ir =>
                                    let '(es', et') := prepare_mc_expr_pair mc_init_ctx allowed e_ir e_mc in
                                    if check_expr_refines mc_init_ctx es' et' then
                                      inr ("c ALGEBRAIC_OK" ++ String (ascii_of_nat 10) "")%string
                                    else
                                      let sz := cert_expr_bit_width es' in
                                      let known_vars := collect_free_vars [] es' ++ collect_free_vars [] et' in
                                      let env0 := blast_ub_ctx mc_init_ctx known_vars mc_init_ctx
                                                    (mk_blast_env (init_blast_state 2%positive) [] []) in
                                      let ms_s := if expr_has_freeze es' then Some ([], default_let_expand_budget) else None in
                                      let ms_t := if expr_has_freeze et' then Some ([], default_let_expand_budget) else None in
                                      match blast_cert_expr mc_init_ctx [] ms_s es' env0 with
                                      | None => inl "failed to bit-blast source IR expression"
                                      | Some (src_r, env1) =>
                                          match blast_cert_expr mc_init_ctx [] ms_t et' env1 with
                                          | None => inl "failed to bit-blast target MC expression"
                                          | Some (tgt_r, env2) =>
                                              let '(cex_lit, st5) := blast_refinement_cex_opt_gates sz lit_true src_r tgt_r (be_st env2) in
                                              let st_final := add_clauses [[cex_lit]] st5 in
                                              inr (format_dimacs_cnf (Pos.pred (bs_next_var st_final)) (bs_cnf st_final))
                                          end
                                      end
                                end
                            end
                        end
                    end
              end
        end
  end.

