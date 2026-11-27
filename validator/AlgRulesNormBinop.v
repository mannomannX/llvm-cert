(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Source UB Context & Binop Normalization ([CertValidator.AlgRulesNormBinop])

    Purpose:
      Defines source UB assumption semantics ([ub_ctx], [ub_ctx_holds]),
      guaranteed-definedness checks ([expr_guaranteed_defined]), constant
      folding, signed range bounds, and binop normalization ([norm_binop_step]).

    Trust Contract & Fail-Closed Boundary:
      Sound semantic analyzer and normalizer; [expr_guaranteed_defined_sound]
      and [norm_binop_step_*] guarantee that flag stripping and algebraic
      rewrites preserve or refine source evaluation under [ub_ctx_holds].

    Assumptions:
      Depends on Stdlib, Vellvm ([Syntax.*], [Numeric.*], [Semantics.*]),
      [CertValidator.common.CoreTactics], and [LratCore]/[AigGates]/[CertFormatAst]/[AlgRulesEval].

    Section Outline:
      6. Source UB Context, Algebraic Normalization & Directional Refinement
      (6.1 Guaranteed Non-Poison & UB-Free Analysis; 6.2 Constant Folding/Binop). *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.String
  List
  Bool
  Lia.
Import ListNotations.

From Vellvm Require Import
  Utils
  Syntax.LLVMAst
  Syntax.AstLib
  Syntax.DynamicTypes
  Numeric.Integers
  Numeric.Zbits
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.Operations.Compare
  Semantics.Operations.Conversion
  Semantics.Operations.Select.

From CertValidator.common Require Import
  CoreTactics.

From CertValidator Require Import
  LratCore
  AigGates
  CertFormatAst
  AlgRulesEval.
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


#[local] Opaque default_let_expand_budget norm_let_expand_budget.

(** ** 6. Source UB Context, Algebraic Normalization & Directional Refinement *)

Definition ub_ctx : Type := list ub_assumption.

Definition ub_assumption_holds {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle) (ua : ub_assumption) : Prop :=
  match ua with
  | UBA_ParamNoUndef param _ =>
      forall dv, penv param = Some dv -> dv <> DVALUE_Base DVALUE_Poison
  | UBA_PtrNonNull param =>
      forall dv, penv param = Some dv -> dv <> DVALUE_Base DVALUE_Poison
  | UBA_PtrDereferenceable param _ =>
      forall dv, penv param = Some dv -> dv <> DVALUE_Base DVALUE_Poison
  | UBA_PtrAligned param align =>
      forall dv, penv param = Some dv ->
        dv <> DVALUE_Base DVALUE_Poison /\
        (forall w (iv : @Integers.bit_int w),
           dv = DVALUE_Base (@DVALUE_I Pa w iv) ->
           Z.divide (Z.of_N align) (@Integers.modulus w) ->
           align = 0%N \/ (@Integers.unsigned w iv mod Z.of_N align = 0)%Z)
  | UBA_DivisorNonZero div_e =>
      exists w (i : @Integers.bit_int w),
        eval_closed_cert_expr penv foracle (expand_lets div_e) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa w i)) /\
        (@Integers.unsigned w i <> 0)%Z
  | UBA_SignedDivNoOverflow lhs_e rhs_e =>
      forall w (il ir : @Integers.bit_int w),
        eval_closed_cert_expr penv foracle (expand_lets lhs_e) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa w il)) ->
        eval_closed_cert_expr penv foracle (expand_lets rhs_e) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa w ir)) ->
        ~ (@Integers.signed w il = @Integers.min_signed w /\
           @Integers.signed w ir = (-1)%Z)
  | UBA_BranchCondDefined cond_e =>
      forall v,
        eval_closed_cert_expr penv foracle (expand_lets cond_e) = raise_ret v ->
        v <> DVALUE_Base DVALUE_Poison
  | UBA_UnreachableEliminated => False
  | UBA_LoadNoUndef slot _ =>
      forall dv, penv slot = Some dv -> dv <> DVALUE_Base DVALUE_Poison
  end.

Definition ub_ctx_holds {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle) (ctx : ub_ctx) : Prop :=
  Forall (ub_assumption_holds penv foracle) ctx.

Definition match_expanded_bounded (d e : cert_expr) : bool :=
  match expand_lets_fueled default_let_expand_budget d with
  | Some ed => cert_expr_eqb ed e
  | None => false
  end.

Lemma match_expanded_bounded_eq : forall d e,
  match_expanded_bounded d e = true -> expand_lets d = e.
Proof.
  intros d e H; unfold match_expanded_bounded in H.
  destruct (expand_lets_fueled default_let_expand_budget d) as [ed |] eqn:Ef;
    [| discriminate H].
  apply cert_expr_eqb_eq in H; subst ed.
  symmetry; exact (expand_lets_fueled_eq default_let_expand_budget d e Ef).
Qed.

Fixpoint ctx_has_unreachable (ctx : ub_ctx) {struct ctx} : bool :=
  match ctx with
  | [] => false
  | UBA_UnreachableEliminated :: _ => true
  | _ :: rest => ctx_has_unreachable rest
  end.

Lemma ctx_has_unreachable_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle ctx,
    ctx_has_unreachable ctx = true ->
    ub_ctx_holds penv foracle ctx ->
    False.
Proof.
  intros Pa penv foracle ctx H Hctx.
  induction Hctx as [| ua rest Hua Hrest IH]; [discriminate H |].
  destruct ua; cbn in H; try exact (IH H); exact Hua.
Qed.

Fixpoint ctx_has_param_noundef (ctx : ub_ctx) (nm : string) (w : positive)
  {struct ctx} : bool :=
  match ctx with
  | [] => false
  | UBA_ParamNoUndef p pw :: rest =>
      (String.eqb p nm && Pos.eqb pw w) || ctx_has_param_noundef rest nm w
  | _ :: rest => ctx_has_param_noundef rest nm w
  end.

Lemma ctx_has_param_noundef_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle ctx nm w dv,
    ctx_has_param_noundef ctx nm w = true ->
    ub_ctx_holds penv foracle ctx ->
    penv nm = Some dv ->
    dv <> DVALUE_Base DVALUE_Poison.
Proof.
  intros Pa penv foracle ctx nm w dv H Hctx Hpm.
  induction Hctx as [| ua rest Hua Hrest IH]; [discriminate H |].
  destruct ua; cbn in H; try exact (IH H).
  apply orb_true_iff in H as [Hhere | Hlater]; [| exact (IH Hlater)].
  apply andb_true_iff in Hhere as [Hp _]; apply String.eqb_eq in Hp; subst.
  exact (Hua dv Hpm).
Qed.

Fixpoint ctx_has_var_nonpoison (ctx : ub_ctx) (nm : string) (w : positive)
  {struct ctx} : bool :=
  match ctx with
  | [] => false
  | UBA_ParamNoUndef p pw :: rest
  | UBA_LoadNoUndef p pw :: rest =>
      (String.eqb p nm && Pos.eqb pw w) || ctx_has_var_nonpoison rest nm w
  | UBA_PtrNonNull p :: rest
  | UBA_PtrDereferenceable p _ :: rest
  | UBA_PtrAligned p _ :: rest =>
      String.eqb p nm || ctx_has_var_nonpoison rest nm w
  | _ :: rest => ctx_has_var_nonpoison rest nm w
  end.

Lemma ctx_has_var_nonpoison_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle ctx nm w dv,
    ctx_has_var_nonpoison ctx nm w = true ->
    ub_ctx_holds penv foracle ctx ->
    penv nm = Some dv ->
    dv <> DVALUE_Base DVALUE_Poison.
Proof.
  intros Pa penv foracle ctx nm w dv H Hctx Hpm.
  induction Hctx as [| ua rest Hua Hrest IH]; [discriminate H |].
  destruct ua; cbn in H; try exact (IH H);
    apply orb_true_iff in H as [Hhere | Hlater]; try exact (IH Hlater).
  - apply andb_true_iff in Hhere as [Hp _]; apply String.eqb_eq in Hp; subst.
    exact (Hua dv Hpm).
  - apply String.eqb_eq in Hhere; subst; exact (Hua dv Hpm).
  - apply String.eqb_eq in Hhere; subst; exact (proj1 (Hua dv Hpm)).
  - apply String.eqb_eq in Hhere; subst; exact (Hua dv Hpm).
  - apply andb_true_iff in Hhere as [Hp _]; apply String.eqb_eq in Hp; subst.
    exact (Hua dv Hpm).
Qed.

Fixpoint ctx_ptr_low_bit_zero
  (ctx : ub_ctx) (nm : string) (w : positive) (k : nat) {struct ctx} : bool :=
  match ctx with
  | [] => false
  | UBA_PtrAligned p align :: rest =>
      (String.eqb p nm &&
       (0 <? Z.of_N align)%Z &&
       (@Integers.modulus w mod Z.of_N align =? 0)%Z &&
       (Z.of_N align mod (2 ^ Z.of_nat (S k)) =? 0)%Z) ||
      ctx_ptr_low_bit_zero rest nm w k
  | _ :: rest => ctx_ptr_low_bit_zero rest nm w k
  end.

Lemma ctx_ptr_low_bit_zero_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle ctx nm w k (iv : @Integers.bit_int w),
    ctx_ptr_low_bit_zero ctx nm w k = true ->
    ub_ctx_holds penv foracle ctx ->
    penv nm = Some (DVALUE_Base (@DVALUE_I Pa w iv)) ->
    Z.testbit (@Integers.unsigned w iv) (Z.of_nat k) = false.
Proof.
  intros Pa penv foracle ctx nm w k iv H Hctx Hpm.
  induction Hctx as [| ua rest Hua Hrest IH]; [discriminate H |].
  destruct ua as [| | p align | | | | | |]; cbn [ctx_ptr_low_bit_zero] in H; try exact (IH H).
  apply orb_true_iff in H as [Hhere | Hlater]; [| exact (IH Hlater)].
  rewrite !andb_true_iff in Hhere.
  destruct Hhere as (((Hp & Ha_pos) & Hmod_m) & Hmod_p2).
  apply String.eqb_eq in Hp; subst p.
  apply Z.ltb_lt in Ha_pos.
  apply Z.eqb_eq in Hmod_m; apply Z.eqb_eq in Hmod_p2.
  assert (Hdiv_m : Z.divide (Z.of_N align) (@Integers.modulus w)).
  { exists (@Integers.modulus w / Z.of_N align)%Z.
    pose proof (Z_div_mod_eq_full (@Integers.modulus w) (Z.of_N align)) as Hdm.
    rewrite Hmod_m, Z.add_0_r, Z.mul_comm in Hdm; exact Hdm. }
  destruct (proj2 (Hua _ Hpm) w iv eq_refl Hdiv_m) as [Hz | Hu_mod];
    [subst align; cbn in Ha_pos; lia |].
  set (p2 := (2 ^ Z.of_nat (S k))%Z) in *.
  assert (Hp2_pos : (0 < p2)%Z) by (unfold p2; apply Z.pow_pos_nonneg; lia).
  pose proof (Z_div_mod_eq_full (@Integers.unsigned w iv) (Z.of_N align)) as Hdu.
  pose proof (Z_div_mod_eq_full (Z.of_N align) p2) as Hda.
  rewrite Hu_mod, Z.add_0_r in Hdu.
  rewrite Hmod_p2, Z.add_0_r in Hda.
  assert (Hu_p2_mod : (@Integers.unsigned w iv mod p2 = 0)%Z).
  { set (qu := (@Integers.unsigned w iv / Z.of_N align)%Z) in Hdu |- *.
    set (qa := (Z.of_N align / p2)%Z) in Hda |- *.
    symmetry; apply (Stdlib.ZArith.Zdiv.Zmod_unique
      (@Integers.unsigned w iv) p2 (qa * qu) 0);
      [lia | rewrite Hdu, Hda; ring]. }
  assert (Hp2_twop : p2 = two_p (Z.of_nat (S k))).
  { unfold p2; rewrite <- two_power_nat_equiv, two_power_nat_two_p; reflexivity. }
  pose proof (Ztestbit_mod_two_p (Z.of_nat (S k)) (@Integers.unsigned w iv) (Z.of_nat k)
                (Nat2Z.is_nonneg (S k)) (Nat2Z.is_nonneg k)) as Htb.
  rewrite <- Hp2_twop, Hu_p2_mod, Z.testbit_0_l in Htb.
  destruct (zlt (Z.of_nat k) (Z.of_nat (S k))); [symmetry; exact Htb | lia].
Qed.

Fixpoint ctx_has_divisor_nonzero (ctx : ub_ctx) (e : cert_expr) {struct ctx} : bool :=
  match ctx with
  | [] => false
  | UBA_DivisorNonZero d :: rest =>
      match_expanded_bounded d e || ctx_has_divisor_nonzero rest e
  | _ :: rest => ctx_has_divisor_nonzero rest e
  end.

Lemma ctx_has_divisor_nonzero_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle ctx e,
    ctx_has_divisor_nonzero ctx e = true ->
    ub_ctx_holds penv foracle ctx ->
    exists w (i : @Integers.bit_int w),
      eval_closed_cert_expr penv foracle e =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w i)) /\
      (@Integers.unsigned w i <> 0)%Z.
Proof.
  intros Pa penv foracle ctx e H Hctx.
  induction Hctx as [| ua rest Hua Hrest IH]; [discriminate H |].
  destruct ua; cbn in H; try exact (IH H).
  apply orb_true_iff in H as [Hhere | Hlater]; [| exact (IH Hlater)].
  apply match_expanded_bounded_eq in Hhere; subst e; exact Hua.
Qed.

Fixpoint ctx_has_branch_cond_defined (ctx : ub_ctx) (e : cert_expr) {struct ctx} : bool :=
  match ctx with
  | [] => false
  | UBA_BranchCondDefined c :: rest =>
      match_expanded_bounded c e || ctx_has_branch_cond_defined rest e
  | _ :: rest => ctx_has_branch_cond_defined rest e
  end.

Lemma ctx_has_branch_cond_defined_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle ctx e v,
    ctx_has_branch_cond_defined ctx e = true ->
    ub_ctx_holds penv foracle ctx ->
    eval_closed_cert_expr penv foracle e = raise_ret v ->
    v <> DVALUE_Base DVALUE_Poison.
Proof.
  intros Pa penv foracle ctx e v H Hctx Hev.
  induction Hctx as [| ua rest Hua Hrest IH]; [discriminate H |].
  destruct ua; cbn in H; try exact (IH H).
  apply orb_true_iff in H as [Hhere | Hlater]; [| exact (IH Hlater)].
  apply match_expanded_bounded_eq in Hhere; subst e; exact (Hua v Hev).
Qed.

(** *** 6.1 Guaranteed Non-Poison & UB-Free Expression Analysis *)

Lemma ub_free_branch_cond_defined_sound :
  forall {Pa : Params} ctx e (penv : param_env Pa) (foracle : freeze_oracle),
    ub_free_expr e && ctx_has_branch_cond_defined ctx e = true ->
    wt_cert_expr [] e = true ->
    wf_param_env_for (collect_free_vars [] e) penv ->
    ub_ctx_holds penv foracle ctx ->
    ub_free_expr e = true /\
    exists i : @Integers.bit_int (cert_expr_bit_width e),
      eval_closed_cert_expr penv foracle e =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (cert_expr_bit_width e) i)).
Proof.
  intros Pa ctx e penv foracle Htop Hwt Hpenv Hctx.
  apply andb_true_iff in Htop as [Hub Hbr].
  split; [exact Hub |].
  destruct (ub_free_expr_eval_ret e [] penv [] foracle Hub Hwt wf_let_val_env_nil Hpenv)
    as [ve [Hev Hwfve]].
  destruct Hwfve as [Hpsn | [iv ->]]; [| exists iv; exact Hev].
  subst ve; exfalso.
  exact (ctx_has_branch_cond_defined_sound penv foracle ctx e _ Hbr Hctx Hev eq_refl).
Qed.

Fixpoint expr_guaranteed_defined (ctx : ub_ctx) (e : cert_expr) {struct e} : bool :=
  match e with
  | CE_BvConst _ _ => true
  | CE_Poison _ | CE_Let _ _ => false
  | CE_Var nm w =>
      ctx_has_var_nonpoison ctx nm w || ctx_has_branch_cond_defined ctx (CE_Var nm w)
  | CE_Freeze _ o =>
      ub_free_expr o
  | CE_BinOp op w fl l r =>
      (ub_free_expr (CE_BinOp op w fl l r) &&
       ctx_has_branch_cond_defined ctx (CE_BinOp op w fl l r)) ||
      (negb (is_div_or_rem_op op) &&
       negb (is_shift_op op) &&
       cert_binop_flags_eqb fl no_binop_flags &&
       expr_guaranteed_defined ctx l &&
       expr_guaranteed_defined ctx r)
  | CE_ICmp pr ss w l r =>
      (ub_free_expr (CE_ICmp pr ss w l r) &&
       ctx_has_branch_cond_defined ctx (CE_ICmp pr ss w l r)) ||
      (negb ss &&
       expr_guaranteed_defined ctx l &&
       expr_guaranteed_defined ctx r)
  | CE_Cast k fw tw fl o =>
      (ub_free_expr (CE_Cast k fw tw fl o) &&
       ctx_has_branch_cond_defined ctx (CE_Cast k fw tw fl o)) ||
      match k with
      | CCK_ZExt => negb (ccf_nneg fl) && expr_guaranteed_defined ctx o
      | CCK_SExt => expr_guaranteed_defined ctx o
      | CCK_Trunc => negb (ccf_nuw fl) && negb (ccf_nsw fl) && expr_guaranteed_defined ctx o
      end
  | CE_Select w c t f =>
      (ub_free_expr (CE_Select w c t f) &&
       ctx_has_branch_cond_defined ctx (CE_Select w c t f)) ||
      (expr_guaranteed_defined ctx c &&
       expr_guaranteed_defined ctx t &&
       expr_guaranteed_defined ctx f)
  end.

Lemma expr_guaranteed_defined_sound :
  forall {Pa : Params} ctx e (penv : param_env Pa) (foracle : freeze_oracle),
    expr_guaranteed_defined ctx e = true ->
    wt_cert_expr [] e = true ->
    wf_param_env_for (collect_free_vars [] e) penv ->
    ub_ctx_holds penv foracle ctx ->
    ub_free_expr e = true /\
    exists i : @Integers.bit_int (cert_expr_bit_width e),
      eval_closed_cert_expr penv foracle e =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (cert_expr_bit_width e) i)).
Proof.
  intros Pa ctx e.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o _
    | bs body _ _ ] using cert_expr_ind_nested;
    intros penv foracle Hdef Hwt Hpenv Hctx;
    try discriminate Hdef.
  - split; [reflexivity | eexists; reflexivity].
  - cbn [expr_guaranteed_defined] in Hdef.
    cbn [collect_free_vars string_in_list] in Hpenv.
    destruct (Hpenv nm w (or_introl eq_refl)) as [dv [Hpm Hwfv]].
    assert (Hev : eval_closed_cert_expr penv foracle (CE_Var nm w) = raise_ret dv).
    { unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val].
      rewrite Hpm; exact (check_scalar_width_ok w dv Hwfv). }
    split; [reflexivity |].
    destruct Hwfv as [Hpsn | [iv ->]]; [| exists iv; exact Hev].
    subst dv; exfalso.
    apply orb_true_iff in Hdef as [Hnu | Hbr].
    + exact (ctx_has_var_nonpoison_sound penv foracle ctx nm w _ Hnu Hctx Hpm eq_refl).
    + exact (ctx_has_branch_cond_defined_sound penv foracle ctx _ _ Hbr Hctx Hev eq_refl).
  - cbn [expr_guaranteed_defined] in Hdef.
    apply orb_true_iff in Hdef as [Htop | Hdef];
      [exact (ub_free_branch_cond_defined_sound ctx _ penv foracle Htop Hwt Hpenv Hctx) |].
    cbn [wt_cert_expr collect_free_vars cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hdef; rewrite !andb_true_iff in Hwt.
    destruct Hdef as ((((Hndiv & Hnsh) & Hfl) & Hdl) & Hdr).
    destruct Hwt as ((((_ & Hwtl) & Hwtr) & Hwl) & Hwr).
    apply cert_binop_flags_eqb_eq in Hfl; subst fl.
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    assert (Hpl : wf_param_env_for (collect_free_vars [] l) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars [] r) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
    destruct (IHl penv foracle Hdl Hwtl Hpl Hctx) as [Hubl [il Hil]].
    destruct (IHr penv foracle Hdr Hwtr Hpr Hctx) as [Hubr [ir Hir]].
    split; [cbn; rewrite Hndiv, Hubl, Hubr; reflexivity |].
    revert il Hil; rewrite Hwl; intros il Hil.
    revert ir Hir; rewrite Hwr; intros ir Hir.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil, Hir; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct op; cbn in Hndiv, Hnsh; try discriminate;
      unfold cert_to_ibinop, eval_int_op; cbn;
      try (eexists; reflexivity).
    destruct (Pos.eqb w 1); cbn; eexists; reflexivity.
  - cbn [expr_guaranteed_defined] in Hdef.
    apply orb_true_iff in Hdef as [Htop | Hdef];
      [exact (ub_free_branch_cond_defined_sound ctx _ penv foracle Htop Hwt Hpenv Hctx) |].
    cbn [wt_cert_expr collect_free_vars cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hdef; rewrite !andb_true_iff in Hwt.
    destruct Hdef as ([Hss Hdl] & Hdr); destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr).
    apply negb_true_iff in Hss; subst ss.
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    assert (Hpl : wf_param_env_for (collect_free_vars [] l) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars [] r) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
    destruct (IHl penv foracle Hdl Hwtl Hpl Hctx) as [Hubl [il Hil]].
    destruct (IHr penv foracle Hdr Hwtr Hpr Hctx) as [Hubr [ir Hir]].
    split; [cbn; rewrite Hubl, Hubr; reflexivity |].
    revert il Hil; rewrite Hwl; intros il Hil.
    revert ir Hir; rewrite Hwr; intros ir Hir.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil, Hir; cbn [eou_bind].
    unfold eval_icmp; rewrite eval_icmp_base_same_width.
    destruct pr; unfold cert_to_icmp, eval_int_icmp; cbn;
      match goal with |- context [if ?b then _ else _] => destruct b end;
      eexists; reflexivity.
  - cbn [expr_guaranteed_defined] in Hdef.
    apply orb_true_iff in Hdef as [Htop | Hdef];
      [exact (ub_free_branch_cond_defined_sound ctx _ penv foracle Htop Hwt Hpenv Hctx) |].
    cbn [wt_cert_expr collect_free_vars cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((Hk & Hwto) & Hwo).
    apply Pos.eqb_eq in Hwo.
    destruct k.
    + apply andb_true_iff in Hdef as [Hnn Hdo]; apply negb_true_iff in Hnn.
      destruct (IHo penv foracle Hdo Hwto Hpenv Hctx) as [Hubo [io Hio]].
      split; [exact Hubo |].
      revert io Hio; rewrite Hwo; intros io Hio.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hio; cbn [eou_bind].
      rewrite !andb_true_iff in Hk; destruct Hk as ([Hlt _] & _).
      cbn; rewrite Pos.eqb_refl, Hlt, Hnn; cbn; eexists; reflexivity.
    + destruct (IHo penv foracle Hdef Hwto Hpenv Hctx) as [Hubo [io Hio]].
      split; [exact Hubo |].
      revert io Hio; rewrite Hwo; intros io Hio.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hio; cbn [eou_bind].
      rewrite !andb_true_iff in Hk; destruct Hk as (([Hlt _] & _) & _).
      cbn; rewrite Pos.eqb_refl, Hlt; cbn; eexists; reflexivity.
    + rewrite !andb_true_iff in Hdef; destruct Hdef as ([Hnuw Hnsw] & Hdo).
      apply negb_true_iff in Hnuw; apply negb_true_iff in Hnsw.
      destruct (IHo penv foracle Hdo Hwto Hpenv Hctx) as [Hubo [io Hio]].
      split; [exact Hubo |].
      revert io Hio; rewrite Hwo; intros io Hio.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hio; cbn [eou_bind].
      apply andb_true_iff in Hk as [Hlt _].
      cbn; rewrite Pos.eqb_refl, Hlt, Hnuw, Hnsw; cbn; eexists; reflexivity.
  - cbn [expr_guaranteed_defined] in Hdef.
    apply orb_true_iff in Hdef as [Htop | Hdef];
      [exact (ub_free_branch_cond_defined_sound ctx _ penv foracle Htop Hwt Hpenv Hctx) |].
    cbn [wt_cert_expr collect_free_vars cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hdef; rewrite !andb_true_iff in Hwt.
    destruct Hdef as ([Hdc Hdt] & Hdf).
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hwc) & Hwt0) & Hwf0).
    apply Pos.eqb_eq in Hwc; apply Pos.eqb_eq in Hwt0; apply Pos.eqb_eq in Hwf0.
    assert (Hpc : wf_param_env_for (collect_free_vars [] c) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpt : wf_param_env_for (collect_free_vars [] t) penv).
    { intros x wx Hx.
      apply Hpenv, in_app_iff; right; apply in_app_iff; left; exact Hx. }
    assert (Hpf : wf_param_env_for (collect_free_vars [] f) penv).
    { intros x wx Hx.
      apply Hpenv, in_app_iff; right; apply in_app_iff; right; exact Hx. }
    destruct (IHc penv foracle Hdc Hwtc Hpc Hctx) as [Hubc [ic Hic]].
    destruct (IHt penv foracle Hdt Hwtt Hpt Hctx) as [Hubt [it Hit]].
    destruct (IHf penv foracle Hdf Hwtf Hpf Hctx) as [Hubf [if0 Hif]].
    split; [cbn; rewrite Hubc, Hubt, Hubf; reflexivity |].
    revert ic Hic; rewrite Hwc; intros ic Hic.
    revert it Hit; rewrite Hwt0; intros it Hit.
    revert if0 Hif; rewrite Hwf0; intros if0 Hif.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hic, Hit, Hif; cbn.
    destruct (@Integers.unsigned 1 ic =? 1)%Z; eexists; reflexivity.
  - cbn [expr_guaranteed_defined wt_cert_expr collect_free_vars cert_expr_bit_width] in *.
    apply andb_true_iff in Hwt as [Hwto Hwo]; apply Pos.eqb_eq in Hwo.
    split; [exact Hdef |].
    destruct (ub_free_expr_eval_ret o [] penv [] foracle Hdef Hwto wf_let_val_env_nil Hpenv)
      as [vo [Hvo Hwfo]].
    rewrite Hwo in Hwfo.
    unfold eval_closed_cert_expr; cbn [eval_cert_expr]; rewrite Hvo; cbn [eou_bind].
    destruct Hwfo as [-> | [io ->]]; eexists; reflexivity.
Qed.

(** *** 6.2 Verified Constant Folding & Algebraic Normalization *)

Definition mk_bv_const (w : positive) (i : @Integers.bit_int w) : cert_expr :=
  CE_BvConst w (Z.to_N (@Integers.unsigned w i)).

Lemma repr_of_N_to_N_unsigned : forall w (r : @Integers.bit_int w),
  @Integers.repr w (Z.of_N (Z.to_N (@Integers.unsigned w r))) = r.
Proof.
  intros w r.
  pose proof (@Integers.unsigned_range w r) as [Hlo _].
  rewrite (Z2N.id _ Hlo), (@Integers.repr_unsigned w r); reflexivity.
Qed.

Lemma alg_shl_zero : forall w (x : @Integers.bit_int w),
  @Integers.shl w x (@Integers.zero w) = x.
Proof.
  intros w x; unfold Integers.shl; rewrite Integers.unsigned_zero, Z.shiftl_0_r.
  apply Integers.repr_unsigned.
Qed.

Lemma alg_shru_zero : forall w (x : @Integers.bit_int w),
  @Integers.shru w x (@Integers.zero w) = x.
Proof.
  intros w x; unfold Integers.shru; rewrite Integers.unsigned_zero, Z.shiftr_0_r.
  apply Integers.repr_unsigned.
Qed.

Lemma alg_shr_zero : forall w (x : @Integers.bit_int w),
  @Integers.shr w x (@Integers.zero w) = x.
Proof.
  intros w x; unfold Integers.shr; rewrite Integers.unsigned_zero, Z.shiftr_0_r.
  apply Integers.repr_signed.
Qed.

Definition fold_const_binop
  (op : cert_binop) (w : positive) (fl : cert_binop_flags) (v1 v2 : N)
  : option cert_expr :=
  let x := @Integers.repr w (Z.of_N v1) in
  let y := @Integers.repr w (Z.of_N v2) in
  match op with
  | CB_Add =>
      Some (if (cbf_nuw fl && @Integers.eq w (@Integers.add_carry w x y (@Integers.zero w)) (@Integers.one w)) ||
               (cbf_nsw fl && @Integers.eq w (@Integers.add_overflow w x y (@Integers.zero w)) (@Integers.one w))
            then CE_Poison w
            else mk_bv_const w (@Integers.add w x y))
  | CB_Sub =>
      Some (if (cbf_nuw fl && @Integers.eq w (@Integers.sub_borrow w x y (@Integers.zero w)) (@Integers.one w)) ||
               (cbf_nsw fl && @Integers.eq w (@Integers.sub_overflow w x y (@Integers.zero w)) (@Integers.one w))
            then CE_Poison w
            else mk_bv_const w (@Integers.sub w x y))
  | CB_Mul =>
      Some (if Pos.eqb w 1%positive
            then mk_bv_const w (@Integers.mul w x y)
            else
              let res := @Integers.mul w x y in
              let res_u' := (@Integers.unsigned w x * @Integers.unsigned w y)%Z in
              let res_s' := (@Integers.signed w x * @Integers.signed w y)%Z in
              if (cbf_nuw fl && (res_u' >? @Integers.unsigned w res)%Z) ||
                 (cbf_nsw fl && ((@Integers.min_signed w >? res_s')%Z ||
                                 (res_s' >? @Integers.max_signed w)%Z))
              then CE_Poison w
              else mk_bv_const w res)
  | CB_Shl =>
      Some (if (@Integers.unsigned w y >=? Z.pos w)%Z
            then CE_Poison w
            else
              let res := @Integers.shl w x y in
              let res_u := @Integers.unsigned w res in
              let res_u' := Z.shiftl (@Integers.unsigned w x) (@Integers.unsigned w y) in
              if cbf_nuw fl && (res_u' >? res_u)%Z
              then CE_Poison w
              else if cbf_nsw fl
                   then
                     let nres := @Integers.negative w res in
                     if negb (Z.shiftr (@Integers.unsigned w x) (Z.pos w - @Integers.unsigned w y) =?
                              @Integers.unsigned w nres * (Z.pow 2 (@Integers.unsigned w y) - 1))%Z
                     then CE_Poison w
                     else mk_bv_const w res
                   else mk_bv_const w res)
  | CB_UDiv =>
      if (@Integers.unsigned w y =? 0)%Z then None
      else Some (if cbf_exact fl && negb ((@Integers.unsigned w x mod @Integers.unsigned w y =? 0)%Z)
                 then CE_Poison w
                 else mk_bv_const w (@Integers.divu w x y))
  | CB_SDiv =>
      if (@Integers.signed w y =? 0)%Z then None
      else if ((@Integers.min_signed w =? @Integers.signed w x)%Z && (@Integers.signed w y =? -1)%Z)
           then None
           else Some (if cbf_exact fl && negb ((@Integers.signed w x mod @Integers.signed w y =? 0)%Z)
                      then CE_Poison w
                      else mk_bv_const w (@Integers.divs w x y))
  | CB_LShr =>
      Some (if (@Integers.unsigned w y >=? Z.pos w)%Z
            then CE_Poison w
            else if cbf_exact fl && negb ((@Integers.unsigned w x mod Z.pow 2 (@Integers.unsigned w y) =? 0)%Z)
                 then CE_Poison w
                 else mk_bv_const w (@Integers.shru w x y))
  | CB_AShr =>
      Some (if (@Integers.unsigned w y >=? Z.pos w)%Z
            then CE_Poison w
            else if cbf_exact fl && negb ((@Integers.unsigned w x mod Z.pow 2 (@Integers.unsigned w y) =? 0)%Z)
                 then CE_Poison w
                 else mk_bv_const w (@Integers.shr w x y))
  | CB_URem =>
      if (@Integers.unsigned w y =? 0)%Z then None
      else Some (mk_bv_const w (@Integers.modu w x y))
  | CB_SRem =>
      if (@Integers.signed w y =? 0)%Z then None
      else if ((@Integers.min_signed w =? @Integers.signed w x)%Z && (@Integers.signed w y =? -1)%Z)
           then None
           else Some (mk_bv_const w (@Integers.mods w x y))
  | CB_And => Some (mk_bv_const w (@Integers.and w x y))
  | CB_Or =>
      Some (if cbf_disjoint fl
            then if @Integers.eq w (@Integers.or w x y) (@Integers.xor w x y)
                 then mk_bv_const w (@Integers.or w x y)
                 else CE_Poison w
            else mk_bv_const w (@Integers.or w x y))
  | CB_Xor => Some (mk_bv_const w (@Integers.xor w x y))
  end.

Lemma fold_const_binop_sound :
  forall {Pa : Params} op w fl v1 v2 out (penv : param_env Pa) foracle,
    fold_const_binop op w fl v1 v2 = Some out ->
    cert_expr_bit_width out = w /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    collect_free_vars [] out = [] /\
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp op w fl (CE_BvConst w v1) (CE_BvConst w v2)))
      (eval_closed_cert_expr penv foracle out).
Proof.
  intros Pa op w fl v1 v2 out penv foracle Hfold.
  unfold eval_closed_cert_expr; cbn [eval_cert_expr eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  destruct op; cbn [fold_const_binop] in Hfold;
    repeat match type of Hfold with
           | (if ?b then None else _) = Some _ =>
               destruct b eqn:?; [discriminate Hfold |]
           end;
    inversion Hfold; subst out; clear Hfold;
    unfold cert_to_ibinop, eval_int_op; cbn - [andb orb]; rewrite ?andb_true_r;
    repeat match goal with
           | H : ?b = false |- context [if ?b then _ else _] => rewrite H
           | |- context [if ?b then _ else _] => destruct b
           end;
    unfold mk_bv_const, dvp; cbn;
    repeat split; try reflexivity;
    try (rewrite repr_of_N_to_N_unsigned; reflexivity).
Qed.

Definition fold_const_icmp (pr : cert_icmp_pred) (ss : bool) (w : positive) (v1 v2 : N)
  : cert_expr :=
  let x := @Integers.repr w (Z.of_N v1) in
  let y := @Integers.repr w (Z.of_N v2) in
  let same_s :=
      ((@Integers.cmp w Integers.Cge x (@Integers.zero w) &&
        @Integers.cmp w Integers.Cge y (@Integers.zero w)) ||
       (@Integers.cmp w Integers.Clt x (@Integers.zero w) &&
        @Integers.cmp w Integers.Clt y (@Integers.zero w))) in
  if ss && negb same_s
  then CE_Poison 1%positive
  else
    let res_b :=
        match pr with
        | CIP_Eq  => @Integers.cmpu w Integers.Ceq x y
        | CIP_Ne  => @Integers.cmpu w Integers.Cne x y
        | CIP_Ugt => @Integers.cmpu w Integers.Cgt x y
        | CIP_Uge => @Integers.cmpu w Integers.Cge x y
        | CIP_Ult => @Integers.cmpu w Integers.Clt x y
        | CIP_Ule => @Integers.cmpu w Integers.Cle x y
        | CIP_Sgt => @Integers.cmp w Integers.Cgt x y
        | CIP_Sge => @Integers.cmp w Integers.Cge x y
        | CIP_Slt => @Integers.cmp w Integers.Clt x y
        | CIP_Sle => @Integers.cmp w Integers.Cle x y
        end in
    CE_BvConst 1%positive (if res_b then 1%N else 0%N).

Lemma fold_const_icmp_sound :
  forall {Pa : Params} pr ss w v1 v2 (penv : param_env Pa) foracle,
    let out := fold_const_icmp pr ss w v1 v2 in
    cert_expr_bit_width out = 1%positive /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    collect_free_vars [] out = [] /\
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_ICmp pr ss w (CE_BvConst w v1) (CE_BvConst w v2)))
      (eval_closed_cert_expr penv foracle out).
Proof.
  intros Pa pr ss w v1 v2 penv foracle; cbn zeta.
  unfold eval_closed_cert_expr; cbn [eval_cert_expr eou_bind].
  unfold eval_icmp; rewrite eval_icmp_base_same_width.
  unfold fold_const_icmp; destruct pr; unfold cert_to_icmp, eval_int_icmp, dvp; cbn;
    (destruct (ss && _); cbn;
     [repeat split; reflexivity
     | match goal with |- context [if ?c then _ else _] => destruct c end;
       cbn; repeat split; try reflexivity;
       try (rewrite repr_one_N; reflexivity);
       try (rewrite repr_zero_N; reflexivity)]).
Qed.

Definition fold_const_cast
  (k : cert_cast_kind) (fw tw : positive) (fl : cert_cast_flags) (val : N)
  : cert_expr :=
  let i1 := @Integers.repr fw (Z.of_N val) in
  match k with
  | CCK_ZExt =>
      if ccf_nneg fl && (@Integers.signed fw i1 <? 0)%Z
      then CE_Poison tw
      else mk_bv_const tw (@Integers.repr tw (@Integers.unsigned fw i1))
  | CCK_SExt =>
      mk_bv_const tw (@Integers.repr tw (@Integers.signed fw i1))
  | CCK_Trunc =>
      let res := @Integers.repr tw (@Integers.unsigned fw i1) in
      if (ccf_nuw fl && negb (Z.eqb (@Integers.unsigned tw res) (@Integers.unsigned fw i1))) ||
         (ccf_nsw fl && negb (Z.eqb (@Integers.signed tw res) (@Integers.signed fw i1)))
      then CE_Poison tw
      else mk_bv_const tw res
  end.

Lemma fold_const_cast_sound :
  forall {Pa : Params} k fw tw fl val (penv : param_env Pa) foracle,
    match k with
    | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg fl) && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg fl)
    end = true ->
    let out := fold_const_cast k fw tw fl val in
    cert_expr_bit_width out = tw /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    collect_free_vars [] out = [] /\
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_Cast k fw tw fl (CE_BvConst fw val)))
      (eval_closed_cert_expr penv foracle out).
Proof.
  intros Pa k fw tw fl val penv foracle Hk; cbn zeta.
  unfold eval_closed_cert_expr; cbn [eval_cert_expr eou_bind].
  destruct k; cbn - [andb Pos.ltb Pos.eqb] in Hk |- *; rewrite !andb_true_iff in Hk.
  - destruct Hk as ([Hlt _] & _); rewrite Pos.eqb_refl, Hlt; cbn.
    destruct (ccf_nneg fl && (@Integers.signed fw (@Integers.repr fw (Z.of_N val)) <? 0)%Z);
      unfold mk_bv_const; cbn; repeat split; try reflexivity;
      rewrite repr_of_N_to_N_unsigned; reflexivity.
  - destruct Hk as (([Hlt _] & _) & _); rewrite Pos.eqb_refl, Hlt.
    unfold mk_bv_const; cbn; repeat split; try reflexivity;
      rewrite repr_of_N_to_N_unsigned; reflexivity.
  - destruct Hk as [Hlt _]; rewrite Pos.eqb_refl, Hlt; cbn - [andb orb].
    match goal with |- context [if ?b then _ else _] => destruct b end;
      unfold mk_bv_const; cbn; repeat split; try reflexivity;
      rewrite repr_of_N_to_N_unsigned; reflexivity.
Qed.

Definition is_refl_true_icmp (pr : cert_icmp_pred) : bool :=
  match pr with
  | CIP_Eq | CIP_Ule | CIP_Uge | CIP_Sle | CIP_Sge => true
  | CIP_Ne | CIP_Ult | CIP_Ugt | CIP_Slt | CIP_Sgt => false
  end.

Definition try_fold_const_binop
  (op : cert_binop) (w : positive) (fl : cert_binop_flags)
  (nl nr : cert_expr) : option cert_expr :=
  match nl, nr with
  | CE_BvConst w1 v1, CE_BvConst w2 v2 =>
      if Pos.eqb w1 w && Pos.eqb w2 w
      then fold_const_binop op w fl v1 v2
      else None
  | _, _ => None
  end.

Definition extract_const_expr (w : positive) (e : cert_expr)
  : option (@Integers.bit_int w) :=
  match e with
  | CE_BvConst w' v =>
      if Pos.eqb w' w then Some (@Integers.repr w (Z.of_N v)) else None
  | _ => None
  end.

Lemma extract_const_expr_inv : forall w e ic,
  extract_const_expr w e = Some ic ->
  exists v, e = CE_BvConst w v /\ ic = @Integers.repr w (Z.of_N v).
Proof.
  intros w [w' v | | | | | | | |] ic H; cbn in H; try discriminate H.
  destruct (Pos.eqb w' w) eqn:Ew; [| discriminate H].
  apply Pos.eqb_eq in Ew; inversion H; subst.
  exists v; split; reflexivity.
Qed.

Definition extract_binop_rhs_const
  (op0 : cert_binop) (w : positive) (e : cert_expr)
  : option (cert_expr * @Integers.bit_int w) :=
  match e with
  | CE_BinOp op' w' fl' a c =>
      if cert_binop_eqb op' op0 && Pos.eqb w' w && cert_binop_flags_eqb fl' no_binop_flags
      then match extract_const_expr w c with
           | Some ic => Some (a, ic)
           | None => None
           end
      else None
  | _ => None
  end.

Lemma extract_binop_rhs_const_inv : forall op0 w e a ic,
  extract_binop_rhs_const op0 w e = Some (a, ic) ->
  exists v,
    e = CE_BinOp op0 w no_binop_flags a (CE_BvConst w v) /\
    ic = @Integers.repr w (Z.of_N v).
Proof.
  intros op0 w [| | | op' w' fl' a0 c | | | | |] a ic H;
    cbn - [andb cert_binop_eqb Pos.eqb cert_binop_flags_eqb] in H; try discriminate H.
  destruct (cert_binop_eqb op' op0 && Pos.eqb w' w && cert_binop_flags_eqb fl' no_binop_flags)
    eqn:Eok; [| discriminate H].
  rewrite !andb_true_iff in Eok; destruct Eok as ([Hop Hw] & Hfl).
  apply cert_binop_eqb_eq in Hop; apply Pos.eqb_eq in Hw; apply cert_binop_flags_eqb_eq in Hfl.
  destruct (extract_const_expr w c) as [ic0 |] eqn:Ec; [| discriminate H].
  inversion H; subst op' w' fl' a0 ic0.
  destruct (extract_const_expr_inv w c ic Ec) as [v [-> ->]].
  exists v; split; reflexivity.
Qed.

Definition extract_neg_expr (w : positive) (e : cert_expr) : option cert_expr :=
  match e with
  | CE_BinOp CB_Sub w' fl' z a =>
      if Pos.eqb w' w && cert_binop_flags_eqb fl' no_binop_flags && is_zero_const_expr w z
      then Some a
      else None
  | _ => None
  end.

Lemma extract_neg_expr_inv : forall w e a,
  extract_neg_expr w e = Some a ->
  e = CE_BinOp CB_Sub w no_binop_flags (CE_BvConst w 0%N) a.
Proof.
  intros w [| | | op' w' fl' z a0 | | | | |] a H; cbn [extract_neg_expr] in H; try discriminate H.
  destruct op'; try discriminate H.
  destruct (Pos.eqb w' w && cert_binop_flags_eqb fl' no_binop_flags && is_zero_const_expr w z)
    eqn:Eok; [| discriminate H].
  rewrite !andb_true_iff in Eok; destruct Eok as ([Hw Hfl] & Hz).
  apply Pos.eqb_eq in Hw; apply cert_binop_flags_eqb_eq in Hfl.
  inversion H; subst w' fl' a0; rewrite (is_zero_const_expr_inv w z Hz); reflexivity.
Qed.

Definition extract_not_expr (w : positive) (e : cert_expr) : option cert_expr :=
  match e with
  | CE_BinOp CB_Xor w' fl' a m =>
      if Pos.eqb w' w && cert_binop_flags_eqb fl' no_binop_flags && is_all_ones_const_expr w m
      then Some a
      else None
  | _ => None
  end.

Lemma extract_not_expr_inv : forall w e a,
  extract_not_expr w e = Some a ->
  e = CE_BinOp CB_Xor w no_binop_flags a (CE_BvConst w (all_ones_N w)).
Proof.
  intros w [| | | op' w' fl' a0 m | | | | |] a H; cbn [extract_not_expr] in H; try discriminate H.
  destruct op'; try discriminate H.
  destruct (Pos.eqb w' w && cert_binop_flags_eqb fl' no_binop_flags && is_all_ones_const_expr w m)
    eqn:Eok; [| discriminate H].
  rewrite !andb_true_iff in Eok; destruct Eok as ([Hw Hfl] & Hm).
  apply Pos.eqb_eq in Hw; apply cert_binop_flags_eqb_eq in Hfl.
  inversion H; subst w' fl' a0; rewrite (is_all_ones_const_expr_inv w m Hm); reflexivity.
Qed.

Lemma alg_two_p_pow : forall z,
  (0 <= z)%Z -> two_p z = (2 ^ z)%Z.
Proof.
  intros z Hz; replace z with (Z.of_nat (Z.to_nat z)) by lia.
  rewrite <- two_power_nat_two_p, two_power_nat_equiv; reflexivity.
Qed.

Lemma alg_modulus_le : forall w1 w2,
  (w1 <= w2)%positive -> (@Integers.modulus w1 <= @Integers.modulus w2)%Z.
Proof.
  intros w1 w2 Hle; rewrite !modulus_pow_sz; apply Z.pow_le_mono_r; lia.
Qed.

Lemma alg_signed_bounds_le : forall w1 w2 (i : @Integers.bit_int w1),
  (w1 <= w2)%positive ->
  (@Integers.min_signed w2 <= @Integers.signed w1 i <= @Integers.max_signed w2)%Z.
Proof.
  intros w1 w2 i Hle.
  pose proof (@Integers.signed_range w1 i) as Hr.
  pose proof (alg_modulus_le w1 w2 Hle) as Hm.
  pose proof (@Integers.half_modulus_modulus w1) as Hh1.
  pose proof (@Integers.half_modulus_modulus w2) as Hh2.
  unfold Integers.min_signed, Integers.max_signed in *; lia.
Qed.

Lemma alg_repr_unsigned_repr_le : forall tw mw z,
  (tw <= mw)%positive ->
  @Integers.repr tw (@Integers.unsigned mw (@Integers.repr mw z)) = @Integers.repr tw z.
Proof.
  intros tw mw z Hle.
  apply @Integers.same_bits_eq; intros i Hi.
  unfold Integers.zwordsize in Hi.
  rewrite (@Integers.testbit_repr tw _ i Hi), (@Integers.testbit_repr tw z i Hi).
  change (Z.testbit (@Integers.unsigned mw (@Integers.repr mw z)) i)
    with (@Integers.testbit mw (@Integers.repr mw z) i).
  apply (@Integers.testbit_repr mw z i); unfold Integers.zwordsize; lia.
Qed.

Lemma alg_add_self_shl1 : forall w (i : @Integers.bit_int w),
  (1 <? w)%positive = true ->
  @Integers.add w i i = @Integers.shl w i (@Integers.one w).
Proof.
  intros w i Hw; apply Pos.ltb_lt in Hw.
  rewrite (@Integers.shl_mul_two_p w i (@Integers.one w)), (@Integers.unsigned_one w).
  change (two_p 1) with 2%Z.
  unfold Integers.mul, Integers.add.
  assert (H2 : @Integers.unsigned w (@Integers.repr w 2) = 2%Z).
  { apply @Integers.unsigned_repr; unfold Integers.max_unsigned; rewrite modulus_pow_sz.
    assert (4 <= 2 ^ Z.pos w)%Z
      by (replace 4%Z with (2 ^ 2)%Z by reflexivity; apply Z.pow_le_mono_r; lia).
    lia. }
  rewrite H2; apply @Integers.eqm_samerepr; apply @Integers.eqm_refl2; lia.
Qed.

Lemma alg_ltu_iwordsize_iff : forall w (y : @Integers.bit_int w),
  (@Integers.unsigned w y < Z.pos w)%Z ->
  @Integers.ltu w y (@Integers.iwordsize w) = true.
Proof.
  intros w y Hlt; unfold Integers.ltu.
  rewrite (@Integers.unsigned_repr_wordsize w); unfold Integers.zwordsize.
  destruct (zlt (@Integers.unsigned w y) (Z.pos w)); [reflexivity | lia].
Qed.

Lemma alg_shift_sum_unsigned : forall w (y z : @Integers.bit_int w),
  (@Integers.unsigned w y + @Integers.unsigned w z < Z.pos w)%Z ->
  @Integers.unsigned w (@Integers.add w y z) =
  (@Integers.unsigned w y + @Integers.unsigned w z)%Z.
Proof.
  intros w y z Hsum; unfold Integers.add; apply @Integers.unsigned_repr.
  pose proof (@Integers.unsigned_range w y) as Hy.
  pose proof (@Integers.unsigned_range w z) as Hz.
  pose proof (@Integers.wordsize_max_unsigned w) as Hwm.
  unfold Integers.zwordsize in Hwm; lia.
Qed.

Lemma alg_zero_neq_one_1 : @Integers.zero 1%positive <> @Integers.one 1%positive.
Proof.
  intros Heq; apply (f_equal (@Integers.unsigned 1%positive)) in Heq.
  rewrite (@Integers.unsigned_zero 1%positive), (@Integers.unsigned_one 1%positive) in Heq.
  discriminate Heq.
Qed.

Lemma alg_i1_cases : forall (i : @Integers.bit_int 1%positive),
  i = @Integers.zero 1%positive \/ i = @Integers.one 1%positive.
Proof.
  intros i; pose proof (@Integers.unsigned_range 1%positive i) as Hr.
  rewrite modulus_pow_sz in Hr; change (2 ^ 1)%Z with 2%Z in Hr.
  assert (Hu : @Integers.unsigned 1%positive i = 0%Z \/ @Integers.unsigned 1%positive i = 1%Z)
    by lia.
  rewrite <- (@Integers.repr_unsigned 1%positive i).
  destruct Hu as [-> | ->]; [left; reflexivity | right; reflexivity].
Qed.

Lemma alg_signed_mul_bounds : forall lol hil lor hir a b : Z,
  (lol <= a <= hil)%Z ->
  (lor <= b <= hir)%Z ->
  (Z.min (Z.min (lol * lor) (lol * hir)) (Z.min (hil * lor) (hil * hir)) <= a * b <=
   Z.max (Z.max (lol * lor) (lol * hir)) (Z.max (hil * lor) (hil * hir)))%Z.
Proof.
  intros lol hil lor hir a b [Hla Hha] [Hlb Hhb].
  assert (Hb : forall x, (lol <= x <= hil -> lol * b <= x * b <= hil * b \/ hil * b <= x * b <= lol * b)%Z).
  { intros x [Hx1 Hx2].
    destruct (Z.le_gt_cases 0 b);
      [left; split; apply Z.mul_le_mono_nonneg_r; lia
      | right; split; apply Z.mul_le_mono_nonpos_r; lia]. }
  assert (Hl : (lol * b <= lol * lor \/ lol * b <= lol * hir)%Z /\
               (lol * lor <= lol * b \/ lol * hir <= lol * b)%Z).
  { destruct (Z.le_gt_cases 0 lol).
    - split.
      + right; apply Z.mul_le_mono_nonneg_l; lia.
      + left; apply Z.mul_le_mono_nonneg_l; lia.
    - split.
      + left; apply Z.mul_le_mono_nonpos_l; lia.
      + right; apply Z.mul_le_mono_nonpos_l; lia. }
  assert (Hh : (hil * b <= hil * lor \/ hil * b <= hil * hir)%Z /\
               (hil * lor <= hil * b \/ hil * hir <= hil * b)%Z).
  { destruct (Z.le_gt_cases 0 hil).
    - split.
      + right; apply Z.mul_le_mono_nonneg_l; lia.
      + left; apply Z.mul_le_mono_nonneg_l; lia.
    - split.
      + left; apply Z.mul_le_mono_nonpos_l; lia.
      + right; apply Z.mul_le_mono_nonpos_l; lia. }
  destruct (Hb a (conj Hla Hha)) as [[H1 H2] | [H1 H2]], Hl as [[Hl1|Hl1] [Hl2|Hl2]], Hh as [[Hh1|Hh1] [Hh2|Hh2]]; lia.
Qed.

Fixpoint expr_srange (e : cert_expr) : Z * Z :=
  let w := cert_expr_bit_width e in
  let def := (@Integers.min_signed w, @Integers.max_signed w) in
  match e with
  | CE_BvConst w' v =>
      let s := @Integers.signed w' (@Integers.repr w' (Z.of_N v)) in
      (s, s)
  | CE_Cast CCK_ZExt fw tw _ _ =>
      if (fw <? tw)%positive then
        (0%Z, (@Integers.modulus fw - 1)%Z)
      else def
  | CE_Cast CCK_SExt fw tw _ x =>
      if (fw <? tw)%positive && Pos.eqb (cert_expr_bit_width x) fw then
        expr_srange x
      else def
  | CE_BinOp op w' _ l r =>
      let '(lol, hil) := expr_srange l in
      let '(lor, hir) := expr_srange r in
      match op with
      | CB_Add =>
          let lo := (lol + lor)%Z in
          let hi := (hil + hir)%Z in
          if Pos.eqb (cert_expr_bit_width l) w' && Pos.eqb (cert_expr_bit_width r) w' &&
             (@Integers.min_signed w' <=? lo)%Z && (hi <=? @Integers.max_signed w')%Z
          then (lo, hi)
          else def
      | CB_Sub =>
          let lo := (lol - hir)%Z in
          let hi := (hil - lor)%Z in
          if Pos.eqb (cert_expr_bit_width l) w' && Pos.eqb (cert_expr_bit_width r) w' &&
             (@Integers.min_signed w' <=? lo)%Z && (hi <=? @Integers.max_signed w')%Z
          then (lo, hi)
          else def
      | CB_Mul =>
          let lo := Z.min (Z.min (lol * lor) (lol * hir)) (Z.min (hil * lor) (hil * hir)) in
          let hi := Z.max (Z.max (lol * lor) (lol * hir)) (Z.max (hil * lor) (hil * hir)) in
          if Pos.eqb (cert_expr_bit_width l) w' && Pos.eqb (cert_expr_bit_width r) w' &&
             (@Integers.min_signed w' <=? lo)%Z && (hi <=? @Integers.max_signed w')%Z
          then (lo, hi)
          else def
      | _ => def
      end
  | CE_Select w' c t f =>
      let '(lot, hit) := expr_srange t in
      let '(lof, hif) := expr_srange f in
      if Pos.eqb (cert_expr_bit_width t) w' && Pos.eqb (cert_expr_bit_width f) w' then
        match c with
        | CE_ICmp pr false wcmp l r =>
            if Pos.eqb wcmp w' &&
               Pos.eqb (cert_expr_bit_width l) w' &&
               Pos.eqb (cert_expr_bit_width r) w' then
              let '(lol, hil) := expr_srange l in
              let '(lor, hir) := expr_srange r in
              match pr with
              | CIP_Slt | CIP_Sle =>
                  if cert_expr_eqb l t && cert_expr_eqb r f then (Z.min lol lor, Z.min hil hir)
                  else if cert_expr_eqb r t && cert_expr_eqb l f then (Z.max lol lor, Z.max hil hir)
                  else (Z.min lot lof, Z.max hit hif)
              | CIP_Sgt | CIP_Sge =>
                  if cert_expr_eqb l t && cert_expr_eqb r f then (Z.max lol lor, Z.max hil hir)
                  else if cert_expr_eqb r t && cert_expr_eqb l f then (Z.min lol lor, Z.min hil hir)
                  else (Z.min lot lof, Z.max hit hif)
              | _ => (Z.min lot lof, Z.max hit hif)
              end
            else (Z.min lot lof, Z.max hit hif)
        | _ => (Z.min lot lof, Z.max hit hif)
        end
      else def
  | _ => def
  end.

Lemma alg_ret_dvalue_I_inj : forall {Pa : Params} sz (a b : @Integers.bit_int sz),
  raise_ret (DVALUE_Base (@DVALUE_I Pa sz a)) =
  raise_ret (DVALUE_Base (@DVALUE_I Pa sz b)) ->
  a = b.
Proof.
  intros Pa sz a b H; apply alg_bit_int_unsigned_inj.
  exact (f_equal (fun r =>
    match r with
    | raise_ret (DVALUE_Base (@DVALUE_I _ _ x)) => @Integers.unsigned _ x
    | _ => 0%Z
    end) H).
Qed.

Local Lemma expr_srange_binop_sound :
  forall {Pa : Params} (op : cert_binop) (w' : positive) (fl : cert_binop_flags)
         (l r : cert_expr) (penv : param_env Pa) (foracle : freeze_oracle)
         (i : @Integers.bit_int w'),
    (forall (w : positive) (penv0 : param_env Pa) (foracle0 : freeze_oracle)
            (il : @Integers.bit_int w),
       cert_expr_bit_width l = w ->
       wt_cert_expr [] l = true ->
       wf_param_env_for (collect_free_vars [] l) penv0 ->
       eval_closed_cert_expr penv0 foracle0 l = raise_ret (DVALUE_Base (@DVALUE_I Pa w il)) ->
       let '(lo, hi) := expr_srange l in
       (lo <= @Integers.signed w il <= hi)%Z) ->
    (forall (w : positive) (penv0 : param_env Pa) (foracle0 : freeze_oracle)
            (ir : @Integers.bit_int w),
       cert_expr_bit_width r = w ->
       wt_cert_expr [] r = true ->
       wf_param_env_for (collect_free_vars [] r) penv0 ->
       eval_closed_cert_expr penv0 foracle0 r = raise_ret (DVALUE_Base (@DVALUE_I Pa w ir)) ->
       let '(lo, hi) := expr_srange r in
       (lo <= @Integers.signed w ir <= hi)%Z) ->
    wt_cert_expr [] (CE_BinOp op w' fl l r) = true ->
    wf_param_env_for (collect_free_vars [] (CE_BinOp op w' fl l r)) penv ->
    eval_closed_cert_expr penv foracle (CE_BinOp op w' fl l r) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w' i)) ->
    let '(lo, hi) := expr_srange (CE_BinOp op w' fl l r) in
    (lo <= @Integers.signed w' i <= hi)%Z.
Proof.
  intros Pa op w' fl l r penv foracle i IHl IHr Hwt Hpenv Hev.
  cbn [wt_cert_expr collect_free_vars] in Hwt, Hpenv;
    rewrite !andb_true_iff in Hwt;
    destruct Hwt as ((((Hfl & Htl) & Htr) & Hwl) & Hwr);
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
  assert (Hpl : wf_param_env_for (collect_free_vars [] l) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
  assert (Hpr : wf_param_env_for (collect_free_vars [] r) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
  cbn [expr_srange].
  destruct (expr_srange l) as [lol hil] eqn:Erl;
    destruct (expr_srange r) as [lor hir] eqn:Err.
  destruct op; try exact (@Integers.signed_range w' i).
  - (* CB_Add *)
    destruct (Pos.eqb (cert_expr_bit_width l) w' && Pos.eqb (cert_expr_bit_width r) w' &&
              (@Integers.min_signed w' <=? lol + lor)%Z &&
              (hil + hir <=? @Integers.max_signed w')%Z) eqn:Eb;
      [| exact (@Integers.signed_range w' i)].
    rewrite !andb_true_iff in Eb; destruct Eb as ([_ Hmin] & Hmax);
      apply Z.leb_le in Hmin; apply Z.leb_le in Hmax.
    unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev.
    destruct (eval_cert_expr penv [] foracle l) as [| | | vl] eqn:El;
      cbn [eou_bind] in Hev; try discriminate Hev.
    destruct (eval_cert_expr penv [] foracle r) as [| | | vr] eqn:Er;
      cbn [eou_bind] in Hev; try discriminate Hev.
    pose proof (eval_cert_expr_ret_wf_scalar l [] penv [] foracle vl Htl El) as Hwvl.
    pose proof (eval_cert_expr_ret_wf_scalar r [] penv [] foracle vr Htr Er) as Hwvr.
    rewrite Hwl in Hwvl; rewrite Hwr in Hwvr.
    destruct Hwvl as [-> | [il ->]];
      [destruct Hwvr as [-> | [ir ->]]; cbn in Hev; discriminate Hev |].
    destruct Hwvr as [-> | [ir ->]]; [cbn in Hev; discriminate Hev |].
    unfold eval_iop in Hev; rewrite eval_iop_integer_base_same_width in Hev.
    unfold cert_to_ibinop, eval_int_op, dvp, tdb in Hev; cbn - [andb orb] in Hev.
    destruct ((cbf_nuw fl && _) || (cbf_nsw fl && _));
      cbn in Hev; [discriminate Hev | apply alg_ret_dvalue_I_inj in Hev; subst i].
    pose proof (IHl w' penv foracle il Hwl Htl Hpl El) as Hrl.
    pose proof (IHr w' penv foracle ir Hwr Htr Hpr Er) as Hrr.
    rewrite (@Integers.add_signed w' il ir), (@Integers.signed_repr w'); lia.
  - (* CB_Sub *)
    destruct (Pos.eqb (cert_expr_bit_width l) w' && Pos.eqb (cert_expr_bit_width r) w' &&
              (@Integers.min_signed w' <=? lol - hir)%Z &&
              (hil - lor <=? @Integers.max_signed w')%Z) eqn:Eb;
      [| exact (@Integers.signed_range w' i)].
    rewrite !andb_true_iff in Eb; destruct Eb as ([_ Hmin] & Hmax);
      apply Z.leb_le in Hmin; apply Z.leb_le in Hmax.
    unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev.
    destruct (eval_cert_expr penv [] foracle l) as [| | | vl] eqn:El;
      cbn [eou_bind] in Hev; try discriminate Hev.
    destruct (eval_cert_expr penv [] foracle r) as [| | | vr] eqn:Er;
      cbn [eou_bind] in Hev; try discriminate Hev.
    pose proof (eval_cert_expr_ret_wf_scalar l [] penv [] foracle vl Htl El) as Hwvl.
    pose proof (eval_cert_expr_ret_wf_scalar r [] penv [] foracle vr Htr Er) as Hwvr.
    rewrite Hwl in Hwvl; rewrite Hwr in Hwvr.
    destruct Hwvl as [-> | [il ->]];
      [destruct Hwvr as [-> | [ir ->]]; cbn in Hev; discriminate Hev |].
    destruct Hwvr as [-> | [ir ->]]; [cbn in Hev; discriminate Hev |].
    unfold eval_iop in Hev; rewrite eval_iop_integer_base_same_width in Hev.
    unfold cert_to_ibinop, eval_int_op, dvp, tdb in Hev; cbn - [andb orb] in Hev.
    destruct ((cbf_nuw fl && _) || (cbf_nsw fl && _));
      cbn in Hev; [discriminate Hev | apply alg_ret_dvalue_I_inj in Hev; subst i].
    pose proof (IHl w' penv foracle il Hwl Htl Hpl El) as Hrl.
    pose proof (IHr w' penv foracle ir Hwr Htr Hpr Er) as Hrr.
    rewrite (@Integers.sub_signed w' il ir), (@Integers.signed_repr w'); lia.
  - (* CB_Mul *)
    set (lo := Z.min (Z.min (lol * lor) (lol * hir)) (Z.min (hil * lor) (hil * hir))) in *.
    set (hi := Z.max (Z.max (lol * lor) (lol * hir)) (Z.max (hil * lor) (hil * hir))) in *.
    destruct (Pos.eqb (cert_expr_bit_width l) w' && Pos.eqb (cert_expr_bit_width r) w' &&
              (@Integers.min_signed w' <=? lo)%Z && (hi <=? @Integers.max_signed w')%Z) eqn:Eb;
      [| exact (@Integers.signed_range w' i)].
    rewrite !andb_true_iff in Eb; destruct Eb as ([_ Hmin] & Hmax);
      apply Z.leb_le in Hmin; apply Z.leb_le in Hmax.
    unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev.
    destruct (eval_cert_expr penv [] foracle l) as [| | | vl] eqn:El;
      cbn [eou_bind] in Hev; try discriminate Hev.
    destruct (eval_cert_expr penv [] foracle r) as [| | | vr] eqn:Er;
      cbn [eou_bind] in Hev; try discriminate Hev.
    pose proof (eval_cert_expr_ret_wf_scalar l [] penv [] foracle vl Htl El) as Hwvl.
    pose proof (eval_cert_expr_ret_wf_scalar r [] penv [] foracle vr Htr Er) as Hwvr.
    rewrite Hwl in Hwvl; rewrite Hwr in Hwvr.
    destruct Hwvl as [-> | [il ->]];
      [destruct Hwvr as [-> | [ir ->]]; cbn in Hev; discriminate Hev |].
    destruct Hwvr as [-> | [ir ->]]; [cbn in Hev; discriminate Hev |].
    unfold eval_iop in Hev; rewrite eval_iop_integer_base_same_width in Hev.
    assert (Hmul_i : i = @Integers.mul w' il ir).
    { unfold cert_to_ibinop, eval_int_op, dvp, tdb in Hev;
        cbn - [andb orb] in Hev.
      destruct (Pos.eqb w' 1); cbn - [andb orb] in Hev;
        [apply alg_ret_dvalue_I_inj in Hev; symmetry; exact Hev |].
      destruct ((cbf_nuw fl && _) || (cbf_nsw fl && _));
        cbn in Hev; [discriminate Hev | apply alg_ret_dvalue_I_inj in Hev; symmetry; exact Hev]. }
    subst i.
    pose proof (IHl w' penv foracle il Hwl Htl Hpl El) as Hrl.
    pose proof (IHr w' penv foracle ir Hwr Htr Hpr Er) as Hrr.
    pose proof (alg_signed_mul_bounds lol hil lor hir
                  (@Integers.signed w' il) (@Integers.signed w' ir) Hrl Hrr) as Hmb.
    fold lo hi in Hmb.
    rewrite (@Integers.mul_signed w' il ir), (@Integers.signed_repr w'); lia.
Qed.

Local Lemma expr_srange_select_sound :
  forall {Pa : Params} (w' : positive) (c t f : cert_expr)
         (penv : param_env Pa) (foracle : freeze_oracle)
         (i : @Integers.bit_int w'),
    (forall (w : positive) (penv0 : param_env Pa) (foracle0 : freeze_oracle)
            (it : @Integers.bit_int w),
       cert_expr_bit_width t = w ->
       wt_cert_expr [] t = true ->
       wf_param_env_for (collect_free_vars [] t) penv0 ->
       eval_closed_cert_expr penv0 foracle0 t = raise_ret (DVALUE_Base (@DVALUE_I Pa w it)) ->
       let '(lo, hi) := expr_srange t in
       (lo <= @Integers.signed w it <= hi)%Z) ->
    (forall (w : positive) (penv0 : param_env Pa) (foracle0 : freeze_oracle)
            (ifv : @Integers.bit_int w),
       cert_expr_bit_width f = w ->
       wt_cert_expr [] f = true ->
       wf_param_env_for (collect_free_vars [] f) penv0 ->
       eval_closed_cert_expr penv0 foracle0 f = raise_ret (DVALUE_Base (@DVALUE_I Pa w ifv)) ->
       let '(lo, hi) := expr_srange f in
       (lo <= @Integers.signed w ifv <= hi)%Z) ->
    wt_cert_expr [] (CE_Select w' c t f) = true ->
    wf_param_env_for (collect_free_vars [] (CE_Select w' c t f)) penv ->
    eval_closed_cert_expr penv foracle (CE_Select w' c t f) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w' i)) ->
    let '(lo, hi) := expr_srange (CE_Select w' c t f) in
    (lo <= @Integers.signed w' i <= hi)%Z.
Proof.
  intros Pa w' c t f penv foracle i IHt IHf Hwt Hpenv Hev.
  cbn [wt_cert_expr collect_free_vars] in Hwt, Hpenv;
    rewrite !andb_true_iff in Hwt;
    destruct Hwt as (((((Htc & Htt) & Htf) & Hwc) & Hwtb) & Hwf).
  apply Pos.eqb_eq in Hwtb; apply Pos.eqb_eq in Hwf.
  assert (Hpt : wf_param_env_for (collect_free_vars [] t) penv).
  { intros x wx Hx.
    apply Hpenv, in_app_iff; right; apply in_app_iff; left; exact Hx. }
  assert (Hpf : wf_param_env_for (collect_free_vars [] f) penv).
  { intros x wx Hx.
    apply Hpenv, in_app_iff; right; apply in_app_iff; right; exact Hx. }
  cbn [expr_srange]; rewrite Hwtb, Hwf, !Pos.eqb_refl; cbn [andb].
  destruct (expr_srange t) as [lot hit] eqn:Ert; destruct (expr_srange f) as [lof hif] eqn:Erf.
  unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev.
  destruct (eval_cert_expr penv [] foracle c) as [| | | vc] eqn:Ec;
    cbn [eou_bind] in Hev; try discriminate Hev.
  destruct (eval_cert_expr penv [] foracle t) as [| | | vt] eqn:Et;
    cbn [eou_bind] in Hev; try discriminate Hev.
  destruct (eval_cert_expr penv [] foracle f) as [| | | vf] eqn:Ef;
    cbn [eou_bind] in Hev; try discriminate Hev.
  pose proof (eval_cert_expr_ret_wf_scalar c [] penv [] foracle vc Htc Ec) as Hwvc;
    apply Pos.eqb_eq in Hwc; rewrite Hwc in Hwvc.
  pose proof (eval_cert_expr_ret_wf_scalar t [] penv [] foracle vt Htt Et) as Hwvt;
    rewrite Hwtb in Hwvt.
  pose proof (eval_cert_expr_ret_wf_scalar f [] penv [] foracle vf Htf Ef) as Hwvf;
    rewrite Hwf in Hwvf.
  destruct Hwvc as [-> | [ic ->]]; [cbn in Hev; discriminate Hev |].
  cbn [bind ret EOU_monad] in Hev.
  pose proof (IHt w' penv foracle) as IHt'.
  pose proof (IHf w' penv foracle) as IHf'.
  assert (Hbase :
    let lo := Z.min lot lof in
    let hi := Z.max hit hif in
    (lo <= @Integers.signed w' i <= hi)%Z).
  { cbn zeta; cbn [eval_select eval_select_base_dvalue ret EOU_monad] in Hev;
    destruct (@Integers.unsigned 1 ic =? 1)%Z.
    - destruct Hwvt as [-> | [it ->]]; [discriminate Hev |].
      apply alg_ret_dvalue_I_inj in Hev; subst i.
      pose proof (IHt' it Hwtb Htt Hpt Et) as Hrt; lia.
    - destruct Hwvf as [-> | [ifv ->]]; [discriminate Hev |].
      apply alg_ret_dvalue_I_inj in Hev; subst i.
      pose proof (IHf' ifv Hwf Htf Hpf Ef) as Hrf; lia. }
  destruct c as [| | | | pr ss_c wcmp l r | | | |]; try exact Hbase.
  destruct ss_c; [exact Hbase |].
  destruct (Pos.eqb wcmp w' && Pos.eqb (cert_expr_bit_width l) w' &&
            Pos.eqb (cert_expr_bit_width r) w') eqn:Hwc_mm;
    [| exact Hbase].
  rewrite !andb_true_iff in Hwc_mm; destruct Hwc_mm as [[Hwcmp Hwl_w] Hwr_w].
  apply Pos.eqb_eq in Hwcmp; apply Pos.eqb_eq in Hwl_w; apply Pos.eqb_eq in Hwr_w; subst wcmp.
  destruct (expr_srange l) as [lol hil] eqn:Erl0; destruct (expr_srange r) as [lor hir] eqn:Err0.
  destruct pr; try exact Hbase;
    [ destruct (cert_expr_eqb l t && cert_expr_eqb r f) eqn:Em1;
      [| destruct (cert_expr_eqb r t && cert_expr_eqb l f) eqn:Em2; [| exact Hbase]]
    | destruct (cert_expr_eqb l t && cert_expr_eqb r f) eqn:Em1;
      [| destruct (cert_expr_eqb r t && cert_expr_eqb l f) eqn:Em2; [| exact Hbase]]
    | destruct (cert_expr_eqb l t && cert_expr_eqb r f) eqn:Em1;
      [| destruct (cert_expr_eqb r t && cert_expr_eqb l f) eqn:Em2; [| exact Hbase]]
    | destruct (cert_expr_eqb l t && cert_expr_eqb r f) eqn:Em1;
      [| destruct (cert_expr_eqb r t && cert_expr_eqb l f) eqn:Em2; [| exact Hbase]] ].
  all: try (apply andb_true_iff in Em1 as [Eeq1 Eeq2];
            apply cert_expr_eqb_eq in Eeq1; apply cert_expr_eqb_eq in Eeq2; subst t f).
  all: try (apply andb_true_iff in Em2 as [Eeq1 Eeq2];
            apply cert_expr_eqb_eq in Eeq1; apply cert_expr_eqb_eq in Eeq2; subst t f).
  all: rewrite ?Erl0, ?Err0 in *.
  all: cbn [eval_cert_expr] in Ec.
  all: first [ rewrite Et in Ec; cbn [eou_bind] in Ec; rewrite Ef in Ec
             | rewrite Ef in Ec; cbn [eou_bind] in Ec; rewrite Et in Ec ];
       cbn [eou_bind] in Ec.
  all: destruct Hwvt as [-> | [iv_t ->]]; destruct Hwvf as [-> | [iv_f ->]];
       [cbn in Ec; discriminate Ec
       |cbn in Ec; discriminate Ec
       |cbn in Ec; discriminate Ec
       |].
  all: unfold eval_icmp in Ec; rewrite eval_icmp_base_same_width in Ec.
  all: unfold cert_to_icmp, eval_int_icmp, Integers.cmp in Ec; cbn in Ec.
  all: repeat match type of Ec with
       | context [@Integers.lt ?sz ?a ?b] =>
           let Hlt := fresh "Elt" in destruct (@Integers.lt sz a b) eqn:Hlt
       end;
       cbn [negb] in Ec;
       try discriminate Ec;
       apply alg_ret_dvalue_I_inj in Ec; subst ic;
       cbn [eval_select eval_select_base_dvalue ret EOU_monad] in Hev;
       rewrite ?(@Integers.unsigned_one 1%positive), ?(@Integers.unsigned_zero 1%positive) in Hev;
       cbn in Hev; apply alg_ret_dvalue_I_inj in Hev; subst i.
  all: repeat match goal with
       | H : @Integers.lt _ _ _ = _ |- _ =>
           unfold Integers.lt in H;
           destruct (Rocqlib.zlt _ _); [try discriminate H | try discriminate H]; clear H
       end.
  all: pose proof (IHt' iv_t Hwtb Htt Hpt Et) as Hrt;
       pose proof (IHf' iv_f Hwf Htf Hpf Ef) as Hrf;
       rewrite ?Erl0, ?Err0 in Ert, Erf; inversion Ert; inversion Erf; subst;
       lia.
Qed.

Lemma expr_srange_sound :
  forall {Pa : Params} (e : cert_expr) (w : positive) (penv : param_env Pa)
         (foracle : freeze_oracle) (i : @Integers.bit_int w),
    cert_expr_bit_width e = w ->
    wt_cert_expr [] e = true ->
    wf_param_env_for (collect_free_vars [] e) penv ->
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa w i)) ->
    let '(lo, hi) := expr_srange e in
    (lo <= @Integers.signed w i <= hi)%Z.
Proof.
  intros Pa e; induction e as
    [w' v
    | w'
    | nm w'
    | op w' fl l IHl r IHr
    | pr ss w' l IHl r IHr
    | k fw tw fl o IHo
    | w' c IHc t IHt f IHf
    | w' o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros w penv foracle i Hbw Hwt Hpenv Hev;
    cbn [cert_expr_bit_width] in Hbw; subst w.
  - cbn in Hev; apply alg_ret_dvalue_I_inj in Hev; subst i; cbn [expr_srange]; lia.
  - cbn in Hev; discriminate Hev.
  - cbn [expr_srange]; exact (@Integers.signed_range w' i).
  - exact (expr_srange_binop_sound op w' fl l r penv foracle i IHl IHr Hwt Hpenv Hev).
  - cbn [expr_srange]; exact (@Integers.signed_range 1%positive i).
  - cbn [wt_cert_expr collect_free_vars] in Hwt, Hpenv;
      rewrite !andb_true_iff in Hwt; destruct Hwt as ((Hk & Hto) & Hwo);
      apply Pos.eqb_eq in Hwo.
    cbn [expr_srange].
    destruct k.
    + destruct (fw <? tw)%positive eqn:Elt; [| exact (@Integers.signed_range tw i)].
      unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev.
      destruct (eval_cert_expr penv [] foracle o) as [| | | vo] eqn:Eo;
        cbn [eou_bind] in Hev; try discriminate Hev.
      pose proof (eval_cert_expr_ret_wf_scalar o [] penv [] foracle vo Hto Eo) as Hwvo.
      rewrite Hwo in Hwvo; destruct Hwvo as [-> | [io ->]]; [cbn in Hev; discriminate Hev |].
      cbn - [andb Pos.ltb Pos.eqb] in Hev; rewrite Pos.eqb_refl, Elt in Hev; cbn in Hev.
      destruct (ccf_nneg fl && (@Integers.signed fw io <? 0)%Z);
        cbn in Hev; [discriminate Hev | apply alg_ret_dvalue_I_inj in Hev; subst i].
      pose proof (@Integers.unsigned_range fw io) as Hur.
      pose proof (Pos.ltb_lt fw tw) as [Hplt _]; specialize (Hplt Elt).
      assert (Hm_le : (@Integers.modulus fw <= @Integers.half_modulus tw)%Z).
      { pose proof (@Integers.half_modulus_modulus tw) as Hhm.
        pose proof (@Integers.half_modulus_pos tw) as Hhp.
        rewrite !modulus_pow_sz in Hhm |- *.
        assert (H2p : (2 * 2 ^ (Z.pos tw - 1) = 2 ^ Z.pos tw)%Z)
          by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
        assert (Hhm_eq : @Integers.half_modulus tw = (2 ^ (Z.pos tw - 1))%Z) by lia.
        rewrite Hhm_eq; apply Z.pow_le_mono_r; lia. }
      pose proof (@Integers.min_signed_neg tw) as Hmn.
      unfold Integers.max_signed in *.
      rewrite (@Integers.signed_repr tw (@Integers.unsigned fw io));
        [lia | unfold Integers.min_signed, Integers.max_signed; lia].
    + cbn [andb] in Hk; rewrite !andb_true_iff in Hk; destruct Hk as (([Elt _] & _) & _).
      rewrite Elt, Hwo, Pos.eqb_refl; cbn [andb].
      unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev.
      destruct (eval_cert_expr penv [] foracle o) as [| | | vo] eqn:Eo;
        cbn [eou_bind] in Hev; try discriminate Hev.
      pose proof (eval_cert_expr_ret_wf_scalar o [] penv [] foracle vo Hto Eo) as Hwvo.
      rewrite Hwo in Hwvo; destruct Hwvo as [-> | [io ->]]; [cbn in Hev; discriminate Hev |].
      cbn - [andb Pos.ltb Pos.eqb] in Hev; rewrite Pos.eqb_refl, Elt in Hev; cbn in Hev.
      apply alg_ret_dvalue_I_inj in Hev; subst i.
      destruct (expr_srange o) as [loo hio].
      pose proof (IHo fw penv foracle io Hwo Hto Hpenv Eo) as Hro.
      pose proof (alg_signed_bounds_le fw tw io (Pos.lt_le_incl _ _ (proj1 (Pos.ltb_lt _ _) Elt))) as Hsb.
      rewrite (@Integers.signed_repr tw (@Integers.signed fw io) Hsb); exact Hro.
    + exact (@Integers.signed_range tw i).
  - exact (expr_srange_select_sound w' c t f penv foracle i IHt IHf Hwt Hpenv Hev).
  - cbn [expr_srange]; exact (@Integers.signed_range w' i).
  - cbn [expr_srange]; exact (@Integers.signed_range (cert_expr_bit_width body) i).
Qed.

Definition binop_nsw_safe (op : cert_binop) (w : positive) (nl nr : cert_expr) : bool :=
  let '(lol, hil) := expr_srange nl in
  let '(lor, hir) := expr_srange nr in
  match op with
  | CB_Add =>
      (@Integers.min_signed w <=? lol + lor)%Z && (hil + hir <=? @Integers.max_signed w)%Z
  | CB_Sub =>
      (@Integers.min_signed w <=? lol - hir)%Z && (hil - lor <=? @Integers.max_signed w)%Z
  | CB_Mul =>
      (1 <? w)%positive &&
      let lo := Z.min (Z.min (lol * lor) (lol * hir)) (Z.min (hil * lor) (hil * hir)) in
      let hi := Z.max (Z.max (lol * lor) (lol * hir)) (Z.max (hil * lor) (hil * hir)) in
      (@Integers.min_signed w <=? lo)%Z && (hi <=? @Integers.max_signed w)%Z
  | _ => false
  end.

Definition strip_safe_nsw_flags
  (op : cert_binop) (w : positive) (fl : cert_binop_flags) (nl nr : cert_expr)
  : cert_binop_flags :=
  if cbf_nsw fl && negb (cbf_nuw fl) && negb (cbf_exact fl) && negb (cbf_disjoint fl) &&
     binop_nsw_safe op w nl nr
  then no_binop_flags
  else fl.

Lemma strip_safe_nsw_flags_wf :
  forall op w fl nl nr,
    wf_binop_flags_for op fl = true ->
    wf_binop_flags_for op (strip_safe_nsw_flags op w fl nl nr) = true.
Proof.
  intros op w fl nl nr Hfl; unfold strip_safe_nsw_flags.
  destruct (cbf_nsw fl && negb (cbf_nuw fl) && negb (cbf_exact fl) &&
            negb (cbf_disjoint fl) && binop_nsw_safe op w nl nr);
    [destruct op; reflexivity | exact Hfl].
Qed.

Lemma strip_safe_nsw_flags_eval :
  forall {Pa : Params} op w fl nl nr (penv : param_env Pa) foracle,
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    wf_param_env_for (collect_free_vars [] nl ++ collect_free_vars [] nr) penv ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp op w fl nl nr))
      (eval_closed_cert_expr penv foracle
         (CE_BinOp op w (strip_safe_nsw_flags op w fl nl nr) nl nr)).
Proof.
  intros Pa op w fl nl nr penv foracle Hwl Hwr Htl Htr Hpenv.
  unfold strip_safe_nsw_flags.
  destruct (cbf_nsw fl && negb (cbf_nuw fl) && negb (cbf_exact fl) &&
            negb (cbf_disjoint fl) && binop_nsw_safe op w nl nr) eqn:Estrip;
    [| apply equiv_eou_dvalue_refl].
  rewrite !andb_true_iff in Estrip.
  destruct Estrip as ((((Hnsw & Hnnuw) & Hnex) & Hndj) & Hsafe).
  apply negb_true_iff in Hnnuw; apply negb_true_iff in Hnex; apply negb_true_iff in Hndj.
  assert (Hpl : wf_param_env_for (collect_free_vars [] nl) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
  assert (Hpr : wf_param_env_for (collect_free_vars [] nr) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
  unfold eval_closed_cert_expr; cbn [eval_cert_expr].
  destruct (eval_cert_expr_totality nl [] penv [] foracle Htl wf_let_val_env_nil Hpl)
    as [[msgl ->] | [vl [El Hwfl]]]; cbn [eou_bind]; [exact I |].
  destruct (eval_cert_expr_totality nr [] penv [] foracle Htr wf_let_val_env_nil Hpr)
    as [[msgr ->] | [vr [Er Hwfr]]]; [rewrite El; cbn [eou_bind]; exact I |].
  rewrite El, Er; cbn [eou_bind].
  rewrite Hwl in Hwfl; rewrite Hwr in Hwfr.
  destruct Hwfl as [-> | [il ->]];
    [destruct Hwfr as [-> | [ir ->]];
     unfold binop_nsw_safe in Hsafe; destruct (expr_srange nl), (expr_srange nr);
     destruct op; cbn in Hsafe; try discriminate;
     unfold eval_iop; cbn; reflexivity |].
  destruct Hwfr as [-> | [ir ->]];
    [unfold binop_nsw_safe in Hsafe; destruct (expr_srange nl), (expr_srange nr);
     destruct op; cbn in Hsafe; try discriminate;
     unfold eval_iop; cbn; reflexivity |].
  pose proof (@expr_srange_sound Pa nl w penv foracle il Hwl Htl Hpl El) as Hrl.
  pose proof (@expr_srange_sound Pa nr w penv foracle ir Hwr Htr Hpr Er) as Hrr.
  unfold binop_nsw_safe in Hsafe.
  destruct (expr_srange nl) as [lol hil]; destruct (expr_srange nr) as [lor hir].
  unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
  destruct op; try discriminate Hsafe.
  - (* CB_Add *)
    apply andb_true_iff in Hsafe as [Hmin Hmax]; apply Z.leb_le in Hmin; apply Z.leb_le in Hmax.
    unfold cert_to_ibinop, eval_int_op; cbn - [andb orb]; rewrite Hnsw, Hnnuw; cbn [andb orb].
    unfold Integers.add_overflow; rewrite (@Integers.signed_zero w), Z.add_0_r.
    destruct (zle (@Integers.min_signed w) (@Integers.signed w il + @Integers.signed w ir));
      [| lia].
    destruct (zle (@Integers.signed w il + @Integers.signed w ir) (@Integers.max_signed w));
      [| lia].
    cbn [proj_sumbool andb];
      rewrite (@Integers.eq_false w (@Integers.zero w) (@Integers.one w)
                 (fun H => @Integers.one_not_zero w (eq_sym H)));
      cbn; reflexivity.
  - (* CB_Sub *)
    apply andb_true_iff in Hsafe as [Hmin Hmax]; apply Z.leb_le in Hmin; apply Z.leb_le in Hmax.
    unfold cert_to_ibinop, eval_int_op; cbn - [andb orb]; rewrite Hnsw, Hnnuw; cbn [andb orb].
    unfold Integers.sub_overflow; rewrite (@Integers.signed_zero w), Z.sub_0_r.
    destruct (zle (@Integers.min_signed w) (@Integers.signed w il - @Integers.signed w ir));
      [| lia].
    destruct (zle (@Integers.signed w il - @Integers.signed w ir) (@Integers.max_signed w));
      [| lia].
    cbn [proj_sumbool andb];
      rewrite (@Integers.eq_false w (@Integers.zero w) (@Integers.one w)
                 (fun H => @Integers.one_not_zero w (eq_sym H)));
      cbn; reflexivity.
  - (* CB_Mul *)
    rewrite !andb_true_iff in Hsafe; destruct Hsafe as [Hw1 [Hmin Hmax]];
      apply Z.leb_le in Hmin; apply Z.leb_le in Hmax.
    pose proof (alg_signed_mul_bounds lol hil lor hir (@Integers.signed w il) (@Integers.signed w ir) Hrl Hrr) as Hmb.
    unfold cert_to_ibinop, eval_int_op, tdb; cbn - [andb orb Pos.eqb].
    assert (Hne1 : Pos.eqb w 1 = false)
      by (apply Pos.eqb_neq; apply Pos.ltb_lt in Hw1; lia).
    rewrite Hne1; cbn [andb orb].
    rewrite Hnsw, Hnnuw; cbn [andb orb].
    destruct ((@Integers.min_signed w >? @Integers.signed w il * @Integers.signed w ir)%Z) eqn:Elo;
      [rewrite Z.gtb_lt in Elo; lia |].
    destruct ((@Integers.signed w il * @Integers.signed w ir >? @Integers.max_signed w)%Z) eqn:Ehi;
      [rewrite Z.gtb_lt in Ehi; lia |].
    cbn; reflexivity.
Qed.

Definition norm_binop_unfolded
  (ctx : ub_ctx) (op : cert_binop) (w : positive) (fl : cert_binop_flags)
  (nl nr : cert_expr) : cert_expr :=
  match op with
      | CB_UDiv =>
          if negb (cbf_nuw fl) && negb (cbf_nsw fl) && negb (cbf_disjoint fl) then
            match extract_const_expr w nr with
            | Some ic =>
                match @Integers.is_power2 w ic with
                | Some logn =>
                    if (@Integers.unsigned w logn =? 0)%Z then nl
                    else CE_BinOp CB_LShr w fl nl (mk_bv_const w logn)
                | None => CE_BinOp op w fl nl nr
                end
            | None => CE_BinOp op w fl nl nr
            end
          else CE_BinOp op w fl nl nr
      | CB_URem =>
          if cert_binop_flags_eqb fl no_binop_flags then
            match extract_const_expr w nr with
            | Some ic =>
                match @Integers.is_power2 w ic with
                | Some _ =>
                    CE_BinOp CB_And w no_binop_flags nl
                      (mk_bv_const w (@Integers.sub w ic (@Integers.one w)))
                | None => CE_BinOp op w fl nl nr
                end
            | None => CE_BinOp op w fl nl nr
            end
          else CE_BinOp op w fl nl nr
      | _ =>
          if cert_binop_flags_eqb fl no_binop_flags then
            match op with
            | CB_Add =>
                if is_zero_const_expr w nr then nl
                else if is_zero_const_expr w nl then nr
                else if (1 <? w)%positive && cert_expr_eqb nl nr then
                  CE_BinOp CB_Shl w no_binop_flags nl (CE_BvConst w 1%N)
                else
                  match extract_neg_expr w nr with
                  | Some y => CE_BinOp CB_Sub w no_binop_flags nl y
                  | None =>
                      match extract_const_expr w nr with
                      | Some ic2 =>
                          match extract_binop_rhs_const CB_Add w nl with
                          | Some (a, ic1) =>
                              let s := @Integers.add w ic1 ic2 in
                              if (@Integers.unsigned w s =? 0)%Z then a
                              else CE_BinOp CB_Add w no_binop_flags a (mk_bv_const w s)
                          | None => CE_BinOp op w fl nl nr
                          end
                      | None =>
                          match extract_const_expr w nl with
                          | Some ic1 => CE_BinOp CB_Add w no_binop_flags nr (mk_bv_const w ic1)
                          | None => CE_BinOp op w fl nl nr
                          end
                      end
                  end
            | CB_Sub =>
                if is_zero_const_expr w nr then nl
                else if cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl
                     then CE_BvConst w 0%N
                else if is_zero_const_expr w nl then
                  match extract_neg_expr w nr with
                  | Some a => a
                  | None => CE_BinOp op w fl nl nr
                  end
                else
                  match extract_const_expr w nr with
                  | Some ic =>
                      CE_BinOp CB_Add w no_binop_flags nl (mk_bv_const w (@Integers.neg w ic))
                  | None => CE_BinOp op w fl nl nr
                  end
            | CB_Mul =>
                if is_one_const_expr w nr then nl
                else if is_one_const_expr w nl then nr
                else if is_zero_const_expr w nr && expr_guaranteed_defined ctx nl
                     then CE_BvConst w 0%N
                else if is_zero_const_expr w nl && expr_guaranteed_defined ctx nr
                     then CE_BvConst w 0%N
                else if is_all_ones_const_expr w nr then
                  CE_BinOp CB_Sub w no_binop_flags (CE_BvConst w 0%N) nl
                else if is_all_ones_const_expr w nl then
                  CE_BinOp CB_Sub w no_binop_flags (CE_BvConst w 0%N) nr
                else
                  match extract_const_expr w nr with
                  | Some ic =>
                      match @Integers.is_power2 w ic with
                      | Some logn => CE_BinOp CB_Shl w no_binop_flags nl (mk_bv_const w logn)
                      | None => CE_BinOp op w fl nl nr
                      end
                  | None =>
                      match extract_const_expr w nl with
                      | Some ic =>
                          match @Integers.is_power2 w ic with
                          | Some logn => CE_BinOp CB_Shl w no_binop_flags nr (mk_bv_const w logn)
                          | None => CE_BinOp CB_Mul w no_binop_flags nr (mk_bv_const w ic)
                          end
                      | None => CE_BinOp op w fl nl nr
                      end
                  end
            | CB_And =>
                if is_all_ones_const_expr w nr then nl
                else if is_all_ones_const_expr w nl then nr
                else if cert_expr_eqb nl nr then nl
                else if is_zero_const_expr w nr && expr_guaranteed_defined ctx nl
                     then CE_BvConst w 0%N
                else if is_zero_const_expr w nl && expr_guaranteed_defined ctx nr
                     then CE_BvConst w 0%N
                else
                  match extract_not_expr w nl, extract_not_expr w nr with
                  | Some a, Some b =>
                      CE_BinOp CB_Xor w no_binop_flags
                        (CE_BinOp CB_Or w no_binop_flags a b)
                        (CE_BvConst w (all_ones_N w))
                  | _, _ =>
                      match extract_const_expr w nr with
                      | Some ic2 =>
                          match extract_binop_rhs_const CB_And w nl with
                          | Some (a, ic1) =>
                              CE_BinOp CB_And w no_binop_flags a
                                (mk_bv_const w (@Integers.and w ic1 ic2))
                          | None => CE_BinOp op w fl nl nr
                          end
                      | None =>
                          match extract_const_expr w nl with
                          | Some ic1 => CE_BinOp CB_And w no_binop_flags nr (mk_bv_const w ic1)
                          | None => CE_BinOp op w fl nl nr
                          end
                      end
                  end
            | CB_Or =>
                if is_zero_const_expr w nr then nl
                else if is_zero_const_expr w nl then nr
                else if cert_expr_eqb nl nr then nl
                else if is_all_ones_const_expr w nr && expr_guaranteed_defined ctx nl
                     then CE_BvConst w (all_ones_N w)
                else if is_all_ones_const_expr w nl && expr_guaranteed_defined ctx nr
                     then CE_BvConst w (all_ones_N w)
                else
                  match extract_not_expr w nl, extract_not_expr w nr with
                  | Some a, Some b =>
                      CE_BinOp CB_Xor w no_binop_flags
                        (CE_BinOp CB_And w no_binop_flags a b)
                        (CE_BvConst w (all_ones_N w))
                  | _, _ =>
                      match extract_const_expr w nr with
                      | Some ic2 =>
                          match extract_binop_rhs_const CB_Or w nl with
                          | Some (a, ic1) =>
                              CE_BinOp CB_Or w no_binop_flags a
                                (mk_bv_const w (@Integers.or w ic1 ic2))
                          | None => CE_BinOp op w fl nl nr
                          end
                      | None =>
                          match extract_const_expr w nl with
                          | Some ic1 => CE_BinOp CB_Or w no_binop_flags nr (mk_bv_const w ic1)
                          | None => CE_BinOp op w fl nl nr
                          end
                      end
                  end
            | CB_Xor =>
                if is_zero_const_expr w nr then nl
                else if is_zero_const_expr w nl then nr
                else if cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl
                     then CE_BvConst w 0%N
                else
                  match extract_const_expr w nr with
                  | Some ic2 =>
                      match extract_binop_rhs_const CB_Xor w nl with
                      | Some (a, ic1) =>
                          let xr := @Integers.xor w ic1 ic2 in
                          if (@Integers.unsigned w xr =? 0)%Z then a
                          else CE_BinOp CB_Xor w no_binop_flags a (mk_bv_const w xr)
                      | None => CE_BinOp op w fl nl nr
                      end
                  | None =>
                      match extract_const_expr w nl with
                      | Some ic1 => CE_BinOp CB_Xor w no_binop_flags nr (mk_bv_const w ic1)
                      | None => CE_BinOp op w fl nl nr
                      end
                  end
            | CB_Shl | CB_LShr | CB_AShr =>
                if is_zero_const_expr w nr then nl
                else
                  match extract_const_expr w nr with
                  | Some ic2 =>
                      match extract_binop_rhs_const op w nl with
                      | Some (a, ic1) =>
                          if (@Integers.unsigned w ic1 + @Integers.unsigned w ic2 <? Z.pos w)%Z
                          then CE_BinOp op w no_binop_flags a
                                 (mk_bv_const w (@Integers.add w ic1 ic2))
                          else CE_BinOp op w fl nl nr
                      | None => CE_BinOp op w fl nl nr
                      end
                  | None => CE_BinOp op w fl nl nr
                  end
            | _ => CE_BinOp op w fl nl nr
            end
          else CE_BinOp op w fl nl nr
      end.

Definition norm_binop_step
  (ctx : ub_ctx) (op : cert_binop) (w : positive) (fl : cert_binop_flags)
  (nl nr : cert_expr) : cert_expr :=
  match try_fold_const_binop op w fl nl nr with
  | Some c => c
  | None =>
      norm_binop_unfolded ctx op w (strip_safe_nsw_flags op w fl nl nr) nl nr
  end.

Lemma try_fold_const_binop_sound :
  forall {Pa : Params} op w fl nl nr out (penv : param_env Pa) foracle,
    try_fold_const_binop op w fl nl nr = Some out ->
    cert_expr_bit_width out = w /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    collect_free_vars [] out = [] /\
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp op w fl nl nr))
      (eval_closed_cert_expr penv foracle out).
Proof.
  intros Pa op w fl nl nr out penv foracle Htf.
  destruct nl as [w1 v1 | | | | | | | |]; try discriminate Htf.
  destruct nr as [w2 v2 | | | | | | | |]; try discriminate Htf.
  cbn [try_fold_const_binop] in Htf.
  destruct (Pos.eqb w1 w && Pos.eqb w2 w) eqn:Eww; [| discriminate Htf].
  apply andb_true_iff in Eww as [Ew1 Ew2]; apply Pos.eqb_eq in Ew1; apply Pos.eqb_eq in Ew2; subst.
  exact (fold_const_binop_sound op w fl v1 v2 out penv foracle Htf).
Qed.

Lemma norm_binop_rhs_const_out :
  forall op0 w fl0 e cval nl nr,
    wf_binop_flags_for op0 fl0 = true ->
    cert_expr_bit_width e = w ->
    wt_cert_expr [] e = true ->
    is_let_free_expr e = true ->
    incl (collect_free_vars [] e) (collect_free_vars [] nl ++ collect_free_vars [] nr) ->
    let out := CE_BinOp op0 w fl0 e (CE_BvConst w cval) in
    cert_expr_bit_width out = w /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    incl (collect_free_vars [] out) (collect_free_vars [] nl ++ collect_free_vars [] nr).
Proof.
  intros op0 w fl0 e cval nl nr Hfl Hw Ht Hlf Hinc; cbn.
  rewrite Hfl, Ht, Hw, Pos.eqb_refl, Hlf, app_nil_r; repeat split; exact Hinc.
Qed.

Lemma norm_binop_lhs_const_out :
  forall op0 w fl0 cval e nl nr,
    wf_binop_flags_for op0 fl0 = true ->
    cert_expr_bit_width e = w ->
    wt_cert_expr [] e = true ->
    is_let_free_expr e = true ->
    incl (collect_free_vars [] e) (collect_free_vars [] nl ++ collect_free_vars [] nr) ->
    let out := CE_BinOp op0 w fl0 (CE_BvConst w cval) e in
    cert_expr_bit_width out = w /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    incl (collect_free_vars [] out) (collect_free_vars [] nl ++ collect_free_vars [] nr).
Proof.
  intros op0 w fl0 cval e nl nr Hfl Hw Ht Hlf Hinc; cbn.
  rewrite Hfl, Ht, Hw, Pos.eqb_refl, Hlf; repeat split; exact Hinc.
Qed.

Lemma wf_no_binop_flags : forall op0, wf_binop_flags_for op0 no_binop_flags = true.
Proof. intros []; reflexivity. Qed.

Local Lemma norm_binop_typing_def :
  forall op w fl nl nr,
    wf_binop_flags_for op fl = true ->
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    is_let_free_expr nl = true ->
    is_let_free_expr nr = true ->
    cert_expr_bit_width (CE_BinOp op w fl nl nr) = w /\
    wt_cert_expr [] (CE_BinOp op w fl nl nr) = true /\
    is_let_free_expr (CE_BinOp op w fl nl nr) = true /\
    incl (collect_free_vars [] (CE_BinOp op w fl nl nr))
         (collect_free_vars [] nl ++ collect_free_vars [] nr).
Proof.
  intros op w fl nl nr Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r.
  cbn; rewrite Hfl, Htl, Htr, Hwl, Hwr, !Pos.eqb_refl, Hfl_l, Hfl_r.
  repeat split; apply incl_refl.
Qed.

Local Lemma norm_binop_typing_bvconst :
  forall w cval nl nr,
    cert_expr_bit_width (CE_BvConst w cval) = w /\
    wt_cert_expr [] (CE_BvConst w cval) = true /\
    is_let_free_expr (CE_BvConst w cval) = true /\
    incl (collect_free_vars [] (CE_BvConst w cval))
         (collect_free_vars [] nl ++ collect_free_vars [] nr).
Proof.
  intros w cval nl nr; cbn; repeat split; intros x [].
Qed.

Local Lemma norm_binop_typing_sub_l :
  forall op0 w a v nl nr,
    nl = CE_BinOp op0 w no_binop_flags a (CE_BvConst w v) ->
    wt_cert_expr [] nl = true ->
    is_let_free_expr nl = true ->
    cert_expr_bit_width a = w /\
    wt_cert_expr [] a = true /\
    is_let_free_expr a = true /\
    incl (collect_free_vars [] a) (collect_free_vars [] nl ++ collect_free_vars [] nr).
Proof.
  intros op0 w a v nl nr Heq Htl Hfl_l; subst nl.
  cbn [wt_cert_expr cert_expr_bit_width] in Htl; cbn in Hfl_l.
  rewrite !andb_true_iff in Htl; rewrite !andb_true_iff in Hfl_l.
  destruct Htl as ((((_ & Hta) & _) & Hwa) & _); destruct Hfl_l as [Hlfa _].
  apply Pos.eqb_eq in Hwa.
  repeat split; [exact Hwa | exact Hta | exact Hlfa |
                 cbn; rewrite app_nil_r; apply incl_appl, incl_refl].
Qed.

Local Lemma norm_binop_unfolded_typing_arith :
  forall ctx op w fl nl nr,
    (op = CB_Add \/ op = CB_Sub \/ op = CB_Mul) ->
    wf_binop_flags_for op fl = true ->
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    is_let_free_expr nl = true ->
    is_let_free_expr nr = true ->
    let out := norm_binop_unfolded ctx op w fl nl nr in
    cert_expr_bit_width out = w /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    incl (collect_free_vars [] out) (collect_free_vars [] nl ++ collect_free_vars [] nr).
Proof.
  intros ctx op w fl nl nr Hop Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r; cbn zeta.
  pose proof (norm_binop_typing_def op w fl nl nr Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r) as Hdef_out.
  assert (Hl_out :
    cert_expr_bit_width nl = w /\ wt_cert_expr [] nl = true /\ is_let_free_expr nl = true /\
    incl (collect_free_vars [] nl) (collect_free_vars [] nl ++ collect_free_vars [] nr))
    by (repeat split; [exact Hwl | exact Htl | exact Hfl_l | apply incl_appl, incl_refl]).
  assert (Hr_out :
    cert_expr_bit_width nr = w /\ wt_cert_expr [] nr = true /\ is_let_free_expr nr = true /\
    incl (collect_free_vars [] nr) (collect_free_vars [] nl ++ collect_free_vars [] nr))
    by (repeat split; [exact Hwr | exact Htr | exact Hfl_r | apply incl_appr, incl_refl]).
  destruct Hop as [-> | [-> | ->]]; unfold norm_binop_unfolded.
  - (* CB_Add *)
    destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
    destruct (is_zero_const_expr w nr); [exact Hl_out |].
    destruct (is_zero_const_expr w nl); [exact Hr_out |].
    destruct ((1 <? w)%positive && cert_expr_eqb nl nr);
      [exact (norm_binop_rhs_const_out CB_Shl w no_binop_flags nl 1%N nl nr
                eq_refl Hwl Htl Hfl_l (incl_appl _ (incl_refl _))) |].
    destruct (extract_neg_expr w nr) as [y |] eqn:Eneg.
    + pose proof (extract_neg_expr_inv w nr y Eneg) as Heqy; subst nr.
      cbn [wt_cert_expr cert_expr_bit_width] in Htr; cbn in Hfl_r; rewrite !andb_true_iff in Htr.
      destruct Htr as ((((_ & _) & Hty) & _) & Hwy); apply Pos.eqb_eq in Hwy.
      cbn - [Pos.eqb]; rewrite Htl, Hty, Hwl, Hwy, !Pos.eqb_refl, Hfl_l, Hfl_r;
        cbn; repeat split; apply incl_refl.
    + destruct (extract_const_expr w nr) as [ic2 |].
      * destruct (extract_binop_rhs_const CB_Add w nl) as [[a ic1] |] eqn:Erc; [| exact Hdef_out].
        destruct (extract_binop_rhs_const_inv CB_Add w nl a ic1 Erc) as [v1 [Heql _]].
        destruct (norm_binop_typing_sub_l CB_Add w a v1 nl nr Heql Htl Hfl_l)
          as (Hwa & Hta & Hlfa & Hinca).
        cbn zeta; destruct (@Integers.unsigned w _ =? 0)%Z;
          [repeat split; assumption |
           unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Add w no_binop_flags a _ nl nr
                                        eq_refl Hwa Hta Hlfa Hinca)].
      * destruct (extract_const_expr w nl) as [ic1 |]; [| exact Hdef_out].
        unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Add w no_binop_flags nr _ nl nr
                                     eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))).
  - (* CB_Sub *)
    destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
    destruct (is_zero_const_expr w nr); [exact Hl_out |].
    destruct (cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl);
      [apply norm_binop_typing_bvconst |].
    destruct (is_zero_const_expr w nl).
    + destruct (extract_neg_expr w nr) as [a |] eqn:Eneg; [| exact Hdef_out].
      pose proof (extract_neg_expr_inv w nr a Eneg) as Heqa; subst nr.
      cbn [wt_cert_expr cert_expr_bit_width] in Htr; cbn in Hfl_r; rewrite !andb_true_iff in Htr.
      destruct Htr as ((((_ & _) & Hta) & _) & Hwa); apply Pos.eqb_eq in Hwa.
      repeat split; [exact Hwa | exact Hta | exact Hfl_r | cbn; apply incl_appr, incl_refl].
    + destruct (extract_const_expr w nr) as [ic |]; [| exact Hdef_out].
      unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Add w no_binop_flags nl _ nl nr
                                   eq_refl Hwl Htl Hfl_l (incl_appl _ (incl_refl _))).
  - (* CB_Mul *)
    destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
    destruct (is_one_const_expr w nr); [exact Hl_out |].
    destruct (is_one_const_expr w nl); [exact Hr_out |].
    destruct (is_zero_const_expr w nr && expr_guaranteed_defined ctx nl);
      [apply norm_binop_typing_bvconst |].
    destruct (is_zero_const_expr w nl && expr_guaranteed_defined ctx nr);
      [apply norm_binop_typing_bvconst |].
    destruct (is_all_ones_const_expr w nr);
      [exact (norm_binop_lhs_const_out CB_Sub w no_binop_flags 0%N nl nl nr
                eq_refl Hwl Htl Hfl_l (incl_appl _ (incl_refl _))) |].
    destruct (is_all_ones_const_expr w nl);
      [exact (norm_binop_lhs_const_out CB_Sub w no_binop_flags 0%N nr nl nr
                eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))) |].
    destruct (extract_const_expr w nr) as [ic |].
    + destruct (@Integers.is_power2 w ic) as [logn |]; [| exact Hdef_out].
      unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Shl w no_binop_flags nl _ nl nr
                                   eq_refl Hwl Htl Hfl_l (incl_appl _ (incl_refl _))).
    + destruct (extract_const_expr w nl) as [ic |]; [| exact Hdef_out].
      destruct (@Integers.is_power2 w ic) as [logn |]; unfold mk_bv_const;
        [exact (norm_binop_rhs_const_out CB_Shl w no_binop_flags nr _ nl nr
                  eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))) |
         exact (norm_binop_rhs_const_out CB_Mul w no_binop_flags nr _ nl nr
                  eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _)))].
Qed.

Local Lemma norm_binop_unfolded_typing_shift :
  forall ctx op w fl nl nr,
    (op = CB_Shl \/ op = CB_LShr \/ op = CB_AShr) ->
    wf_binop_flags_for op fl = true ->
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    is_let_free_expr nl = true ->
    is_let_free_expr nr = true ->
    let out := norm_binop_unfolded ctx op w fl nl nr in
    cert_expr_bit_width out = w /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    incl (collect_free_vars [] out) (collect_free_vars [] nl ++ collect_free_vars [] nr).
Proof.
  intros ctx op w fl nl nr Hop Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r; cbn zeta.
  pose proof (norm_binop_typing_def op w fl nl nr Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r) as Hdef_out.
  assert (Hl_out :
    cert_expr_bit_width nl = w /\ wt_cert_expr [] nl = true /\ is_let_free_expr nl = true /\
    incl (collect_free_vars [] nl) (collect_free_vars [] nl ++ collect_free_vars [] nr))
    by (repeat split; [exact Hwl | exact Htl | exact Hfl_l | apply incl_appl, incl_refl]).
  destruct Hop as [-> | [-> | ->]]; unfold norm_binop_unfolded.
  - (* CB_Shl *)
    destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
    destruct (is_zero_const_expr w nr); [exact Hl_out |].
    destruct (extract_const_expr w nr) as [ic2 |]; [| exact Hdef_out].
    destruct (extract_binop_rhs_const CB_Shl w nl) as [[a ic1] |] eqn:Erc; [| exact Hdef_out].
    destruct (extract_binop_rhs_const_inv CB_Shl w nl a ic1 Erc) as [v1 [Heql _]].
    destruct (norm_binop_typing_sub_l CB_Shl w a v1 nl nr Heql Htl Hfl_l)
      as (Hwa & Hta & Hlfa & Hinca).
    destruct (_ <? Z.pos w)%Z; [| exact Hdef_out].
    unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Shl w no_binop_flags a _ nl nr
                                 eq_refl Hwa Hta Hlfa Hinca).
  - (* CB_LShr *)
    destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
    destruct (is_zero_const_expr w nr); [exact Hl_out |].
    destruct (extract_const_expr w nr) as [ic2 |]; [| exact Hdef_out].
    destruct (extract_binop_rhs_const CB_LShr w nl) as [[a ic1] |] eqn:Erc; [| exact Hdef_out].
    destruct (extract_binop_rhs_const_inv CB_LShr w nl a ic1 Erc) as [v1 [Heql _]].
    destruct (norm_binop_typing_sub_l CB_LShr w a v1 nl nr Heql Htl Hfl_l)
      as (Hwa & Hta & Hlfa & Hinca).
    destruct (_ <? Z.pos w)%Z; [| exact Hdef_out].
    unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_LShr w no_binop_flags a _ nl nr
                                 eq_refl Hwa Hta Hlfa Hinca).
  - (* CB_AShr *)
    destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
    destruct (is_zero_const_expr w nr); [exact Hl_out |].
    destruct (extract_const_expr w nr) as [ic2 |]; [| exact Hdef_out].
    destruct (extract_binop_rhs_const CB_AShr w nl) as [[a ic1] |] eqn:Erc; [| exact Hdef_out].
    destruct (extract_binop_rhs_const_inv CB_AShr w nl a ic1 Erc) as [v1 [Heql _]].
    destruct (norm_binop_typing_sub_l CB_AShr w a v1 nl nr Heql Htl Hfl_l)
      as (Hwa & Hta & Hlfa & Hinca).
    destruct (_ <? Z.pos w)%Z; [| exact Hdef_out].
    unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_AShr w no_binop_flags a _ nl nr
                                 eq_refl Hwa Hta Hlfa Hinca).
Qed.

Local Lemma norm_binop_unfolded_typing_bitwise :
  forall ctx op w fl nl nr,
    (op = CB_And \/ op = CB_Or \/ op = CB_Xor) ->
    wf_binop_flags_for op fl = true ->
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    is_let_free_expr nl = true ->
    is_let_free_expr nr = true ->
    let out := norm_binop_unfolded ctx op w fl nl nr in
    cert_expr_bit_width out = w /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    incl (collect_free_vars [] out) (collect_free_vars [] nl ++ collect_free_vars [] nr).
Proof.
  intros ctx op w fl nl nr Hop Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r; cbn zeta.
  pose proof (norm_binop_typing_def op w fl nl nr Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r) as Hdef_out.
  assert (Hl_out :
    cert_expr_bit_width nl = w /\ wt_cert_expr [] nl = true /\ is_let_free_expr nl = true /\
    incl (collect_free_vars [] nl) (collect_free_vars [] nl ++ collect_free_vars [] nr))
    by (repeat split; [exact Hwl | exact Htl | exact Hfl_l | apply incl_appl, incl_refl]).
  assert (Hr_out :
    cert_expr_bit_width nr = w /\ wt_cert_expr [] nr = true /\ is_let_free_expr nr = true /\
    incl (collect_free_vars [] nr) (collect_free_vars [] nl ++ collect_free_vars [] nr))
    by (repeat split; [exact Hwr | exact Htr | exact Hfl_r | apply incl_appr, incl_refl]).
  destruct Hop as [-> | [-> | ->]]; unfold norm_binop_unfolded.
  - (* CB_And *)
    destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
    destruct (is_all_ones_const_expr w nr); [exact Hl_out |].
    destruct (is_all_ones_const_expr w nl); [exact Hr_out |].
    destruct (cert_expr_eqb nl nr); [exact Hl_out |].
    destruct (is_zero_const_expr w nr && expr_guaranteed_defined ctx nl);
      [apply norm_binop_typing_bvconst |].
    destruct (is_zero_const_expr w nl && expr_guaranteed_defined ctx nr);
      [apply norm_binop_typing_bvconst |].
    assert (Hrest_and :
      let out_r :=
        match extract_const_expr w nr with
        | Some ic2 =>
            match extract_binop_rhs_const CB_And w nl with
            | Some (a0, ic1) =>
                CE_BinOp CB_And w no_binop_flags a0 (mk_bv_const w (@Integers.and w ic1 ic2))
            | None => CE_BinOp CB_And w fl nl nr
            end
        | None =>
            match extract_const_expr w nl with
            | Some ic1 => CE_BinOp CB_And w no_binop_flags nr (mk_bv_const w ic1)
            | None => CE_BinOp CB_And w fl nl nr
            end
        end in
      cert_expr_bit_width out_r = w /\ wt_cert_expr [] out_r = true /\
      is_let_free_expr out_r = true /\
      incl (collect_free_vars [] out_r) (collect_free_vars [] nl ++ collect_free_vars [] nr)).
    { cbn zeta; destruct (extract_const_expr w nr) as [ic2 |].
      - destruct (extract_binop_rhs_const CB_And w nl) as [[a0 ic1] |] eqn:Erc; [| exact Hdef_out].
        destruct (extract_binop_rhs_const_inv CB_And w nl a0 ic1 Erc) as [v1 [Heql _]].
        destruct (norm_binop_typing_sub_l CB_And w a0 v1 nl nr Heql Htl Hfl_l)
          as (Hwa & Hta & Hlfa & Hinca).
        unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_And w no_binop_flags a0 _ nl nr
                                     eq_refl Hwa Hta Hlfa Hinca).
      - destruct (extract_const_expr w nl) as [ic1 |]; [| exact Hdef_out].
        unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_And w no_binop_flags nr _ nl nr
                                     eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))). }
    cbn zeta in Hrest_and.
    destruct (extract_not_expr w nl) as [a |] eqn:Enl,
             (extract_not_expr w nr) as [b |] eqn:Enr;
      try exact Hrest_and.
    pose proof (extract_not_expr_inv w nl a Enl) as Heql.
    destruct (norm_binop_typing_sub_l CB_Xor w a (all_ones_N w) nl nr Heql Htl Hfl_l)
      as (Hwa & Hta & Hlfa & _).
    pose proof (extract_not_expr_inv w nr b Enr) as Heqr; subst nl nr.
    cbn [wt_cert_expr cert_expr_bit_width] in Htr; cbn in Hfl_r;
      rewrite !andb_true_iff in Htr; rewrite !andb_true_iff in Hfl_r.
    destruct Htr as ((((_ & Htb) & _) & Hwb) & _); destruct Hfl_r as [Hlfb _].
    apply Pos.eqb_eq in Hwb.
    cbn - [Pos.eqb]; rewrite Hta, Htb, Hwa, Hwb, !Pos.eqb_refl, Hlfa, Hlfb, !app_nil_r.
    cbn; repeat split; apply incl_refl.
  - (* CB_Or *)
    destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
    destruct (is_zero_const_expr w nr); [exact Hl_out |].
    destruct (is_zero_const_expr w nl); [exact Hr_out |].
    destruct (cert_expr_eqb nl nr); [exact Hl_out |].
    destruct (is_all_ones_const_expr w nr && expr_guaranteed_defined ctx nl);
      [apply norm_binop_typing_bvconst |].
    destruct (is_all_ones_const_expr w nl && expr_guaranteed_defined ctx nr);
      [apply norm_binop_typing_bvconst |].
    assert (Hrest_or :
      let out_r :=
        match extract_const_expr w nr with
        | Some ic2 =>
            match extract_binop_rhs_const CB_Or w nl with
            | Some (a0, ic1) =>
                CE_BinOp CB_Or w no_binop_flags a0 (mk_bv_const w (@Integers.or w ic1 ic2))
            | None => CE_BinOp CB_Or w fl nl nr
            end
        | None =>
            match extract_const_expr w nl with
            | Some ic1 => CE_BinOp CB_Or w no_binop_flags nr (mk_bv_const w ic1)
            | None => CE_BinOp CB_Or w fl nl nr
            end
        end in
      cert_expr_bit_width out_r = w /\ wt_cert_expr [] out_r = true /\
      is_let_free_expr out_r = true /\
      incl (collect_free_vars [] out_r) (collect_free_vars [] nl ++ collect_free_vars [] nr)).
    { cbn zeta; destruct (extract_const_expr w nr) as [ic2 |].
      - destruct (extract_binop_rhs_const CB_Or w nl) as [[a0 ic1] |] eqn:Erc; [| exact Hdef_out].
        destruct (extract_binop_rhs_const_inv CB_Or w nl a0 ic1 Erc) as [v1 [Heql _]].
        destruct (norm_binop_typing_sub_l CB_Or w a0 v1 nl nr Heql Htl Hfl_l)
          as (Hwa & Hta & Hlfa & Hinca).
        unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Or w no_binop_flags a0 _ nl nr
                                     eq_refl Hwa Hta Hlfa Hinca).
      - destruct (extract_const_expr w nl) as [ic1 |]; [| exact Hdef_out].
        unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Or w no_binop_flags nr _ nl nr
                                     eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))). }
    cbn zeta in Hrest_or.
    destruct (extract_not_expr w nl) as [a |] eqn:Enl,
             (extract_not_expr w nr) as [b |] eqn:Enr;
      try exact Hrest_or.
    pose proof (extract_not_expr_inv w nl a Enl) as Heql.
    destruct (norm_binop_typing_sub_l CB_Xor w a (all_ones_N w) nl nr Heql Htl Hfl_l)
      as (Hwa & Hta & Hlfa & _).
    pose proof (extract_not_expr_inv w nr b Enr) as Heqr; subst nl nr.
    cbn [wt_cert_expr cert_expr_bit_width] in Htr; cbn in Hfl_r;
      rewrite !andb_true_iff in Htr; rewrite !andb_true_iff in Hfl_r.
    destruct Htr as ((((_ & Htb) & _) & Hwb) & _); destruct Hfl_r as [Hlfb _].
    apply Pos.eqb_eq in Hwb.
    cbn - [Pos.eqb]; rewrite Hta, Htb, Hwa, Hwb, !Pos.eqb_refl, Hlfa, Hlfb, !app_nil_r.
    cbn; repeat split; apply incl_refl.
  - (* CB_Xor *)
    destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
    destruct (is_zero_const_expr w nr); [exact Hl_out |].
    destruct (is_zero_const_expr w nl); [exact Hr_out |].
    destruct (cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl);
      [apply norm_binop_typing_bvconst |].
    destruct (extract_const_expr w nr) as [ic2 |].
    + destruct (extract_binop_rhs_const CB_Xor w nl) as [[a ic1] |] eqn:Erc; [| exact Hdef_out].
      destruct (extract_binop_rhs_const_inv CB_Xor w nl a ic1 Erc) as [v1 [Heql _]].
      destruct (norm_binop_typing_sub_l CB_Xor w a v1 nl nr Heql Htl Hfl_l)
        as (Hwa & Hta & Hlfa & Hinca).
      cbn zeta; destruct (@Integers.unsigned w _ =? 0)%Z;
        [repeat split; assumption |
         unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Xor w no_binop_flags a _ nl nr
                                      eq_refl Hwa Hta Hlfa Hinca)].
    + destruct (extract_const_expr w nl) as [ic1 |]; [| exact Hdef_out].
      unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Xor w no_binop_flags nr _ nl nr
                                   eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))).
Qed.

Lemma norm_binop_unfolded_typing :
  forall ctx op w fl nl nr,
    wf_binop_flags_for op fl = true ->
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    is_let_free_expr nl = true ->
    is_let_free_expr nr = true ->
    let out := norm_binop_unfolded ctx op w fl nl nr in
    cert_expr_bit_width out = w /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    incl (collect_free_vars [] out) (collect_free_vars [] nl ++ collect_free_vars [] nr).
Proof.
  intros ctx op w fl nl nr Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r; cbn zeta.
  pose proof (norm_binop_typing_def op w fl nl nr Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r) as Hdef_out.
  assert (Hl_out :
    cert_expr_bit_width nl = w /\ wt_cert_expr [] nl = true /\ is_let_free_expr nl = true /\
    incl (collect_free_vars [] nl) (collect_free_vars [] nl ++ collect_free_vars [] nr))
    by (repeat split; [exact Hwl | exact Htl | exact Hfl_l | apply incl_appl, incl_refl]).
  destruct op.
  - exact (norm_binop_unfolded_typing_arith ctx CB_Add w fl nl nr (or_introl eq_refl)
             Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r).
  - exact (norm_binop_unfolded_typing_arith ctx CB_Sub w fl nl nr (or_intror (or_introl eq_refl))
             Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r).
  - exact (norm_binop_unfolded_typing_arith ctx CB_Mul w fl nl nr (or_intror (or_intror eq_refl))
             Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r).
  - (* CB_UDiv *)
    unfold norm_binop_unfolded.
    destruct (negb (cbf_nuw fl) && negb (cbf_nsw fl) && negb (cbf_disjoint fl)) eqn:Efl_ok;
      [| exact Hdef_out].
    destruct (extract_const_expr w nr) as [ic |]; [| exact Hdef_out].
    destruct (@Integers.is_power2 w ic) as [logn |]; [| exact Hdef_out].
    destruct (@Integers.unsigned w logn =? 0)%Z; [exact Hl_out |].
    unfold mk_bv_const.
    exact (norm_binop_rhs_const_out CB_LShr w fl nl _ nl nr
             Efl_ok Hwl Htl Hfl_l (incl_appl _ (incl_refl _))).
  - (* CB_SDiv *)
    unfold norm_binop_unfolded; destruct (cert_binop_flags_eqb fl no_binop_flags); exact Hdef_out.
  - (* CB_URem *)
    unfold norm_binop_unfolded.
    destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
    destruct (extract_const_expr w nr) as [ic |]; [| exact Hdef_out].
    destruct (@Integers.is_power2 w ic); [| exact Hdef_out].
    unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_And w no_binop_flags nl _ nl nr
                                 eq_refl Hwl Htl Hfl_l (incl_appl _ (incl_refl _))).
  - (* CB_SRem *)
    unfold norm_binop_unfolded; destruct (cert_binop_flags_eqb fl no_binop_flags); exact Hdef_out.
  - exact (norm_binop_unfolded_typing_shift ctx CB_Shl w fl nl nr (or_introl eq_refl)
             Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r).
  - exact (norm_binop_unfolded_typing_shift ctx CB_LShr w fl nl nr (or_intror (or_introl eq_refl))
             Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r).
  - exact (norm_binop_unfolded_typing_shift ctx CB_AShr w fl nl nr (or_intror (or_intror eq_refl))
             Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r).
  - exact (norm_binop_unfolded_typing_bitwise ctx CB_And w fl nl nr (or_introl eq_refl)
             Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r).
  - exact (norm_binop_unfolded_typing_bitwise ctx CB_Or w fl nl nr (or_intror (or_introl eq_refl))
             Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r).
  - exact (norm_binop_unfolded_typing_bitwise ctx CB_Xor w fl nl nr (or_intror (or_intror eq_refl))
             Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r).
Qed.

Lemma norm_binop_step_typing :
  forall ctx op w fl nl nr,
    wf_binop_flags_for op fl = true ->
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    is_let_free_expr nl = true ->
    is_let_free_expr nr = true ->
    let out := norm_binop_step ctx op w fl nl nr in
    cert_expr_bit_width out = w /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    incl (collect_free_vars [] out) (collect_free_vars [] nl ++ collect_free_vars [] nr).
Proof.
  intros ctx op w fl nl nr Hfl Hwl Hwr Htl Htr Hfl_l Hfl_r; cbn zeta.
  unfold norm_binop_step.
  destruct (try_fold_const_binop op w fl nl nr) as [c |] eqn:Etc.
  - destruct nl as [w1 v1 | | | | | | | |]; try discriminate Etc.
    destruct nr as [w2 v2 | | | | | | | |]; try discriminate Etc.
    cbn [try_fold_const_binop] in Etc.
    destruct (Pos.eqb w1 w && Pos.eqb w2 w); [| discriminate Etc].
    unfold fold_const_binop in Etc;
      destruct op;
      repeat match type of Etc with
             | (if ?b then None else _) = Some _ =>
                 destruct b; [discriminate Etc |]
             end;
      inversion Etc; subst c; clear Etc;
      repeat match goal with
             | |- context [if ?b then _ else _] => destruct b
             end;
      unfold mk_bv_const; cbn; repeat split; intros x [].
  - exact (norm_binop_unfolded_typing ctx op w (strip_safe_nsw_flags op w fl nl nr) nl nr
             (strip_safe_nsw_flags_wf op w fl nl nr Hfl) Hwl Hwr Htl Htr Hfl_l Hfl_r).
Qed.

Definition is_commutative_binop (op : cert_binop) : bool :=
  match op with
  | CB_Add | CB_Mul | CB_And | CB_Or | CB_Xor => true
  | _ => false
  end.

Definition swap_cert_icmp (pr : cert_icmp_pred) : cert_icmp_pred :=
  match pr with
  | CIP_Eq  => CIP_Eq
  | CIP_Ne  => CIP_Ne
  | CIP_Ult => CIP_Ugt
  | CIP_Ule => CIP_Uge
  | CIP_Ugt => CIP_Ult
  | CIP_Uge => CIP_Ule
  | CIP_Slt => CIP_Sgt
  | CIP_Sle => CIP_Sge
  | CIP_Sgt => CIP_Slt
  | CIP_Sge => CIP_Sle
  end.

Lemma alg_add_carry_comm : forall w (x y : @Integers.bit_int w),
  @Integers.add_carry w x y (@Integers.zero w) =
  @Integers.add_carry w y x (@Integers.zero w).
Proof.
  intros w x y; unfold Integers.add_carry.
  rewrite (Z.add_comm (@Integers.unsigned w x) (@Integers.unsigned w y)); reflexivity.
Qed.

Lemma alg_add_overflow_comm : forall w (x y : @Integers.bit_int w),
  @Integers.add_overflow w x y (@Integers.zero w) =
  @Integers.add_overflow w y x (@Integers.zero w).
Proof.
  intros w x y; unfold Integers.add_overflow.
  rewrite (Z.add_comm (@Integers.signed w x) (@Integers.signed w y)); reflexivity.
Qed.

Lemma eval_iop_commut :
  forall {Pa : Params} op fl w (vl vr : @dvalue Pa),
    is_commutative_binop op = true ->
    wf_scalar_dvalue w vl ->
    wf_scalar_dvalue w vr ->
    @eval_iop Pa (cert_to_ibinop op fl) vl vr =
    @eval_iop Pa (cert_to_ibinop op fl) vr vl.
Proof.
  intros Pa op fl w vl vr Hcomm [-> | [il ->]] [-> | [ir ->]].
  - reflexivity.
  - destruct op; cbn in Hcomm; try discriminate; reflexivity.
  - destruct op; cbn in Hcomm; try discriminate; reflexivity.
  - unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
    destruct op; cbn in Hcomm; try discriminate;
      unfold cert_to_ibinop, eval_int_op; cbn.
    + rewrite alg_add_carry_comm, alg_add_overflow_comm, (@Integers.add_commut w il ir).
      reflexivity.
    + rewrite (@Integers.mul_commut w il ir),
              (Z.mul_comm (@Integers.unsigned w il) (@Integers.unsigned w ir)),
              (Z.mul_comm (@Integers.signed w il) (@Integers.signed w ir)).
      reflexivity.
    + rewrite (@Integers.and_commut w il ir); reflexivity.
    + rewrite (@Integers.or_commut w il ir), (@Integers.xor_commut w il ir); reflexivity.
    + rewrite (@Integers.xor_commut w il ir); reflexivity.
Qed.

Local Lemma norm_binop_eval_id_r :
  forall {Pa : Params} op w fl nl nr (penv : param_env Pa) foracle cval,
    cert_expr_bit_width nl = w ->
    wt_cert_expr [] nl = true ->
    wf_param_env_for (collect_free_vars [] nl) penv ->
    cert_binop_flags_eqb fl no_binop_flags = true ->
    nr = CE_BvConst w cval ->
    (forall i : @Integers.bit_int w,
       @eval_iop Pa (cert_to_ibinop op no_binop_flags)
         (DVALUE_Base (@DVALUE_I Pa w i))
         (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N cval)))) =
       raise_ret (DVALUE_Base (@DVALUE_I Pa w i))) ->
    is_div_or_rem_op op = false ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp op w fl nl nr))
      (eval_closed_cert_expr penv foracle nl).
Proof.
  intros Pa op w fl nl nr penv foracle cval Hwl Htl Hpl Hfl0 -> Hiop Hndiv.
  apply cert_binop_flags_eqb_eq in Hfl0; subst fl.
  unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
  destruct (eval_cert_expr_totality nl [] penv [] foracle Htl wf_let_val_env_nil Hpl)
    as [[msgl ->] | [vl [-> Hwfl]]]; cbn [eou_bind]; [exact I |].
  rewrite Hwl in Hwfl; destruct Hwfl as [-> | [il ->]].
  - destruct op; cbn in Hndiv; try discriminate; cbn; reflexivity.
  - rewrite Hiop; cbn; reflexivity.
Qed.

Local Lemma norm_binop_eval_id_l :
  forall {Pa : Params} op w fl nl nr (penv : param_env Pa) foracle cval,
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nr = true ->
    wf_param_env_for (collect_free_vars [] nr) penv ->
    cert_binop_flags_eqb fl no_binop_flags = true ->
    nl = CE_BvConst w cval ->
    (forall i : @Integers.bit_int w,
       @eval_iop Pa (cert_to_ibinop op no_binop_flags)
         (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N cval))))
         (DVALUE_Base (@DVALUE_I Pa w i)) =
       raise_ret (DVALUE_Base (@DVALUE_I Pa w i))) ->
    is_div_or_rem_op op = false ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp op w fl nl nr))
      (eval_closed_cert_expr penv foracle nr).
Proof.
  intros Pa op w fl nl nr penv foracle cval Hwr Htr Hpr Hfl0 -> Hiop Hndiv.
  apply cert_binop_flags_eqb_eq in Hfl0; subst fl.
  unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
  destruct (eval_cert_expr_totality nr [] penv [] foracle Htr wf_let_val_env_nil Hpr)
    as [[msgr ->] | [vr [-> Hwfr]]]; cbn [eou_bind]; [exact I |].
  rewrite Hwr in Hwfr; destruct Hwfr as [-> | [ir ->]].
  - destruct op; cbn in Hndiv; try discriminate; cbn; reflexivity.
  - rewrite Hiop; cbn; reflexivity.
Qed.

Local Lemma norm_binop_eval_comm_l :
  forall {Pa : Params} op w fl nl nr (penv : param_env Pa) foracle v1,
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nr = true ->
    wf_param_env_for (collect_free_vars [] nr) penv ->
    cert_binop_flags_eqb fl no_binop_flags = true ->
    nl = CE_BvConst w v1 ->
    is_commutative_binop op = true ->
    is_div_or_rem_op op = false ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp op w fl nl nr))
      (eval_closed_cert_expr penv foracle
         (CE_BinOp op w no_binop_flags nr (mk_bv_const w (@Integers.repr w (Z.of_N v1))))).
Proof.
  intros Pa op w fl nl nr penv foracle v1 Hwr Htr Hpr Hfl0 -> Hcomm Hndiv.
  apply cert_binop_flags_eqb_eq in Hfl0; subst fl.
  unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
  rewrite repr_of_N_to_N_unsigned.
  destruct (eval_cert_expr_totality nr [] penv [] foracle Htr wf_let_val_env_nil Hpr)
    as [[msgr ->] | [vr [-> Hwfvr]]]; cbn [eou_bind]; [exact I |].
  rewrite Hwr in Hwfvr.
  rewrite (eval_iop_commut op no_binop_flags w _ vr Hcomm
             (or_intror (ex_intro _ _ eq_refl)) Hwfvr).
  apply equiv_eou_dvalue_refl.
Qed.

Local Lemma norm_binop_eval_reassoc :
  forall {Pa : Params} op w fl nl nr (penv : param_env Pa) foracle a v1 v2
         (iop : @Integers.bit_int w -> @Integers.bit_int w -> @Integers.bit_int w),
    wt_cert_expr [] nl = true ->
    wf_param_env_for (collect_free_vars [] nl) penv ->
    cert_binop_flags_eqb fl no_binop_flags = true ->
    nl = CE_BinOp op w no_binop_flags a (CE_BvConst w v1) ->
    nr = CE_BvConst w v2 ->
    is_div_or_rem_op op = false ->
    (forall x y,
       eval_int_op (cert_to_ibinop op no_binop_flags) x y =
       raise_ret (@DVALUE_I Pa w (iop x y))) ->
    (forall x y z, iop (iop x y) z = iop x (iop y z)) ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp op w fl nl nr))
      (eval_closed_cert_expr penv foracle
         (CE_BinOp op w no_binop_flags a
            (mk_bv_const w (iop (@Integers.repr w (Z.of_N v1)) (@Integers.repr w (Z.of_N v2)))))).
Proof.
  intros Pa op w fl nl nr penv foracle a v1 v2 iop Htl Hpl Hfl0 -> -> Hndiv Hiop Hassoc.
  apply cert_binop_flags_eqb_eq in Hfl0; subst fl.
  cbn [wt_cert_expr cert_expr_bit_width] in Htl; cbn in Hpl;
    rewrite !andb_true_iff in Htl; destruct Htl as ((((_ & Hta) & _) & Hwa) & _).
  apply Pos.eqb_eq in Hwa; rewrite app_nil_r in Hpl.
  unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
  rewrite repr_of_N_to_N_unsigned.
  destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpl)
    as [[msga ->] | [va [-> Hwfva]]]; cbn [eou_bind]; [exact I |].
  rewrite Hwa in Hwfva; destruct Hwfva as [-> | [ia ->]].
  - assert (Hp1 : forall c0,
                    @eval_iop Pa (cert_to_ibinop op no_binop_flags)
                      (DVALUE_Base DVALUE_Poison) (DVALUE_Base (@DVALUE_I Pa w c0)) =
                    raise_ret (DVALUE_Base DVALUE_Poison))
      by (intros c0; destruct op; cbn in Hndiv; try discriminate; reflexivity).
    rewrite !Hp1; cbn [eou_bind]; rewrite !Hp1; apply equiv_eou_dvalue_refl.
  - assert (Hiop' : forall x y,
              @eval_iop Pa (cert_to_ibinop op no_binop_flags)
                (DVALUE_Base (@DVALUE_I Pa w x)) (DVALUE_Base (@DVALUE_I Pa w y)) =
              raise_ret (DVALUE_Base (@DVALUE_I Pa w (iop x y))))
      by (intros x y; unfold eval_iop; rewrite eval_iop_integer_base_same_width, Hiop; reflexivity).
    rewrite !Hiop'; cbn [eou_bind]; rewrite !Hiop', Hassoc; cbn; reflexivity.
Qed.

Local Lemma norm_binop_unfolded_eval_add :
  forall {Pa : Params} ctx w fl nl nr (penv : param_env Pa) foracle,
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    wf_param_env_for (collect_free_vars [] nl ++ collect_free_vars [] nr) penv ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp CB_Add w fl nl nr))
      (eval_closed_cert_expr penv foracle (norm_binop_unfolded ctx CB_Add w fl nl nr)).
Proof.
  intros Pa ctx w fl nl nr penv foracle Hwl Hwr Htl Htr Hpenv.
  assert (Hpl : wf_param_env_for (collect_free_vars [] nl) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
  assert (Hpr : wf_param_env_for (collect_free_vars [] nr) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
  unfold norm_binop_unfolded.
  case_eq (cert_binop_flags_eqb fl no_binop_flags); intros Efl; [| apply equiv_eou_dvalue_refl].
  destruct (is_zero_const_expr w nr) eqn:Ezr.
  - apply (norm_binop_eval_id_r CB_Add w fl nl nr penv foracle 0%N
             Hwl Htl Hpl Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
    intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
    rewrite Integers.add_zero; reflexivity.
  - destruct (is_zero_const_expr w nl) eqn:Ezl.
    + apply (norm_binop_eval_id_l CB_Add w fl nl nr penv foracle 0%N
               Hwr Htr Hpr Efl (is_zero_const_expr_inv w nl Ezl)); [| reflexivity].
      intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
      rewrite Integers.add_zero_l; reflexivity.
    + destruct ((1 <? w)%positive && cert_expr_eqb nl nr) eqn:Edbl.
      * apply andb_true_iff in Edbl as [Hw1 Eeq].
        apply cert_expr_eqb_eq in Eeq; apply cert_binop_flags_eqb_eq in Efl; subst nr fl.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct (eval_cert_expr_totality nl [] penv [] foracle Htl wf_let_val_env_nil Hpl)
          as [[msgl ->] | [vl [-> Hwfvl]]]; cbn [eou_bind]; [exact I |].
        rewrite Hwl in Hwfvl; destruct Hwfvl as [-> | [il ->]]; [reflexivity |].
        unfold eval_iop; rewrite !eval_iop_integer_base_same_width, repr_one_N.
        unfold cert_to_ibinop, eval_int_op; cbn.
        rewrite (@Integers.unsigned_one w).
        assert (Hge : (1 >=? Z.pos w)%Z = false)
          by (apply Pos.ltb_lt in Hw1; rewrite Z.geb_leb; apply Z.leb_gt; lia).
        rewrite Hge, (alg_add_self_shl1 w il Hw1); cbn; reflexivity.
      * destruct (extract_neg_expr w nr) as [y |] eqn:Eneg.
        -- pose proof (extract_neg_expr_inv w nr y Eneg) as Heqr; subst nr.
           apply cert_binop_flags_eqb_eq in Efl; subst fl.
           cbn [wt_cert_expr cert_expr_bit_width] in Htr; cbn in Hpr; rewrite !andb_true_iff in Htr.
           destruct Htr as ((((_ & _) & Hty) & _) & Hwy); apply Pos.eqb_eq in Hwy.
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
           destruct (eval_cert_expr_totality nl [] penv [] foracle Htl wf_let_val_env_nil Hpl)
             as [[msgl ->] | [vl [-> Hwfvl]]]; cbn [eou_bind]; [exact I |].
           rewrite Hwl in Hwfvl.
           destruct (eval_cert_expr_totality y [] penv [] foracle Hty wf_let_val_env_nil Hpr)
             as [[msgy ->] | [vy [-> Hwfvy]]]; cbn [eou_bind]; [exact I |].
           rewrite Hwy in Hwfvy.
           destruct Hwfvl as [-> | [il ->]], Hwfvy as [-> | [iy ->]];
             unfold eval_iop; rewrite ?eval_iop_integer_base_same_width, ?repr_zero_N;
             cbn - [eval_iop_integer_base];
             rewrite ?eval_iop_integer_base_same_width; cbn; try reflexivity.
           rewrite Integers.sub_zero_r, <- Integers.sub_add_opp; reflexivity.
        -- destruct (extract_const_expr w nr) as [ic2 |] eqn:Ec2.
           ++ destruct (extract_binop_rhs_const CB_Add w nl) as [[a ic1] |] eqn:Erc;
                [| apply equiv_eou_dvalue_refl].
              destruct (extract_const_expr_inv w nr ic2 Ec2) as [v2 [Heqr ->]].
              destruct (extract_binop_rhs_const_inv CB_Add w nl a ic1 Erc) as [v1 [Heql ->]].
              pose proof (norm_binop_eval_reassoc CB_Add w fl nl nr penv foracle a v1 v2
                            (@Integers.add w) Htl Hpl Efl Heql Heqr eq_refl
                            (fun x y => eq_refl) (@Integers.add_assoc w)) as Hra.
              cbn zeta; destruct (@Integers.unsigned w _ =? 0)%Z eqn:Esum0; [| exact Hra].
              apply (equiv_eou_dvalue_trans _ _ _ Hra).
              apply Z.eqb_eq in Esum0.
              assert (Hs_zero : @Integers.add w (@Integers.repr w (Z.of_N v1))
                                                (@Integers.repr w (Z.of_N v2)) =
                                @Integers.zero w)
                by (rewrite <- (@Integers.repr_unsigned w (_)), Esum0; reflexivity).
              subst nl; cbn [wt_cert_expr cert_expr_bit_width] in Htl; cbn in Hpl;
                rewrite !andb_true_iff in Htl.
              destruct Htl as ((((_ & Hta) & _) & Hwa) & _); apply Pos.eqb_eq in Hwa.
              rewrite app_nil_r in Hpl.
              unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
              rewrite Hs_zero, (@Integers.unsigned_zero w), repr_zero_N.
              destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpl)
                as [[msga ->] | [va [-> Hwfva]]]; cbn [eou_bind]; [exact I |].
              rewrite Hwa in Hwfva; destruct Hwfva as [-> | [ia ->]];
                unfold eval_iop; rewrite ?eval_iop_integer_base_same_width; cbn;
                [reflexivity | rewrite Integers.add_zero; reflexivity].
           ++ destruct (extract_const_expr w nl) as [ic1 |] eqn:Ec1;
                [| apply equiv_eou_dvalue_refl].
              destruct (extract_const_expr_inv w nl ic1 Ec1) as [v1 [Heql ->]].
              exact (norm_binop_eval_comm_l CB_Add w fl nl nr penv foracle v1
                       Hwr Htr Hpr Efl Heql eq_refl eq_refl).
Qed.

Local Lemma norm_binop_unfolded_eval_sub :
  forall {Pa : Params} ctx w fl nl nr (penv : param_env Pa) foracle,
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    wf_param_env_for (collect_free_vars [] nl ++ collect_free_vars [] nr) penv ->
    ub_ctx_holds penv foracle ctx ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp CB_Sub w fl nl nr))
      (eval_closed_cert_expr penv foracle (norm_binop_unfolded ctx CB_Sub w fl nl nr)).
Proof.
  intros Pa ctx w fl nl nr penv foracle Hwl Hwr Htl Htr Hpenv Hctx.
  assert (Hpl : wf_param_env_for (collect_free_vars [] nl) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
  assert (Hpr : wf_param_env_for (collect_free_vars [] nr) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
  unfold norm_binop_unfolded.
  case_eq (cert_binop_flags_eqb fl no_binop_flags); intros Efl; [| apply equiv_eou_dvalue_refl].
  destruct (is_zero_const_expr w nr) eqn:Ezr.
  - apply (norm_binop_eval_id_r CB_Sub w fl nl nr penv foracle 0%N
             Hwl Htl Hpl Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
    intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
    rewrite Integers.sub_zero_l; reflexivity.
  - destruct (cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl) eqn:Eself.
    + apply andb_true_iff in Eself as [Eeq Edef].
      apply cert_expr_eqb_eq in Eeq; apply cert_binop_flags_eqb_eq in Efl; subst nr fl.
      destruct (expr_guaranteed_defined_sound ctx nl penv foracle Edef Htl Hpl Hctx)
        as [_ [il Hil]].
      revert il Hil; rewrite Hwl; intros il Hil.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
      rewrite Integers.sub_idem; reflexivity.
    + destruct (is_zero_const_expr w nl) eqn:Ezl.
      * destruct (extract_neg_expr w nr) as [a |] eqn:Eneg; [| apply equiv_eou_dvalue_refl].
        rewrite (is_zero_const_expr_inv w nl Ezl).
        pose proof (extract_neg_expr_inv w nr a Eneg) as Heqr; subst nr.
        apply cert_binop_flags_eqb_eq in Efl; subst fl.
        cbn [wt_cert_expr cert_expr_bit_width] in Htr; cbn in Hpr; rewrite !andb_true_iff in Htr.
        destruct Htr as ((((_ & _) & Hta) & _) & Hwa); apply Pos.eqb_eq in Hwa.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
        destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpr)
          as [[msga ->] | [va [-> Hwfva]]]; cbn [eou_bind]; [exact I |].
        rewrite Hwa in Hwfva; destruct Hwfva as [-> | [ia ->]]; [cbn; reflexivity |].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width, !repr_zero_N;
          cbn - [eval_iop_integer_base];
          rewrite eval_iop_integer_base_same_width; cbn.
        rewrite !Integers.sub_zero_r, Integers.neg_involutive; reflexivity.
      * destruct (extract_const_expr w nr) as [ic |] eqn:Ec; [| apply equiv_eou_dvalue_refl].
        destruct (extract_const_expr_inv w nr ic Ec) as [v [-> ->]].
        apply cert_binop_flags_eqb_eq in Efl; subst fl.
        unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
        rewrite repr_of_N_to_N_unsigned.
        destruct (eval_cert_expr_totality nl [] penv [] foracle Htl wf_let_val_env_nil Hpl)
          as [[msgl ->] | [vl [-> Hwfvl]]]; cbn [eou_bind]; [exact I |].
        rewrite Hwl in Hwfvl; destruct Hwfvl as [-> | [il ->]]; [reflexivity |].
        unfold eval_iop; rewrite !eval_iop_integer_base_same_width; cbn.
        rewrite Integers.sub_add_opp; reflexivity.
Qed.

Local Lemma norm_binop_unfolded_eval_mul :
  forall {Pa : Params} ctx w fl nl nr (penv : param_env Pa) foracle,
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    wf_param_env_for (collect_free_vars [] nl ++ collect_free_vars [] nr) penv ->
    ub_ctx_holds penv foracle ctx ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp CB_Mul w fl nl nr))
      (eval_closed_cert_expr penv foracle (norm_binop_unfolded ctx CB_Mul w fl nl nr)).
Proof.
  intros Pa ctx w fl nl nr penv foracle Hwl Hwr Htl Htr Hpenv Hctx.
  assert (Hpl : wf_param_env_for (collect_free_vars [] nl) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
  assert (Hpr : wf_param_env_for (collect_free_vars [] nr) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
  unfold norm_binop_unfolded.
  case_eq (cert_binop_flags_eqb fl no_binop_flags); intros Efl; [| apply equiv_eou_dvalue_refl].
  destruct (is_one_const_expr w nr) eqn:E1r.
  - apply (norm_binop_eval_id_r CB_Mul w fl nl nr penv foracle 1%N
             Hwl Htl Hpl Efl (is_one_const_expr_inv w nr E1r)); [| reflexivity].
    intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_one_N; cbn.
    destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_one; reflexivity.
  - destruct (is_one_const_expr w nl) eqn:E1l.
    + apply (norm_binop_eval_id_l CB_Mul w fl nl nr penv foracle 1%N
               Hwr Htr Hpr Efl (is_one_const_expr_inv w nl E1l)); [| reflexivity].
      intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_one_N; cbn.
      destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_commut, Integers.mul_one; reflexivity.
    + destruct (is_zero_const_expr w nr && expr_guaranteed_defined ctx nl) eqn:Ezr.
      * apply andb_true_iff in Ezr as [Ez0 Edef].
        rewrite (is_zero_const_expr_inv w nr Ez0).
        apply cert_binop_flags_eqb_eq in Efl; subst fl.
        destruct (expr_guaranteed_defined_sound ctx nl penv foracle Edef Htl Hpl Hctx)
          as [_ [il Hil]].
        revert il Hil; rewrite Hwl; intros il Hil.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil; cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_zero; reflexivity.
      * destruct (is_zero_const_expr w nl && expr_guaranteed_defined ctx nr) eqn:Ezl.
        -- apply andb_true_iff in Ezl as [Ez0 Edef].
           rewrite (is_zero_const_expr_inv w nl Ez0).
           apply cert_binop_flags_eqb_eq in Efl; subst fl.
           destruct (expr_guaranteed_defined_sound ctx nr penv foracle Edef Htr Hpr Hctx)
             as [_ [ir Hir]].
           revert ir Hir; rewrite Hwr; intros ir Hir.
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hir; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
           destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_commut, Integers.mul_zero; reflexivity.
        -- destruct (is_all_ones_const_expr w nr) eqn:Emr.
           ++ rewrite (is_all_ones_const_expr_inv w nr Emr).
              apply cert_binop_flags_eqb_eq in Efl; subst fl.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
              destruct (eval_cert_expr_totality nl [] penv [] foracle Htl wf_let_val_env_nil Hpl)
                as [[msgl ->] | [vl [-> Hwfvl]]]; cbn [eou_bind]; [exact I |].
              rewrite Hwl in Hwfvl; destruct Hwfvl as [-> | [il ->]]; [reflexivity |].
              unfold eval_iop; rewrite !eval_iop_integer_base_same_width,
                                       repr_all_ones_N, repr_zero_N; cbn.
              destruct (Pos.eqb w 1); cbn;
                rewrite Integers.mul_mone, Integers.sub_zero_r; reflexivity.
           ++ destruct (is_all_ones_const_expr w nl) eqn:Eml.
              ** rewrite (is_all_ones_const_expr_inv w nl Eml).
                 apply cert_binop_flags_eqb_eq in Efl; subst fl.
                 unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
                 destruct (eval_cert_expr_totality nr [] penv [] foracle Htr wf_let_val_env_nil Hpr)
                   as [[msgr ->] | [vr [-> Hwfvr]]]; cbn [eou_bind]; [exact I |].
                 rewrite Hwr in Hwfvr; destruct Hwfvr as [-> | [ir ->]]; [reflexivity |].
                 unfold eval_iop; rewrite !eval_iop_integer_base_same_width,
                                          repr_all_ones_N, repr_zero_N; cbn.
                 destruct (Pos.eqb w 1); cbn;
                   rewrite Integers.mul_commut, Integers.mul_mone, Integers.sub_zero_r; reflexivity.
              ** destruct (extract_const_expr w nr) as [ic |] eqn:Ecr.
                 --- destruct (@Integers.is_power2 w ic) as [logn |] eqn:Ep2;
                       [| apply equiv_eou_dvalue_refl].
                     destruct (extract_const_expr_inv w nr ic Ecr) as [v [-> ->]].
                     apply cert_binop_flags_eqb_eq in Efl; subst fl.
                     pose proof (@Integers.is_power2_rng w _ logn Ep2) as Hrng.
                     unfold Integers.zwordsize in Hrng.
                     assert (Hge : (@Integers.unsigned w logn >=? Z.pos w)%Z = false)
                       by (rewrite Z.geb_leb; apply Z.leb_gt; lia).
                     unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
                     rewrite repr_of_N_to_N_unsigned.
                     destruct (eval_cert_expr_totality nl [] penv [] foracle Htl wf_let_val_env_nil Hpl)
                       as [[msgl ->] | [vl [-> Hwfvl]]]; cbn [eou_bind]; [exact I |].
                     rewrite Hwl in Hwfvl; destruct Hwfvl as [-> | [il ->]]; [reflexivity |].
                     unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
                     unfold cert_to_ibinop, eval_int_op; cbn.
                     rewrite Hge, (@Integers.mul_pow2 w il _ logn Ep2).
                     destruct (Pos.eqb w 1); reflexivity.
                 --- destruct (extract_const_expr w nl) as [ic |] eqn:Ecl;
                       [| apply equiv_eou_dvalue_refl].
                     destruct (extract_const_expr_inv w nl ic Ecl) as [v [Heql ->]].
                     destruct (@Integers.is_power2 w (@Integers.repr w (Z.of_N v)))
                       as [logn |] eqn:Ep2;
                       [| exact (norm_binop_eval_comm_l CB_Mul w fl nl nr penv foracle v
                                   Hwr Htr Hpr Efl Heql eq_refl eq_refl)].
                     subst nl; apply cert_binop_flags_eqb_eq in Efl; subst fl.
                     pose proof (@Integers.is_power2_rng w _ logn Ep2) as Hrng.
                     unfold Integers.zwordsize in Hrng.
                     assert (Hge : (@Integers.unsigned w logn >=? Z.pos w)%Z = false)
                       by (rewrite Z.geb_leb; apply Z.leb_gt; lia).
                     unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
                     rewrite repr_of_N_to_N_unsigned.
                     destruct (eval_cert_expr_totality nr [] penv [] foracle Htr wf_let_val_env_nil Hpr)
                       as [[msgr ->] | [vr [-> Hwfvr]]]; cbn [eou_bind]; [exact I |].
                     rewrite Hwr in Hwfvr; destruct Hwfvr as [-> | [ir ->]]; [reflexivity |].
                     unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
                     unfold cert_to_ibinop, eval_int_op; cbn.
                     rewrite Hge, Integers.mul_commut, (@Integers.mul_pow2 w ir _ logn Ep2).
                     destruct (Pos.eqb w 1); reflexivity.
Qed.

Local Lemma norm_binop_unfolded_eval_div_rem :
  forall {Pa : Params} ctx op w fl nl nr (penv : param_env Pa) foracle,
    (op = CB_UDiv \/ op = CB_SDiv \/ op = CB_URem \/ op = CB_SRem) ->
    cert_expr_bit_width nl = w ->
    wt_cert_expr [] nl = true ->
    wf_param_env_for (collect_free_vars [] nl) penv ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp op w fl nl nr))
      (eval_closed_cert_expr penv foracle (norm_binop_unfolded ctx op w fl nl nr)).
Proof.
  intros Pa ctx op w fl nl nr penv foracle Hop Hwl Htl Hpl.
  destruct Hop as [-> | [-> | [-> | ->]]]; unfold norm_binop_unfolded.
  - (* CB_UDiv *)
    destruct (negb (cbf_nuw fl) && negb (cbf_nsw fl) && negb (cbf_disjoint fl)) eqn:Efl_ok;
      [| apply equiv_eou_dvalue_refl].
    destruct (extract_const_expr w nr) as [ic |] eqn:Ecr; [| apply equiv_eou_dvalue_refl].
    destruct (@Integers.is_power2 w ic) as [logn |] eqn:Ep2; [| apply equiv_eou_dvalue_refl].
    destruct (extract_const_expr_inv w nr ic Ecr) as [v [-> ->]].
    set (ic := @Integers.repr w (Z.of_N v)) in *.
    pose proof (@Integers.is_power2_rng w ic logn Ep2) as Hrng.
    pose proof (@Integers.is_power2_correct w ic logn Ep2) as Hpow.
    unfold Integers.zwordsize in Hrng.
    rewrite (alg_two_p_pow _ (proj1 Hrng)) in Hpow.
    assert (Hpos_ic : (0 < @Integers.unsigned w ic)%Z)
      by (rewrite Hpow; apply Z.pow_pos_nonneg; lia).
    assert (Hnz_ic : (@Integers.unsigned w ic =? 0)%Z = false)
      by (apply Z.eqb_neq; lia).
    assert (Hge_ln : (@Integers.unsigned w logn >=? Z.pos w)%Z = false)
      by (rewrite Z.geb_leb; apply Z.leb_gt; lia).
    destruct (@Integers.unsigned w logn =? 0)%Z eqn:Eln0.
    + apply Z.eqb_eq in Eln0.
      assert (Hic1 : @Integers.unsigned w ic = 1%Z) by (rewrite Hpow, Eln0; reflexivity).
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
      destruct (eval_cert_expr_totality nl [] penv [] foracle Htl wf_let_val_env_nil Hpl)
        as [[msgl ->] | [vl [-> Hwfvl]]]; cbn [eou_bind]; [exact I |].
      rewrite Hwl in Hwfvl; destruct Hwfvl as [-> | [il ->]]; [reflexivity |].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      unfold cert_to_ibinop, eval_int_op; cbn; fold ic.
      rewrite Hnz_ic, Hic1, Z.mod_1_r, Z.eqb_refl; cbn; rewrite andb_false_r.
      assert (Hic_one : ic = @Integers.one w)
        by (rewrite <- (@Integers.repr_unsigned w ic), Hic1; reflexivity).
      rewrite Hic_one, (@Integers.divu_one w il); reflexivity.
    + unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
      rewrite repr_of_N_to_N_unsigned.
      destruct (eval_cert_expr_totality nl [] penv [] foracle Htl wf_let_val_env_nil Hpl)
        as [[msgl ->] | [vl [-> Hwfvl]]]; cbn [eou_bind]; [exact I |].
      rewrite Hwl in Hwfvl; destruct Hwfvl as [-> | [il ->]]; [reflexivity |].
      unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
      unfold cert_to_ibinop, eval_int_op; cbn; fold ic.
      rewrite Hnz_ic, Hge_ln, Hpow, (@Integers.divu_pow2 w il ic logn Ep2).
      destruct (cbf_exact fl && _); reflexivity.
  - (* CB_SDiv *)
    destruct (cert_binop_flags_eqb fl no_binop_flags); apply equiv_eou_dvalue_refl.
  - (* CB_URem *)
    case_eq (cert_binop_flags_eqb fl no_binop_flags); intros Efl; [| apply equiv_eou_dvalue_refl].
    destruct (extract_const_expr w nr) as [ic |] eqn:Ecr; [| apply equiv_eou_dvalue_refl].
    destruct (@Integers.is_power2 w ic) as [logn |] eqn:Ep2; [| apply equiv_eou_dvalue_refl].
    destruct (extract_const_expr_inv w nr ic Ecr) as [v [-> ->]].
    apply cert_binop_flags_eqb_eq in Efl; subst fl.
    set (ic := @Integers.repr w (Z.of_N v)) in *.
    pose proof (@Integers.is_power2_rng w ic logn Ep2) as Hrng.
    pose proof (@Integers.is_power2_correct w ic logn Ep2) as Hpow.
    rewrite (alg_two_p_pow _ (proj1 Hrng)) in Hpow.
    assert (Hnz_ic : (@Integers.unsigned w ic =? 0)%Z = false)
      by (apply Z.eqb_neq; rewrite Hpow; pose proof (Z.pow_pos_nonneg 2 (@Integers.unsigned w logn)); lia).
    unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
    rewrite repr_of_N_to_N_unsigned.
    destruct (eval_cert_expr_totality nl [] penv [] foracle Htl wf_let_val_env_nil Hpl)
      as [[msgl ->] | [vl [-> Hwfvl]]]; cbn [eou_bind]; [exact I |].
    rewrite Hwl in Hwfvl; destruct Hwfvl as [-> | [il ->]]; [reflexivity |].
    unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
    unfold cert_to_ibinop, eval_int_op; cbn; fold ic.
    rewrite Hnz_ic, (@Integers.modu_and w il ic logn Ep2); reflexivity.
  - (* CB_SRem *)
    destruct (cert_binop_flags_eqb fl no_binop_flags); apply equiv_eou_dvalue_refl.
Qed.

Local Lemma norm_binop_unfolded_eval_shift :
  forall {Pa : Params} ctx op w fl nl nr (penv : param_env Pa) foracle,
    (op = CB_Shl \/ op = CB_LShr \/ op = CB_AShr) ->
    cert_expr_bit_width nl = w ->
    wt_cert_expr [] nl = true ->
    wf_param_env_for (collect_free_vars [] nl) penv ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp op w fl nl nr))
      (eval_closed_cert_expr penv foracle (norm_binop_unfolded ctx op w fl nl nr)).
Proof.
  intros Pa ctx op w fl nl nr penv foracle Hop Hwl Htl Hpl.
  destruct Hop as [-> | [-> | ->]]; unfold norm_binop_unfolded.
  - (* CB_Shl *)
    case_eq (cert_binop_flags_eqb fl no_binop_flags); intros Efl; [| apply equiv_eou_dvalue_refl].
    destruct (is_zero_const_expr w nr) eqn:Ezr.
    + apply (norm_binop_eval_id_r CB_Shl w fl nl nr penv foracle 0%N
               Hwl Htl Hpl Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
      intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
      unfold cert_to_ibinop, eval_int_op; cbn.
      rewrite (@Integers.unsigned_zero w); cbn; rewrite alg_shl_zero; reflexivity.
    + destruct (extract_const_expr w nr) as [ic2 |] eqn:Ec2; [| apply equiv_eou_dvalue_refl].
      destruct (extract_binop_rhs_const CB_Shl w nl) as [[a ic1] |] eqn:Erc;
        [| apply equiv_eou_dvalue_refl].
      destruct ((@Integers.unsigned w ic1 + @Integers.unsigned w ic2 <? Z.pos w)%Z) eqn:Esum;
        [| apply equiv_eou_dvalue_refl].
      apply Z.ltb_lt in Esum; apply cert_binop_flags_eqb_eq in Efl; subst fl.
      destruct (extract_const_expr_inv w nr ic2 Ec2) as [v2 [-> ->]].
      destruct (extract_binop_rhs_const_inv CB_Shl w nl a ic1 Erc) as [v1 [Heql ->]]; subst nl.
      set (c1 := @Integers.repr w (Z.of_N v1)) in *; set (c2 := @Integers.repr w (Z.of_N v2)) in *.
      pose proof (@Integers.unsigned_range w c1) as Hr1;
        pose proof (@Integers.unsigned_range w c2) as Hr2.
      pose proof (alg_shift_sum_unsigned w c1 c2 Esum) as Hu_add.
      assert (Hg1 : (@Integers.unsigned w c1 >=? Z.pos w)%Z = false)
        by (rewrite Z.geb_leb; apply Z.leb_gt; lia).
      assert (Hg2 : (@Integers.unsigned w c2 >=? Z.pos w)%Z = false)
        by (rewrite Z.geb_leb; apply Z.leb_gt; lia).
      assert (Hg12 : (@Integers.unsigned w (@Integers.add w c1 c2) >=? Z.pos w)%Z = false)
        by (rewrite Hu_add; rewrite Z.geb_leb; apply Z.leb_gt; lia).
      cbn [wt_cert_expr cert_expr_bit_width] in Htl; cbn in Hpl; rewrite !andb_true_iff in Htl;
        destruct Htl as ((((_ & Hta) & _) & Hwa) & _); apply Pos.eqb_eq in Hwa; rewrite app_nil_r in Hpl.
      unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
      rewrite repr_of_N_to_N_unsigned.
      destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpl)
        as [[msga ->] | [va [-> Hwfva]]]; cbn [eou_bind]; [exact I |].
      rewrite Hwa in Hwfva; destruct Hwfva as [-> | [ia ->]]; [cbn; reflexivity |].
      unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
      unfold cert_to_ibinop, eval_int_op; cbn - [eval_iop_integer_base]; fold c1 c2.
      rewrite Hg1; cbn - [eval_iop_integer_base]; rewrite eval_iop_integer_base_same_width.
      unfold eval_int_op; cbn; rewrite Hg2, Hg12.
      rewrite (@Integers.shl_shl w ia c1 c2);
        [reflexivity | apply alg_ltu_iwordsize_iff; lia |
         apply alg_ltu_iwordsize_iff; lia | apply alg_ltu_iwordsize_iff; lia].
  - (* CB_LShr *)
    case_eq (cert_binop_flags_eqb fl no_binop_flags); intros Efl; [| apply equiv_eou_dvalue_refl].
    destruct (is_zero_const_expr w nr) eqn:Ezr.
    + apply (norm_binop_eval_id_r CB_LShr w fl nl nr penv foracle 0%N
               Hwl Htl Hpl Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
      intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
      unfold cert_to_ibinop, eval_int_op; cbn.
      rewrite (@Integers.unsigned_zero w); cbn; rewrite alg_shru_zero; reflexivity.
    + destruct (extract_const_expr w nr) as [ic2 |] eqn:Ec2; [| apply equiv_eou_dvalue_refl].
      destruct (extract_binop_rhs_const CB_LShr w nl) as [[a ic1] |] eqn:Erc;
        [| apply equiv_eou_dvalue_refl].
      destruct ((@Integers.unsigned w ic1 + @Integers.unsigned w ic2 <? Z.pos w)%Z) eqn:Esum;
        [| apply equiv_eou_dvalue_refl].
      apply Z.ltb_lt in Esum; apply cert_binop_flags_eqb_eq in Efl; subst fl.
      destruct (extract_const_expr_inv w nr ic2 Ec2) as [v2 [-> ->]].
      destruct (extract_binop_rhs_const_inv CB_LShr w nl a ic1 Erc) as [v1 [Heql ->]]; subst nl.
      set (c1 := @Integers.repr w (Z.of_N v1)) in *; set (c2 := @Integers.repr w (Z.of_N v2)) in *.
      pose proof (@Integers.unsigned_range w c1) as Hr1;
        pose proof (@Integers.unsigned_range w c2) as Hr2.
      pose proof (alg_shift_sum_unsigned w c1 c2 Esum) as Hu_add.
      assert (Hg1 : (@Integers.unsigned w c1 >=? Z.pos w)%Z = false)
        by (rewrite Z.geb_leb; apply Z.leb_gt; lia).
      assert (Hg2 : (@Integers.unsigned w c2 >=? Z.pos w)%Z = false)
        by (rewrite Z.geb_leb; apply Z.leb_gt; lia).
      assert (Hg12 : (@Integers.unsigned w (@Integers.add w c1 c2) >=? Z.pos w)%Z = false)
        by (rewrite Hu_add; rewrite Z.geb_leb; apply Z.leb_gt; lia).
      cbn [wt_cert_expr cert_expr_bit_width] in Htl; cbn in Hpl; rewrite !andb_true_iff in Htl;
        destruct Htl as ((((_ & Hta) & _) & Hwa) & _); apply Pos.eqb_eq in Hwa; rewrite app_nil_r in Hpl.
      unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
      rewrite repr_of_N_to_N_unsigned.
      destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpl)
        as [[msga ->] | [va [-> Hwfva]]]; cbn [eou_bind]; [exact I |].
      rewrite Hwa in Hwfva; destruct Hwfva as [-> | [ia ->]]; [cbn; reflexivity |].
      unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
      unfold cert_to_ibinop, eval_int_op; cbn - [eval_iop_integer_base]; fold c1 c2.
      rewrite Hg1; cbn - [eval_iop_integer_base]; rewrite eval_iop_integer_base_same_width.
      unfold eval_int_op; cbn; rewrite Hg2, Hg12.
      rewrite (@Integers.shru_shru w ia c1 c2);
        [reflexivity | apply alg_ltu_iwordsize_iff; lia |
         apply alg_ltu_iwordsize_iff; lia | apply alg_ltu_iwordsize_iff; lia].
  - (* CB_AShr *)
    case_eq (cert_binop_flags_eqb fl no_binop_flags); intros Efl; [| apply equiv_eou_dvalue_refl].
    destruct (is_zero_const_expr w nr) eqn:Ezr.
    + apply (norm_binop_eval_id_r CB_AShr w fl nl nr penv foracle 0%N
               Hwl Htl Hpl Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
      intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
      unfold cert_to_ibinop, eval_int_op; cbn.
      rewrite (@Integers.unsigned_zero w); cbn; rewrite alg_shr_zero; reflexivity.
    + destruct (extract_const_expr w nr) as [ic2 |] eqn:Ec2; [| apply equiv_eou_dvalue_refl].
      destruct (extract_binop_rhs_const CB_AShr w nl) as [[a ic1] |] eqn:Erc;
        [| apply equiv_eou_dvalue_refl].
      destruct ((@Integers.unsigned w ic1 + @Integers.unsigned w ic2 <? Z.pos w)%Z) eqn:Esum;
        [| apply equiv_eou_dvalue_refl].
      apply Z.ltb_lt in Esum; apply cert_binop_flags_eqb_eq in Efl; subst fl.
      destruct (extract_const_expr_inv w nr ic2 Ec2) as [v2 [-> ->]].
      destruct (extract_binop_rhs_const_inv CB_AShr w nl a ic1 Erc) as [v1 [Heql ->]]; subst nl.
      set (c1 := @Integers.repr w (Z.of_N v1)) in *; set (c2 := @Integers.repr w (Z.of_N v2)) in *.
      pose proof (@Integers.unsigned_range w c1) as Hr1;
        pose proof (@Integers.unsigned_range w c2) as Hr2.
      pose proof (alg_shift_sum_unsigned w c1 c2 Esum) as Hu_add.
      assert (Hg1 : (@Integers.unsigned w c1 >=? Z.pos w)%Z = false)
        by (rewrite Z.geb_leb; apply Z.leb_gt; lia).
      assert (Hg2 : (@Integers.unsigned w c2 >=? Z.pos w)%Z = false)
        by (rewrite Z.geb_leb; apply Z.leb_gt; lia).
      assert (Hg12 : (@Integers.unsigned w (@Integers.add w c1 c2) >=? Z.pos w)%Z = false)
        by (rewrite Hu_add; rewrite Z.geb_leb; apply Z.leb_gt; lia).
      cbn [wt_cert_expr cert_expr_bit_width] in Htl; cbn in Hpl; rewrite !andb_true_iff in Htl;
        destruct Htl as ((((_ & Hta) & _) & Hwa) & _); apply Pos.eqb_eq in Hwa; rewrite app_nil_r in Hpl.
      unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
      rewrite repr_of_N_to_N_unsigned.
      destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpl)
        as [[msga ->] | [va [-> Hwfva]]]; cbn [eou_bind]; [exact I |].
      rewrite Hwa in Hwfva; destruct Hwfva as [-> | [ia ->]]; [cbn; reflexivity |].
      unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
      unfold cert_to_ibinop, eval_int_op; cbn - [eval_iop_integer_base]; fold c1 c2.
      rewrite Hg1; cbn - [eval_iop_integer_base]; rewrite eval_iop_integer_base_same_width.
      unfold eval_int_op; cbn; rewrite Hg2, Hg12.
      rewrite (@Integers.shr_shr w ia c1 c2);
        [reflexivity | apply alg_ltu_iwordsize_iff; lia |
         apply alg_ltu_iwordsize_iff; lia | apply alg_ltu_iwordsize_iff; lia].
Qed.

Local Lemma norm_binop_unfolded_eval_and :
  forall {Pa : Params} ctx w fl nl nr (penv : param_env Pa) foracle,
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    wf_param_env_for (collect_free_vars [] nl ++ collect_free_vars [] nr) penv ->
    ub_ctx_holds penv foracle ctx ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp CB_And w fl nl nr))
      (eval_closed_cert_expr penv foracle (norm_binop_unfolded ctx CB_And w fl nl nr)).
Proof.
  intros Pa ctx w fl nl nr penv foracle Hwl Hwr Htl Htr Hpenv Hctx.
  assert (Hpl : wf_param_env_for (collect_free_vars [] nl) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
  assert (Hpr : wf_param_env_for (collect_free_vars [] nr) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
  unfold norm_binop_unfolded.
  case_eq (cert_binop_flags_eqb fl no_binop_flags); intros Efl; [| apply equiv_eou_dvalue_refl].
  destruct (is_all_ones_const_expr w nr) eqn:Emr.
  - apply (norm_binop_eval_id_r CB_And w fl nl nr penv foracle (all_ones_N w)
             Hwl Htl Hpl Efl (is_all_ones_const_expr_inv w nr Emr)); [| reflexivity].
    intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
    rewrite Integers.and_mone; reflexivity.
  - destruct (is_all_ones_const_expr w nl) eqn:Eml.
    + apply (norm_binop_eval_id_l CB_And w fl nl nr penv foracle (all_ones_N w)
               Hwr Htr Hpr Efl (is_all_ones_const_expr_inv w nl Eml)); [| reflexivity].
      intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
      rewrite Integers.and_mone_l; reflexivity.
    + destruct (cert_expr_eqb nl nr) eqn:Eidem.
      * apply cert_expr_eqb_eq in Eidem; apply cert_binop_flags_eqb_eq in Efl; subst nr fl.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct (eval_cert_expr_totality nl [] penv [] foracle Htl wf_let_val_env_nil Hpl)
          as [[msgl ->] | [vl [-> Hwfvl]]]; cbn [eou_bind]; [exact I |].
        rewrite Hwl in Hwfvl; destruct Hwfvl as [-> | [il ->]]; [reflexivity |].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn.
        rewrite Integers.and_idem; reflexivity.
      * destruct (is_zero_const_expr w nr && expr_guaranteed_defined ctx nl) eqn:Ezr.
        -- apply andb_true_iff in Ezr as [Ez0 Edef].
           rewrite (is_zero_const_expr_inv w nr Ez0).
           apply cert_binop_flags_eqb_eq in Efl; subst fl.
           destruct (expr_guaranteed_defined_sound ctx nl penv foracle Edef Htl Hpl Hctx)
             as [_ [il Hil]].
           revert il Hil; rewrite Hwl; intros il Hil.
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
           rewrite Integers.and_zero; reflexivity.
        -- destruct (is_zero_const_expr w nl && expr_guaranteed_defined ctx nr) eqn:Ezl.
           ++ apply andb_true_iff in Ezl as [Ez0 Edef].
              rewrite (is_zero_const_expr_inv w nl Ez0).
              apply cert_binop_flags_eqb_eq in Efl; subst fl.
              destruct (expr_guaranteed_defined_sound ctx nr penv foracle Edef Htr Hpr Hctx)
                as [_ [ir Hir]].
              revert ir Hir; rewrite Hwr; intros ir Hir.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hir; cbn [eou_bind].
              unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
              rewrite Integers.and_zero_l; reflexivity.
           ++ assert (Hrest_and :
                equiv_eou_dvalue
                  (eval_closed_cert_expr penv foracle (CE_BinOp CB_And w fl nl nr))
                  (eval_closed_cert_expr penv foracle
                     match extract_const_expr w nr with
                     | Some ic2 =>
                         match extract_binop_rhs_const CB_And w nl with
                         | Some (a, ic1) =>
                             CE_BinOp CB_And w no_binop_flags a
                               (mk_bv_const w (@Integers.and w ic1 ic2))
                         | None => CE_BinOp CB_And w fl nl nr
                         end
                     | None =>
                         match extract_const_expr w nl with
                         | Some ic1 => CE_BinOp CB_And w no_binop_flags nr (mk_bv_const w ic1)
                         | None => CE_BinOp CB_And w fl nl nr
                         end
                     end)).
              { destruct (extract_const_expr w nr) as [ic2 |] eqn:Ec2.
                - destruct (extract_binop_rhs_const CB_And w nl) as [[a ic1] |] eqn:Erc;
                    [| apply equiv_eou_dvalue_refl].
                  destruct (extract_const_expr_inv w nr ic2 Ec2) as [v2 [Heqr ->]].
                  destruct (extract_binop_rhs_const_inv CB_And w nl a ic1 Erc) as [v1 [Heql ->]].
                  exact (norm_binop_eval_reassoc CB_And w fl nl nr penv foracle a v1 v2
                           (@Integers.and w) Htl Hpl Efl Heql Heqr eq_refl
                           (fun x y => eq_refl) (@Integers.and_assoc w)).
                - destruct (extract_const_expr w nl) as [ic1 |] eqn:Ec1;
                    [| apply equiv_eou_dvalue_refl].
                  destruct (extract_const_expr_inv w nl ic1 Ec1) as [v1 [Heql ->]].
                  exact (norm_binop_eval_comm_l CB_And w fl nl nr penv foracle v1
                           Hwr Htr Hpr Efl Heql eq_refl eq_refl). }
              destruct (extract_not_expr w nl) as [a |] eqn:Enl,
                       (extract_not_expr w nr) as [b |] eqn:Enr;
                try exact Hrest_and.
              pose proof (extract_not_expr_inv w nl a Enl) as Heql;
                pose proof (extract_not_expr_inv w nr b Enr) as Heqr.
              apply cert_binop_flags_eqb_eq in Efl; subst nl nr fl.
              cbn [wt_cert_expr cert_expr_bit_width] in Htl, Htr; cbn in Hpl, Hpr;
                rewrite !andb_true_iff in Htl; rewrite !andb_true_iff in Htr;
                rewrite !app_nil_r in Hpl; rewrite !app_nil_r in Hpr.
              destruct Htl as ((((_ & Hta) & _) & Hwa) & _);
                destruct Htr as ((((_ & Htb) & _) & Hwb) & _).
              apply Pos.eqb_eq in Hwa; apply Pos.eqb_eq in Hwb.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
              destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpl)
                as [[msga ->] | [va [-> Hwfva]]]; cbn [eou_bind]; [exact I |].
              rewrite Hwa in Hwfva.
              assert (Hxa : forall x0,
                        wf_scalar_dvalue w x0 ->
                        exists vx,
                          @eval_iop Pa (cert_to_ibinop CB_Xor no_binop_flags) x0
                            (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N (all_ones_N w))))) =
                          raise_ret vx)
                by (intros x0 [-> | [ix0 ->]]; [eexists; reflexivity |
                    unfold eval_iop; rewrite eval_iop_integer_base_same_width; eexists; reflexivity]).
              destruct (Hxa va Hwfva) as [vxa Hvxa]; rewrite Hvxa; cbn [eou_bind].
              destruct (eval_cert_expr_totality b [] penv [] foracle Htb wf_let_val_env_nil Hpr)
                as [[msgb ->] | [vb [-> Hwfvb]]]; cbn [eou_bind]; [exact I |].
              rewrite Hwb in Hwfvb.
              destruct Hwfva as [-> | [ia ->]], Hwfvb as [-> | [ib ->]];
                unfold eval_iop in Hvxa |- *;
                rewrite ?eval_iop_integer_base_same_width in Hvxa;
                rewrite ?eval_iop_integer_base_same_width, ?repr_all_ones_N in Hvxa |- *;
                cbn in Hvxa; inversion Hvxa; subst vxa; clear Hvxa;
                unfold eval_int_op; cbn - [eval_iop_integer_base];
                rewrite ?eval_iop_integer_base_same_width;
                unfold eval_int_op; rewrite ?repr_all_ones_N; cbn;
                try reflexivity.
              rewrite !(alg_pos_eq_dec_refl w); cbn.
              change (@Integers.xor w ia (@Integers.mone w)) with (@Integers.not w ia).
              change (@Integers.xor w ib (@Integers.mone w)) with (@Integers.not w ib).
              change (@Integers.xor w (@Integers.or w ia ib) (@Integers.mone w))
                with (@Integers.not w (@Integers.or w ia ib)).
              rewrite Integers.not_or_and_not; reflexivity.
Qed.

Local Lemma norm_binop_unfolded_eval_or :
  forall {Pa : Params} ctx w fl nl nr (penv : param_env Pa) foracle,
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    wf_param_env_for (collect_free_vars [] nl ++ collect_free_vars [] nr) penv ->
    ub_ctx_holds penv foracle ctx ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp CB_Or w fl nl nr))
      (eval_closed_cert_expr penv foracle (norm_binop_unfolded ctx CB_Or w fl nl nr)).
Proof.
  intros Pa ctx w fl nl nr penv foracle Hwl Hwr Htl Htr Hpenv Hctx.
  assert (Hpl : wf_param_env_for (collect_free_vars [] nl) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
  assert (Hpr : wf_param_env_for (collect_free_vars [] nr) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
  unfold norm_binop_unfolded.
  case_eq (cert_binop_flags_eqb fl no_binop_flags); intros Efl; [| apply equiv_eou_dvalue_refl].
  destruct (is_zero_const_expr w nr) eqn:Ezr.
  - apply (norm_binop_eval_id_r CB_Or w fl nl nr penv foracle 0%N
             Hwl Htl Hpl Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
    intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
    rewrite Integers.or_zero; reflexivity.
  - destruct (is_zero_const_expr w nl) eqn:Ezl.
    + apply (norm_binop_eval_id_l CB_Or w fl nl nr penv foracle 0%N
               Hwr Htr Hpr Efl (is_zero_const_expr_inv w nl Ezl)); [| reflexivity].
      intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
      rewrite Integers.or_zero_l; reflexivity.
    + destruct (cert_expr_eqb nl nr) eqn:Eidem.
      * apply cert_expr_eqb_eq in Eidem; apply cert_binop_flags_eqb_eq in Efl; subst nr fl.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct (eval_cert_expr_totality nl [] penv [] foracle Htl wf_let_val_env_nil Hpl)
          as [[msgl ->] | [vl [-> Hwfvl]]]; cbn [eou_bind]; [exact I |].
        rewrite Hwl in Hwfvl; destruct Hwfvl as [-> | [il ->]]; [reflexivity |].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn.
        rewrite Integers.or_idem; reflexivity.
      * destruct (is_all_ones_const_expr w nr && expr_guaranteed_defined ctx nl) eqn:Emr.
        -- apply andb_true_iff in Emr as [Em0 Edef].
           rewrite (is_all_ones_const_expr_inv w nr Em0).
           apply cert_binop_flags_eqb_eq in Efl; subst fl.
           destruct (expr_guaranteed_defined_sound ctx nl penv foracle Edef Htl Hpl Hctx)
             as [_ [il Hil]].
           revert il Hil; rewrite Hwl; intros il Hil.
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
           rewrite Integers.or_mone; reflexivity.
        -- destruct (is_all_ones_const_expr w nl && expr_guaranteed_defined ctx nr) eqn:Eml.
           ++ apply andb_true_iff in Eml as [Em0 Edef].
              rewrite (is_all_ones_const_expr_inv w nl Em0).
              apply cert_binop_flags_eqb_eq in Efl; subst fl.
              destruct (expr_guaranteed_defined_sound ctx nr penv foracle Edef Htr Hpr Hctx)
                as [_ [ir Hir]].
              revert ir Hir; rewrite Hwr; intros ir Hir.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hir; cbn [eou_bind].
              unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
              rewrite Integers.or_commut, Integers.or_mone; reflexivity.
           ++ assert (Hrest_or :
                equiv_eou_dvalue
                  (eval_closed_cert_expr penv foracle (CE_BinOp CB_Or w fl nl nr))
                  (eval_closed_cert_expr penv foracle
                     match extract_const_expr w nr with
                     | Some ic2 =>
                         match extract_binop_rhs_const CB_Or w nl with
                         | Some (a, ic1) =>
                             CE_BinOp CB_Or w no_binop_flags a
                               (mk_bv_const w (@Integers.or w ic1 ic2))
                         | None => CE_BinOp CB_Or w fl nl nr
                         end
                     | None =>
                         match extract_const_expr w nl with
                         | Some ic1 => CE_BinOp CB_Or w no_binop_flags nr (mk_bv_const w ic1)
                         | None => CE_BinOp CB_Or w fl nl nr
                         end
                     end)).
              { destruct (extract_const_expr w nr) as [ic2 |] eqn:Ec2.
                - destruct (extract_binop_rhs_const CB_Or w nl) as [[a ic1] |] eqn:Erc;
                    [| apply equiv_eou_dvalue_refl].
                  destruct (extract_const_expr_inv w nr ic2 Ec2) as [v2 [Heqr ->]].
                  destruct (extract_binop_rhs_const_inv CB_Or w nl a ic1 Erc) as [v1 [Heql ->]].
                  exact (norm_binop_eval_reassoc CB_Or w fl nl nr penv foracle a v1 v2
                           (@Integers.or w) Htl Hpl Efl Heql Heqr eq_refl
                           (fun x y => eq_refl) (@Integers.or_assoc w)).
                - destruct (extract_const_expr w nl) as [ic1 |] eqn:Ec1;
                    [| apply equiv_eou_dvalue_refl].
                  destruct (extract_const_expr_inv w nl ic1 Ec1) as [v1 [Heql ->]].
                  exact (norm_binop_eval_comm_l CB_Or w fl nl nr penv foracle v1
                           Hwr Htr Hpr Efl Heql eq_refl eq_refl). }
              destruct (extract_not_expr w nl) as [a |] eqn:Enl,
                       (extract_not_expr w nr) as [b |] eqn:Enr;
                try exact Hrest_or.
              pose proof (extract_not_expr_inv w nl a Enl) as Heql;
                pose proof (extract_not_expr_inv w nr b Enr) as Heqr.
              apply cert_binop_flags_eqb_eq in Efl; subst nl nr fl.
              cbn [wt_cert_expr cert_expr_bit_width] in Htl, Htr; cbn in Hpl, Hpr;
                rewrite !andb_true_iff in Htl; rewrite !andb_true_iff in Htr;
                rewrite !app_nil_r in Hpl; rewrite !app_nil_r in Hpr.
              destruct Htl as ((((_ & Hta) & _) & Hwa) & _);
                destruct Htr as ((((_ & Htb) & _) & Hwb) & _).
              apply Pos.eqb_eq in Hwa; apply Pos.eqb_eq in Hwb.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
              destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpl)
                as [[msga ->] | [va [-> Hwfva]]]; cbn [eou_bind]; [exact I |].
              rewrite Hwa in Hwfva.
              assert (Hxa : forall x0,
                        wf_scalar_dvalue w x0 ->
                        exists vx,
                          @eval_iop Pa (cert_to_ibinop CB_Xor no_binop_flags) x0
                            (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N (all_ones_N w))))) =
                          raise_ret vx)
                by (intros x0 [-> | [ix0 ->]]; [eexists; reflexivity |
                    unfold eval_iop; rewrite eval_iop_integer_base_same_width; eexists; reflexivity]).
              destruct (Hxa va Hwfva) as [vxa Hvxa]; rewrite Hvxa; cbn [eou_bind].
              destruct (eval_cert_expr_totality b [] penv [] foracle Htb wf_let_val_env_nil Hpr)
                as [[msgb ->] | [vb [-> Hwfvb]]]; cbn [eou_bind]; [exact I |].
              rewrite Hwb in Hwfvb.
              destruct Hwfva as [-> | [ia ->]], Hwfvb as [-> | [ib ->]];
                unfold eval_iop in Hvxa |- *;
                rewrite ?eval_iop_integer_base_same_width in Hvxa;
                rewrite ?eval_iop_integer_base_same_width, ?repr_all_ones_N in Hvxa |- *;
                cbn in Hvxa; inversion Hvxa; subst vxa; clear Hvxa;
                unfold eval_int_op; cbn - [eval_iop_integer_base];
                rewrite ?eval_iop_integer_base_same_width;
                unfold eval_int_op; rewrite ?repr_all_ones_N; cbn;
                try reflexivity.
              rewrite !(alg_pos_eq_dec_refl w); cbn.
              change (@Integers.xor w ia (@Integers.mone w)) with (@Integers.not w ia).
              change (@Integers.xor w ib (@Integers.mone w)) with (@Integers.not w ib).
              change (@Integers.xor w (@Integers.and w ia ib) (@Integers.mone w))
                with (@Integers.not w (@Integers.and w ia ib)).
              rewrite Integers.not_and_or_not; reflexivity.
Qed.

Local Lemma norm_binop_unfolded_eval_xor :
  forall {Pa : Params} ctx w fl nl nr (penv : param_env Pa) foracle,
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    wf_param_env_for (collect_free_vars [] nl ++ collect_free_vars [] nr) penv ->
    ub_ctx_holds penv foracle ctx ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp CB_Xor w fl nl nr))
      (eval_closed_cert_expr penv foracle (norm_binop_unfolded ctx CB_Xor w fl nl nr)).
Proof.
  intros Pa ctx w fl nl nr penv foracle Hwl Hwr Htl Htr Hpenv Hctx.
  assert (Hpl : wf_param_env_for (collect_free_vars [] nl) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
  assert (Hpr : wf_param_env_for (collect_free_vars [] nr) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
  unfold norm_binop_unfolded.
  case_eq (cert_binop_flags_eqb fl no_binop_flags); intros Efl; [| apply equiv_eou_dvalue_refl].
  destruct (is_zero_const_expr w nr) eqn:Ezr.
  - apply (norm_binop_eval_id_r CB_Xor w fl nl nr penv foracle 0%N
             Hwl Htl Hpl Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
    intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
    rewrite Integers.xor_zero; reflexivity.
  - destruct (is_zero_const_expr w nl) eqn:Ezl.
    + apply (norm_binop_eval_id_l CB_Xor w fl nl nr penv foracle 0%N
               Hwr Htr Hpr Efl (is_zero_const_expr_inv w nl Ezl)); [| reflexivity].
      intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
      rewrite Integers.xor_zero_l; reflexivity.
    + destruct (cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl) eqn:Eself.
      * apply andb_true_iff in Eself as [Eeq Edef].
        apply cert_expr_eqb_eq in Eeq; apply cert_binop_flags_eqb_eq in Efl; subst nr fl.
        destruct (expr_guaranteed_defined_sound ctx nl penv foracle Edef Htl Hpl Hctx)
          as [_ [il Hil]].
        revert il Hil; rewrite Hwl; intros il Hil.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil; cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.xor_idem; reflexivity.
      * destruct (extract_const_expr w nr) as [ic2 |] eqn:Ec2.
        -- destruct (extract_binop_rhs_const CB_Xor w nl) as [[a ic1] |] eqn:Erc;
             [| apply equiv_eou_dvalue_refl].
           destruct (extract_const_expr_inv w nr ic2 Ec2) as [v2 [Heqr ->]].
           destruct (extract_binop_rhs_const_inv CB_Xor w nl a ic1 Erc) as [v1 [Heql ->]].
           pose proof (norm_binop_eval_reassoc CB_Xor w fl nl nr penv foracle a v1 v2
                         (@Integers.xor w) Htl Hpl Efl Heql Heqr eq_refl
                         (fun x y => eq_refl) (@Integers.xor_assoc w)) as Hra.
           cbn zeta; destruct (@Integers.unsigned w _ =? 0)%Z eqn:Exr0; [| exact Hra].
           apply (equiv_eou_dvalue_trans _ _ _ Hra).
           apply Z.eqb_eq in Exr0.
           assert (Hx_zero : @Integers.xor w (@Integers.repr w (Z.of_N v1))
                                             (@Integers.repr w (Z.of_N v2)) =
                             @Integers.zero w)
             by (rewrite <- (@Integers.repr_unsigned w (_)), Exr0; reflexivity).
           subst nl; cbn [wt_cert_expr cert_expr_bit_width] in Htl; cbn in Hpl;
             rewrite !andb_true_iff in Htl.
           destruct Htl as ((((_ & Hta) & _) & Hwa) & _); apply Pos.eqb_eq in Hwa.
           rewrite app_nil_r in Hpl.
           unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
           rewrite Hx_zero, (@Integers.unsigned_zero w), repr_zero_N.
           destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpl)
             as [[msga ->] | [va [-> Hwfva]]]; cbn [eou_bind]; [exact I |].
           rewrite Hwa in Hwfva; destruct Hwfva as [-> | [ia ->]]; [cbn; reflexivity |].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn.
           rewrite Integers.xor_zero; reflexivity.
        -- destruct (extract_const_expr w nl) as [ic1 |] eqn:Ec1;
             [| apply equiv_eou_dvalue_refl].
           destruct (extract_const_expr_inv w nl ic1 Ec1) as [v1 [Heql ->]].
           exact (norm_binop_eval_comm_l CB_Xor w fl nl nr penv foracle v1
                    Hwr Htr Hpr Efl Heql eq_refl eq_refl).
Qed.

Lemma norm_binop_unfolded_eval :
  forall {Pa : Params} ctx op w fl nl nr (penv : param_env Pa) foracle,
    wf_binop_flags_for op fl = true ->
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    wf_param_env_for (collect_free_vars [] nl ++ collect_free_vars [] nr) penv ->
    ub_ctx_holds penv foracle ctx ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp op w fl nl nr))
      (eval_closed_cert_expr penv foracle (norm_binop_unfolded ctx op w fl nl nr)).
Proof.
  intros Pa ctx op w fl nl nr penv foracle _ Hwl Hwr Htl Htr Hpenv Hctx.
  assert (Hpl : wf_param_env_for (collect_free_vars [] nl) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
  destruct op.
  - exact (norm_binop_unfolded_eval_add ctx w fl nl nr penv foracle Hwl Hwr Htl Htr Hpenv).
  - exact (norm_binop_unfolded_eval_sub ctx w fl nl nr penv foracle Hwl Hwr Htl Htr Hpenv Hctx).
  - exact (norm_binop_unfolded_eval_mul ctx w fl nl nr penv foracle Hwl Hwr Htl Htr Hpenv Hctx).
  - exact (norm_binop_unfolded_eval_div_rem ctx CB_UDiv w fl nl nr penv foracle
             (or_introl eq_refl) Hwl Htl Hpl).
  - exact (norm_binop_unfolded_eval_div_rem ctx CB_SDiv w fl nl nr penv foracle
             (or_intror (or_introl eq_refl)) Hwl Htl Hpl).
  - exact (norm_binop_unfolded_eval_div_rem ctx CB_URem w fl nl nr penv foracle
             (or_intror (or_intror (or_introl eq_refl))) Hwl Htl Hpl).
  - exact (norm_binop_unfolded_eval_div_rem ctx CB_SRem w fl nl nr penv foracle
             (or_intror (or_intror (or_intror eq_refl))) Hwl Htl Hpl).
  - exact (norm_binop_unfolded_eval_shift ctx CB_Shl w fl nl nr penv foracle
             (or_introl eq_refl) Hwl Htl Hpl).
  - exact (norm_binop_unfolded_eval_shift ctx CB_LShr w fl nl nr penv foracle
             (or_intror (or_introl eq_refl)) Hwl Htl Hpl).
  - exact (norm_binop_unfolded_eval_shift ctx CB_AShr w fl nl nr penv foracle
             (or_intror (or_intror eq_refl)) Hwl Htl Hpl).
  - exact (norm_binop_unfolded_eval_and ctx w fl nl nr penv foracle Hwl Hwr Htl Htr Hpenv Hctx).
  - exact (norm_binop_unfolded_eval_or ctx w fl nl nr penv foracle Hwl Hwr Htl Htr Hpenv Hctx).
  - exact (norm_binop_unfolded_eval_xor ctx w fl nl nr penv foracle Hwl Hwr Htl Htr Hpenv Hctx).
Qed.

Lemma norm_binop_step_eval :
  forall {Pa : Params} ctx op w fl nl nr (penv : param_env Pa) foracle,
    wf_binop_flags_for op fl = true ->
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    wf_param_env_for (collect_free_vars [] nl ++ collect_free_vars [] nr) penv ->
    ub_ctx_holds penv foracle ctx ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp op w fl nl nr))
      (eval_closed_cert_expr penv foracle (norm_binop_step ctx op w fl nl nr)).
Proof.
  intros Pa ctx op w fl nl nr penv foracle Hfl Hwl Hwr Htl Htr Hpenv Hctx.
  unfold norm_binop_step.
  destruct (try_fold_const_binop op w fl nl nr) as [c |] eqn:Etc.
  - exact (proj2 (proj2 (proj2 (proj2 (try_fold_const_binop_sound op w fl nl nr c penv foracle Etc))))).
  - apply (equiv_eou_dvalue_trans _ _ _ (strip_safe_nsw_flags_eval op w fl nl nr penv foracle Hwl Hwr Htl Htr Hpenv)).
    exact (norm_binop_unfolded_eval ctx op w (strip_safe_nsw_flags op w fl nl nr) nl nr penv foracle
             (strip_safe_nsw_flags_wf op w fl nl nr Hfl) Hwl Hwr Htl Htr Hpenv Hctx).
Qed.


