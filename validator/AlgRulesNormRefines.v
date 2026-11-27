(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * [CertValidator.AlgRulesNormRefines] Expression Normalization & Algebraic Refinement

    Defines:
    - [icmp], [cast], [select], and [freeze] constant folding and algebraic
      normalization ([try_fold_const_icmp] through [normalize_cert_expr]).
    - Directional poison/flag/identity refinement checking
      ([check_expr_refines]) and its soundness proof
      ([check_expr_refines_sound]). *)

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
  AlgRulesEval
  AlgRulesNormBinop.
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

Definition try_fold_const_icmp
  (pr : cert_icmp_pred) (ss : bool) (w : positive) (nl nr : cert_expr)
  : option cert_expr :=
  match nl, nr with
  | CE_BvConst w1 v1, CE_BvConst w2 v2 =>
      if Pos.eqb w1 w && Pos.eqb w2 w
      then Some (fold_const_icmp pr ss w v1 v2)
      else None
  | _, _ => None
  end.

Definition norm_icmp_i1_rhs_const
  (pr : cert_icmp_pred) (nl : cert_expr) (ic : @Integers.bit_int 1%positive)
  : option cert_expr :=
  match pr with
  | CIP_Eq =>
      if (@Integers.unsigned 1%positive ic =? 1)%Z then Some nl
      else Some (CE_BinOp CB_Xor 1%positive no_binop_flags nl (CE_BvConst 1%positive 1%N))
  | CIP_Ne =>
      if (@Integers.unsigned 1%positive ic =? 0)%Z then Some nl
      else Some (CE_BinOp CB_Xor 1%positive no_binop_flags nl (CE_BvConst 1%positive 1%N))
  | _ => None
  end.

Definition norm_icmp_step
  (ctx : ub_ctx) (pr : cert_icmp_pred) (ss : bool) (w : positive)
  (nl nr : cert_expr) : cert_expr :=
  match try_fold_const_icmp pr ss w nl nr with
  | Some c => c
  | None =>
      if negb ss && cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl
      then CE_BvConst 1%positive (if is_refl_true_icmp pr then 1%N else 0%N)
      else if negb ss && Pos.eqb w 1%positive then
        match extract_const_expr 1%positive nr with
        | Some ic =>
            match norm_icmp_i1_rhs_const pr nl ic with
            | Some out => out
            | None => CE_ICmp pr ss w nl nr
            end
        | None =>
            match extract_const_expr 1%positive nl with
            | Some ic =>
                match norm_icmp_i1_rhs_const (swap_cert_icmp pr) nr ic with
                | Some out => out
                | None => CE_ICmp (swap_cert_icmp pr) ss w nr (mk_bv_const 1%positive ic)
                end
            | None => CE_ICmp pr ss w nl nr
            end
        end
      else
        match extract_const_expr w nl with
        | Some ic => CE_ICmp (swap_cert_icmp pr) ss w nr (mk_bv_const w ic)
        | None => CE_ICmp pr ss w nl nr
        end
  end.

Lemma alg_eval_icmp_refl :
  forall {Pa : Params} w pr (i : @Integers.bit_int w),
    @eval_icmp Pa false (cert_to_icmp pr)
      (DVALUE_Base (@DVALUE_I Pa w i)) (DVALUE_Base (@DVALUE_I Pa w i)) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
                 (if is_refl_true_icmp pr then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa w pr i.
  unfold eval_icmp; rewrite eval_icmp_base_same_width.
  destruct pr; unfold cert_to_icmp, eval_int_icmp, is_refl_true_icmp; cbn;
    unfold Integers.cmpu, Integers.cmp, Integers.eq, Integers.ltu, Integers.lt;
    repeat match goal with
           | |- context [zeq ?a ?a] => destruct (zeq a a); [| lia]
           | |- context [zlt ?a ?a] => destruct (zlt a a); [lia |]
           end;
    cbn; reflexivity.
Qed.

Lemma norm_icmp_i1_rhs_const_typing :
  forall pr e ic out vs,
    cert_expr_bit_width e = 1%positive ->
    wt_cert_expr [] e = true ->
    is_let_free_expr e = true ->
    incl (collect_free_vars [] e) vs ->
    norm_icmp_i1_rhs_const pr e ic = Some out ->
    cert_expr_bit_width out = 1%positive /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    incl (collect_free_vars [] out) vs.
Proof.
  intros pr e ic out vs Hw Ht Hlf Hinc Hn.
  destruct pr; cbn in Hn; try discriminate Hn;
    destruct (_ =? _)%Z; inversion Hn; subst out;
    [repeat split; assumption |
     cbn; rewrite Ht, Hw, Hlf, app_nil_r; repeat split; exact Hinc |
     repeat split; assumption |
     cbn; rewrite Ht, Hw, Hlf, app_nil_r; repeat split; exact Hinc].
Qed.

Lemma norm_icmp_step_typing :
  forall ctx pr ss w nl nr,
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    is_let_free_expr nl = true ->
    is_let_free_expr nr = true ->
    let out := norm_icmp_step ctx pr ss w nl nr in
    cert_expr_bit_width out = 1%positive /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    incl (collect_free_vars [] out) (collect_free_vars [] nl ++ collect_free_vars [] nr).
Proof.
  intros ctx pr ss w nl nr Hwl Hwr Htl Htr Hfl_l Hfl_r; cbn zeta.
  assert (Hdef_out :
    cert_expr_bit_width (CE_ICmp pr ss w nl nr) = 1%positive /\
    wt_cert_expr [] (CE_ICmp pr ss w nl nr) = true /\
    is_let_free_expr (CE_ICmp pr ss w nl nr) = true /\
    incl (collect_free_vars [] (CE_ICmp pr ss w nl nr))
         (collect_free_vars [] nl ++ collect_free_vars [] nr)).
  { cbn; rewrite Htl, Htr, Hwl, Hwr, !Pos.eqb_refl, Hfl_l, Hfl_r.
    repeat split; apply incl_refl. }
  assert (Hswp_out : forall ic,
    cert_expr_bit_width (CE_ICmp (swap_cert_icmp pr) ss w nr (mk_bv_const w ic)) = 1%positive /\
    wt_cert_expr [] (CE_ICmp (swap_cert_icmp pr) ss w nr (mk_bv_const w ic)) = true /\
    is_let_free_expr (CE_ICmp (swap_cert_icmp pr) ss w nr (mk_bv_const w ic)) = true /\
    incl (collect_free_vars [] (CE_ICmp (swap_cert_icmp pr) ss w nr (mk_bv_const w ic)))
         (collect_free_vars [] nl ++ collect_free_vars [] nr)).
  { intros ic; unfold mk_bv_const; cbn; rewrite Htr, Hwr, Pos.eqb_refl, Hfl_r, app_nil_r.
    repeat split; apply incl_appr, incl_refl. }
  unfold norm_icmp_step.
  destruct (try_fold_const_icmp pr ss w nl nr) as [c |] eqn:Etc.
  - destruct nl as [w1 v1 | | | | | | | |]; try discriminate Etc.
    destruct nr as [w2 v2 | | | | | | | |]; try discriminate Etc.
    cbn [try_fold_const_icmp] in Etc.
    destruct (Pos.eqb w1 w && Pos.eqb w2 w); [| discriminate Etc].
    inversion Etc; subst c; clear Etc.
    unfold fold_const_icmp; destruct (ss && _); cbn; repeat split; intros x [].
  - destruct (negb ss && cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl).
    + cbn; repeat split; intros x [].
    + destruct (negb ss && Pos.eqb w 1%positive) eqn:Ei1.
      * apply andb_true_iff in Ei1 as [_ Ew1]; apply Pos.eqb_eq in Ew1; rewrite Ew1 in *.
        destruct (extract_const_expr 1%positive nr) as [ic |].
        -- destruct (norm_icmp_i1_rhs_const pr nl ic) as [out0 |] eqn:Eo; [| exact Hdef_out].
           exact (norm_icmp_i1_rhs_const_typing pr nl ic out0 _
                    Hwl Htl Hfl_l (incl_appl _ (incl_refl _)) Eo).
        -- destruct (extract_const_expr 1%positive nl) as [ic |]; [| exact Hdef_out].
           destruct (norm_icmp_i1_rhs_const (swap_cert_icmp pr) nr ic) as [out0 |] eqn:Eo;
             [| apply Hswp_out].
           exact (norm_icmp_i1_rhs_const_typing (swap_cert_icmp pr) nr ic out0 _
                    Hwr Htr Hfl_r (incl_appr _ (incl_refl _)) Eo).
      * destruct (extract_const_expr w nl) as [ic |]; [apply Hswp_out | exact Hdef_out].
Qed.

Lemma norm_icmp_i1_rhs_const_eval :
  forall {Pa : Params} pr e v out (penv : param_env Pa) foracle,
    cert_expr_bit_width e = 1%positive ->
    wt_cert_expr [] e = true ->
    wf_param_env_for (collect_free_vars [] e) penv ->
    norm_icmp_i1_rhs_const pr e (@Integers.repr 1%positive (Z.of_N v)) = Some out ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_ICmp pr false 1%positive e (CE_BvConst 1%positive v)))
      (eval_closed_cert_expr penv foracle out).
Proof.
  intros Pa pr e v out penv foracle Hwe Hte Hpe Hn.
  set (ic := @Integers.repr 1%positive (Z.of_N v)) in *.
  destruct pr; cbn [norm_icmp_i1_rhs_const] in Hn; try discriminate Hn.
  - (* CIP_Eq *)
    destruct (alg_i1_cases ic) as [Hic | Hic]; rewrite Hic in Hn.
    + rewrite (@Integers.unsigned_zero 1%positive) in Hn; cbn in Hn; inversion Hn; subst out.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; fold ic; rewrite Hic.
      destruct (eval_cert_expr_totality e [] penv [] foracle Hte wf_let_val_env_nil Hpe)
        as [[msge ->] | [ve [-> Hwfve]]]; cbn [eou_bind]; [exact I |].
      rewrite Hwe in Hwfve; destruct Hwfve as [-> | [ie ->]]; [cbn; reflexivity | cbn [eou_bind]].
      unfold eval_icmp, eval_iop;
        rewrite eval_icmp_base_same_width, eval_iop_integer_base_same_width, repr_one_N; cbn.
      destruct (alg_i1_cases ie) as [-> | ->]; cbn [Integers.cmpu].
      * rewrite (@Integers.eq_true 1%positive), (@Integers.xor_zero_l 1%positive); reflexivity.
      * rewrite (@Integers.eq_false 1%positive _ _ (not_eq_sym alg_zero_neq_one_1)),
                (@Integers.xor_idem 1%positive); reflexivity.
    + rewrite (@Integers.unsigned_one 1%positive) in Hn; cbn in Hn; inversion Hn; subst out.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; fold ic; rewrite Hic.
      destruct (eval_cert_expr_totality e [] penv [] foracle Hte wf_let_val_env_nil Hpe)
        as [[msge ->] | [ve [-> Hwfve]]]; cbn [eou_bind]; [exact I |].
      rewrite Hwe in Hwfve; destruct Hwfve as [-> | [ie ->]]; [cbn; reflexivity | cbn [eou_bind]].
      unfold eval_icmp; rewrite eval_icmp_base_same_width; cbn.
      destruct (alg_i1_cases ie) as [-> | ->]; cbn [Integers.cmpu].
      * rewrite (@Integers.eq_false 1%positive _ _ alg_zero_neq_one_1); reflexivity.
      * rewrite (@Integers.eq_true 1%positive); reflexivity.
  - (* CIP_Ne *)
    destruct (alg_i1_cases ic) as [Hic | Hic]; rewrite Hic in Hn.
    + rewrite (@Integers.unsigned_zero 1%positive) in Hn; cbn in Hn; inversion Hn; subst out.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; fold ic; rewrite Hic.
      destruct (eval_cert_expr_totality e [] penv [] foracle Hte wf_let_val_env_nil Hpe)
        as [[msge ->] | [ve [-> Hwfve]]]; cbn [eou_bind]; [exact I |].
      rewrite Hwe in Hwfve; destruct Hwfve as [-> | [ie ->]]; [cbn; reflexivity | cbn [eou_bind]].
      unfold eval_icmp; rewrite eval_icmp_base_same_width; cbn.
      destruct (alg_i1_cases ie) as [-> | ->]; cbn [Integers.cmpu].
      * rewrite (@Integers.eq_true 1%positive); reflexivity.
      * rewrite (@Integers.eq_false 1%positive _ _ (not_eq_sym alg_zero_neq_one_1)); reflexivity.
    + rewrite (@Integers.unsigned_one 1%positive) in Hn; cbn in Hn; inversion Hn; subst out.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; fold ic; rewrite Hic.
      destruct (eval_cert_expr_totality e [] penv [] foracle Hte wf_let_val_env_nil Hpe)
        as [[msge ->] | [ve [-> Hwfve]]]; cbn [eou_bind]; [exact I |].
      rewrite Hwe in Hwfve; destruct Hwfve as [-> | [ie ->]]; [cbn; reflexivity | cbn [eou_bind]].
      unfold eval_icmp, eval_iop;
        rewrite eval_icmp_base_same_width, eval_iop_integer_base_same_width, repr_one_N; cbn.
      destruct (alg_i1_cases ie) as [-> | ->]; cbn [Integers.cmpu].
      * rewrite (@Integers.eq_false 1%positive _ _ alg_zero_neq_one_1),
                (@Integers.xor_zero_l 1%positive); reflexivity.
      * rewrite (@Integers.eq_true 1%positive), (@Integers.xor_idem 1%positive); reflexivity.
Qed.

Lemma alg_icmp_swap_lhs_const :
  forall {Pa : Params} pr ss w v nr (penv : param_env Pa) foracle,
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nr = true ->
    wf_param_env_for (collect_free_vars [] nr) penv ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_ICmp pr ss w (CE_BvConst w v) nr))
      (eval_closed_cert_expr penv foracle
         (CE_ICmp (swap_cert_icmp pr) ss w nr (mk_bv_const w (@Integers.repr w (Z.of_N v))))).
Proof.
  intros Pa pr ss w v nr penv foracle Hwr Htr Hpr.
  unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
  rewrite repr_of_N_to_N_unsigned.
  destruct (eval_cert_expr_totality nr [] penv [] foracle Htr wf_let_val_env_nil Hpr)
    as [[msgr ->] | [vr [-> Hwfvr]]]; cbn [eou_bind]; [exact I |].
  rewrite Hwr in Hwfvr; destruct Hwfvr as [-> | [ir ->]]; [reflexivity |].
  unfold eval_icmp; rewrite !eval_icmp_base_same_width; unfold eval_int_icmp.
  cbn [msamesign VIntVMemInt samesign VInt_Bounded].
  rewrite (andb_comm (@Integers.cmp w Cge (@Integers.repr w (Z.of_N v)) (@Integers.zero w))),
          (andb_comm (@Integers.cmp w Clt (@Integers.repr w (Z.of_N v)) (@Integers.zero w))).
  destruct pr; unfold swap_cert_icmp, cert_to_icmp; cbn;
    try rewrite (@Integers.eq_sym w (@Integers.repr w (Z.of_N v)) ir);
    reflexivity.
Qed.

Lemma norm_icmp_step_eval :
  forall {Pa : Params} ctx pr ss w nl nr (penv : param_env Pa) foracle,
    cert_expr_bit_width nl = w ->
    cert_expr_bit_width nr = w ->
    wt_cert_expr [] nl = true ->
    wt_cert_expr [] nr = true ->
    wf_param_env_for (collect_free_vars [] nl ++ collect_free_vars [] nr) penv ->
    ub_ctx_holds penv foracle ctx ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_ICmp pr ss w nl nr))
      (eval_closed_cert_expr penv foracle (norm_icmp_step ctx pr ss w nl nr)).
Proof.
  intros Pa ctx pr ss w nl nr penv foracle Hwl Hwr Htl Htr Hpenv Hctx.
  assert (Hpl : wf_param_env_for (collect_free_vars [] nl) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
  assert (Hpr : wf_param_env_for (collect_free_vars [] nr) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
  unfold norm_icmp_step.
  destruct (try_fold_const_icmp pr ss w nl nr) as [c |] eqn:Etc.
  - destruct nl as [w1 v1 | | | | | | | |]; try discriminate Etc.
    destruct nr as [w2 v2 | | | | | | | |]; try discriminate Etc.
    cbn [try_fold_const_icmp] in Etc.
    destruct (Pos.eqb w1 w && Pos.eqb w2 w) eqn:Eww; [| discriminate Etc].
    apply andb_true_iff in Eww as [Ew1 Ew2]; apply Pos.eqb_eq in Ew1; apply Pos.eqb_eq in Ew2.
    inversion Etc; subst w1 w2 c.
    exact (proj2 (proj2 (proj2 (proj2 (fold_const_icmp_sound pr ss w v1 v2 penv foracle))))).
  - destruct (negb ss && cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl) eqn:Erefl.
    + rewrite !andb_true_iff in Erefl; destruct Erefl as ([Ess Eeq] & Edef).
      apply negb_true_iff in Ess; apply cert_expr_eqb_eq in Eeq; subst ss nr.
      destruct (expr_guaranteed_defined_sound ctx nl penv foracle Edef Htl Hpl Hctx)
        as [_ [il Hil]].
      revert il Hil; rewrite Hwl; intros il Hil.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil; cbn [eou_bind].
      rewrite alg_eval_icmp_refl; cbn.
      destruct (is_refl_true_icmp pr);
        [rewrite repr_one_N; reflexivity | rewrite repr_zero_N; reflexivity].
    + destruct (negb ss && Pos.eqb w 1%positive) eqn:Ei1.
      * apply andb_true_iff in Ei1 as [Ess Ew1];
          apply negb_true_iff in Ess; apply Pos.eqb_eq in Ew1; subst ss; rewrite Ew1 in *.
        destruct (extract_const_expr 1%positive nr) as [ic |] eqn:Ecr.
        -- destruct (norm_icmp_i1_rhs_const pr nl ic) as [out0 |] eqn:Eo;
             [| apply equiv_eou_dvalue_refl].
           destruct (extract_const_expr_inv 1%positive nr ic Ecr) as [v [-> ->]].
           exact (norm_icmp_i1_rhs_const_eval pr nl v out0 penv foracle Hwl Htl Hpl Eo).
        -- destruct (extract_const_expr 1%positive nl) as [ic |] eqn:Ecl;
             [| apply equiv_eou_dvalue_refl].
           destruct (extract_const_expr_inv 1%positive nl ic Ecl) as [v [-> ->]].
           pose proof (alg_icmp_swap_lhs_const pr false 1%positive v nr penv foracle Hwr Htr Hpr)
             as Hswp.
           destruct (norm_icmp_i1_rhs_const (swap_cert_icmp pr) nr
                       (@Integers.repr 1%positive (Z.of_N v))) as [out0 |] eqn:Eo;
             [| exact Hswp].
           apply (equiv_eou_dvalue_trans _ _ _ Hswp).
           unfold mk_bv_const.
           rewrite <- (repr_of_N_to_N_unsigned 1%positive (@Integers.repr 1%positive (Z.of_N v))) in Eo.
           exact (norm_icmp_i1_rhs_const_eval (swap_cert_icmp pr) nr _ out0
                    penv foracle Hwr Htr Hpr Eo).
      * destruct (extract_const_expr w nl) as [ic |] eqn:Ecl; [| apply equiv_eou_dvalue_refl].
        destruct (extract_const_expr_inv w nl ic Ecl) as [v [-> ->]].
        exact (alg_icmp_swap_lhs_const pr ss w v nr penv foracle Hwr Htr Hpr).
Qed.

Definition try_fold_const_cast
  (k : cert_cast_kind) (fw tw : positive) (fl : cert_cast_flags) (no : cert_expr)
  : option cert_expr :=
  match no with
  | CE_BvConst fw' val =>
      if Pos.eqb fw' fw then Some (fold_const_cast k fw tw fl val) else None
  | CE_Poison _ =>
      Some (CE_Poison tw)
  | _ => None
  end.

Definition is_no_cast_flags (fl : cert_cast_flags) : bool :=
  negb (ccf_nneg fl) && negb (ccf_nuw fl) && negb (ccf_nsw fl).

Lemma is_no_cast_flags_inv : forall fl,
  is_no_cast_flags fl = true -> fl = no_cast_flags.
Proof.
  intros [nn nu ns] H; unfold is_no_cast_flags in H; cbn in H.
  destruct nn, nu, ns; try discriminate H; reflexivity.
Qed.

Definition norm_cast_chain
  (k : cert_cast_kind) (fw tw : positive) (no : cert_expr) : option cert_expr :=
  match no with
  | CE_Cast k_in iw fw' fl_in inner =>
      if Pos.eqb fw' fw && is_no_cast_flags fl_in then
        match k, k_in with
        | CCK_ZExt, CCK_ZExt =>
            if (iw <? fw)%positive then Some (CE_Cast CCK_ZExt iw tw no_cast_flags inner)
            else None
        | CCK_SExt, CCK_SExt =>
            if (iw <? fw)%positive then Some (CE_Cast CCK_SExt iw tw no_cast_flags inner)
            else None
        | CCK_Trunc, CCK_Trunc =>
            if (fw <? iw)%positive then Some (CE_Cast CCK_Trunc iw tw no_cast_flags inner)
            else None
        | CCK_Trunc, CCK_ZExt =>
            if Pos.eqb iw tw then Some inner else None
        | CCK_Trunc, CCK_SExt =>
            if Pos.eqb iw tw then Some inner else None
        | _, _ => None
        end
      else None
  | _ => None
  end.

Definition norm_cast_basic
  (k : cert_cast_kind) (fw tw : positive) (fl : cert_cast_flags) (no : cert_expr)
  : cert_expr :=
  match try_fold_const_cast k fw tw fl no with
  | Some c => c
  | None =>
      if is_no_cast_flags fl then
        match norm_cast_chain k fw tw no with
        | Some out => out
        | None => CE_Cast k fw tw fl no
        end
      else CE_Cast k fw tw fl no
  end.

Lemma norm_cast_basic_typing :
  forall k fw tw fl no,
    match k with
    | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg fl) && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg fl)
    end = true ->
    cert_expr_bit_width no = fw ->
    wt_cert_expr [] no = true ->
    is_let_free_expr no = true ->
    let out := norm_cast_basic k fw tw fl no in
    cert_expr_bit_width out = tw /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    incl (collect_free_vars [] out) (collect_free_vars [] no).
Proof.
  intros k fw tw fl no Hk Hwo Hto Hfl_o; cbn zeta.
  assert (Hdef_out :
    cert_expr_bit_width (CE_Cast k fw tw fl no) = tw /\
    wt_cert_expr [] (CE_Cast k fw tw fl no) = true /\
    is_let_free_expr (CE_Cast k fw tw fl no) = true /\
    incl (collect_free_vars [] (CE_Cast k fw tw fl no)) (collect_free_vars [] no)).
  { cbn; rewrite Hk, Hto, Hwo, Pos.eqb_refl, Hfl_o; repeat split; apply incl_refl. }
  unfold norm_cast_basic.
  destruct (try_fold_const_cast k fw tw fl no) as [c |] eqn:Etc.
  - destruct no as [fw' val | pw | | | | | | |]; try discriminate Etc;
      cbn [try_fold_const_cast] in Etc.
    + destruct (Pos.eqb fw' fw); [| discriminate Etc].
      inversion Etc; subst c; clear Etc.
      unfold fold_const_cast; destruct k;
        repeat match goal with |- context [if ?b then _ else _] => destruct b end;
        unfold mk_bv_const; cbn; repeat split; intros x [].
    + inversion Etc; subst c; cbn; repeat split; intros x [].
  - destruct (is_no_cast_flags fl) eqn:Eno; [| exact Hdef_out].
    destruct (norm_cast_chain k fw tw no) as [out0 |] eqn:Ech; [| exact Hdef_out].
    destruct no as [| | | | | k_in iw fw' fl_in inner | | |];
      cbn - [andb Pos.eqb Pos.ltb] in Ech; try discriminate Ech.
    destruct (Pos.eqb fw' fw && is_no_cast_flags fl_in) eqn:Ein; [| discriminate Ech].
    apply andb_true_iff in Ein as [Efw Efl_in]; apply Pos.eqb_eq in Efw; subst fw'.
    cbn [wt_cert_expr] in Hto; cbn in Hfl_o; rewrite !andb_true_iff in Hto;
      destruct Hto as ((Hk_in & Hti) & Hwi); apply Pos.eqb_eq in Hwi.
    destruct k, k_in; try discriminate Ech.
    + destruct (iw <? fw)%positive eqn:Eif; [| discriminate Ech]; inversion Ech; subst out0.
      rewrite !andb_true_iff in Hk; destruct Hk as ([Hft _] & _).
      assert (Hit : (iw <? tw)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.ltb_lt in Eif; apply Pos.ltb_lt in Hft; lia).
      cbn - [Pos.ltb Pos.eqb]; rewrite Hit, Hti, Hwi, Pos.eqb_refl, Hfl_o;
        cbn; repeat split; apply incl_refl.
    + destruct (iw <? fw)%positive eqn:Eif; [| discriminate Ech]; inversion Ech; subst out0.
      rewrite !andb_true_iff in Hk; destruct Hk as (([Hft _] & _) & _).
      assert (Hit : (iw <? tw)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.ltb_lt in Eif; apply Pos.ltb_lt in Hft; lia).
      cbn - [Pos.ltb Pos.eqb]; rewrite Hit, Hti, Hwi, Pos.eqb_refl, Hfl_o;
        cbn; repeat split; apply incl_refl.
    + destruct (Pos.eqb iw tw) eqn:Eit; [| discriminate Ech];
        apply Pos.eqb_eq in Eit; inversion Ech; subst out0; rewrite <- Eit.
      repeat split; [exact Hwi | exact Hti | exact Hfl_o | apply incl_refl].
    + destruct (Pos.eqb iw tw) eqn:Eit; [| discriminate Ech];
        apply Pos.eqb_eq in Eit; inversion Ech; subst out0; rewrite <- Eit.
      repeat split; [exact Hwi | exact Hti | exact Hfl_o | apply incl_refl].
    + destruct (fw <? iw)%positive eqn:Efi; [| discriminate Ech]; inversion Ech; subst out0.
      rewrite !andb_true_iff in Hk; destruct Hk as [Htf _].
      assert (Hti_lt : (tw <? iw)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.ltb_lt in Efi; apply Pos.ltb_lt in Htf; lia).
      cbn - [Pos.ltb Pos.eqb]; rewrite Hti_lt, Hti, Hwi, Pos.eqb_refl, Hfl_o;
        cbn; repeat split; apply incl_refl.
Qed.

Lemma norm_cast_basic_eval :
  forall {Pa : Params} k fw tw fl no (penv : param_env Pa) foracle,
    match k with
    | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg fl) && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg fl)
    end = true ->
    wt_cert_expr [] no = true ->
    wf_param_env_for (collect_free_vars [] no) penv ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_Cast k fw tw fl no))
      (eval_closed_cert_expr penv foracle (norm_cast_basic k fw tw fl no)).
Proof.
  intros Pa k fw tw fl no penv foracle Hk Hto Hpo.
  unfold norm_cast_basic.
  destruct (try_fold_const_cast k fw tw fl no) as [c |] eqn:Etc.
  - destruct no as [fw' val | pw | | | | | | |]; try discriminate Etc;
      cbn [try_fold_const_cast] in Etc.
    + destruct (Pos.eqb fw' fw) eqn:Efw; [| discriminate Etc].
      apply Pos.eqb_eq in Efw; inversion Etc; subst fw' c.
      exact (proj2 (proj2 (proj2 (proj2 (fold_const_cast_sound k fw tw fl val penv foracle Hk))))).
    + inversion Etc; subst c; destruct k; cbn; reflexivity.
  - destruct (is_no_cast_flags fl) eqn:Eno; [| apply equiv_eou_dvalue_refl].
    destruct (norm_cast_chain k fw tw no) as [out0 |] eqn:Ech; [| apply equiv_eou_dvalue_refl].
    pose proof (is_no_cast_flags_inv fl Eno) as Hfl0; subst fl.
    destruct no as [| | | | | k_in iw fw' fl_in inner | | |];
      cbn - [andb Pos.eqb Pos.ltb] in Ech; try discriminate Ech.
    destruct (Pos.eqb fw' fw && is_no_cast_flags fl_in) eqn:Ein; [| discriminate Ech].
    apply andb_true_iff in Ein as [Efw Efl_in];
      apply Pos.eqb_eq in Efw; pose proof (is_no_cast_flags_inv fl_in Efl_in) as Hfl_in;
      subst fw' fl_in.
    cbn [wt_cert_expr collect_free_vars] in Hto, Hpo; rewrite !andb_true_iff in Hto.
    destruct Hto as ((Hk_in & Hti) & Hwi); apply Pos.eqb_eq in Hwi.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    destruct (eval_cert_expr_totality inner [] penv [] foracle Hti wf_let_val_env_nil Hpo)
      as [[msgi Emsgi] | [vi [Evi Hwfvi]]];
      [rewrite ?Emsgi; destruct k, k_in; try discriminate Ech;
       repeat match type of Ech with (if ?b then _ else _) = _ => destruct b; try discriminate Ech end;
       inversion Ech; subst out0; cbn [eval_cert_expr eou_bind]; rewrite ?Emsgi; cbn [eou_bind];
       first [exact I | reflexivity] |].
    rewrite Hwi in Hwfvi.
    destruct k, k_in; try discriminate Ech.
    + (* ZExt(ZExt) *)
      destruct (iw <? fw)%positive eqn:Eif; [| discriminate Ech]; inversion Ech; subst out0.
      cbn [eval_cert_expr]; rewrite Evi; cbn [eou_bind].
      destruct Hwfvi as [-> | [ii ->]]; [cbn; reflexivity |].
      cbn - [andb Pos.ltb] in Hk; rewrite !andb_true_iff in Hk; destruct Hk as ([Hft _] & _).
      assert (Hit : (iw <? tw)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.ltb_lt in Eif; apply Pos.ltb_lt in Hft; lia).
      cbn - [Pos.eqb Pos.ltb]; rewrite !Pos.eqb_refl, Eif, Hit;
        cbn - [Pos.eqb Pos.ltb]; rewrite !Pos.eqb_refl, Hft; cbn.
      rewrite (@Integers.unsigned_repr fw (@Integers.unsigned iw ii)); [reflexivity |].
      pose proof (@Integers.unsigned_range_2 iw ii) as Hur.
      pose proof (alg_modulus_le iw fw (Pos.lt_le_incl _ _ (proj1 (Pos.ltb_lt _ _) Eif))) as Hm.
      unfold Integers.max_unsigned in *; lia.
    + (* SExt(SExt) *)
      destruct (iw <? fw)%positive eqn:Eif; [| discriminate Ech]; inversion Ech; subst out0.
      cbn [eval_cert_expr]; rewrite Evi; cbn [eou_bind].
      destruct Hwfvi as [-> | [ii ->]]; [cbn; reflexivity |].
      cbn - [andb Pos.ltb] in Hk; rewrite !andb_true_iff in Hk; destruct Hk as (([Hft _] & _) & _).
      assert (Hit : (iw <? tw)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.ltb_lt in Eif; apply Pos.ltb_lt in Hft; lia).
      cbn - [Pos.eqb Pos.ltb]; rewrite !Pos.eqb_refl, Eif, Hit;
        cbn - [Pos.eqb Pos.ltb]; rewrite !Pos.eqb_refl, Hft; cbn.
      rewrite (@Integers.signed_repr fw (@Integers.signed iw ii)); [reflexivity |].
      exact (alg_signed_bounds_le iw fw ii (Pos.lt_le_incl _ _ (proj1 (Pos.ltb_lt _ _) Eif))).
    + (* Trunc(ZExt) *)
      destruct (Pos.eqb iw tw) eqn:Eit; [| discriminate Ech];
        apply Pos.eqb_eq in Eit; clear Hwi; inversion Ech; subst iw out0.
      rewrite Evi; cbn [eou_bind].
      destruct Hwfvi as [-> | [ii ->]]; [cbn; reflexivity |].
      cbn - [andb Pos.ltb] in Hk; rewrite !andb_true_iff in Hk; destruct Hk as [Htf _].
      cbn - [Pos.eqb Pos.ltb]; rewrite !Pos.eqb_refl, Htf;
        cbn - [Pos.eqb Pos.ltb]; rewrite !Pos.eqb_refl, Htf; cbn.
      rewrite (alg_repr_unsigned_repr_le tw fw _ (Pos.lt_le_incl _ _ (proj1 (Pos.ltb_lt _ _) Htf))),
              (@Integers.repr_unsigned tw ii); reflexivity.
    + (* Trunc(SExt) *)
      destruct (Pos.eqb iw tw) eqn:Eit; [| discriminate Ech];
        apply Pos.eqb_eq in Eit; clear Hwi; inversion Ech; subst iw out0.
      rewrite Evi; cbn [eou_bind].
      destruct Hwfvi as [-> | [ii ->]]; [cbn; reflexivity |].
      cbn - [andb Pos.ltb] in Hk; rewrite !andb_true_iff in Hk; destruct Hk as [Htf _].
      cbn - [Pos.eqb Pos.ltb]; rewrite !Pos.eqb_refl, Htf;
        cbn - [Pos.eqb Pos.ltb]; rewrite !Pos.eqb_refl, Htf; cbn.
      rewrite (alg_repr_unsigned_repr_le tw fw _ (Pos.lt_le_incl _ _ (proj1 (Pos.ltb_lt _ _) Htf))),
              (@Integers.repr_signed tw ii); reflexivity.
    + (* Trunc(Trunc) *)
      destruct (fw <? iw)%positive eqn:Efi; [| discriminate Ech]; inversion Ech; subst out0.
      cbn [eval_cert_expr]; rewrite Evi; cbn [eou_bind].
      destruct Hwfvi as [-> | [ii ->]]; [cbn; reflexivity |].
      cbn - [andb Pos.ltb] in Hk; rewrite !andb_true_iff in Hk; destruct Hk as [Htf _].
      assert (Hti_lt : (tw <? iw)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.ltb_lt in Efi; apply Pos.ltb_lt in Htf; lia).
      cbn - [Pos.eqb Pos.ltb]; rewrite !Pos.eqb_refl, Efi, Hti_lt;
        cbn - [Pos.eqb Pos.ltb]; rewrite !Pos.eqb_refl, Htf; cbn.
      rewrite (alg_repr_unsigned_repr_le tw fw _ (Pos.lt_le_incl _ _ (proj1 (Pos.ltb_lt _ _) Htf)));
        reflexivity.
Qed.

Lemma alg_eqm_repr_unsigned : forall w z,
  @Integers.eqm w z (@Integers.unsigned w (@Integers.repr w z)).
Proof.
  intros w z; unfold Integers.eqm, Integers.eqmod.
  rewrite (@Integers.unsigned_repr_eq w z).
  exists (z / @Integers.modulus w)%Z.
  pose proof (@Integers.modulus_pos w) as Hmp.
  pose proof (@Z.div_mod z (@Integers.modulus w) (ltac:(lia))).
  lia.
Qed.

Definition is_ext_from_width (iw fw : positive) (e : cert_expr) : bool :=
  match e with
  | CE_Cast k iw' fw' fl_in _ =>
      match k with
      | CCK_ZExt | CCK_SExt =>
          Pos.eqb iw' iw && Pos.eqb fw' fw && is_no_cast_flags fl_in
      | CCK_Trunc => false
      end
  | _ => false
  end.

Definition norm_trunc_binop
  (k : cert_cast_kind) (fw tw : positive) (no : cert_expr) : option cert_expr :=
  match k, no with
  | CCK_Trunc, CE_BinOp op fw' fl_b x y =>
      if (tw <? fw)%positive && Pos.eqb fw' fw &&
         cert_binop_flags_eqb fl_b no_binop_flags &&
         match op with CB_Add | CB_Sub | CB_Mul => true | _ => false end &&
         (is_ext_from_width tw fw x || is_ext_from_width tw fw y)
      then
        Some (CE_BinOp op tw no_binop_flags
                (norm_cast_basic CCK_Trunc fw tw no_cast_flags x)
                (norm_cast_basic CCK_Trunc fw tw no_cast_flags y))
      else None
  | _, _ => None
  end.

Definition norm_cast_step
  (k : cert_cast_kind) (fw tw : positive) (fl : cert_cast_flags) (no : cert_expr)
  : cert_expr :=
  match try_fold_const_cast k fw tw fl no with
  | Some c => c
  | None =>
      if is_no_cast_flags fl then
        match norm_cast_chain k fw tw no with
        | Some out => out
        | None =>
            match norm_trunc_binop k fw tw no with
            | Some out => out
            | None => CE_Cast k fw tw fl no
            end
        end
      else CE_Cast k fw tw fl no
  end.

Lemma norm_cast_step_typing :
  forall k fw tw fl no,
    match k with
    | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg fl) && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg fl)
    end = true ->
    cert_expr_bit_width no = fw ->
    wt_cert_expr [] no = true ->
    is_let_free_expr no = true ->
    let out := norm_cast_step k fw tw fl no in
    cert_expr_bit_width out = tw /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    incl (collect_free_vars [] out) (collect_free_vars [] no).
Proof.
  intros k fw tw fl no Hk Hwo Hto Hfl_o; cbn zeta.
  unfold norm_cast_step.
  pose proof (norm_cast_basic_typing k fw tw fl no Hk Hwo Hto Hfl_o) as Hbas.
  unfold norm_cast_basic in Hbas; cbn zeta in Hbas.
  destruct (try_fold_const_cast k fw tw fl no) as [c |]; [exact Hbas |].
  destruct (is_no_cast_flags fl); [| exact Hbas].
  destruct (norm_cast_chain k fw tw no) as [oc |]; [exact Hbas |].
  destruct (norm_trunc_binop k fw tw no) as [ot |] eqn:Etr; [| exact Hbas].
  destruct k, no as [| | | op fw' fl_b x y | | | | |];
    cbn [norm_trunc_binop] in Etr; try discriminate Etr.
  destruct ((tw <? fw)%positive && Pos.eqb fw' fw &&
            cert_binop_flags_eqb fl_b no_binop_flags &&
            match op with CB_Add | CB_Sub | CB_Mul => true | _ => false end &&
            (is_ext_from_width tw fw x || is_ext_from_width tw fw y)) eqn:Econd;
    [| discriminate Etr].
  inversion Etr; subst ot; clear Etr.
  rewrite !andb_true_iff in Econd;
    destruct Econd as ((((Htf & Hfw) & Hfb) & Hop) & _);
    apply Pos.eqb_eq in Hfw; subst fw'.
  cbn [wt_cert_expr] in Hto; cbn [is_let_free_expr] in Hfl_o; cbn [collect_free_vars].
  rewrite !andb_true_iff in Hto; rewrite !andb_true_iff in Hfl_o.
  destruct Hto as ((((_ & Htx) & Hty) & Hwx) & Hwy);
    destruct Hfl_o as [Hlfx Hlfy];
    apply Pos.eqb_eq in Hwx; apply Pos.eqb_eq in Hwy.
  assert (Hk_tr : ((tw <? fw)%positive && negb (ccf_nneg no_cast_flags)) = true)
    by (rewrite Htf; reflexivity).
  destruct (norm_cast_basic_typing CCK_Trunc fw tw no_cast_flags x Hk_tr Hwx Htx Hlfx)
    as (Hwx' & Htx' & Hlfx' & Hinc_x).
  destruct (norm_cast_basic_typing CCK_Trunc fw tw no_cast_flags y Hk_tr Hwy Hty Hlfy)
    as (Hwy' & Hty' & Hlfy' & Hinc_y).
  assert (Hwf_op : wf_binop_flags_for op no_binop_flags = true) by (destruct op; reflexivity).
  cbn [cert_expr_bit_width wt_cert_expr is_let_free_expr collect_free_vars].
  rewrite Hwf_op, Htx', Hty', Hwx', Hwy', !Pos.eqb_refl, Hlfx', Hlfy'.
  repeat split; try reflexivity.
  intros z Hz; apply in_app_iff in Hz as [Hz | Hz];
    [apply in_app_iff; left; exact (Hinc_x z Hz)
    | apply in_app_iff; right; exact (Hinc_y z Hz)].
Qed.

Lemma norm_cast_step_eval :
  forall {Pa : Params} k fw tw fl no (penv : param_env Pa) foracle,
    match k with
    | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg fl) && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg fl)
    end = true ->
    wt_cert_expr [] no = true ->
    wf_param_env_for (collect_free_vars [] no) penv ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_Cast k fw tw fl no))
      (eval_closed_cert_expr penv foracle (norm_cast_step k fw tw fl no)).
Proof.
  intros Pa k fw tw fl no penv foracle Hk Hto Hpo.
  unfold norm_cast_step.
  pose proof (norm_cast_basic_eval k fw tw fl no penv foracle Hk Hto Hpo) as Hbas.
  unfold norm_cast_basic in Hbas.
  destruct (try_fold_const_cast k fw tw fl no) as [c |]; [exact Hbas |].
  destruct (is_no_cast_flags fl) eqn:Eno; [| exact Hbas].
  destruct (norm_cast_chain k fw tw no) as [oc |]; [exact Hbas |].
  destruct (norm_trunc_binop k fw tw no) as [ot |] eqn:Etr; [| exact Hbas].
  pose proof (is_no_cast_flags_inv fl Eno) as Hfl0; subst fl.
  destruct k, no as [| | | op fw' fl_b x y | | | | |];
    cbn [norm_trunc_binop] in Etr; try discriminate Etr.
  destruct ((tw <? fw)%positive && Pos.eqb fw' fw &&
            cert_binop_flags_eqb fl_b no_binop_flags &&
            match op with CB_Add | CB_Sub | CB_Mul => true | _ => false end &&
            (is_ext_from_width tw fw x || is_ext_from_width tw fw y)) eqn:Econd;
    [| discriminate Etr].
  inversion Etr; subst ot; clear Etr.
  rewrite !andb_true_iff in Econd;
    destruct Econd as ((((Htf & Hfw) & Hfb) & Hop) & _);
    apply Pos.eqb_eq in Hfw; apply cert_binop_flags_eqb_eq in Hfb; subst fw' fl_b.
  cbn [wt_cert_expr collect_free_vars] in Hto, Hpo; rewrite !andb_true_iff in Hto.
  destruct Hto as ((((_ & Htx) & Hty) & Hwx) & Hwy);
    apply Pos.eqb_eq in Hwx; apply Pos.eqb_eq in Hwy.
  assert (Hpx : wf_param_env_for (collect_free_vars [] x) penv)
    by (intros z wz Hz; apply Hpo, in_app_iff; left; exact Hz).
  assert (Hpy : wf_param_env_for (collect_free_vars [] y) penv)
    by (intros z wz Hz; apply Hpo, in_app_iff; right; exact Hz).
  assert (Hk_tr : ((tw <? fw)%positive && negb (ccf_nneg no_cast_flags)) = true)
    by (rewrite Htf; reflexivity).
  pose proof (norm_cast_basic_eval CCK_Trunc fw tw no_cast_flags x penv foracle Hk_tr Htx Hpx) as Hbx.
  pose proof (norm_cast_basic_eval CCK_Trunc fw tw no_cast_flags y penv foracle Hk_tr Hty Hpy) as Hby.
  unfold eval_closed_cert_expr in *.
  cbn [eval_cert_expr] in Hbx, Hby |- *.
  destruct (eval_cert_expr_totality x [] penv [] foracle Htx wf_let_val_env_nil Hpx)
    as [[msgx Ex] | [vx [Ex Hwvx]]];
    [rewrite Ex in Hbx |- *; cbn [eou_bind] in Hbx |- *;
     destruct (eval_cert_expr penv [] foracle (norm_cast_basic CCK_Trunc fw tw no_cast_flags x));
     cbn in Hbx; try contradiction; cbn [eou_bind equiv_eou_dvalue]; exact I |].
  destruct (eval_cert_expr_totality y [] penv [] foracle Hty wf_let_val_env_nil Hpy)
    as [[msgy Ey] | [vy [Ey Hwvy]]].
  { rewrite Ex in Hbx |- *; rewrite Ey in Hby |- *; cbn [eou_bind] in Hbx, Hby |- *.
    rewrite Hwx in Hwvx.
    destruct (eval_cast_wf_scalar CCK_Trunc fw tw no_cast_flags vx Hk_tr Hwvx) as [vx' [Evx' _]].
    cbn [cert_to_pure_conv no_cast_flags ccf_nuw ccf_nsw] in Evx', Hbx.
    rewrite Evx' in Hbx.
    destruct (eval_cert_expr penv [] foracle (norm_cast_basic CCK_Trunc fw tw no_cast_flags x))
      as [| | | vx''];
      [cbn in Hbx; contradiction .. | cbn [eou_bind]].
    destruct (eval_cert_expr penv [] foracle (norm_cast_basic CCK_Trunc fw tw no_cast_flags y))
      as [| | msgy' |];
      [cbn in Hby; contradiction | cbn in Hby; contradiction | | cbn in Hby; contradiction].
    cbn [eou_bind equiv_eou_dvalue]; exact I. }
  rewrite Ex in Hbx |- *; rewrite Ey in Hby |- *.
  rewrite Hwx in Hwvx; rewrite Hwy in Hwvy.
  cbn [eou_bind] in Hbx, Hby |- *.
  destruct (eval_cert_expr penv [] foracle (norm_cast_basic CCK_Trunc fw tw no_cast_flags x))
    as [| | | vx'] eqn:Enx;
    [cbn [convert_pure eou_bind] in Hbx;
     destruct Hwvx as [-> | [ix ->]];
     [cbn in Hbx; contradiction
     | cbn - [Pos.eqb Pos.ltb] in Hbx; rewrite Pos.eqb_refl, Htf in Hbx; cbn in Hbx; contradiction] ..
    |].
  destruct (eval_cert_expr penv [] foracle (norm_cast_basic CCK_Trunc fw tw no_cast_flags y))
    as [| | | vy'] eqn:Eny;
    [cbn [convert_pure eou_bind] in Hby;
     destruct Hwvy as [-> | [iy ->]];
     [cbn in Hby; contradiction
     | cbn - [Pos.eqb Pos.ltb] in Hby; rewrite Pos.eqb_refl, Htf in Hby; cbn in Hby; contradiction] ..
    |].
  cbn in Hbx, Hby; cbn [eou_bind].
  assert (Htw_le : (tw <= fw)%positive) by (apply Pos.lt_le_incl, Pos.ltb_lt; exact Htf).
  destruct Hwvx as [-> | [ix ->]], Hwvy as [-> | [iy ->]];
    cbn - [Pos.eqb Pos.ltb] in Hbx, Hby |- *.
  - subst vx' vy'; destruct op; try discriminate Hop; unfold eval_iop; cbn; reflexivity.
  - rewrite Pos.eqb_refl, Htf in Hby; cbn in Hby; subst vx' vy';
      destruct op; try discriminate Hop; unfold eval_iop; cbn; reflexivity.
  - rewrite Pos.eqb_refl, Htf in Hbx; cbn in Hbx; subst vx' vy';
      destruct op; try discriminate Hop; unfold eval_iop; cbn; reflexivity.
  - rewrite Pos.eqb_refl, Htf in Hbx, Hby; cbn in Hbx, Hby; subst vx' vy'.
    destruct op; try discriminate Hop;
      unfold eval_iop; rewrite !eval_iop_integer_base_same_width;
      unfold cert_to_ibinop, eval_int_op, tdb;
      rewrite ?alg_pos_eq_dec_refl;
      cbn - [Pos.eqb Pos.ltb Integers.add Integers.sub Integers.mul Integers.repr Integers.unsigned];
      rewrite ?Pos.eqb_refl, ?Htf;
      cbn - [Integers.add Integers.sub Integers.mul Integers.repr Integers.unsigned].
    + do 2 f_equal; unfold Integers.add;
        rewrite (alg_repr_unsigned_repr_le tw fw _ Htw_le);
        apply @Integers.eqm_samerepr, @Integers.eqm_add;
        first [apply alg_eqm_repr_unsigned | apply @Integers.eqm_sym, alg_eqm_repr_unsigned].
    + do 2 f_equal; unfold Integers.sub;
        rewrite (alg_repr_unsigned_repr_le tw fw _ Htw_le);
        apply @Integers.eqm_samerepr, @Integers.eqm_sub;
        first [apply alg_eqm_repr_unsigned | apply @Integers.eqm_sym, alg_eqm_repr_unsigned].
    + repeat match goal with
             | |- context [if Pos.eqb ?w 1%positive then _ else _] => destruct (Pos.eqb w 1%positive)
             end;
        cbn - [Pos.eqb Pos.ltb Integers.add Integers.sub Integers.mul Integers.repr Integers.unsigned];
        rewrite ?Pos.eqb_refl, ?Htf;
        cbn - [Integers.add Integers.sub Integers.mul Integers.repr Integers.unsigned];
        do 2 f_equal; unfold Integers.mul;
        rewrite (alg_repr_unsigned_repr_le tw fw _ Htw_le);
        apply @Integers.eqm_samerepr, @Integers.eqm_mult;
        first [apply alg_eqm_repr_unsigned | apply @Integers.eqm_sym, alg_eqm_repr_unsigned].
Qed.

Definition norm_select_step
  (ctx : ub_ctx) (w : positive) (nc nt nf : cert_expr) : cert_expr :=
  if is_one_const_expr 1%positive nc && ub_free_expr nf then nt
  else if is_zero_const_expr 1%positive nc && ub_free_expr nt then nf
  else if cert_expr_eqb nt nf && expr_guaranteed_defined ctx nc then nt
  else if Pos.eqb w 1%positive && is_one_const_expr 1%positive nt && is_zero_const_expr 1%positive nf
       then nc
  else if Pos.eqb w 1%positive && is_zero_const_expr 1%positive nt && is_one_const_expr 1%positive nf
       then CE_BinOp CB_Xor 1%positive no_binop_flags nc (CE_BvConst 1%positive 1%N)
  else
    match extract_not_expr 1%positive nc with
    | Some c0 =>
        if ub_free_expr nt && ub_free_expr nf
        then CE_Select w c0 nf nt
        else CE_Select w nc nt nf
    | None => CE_Select w nc nt nf
    end.

Lemma norm_select_step_typing :
  forall ctx w nc nt nf,
    cert_expr_bit_width nc = 1%positive ->
    cert_expr_bit_width nt = w ->
    cert_expr_bit_width nf = w ->
    wt_cert_expr [] nc = true ->
    wt_cert_expr [] nt = true ->
    wt_cert_expr [] nf = true ->
    is_let_free_expr nc = true ->
    is_let_free_expr nt = true ->
    is_let_free_expr nf = true ->
    let out := norm_select_step ctx w nc nt nf in
    cert_expr_bit_width out = w /\
    wt_cert_expr [] out = true /\
    is_let_free_expr out = true /\
    incl (collect_free_vars [] out)
         (collect_free_vars [] nc ++ collect_free_vars [] nt ++ collect_free_vars [] nf).
Proof.
  intros ctx w nc nt nf Hwc Hwt0 Hwf0 Htc Htt Htf Hlc Hlt Hlf; cbn zeta.
  assert (Hdef_out :
    cert_expr_bit_width (CE_Select w nc nt nf) = w /\
    wt_cert_expr [] (CE_Select w nc nt nf) = true /\
    is_let_free_expr (CE_Select w nc nt nf) = true /\
    incl (collect_free_vars [] (CE_Select w nc nt nf))
         (collect_free_vars [] nc ++ collect_free_vars [] nt ++ collect_free_vars [] nf)).
  { cbn; rewrite Htc, Htt, Htf, Hwc, Hwt0, Hwf0, !Pos.eqb_refl, Hlc, Hlt, Hlf.
    repeat split; apply incl_refl. }
  unfold norm_select_step.
  destruct (is_one_const_expr 1 nc && ub_free_expr nf).
  - repeat split; [exact Hwt0 | exact Htt | exact Hlt |].
    intros x Hx; apply in_app_iff; right; apply in_app_iff; left; exact Hx.
  - destruct (is_zero_const_expr 1 nc && ub_free_expr nt).
    + repeat split; [exact Hwf0 | exact Htf | exact Hlf |].
      intros x Hx; apply in_app_iff; right; apply in_app_iff; right; exact Hx.
    + destruct (cert_expr_eqb nt nf && expr_guaranteed_defined ctx nc).
      * repeat split; [exact Hwt0 | exact Htt | exact Hlt |].
        intros x Hx; apply in_app_iff; right; apply in_app_iff; left; exact Hx.
      * destruct (Pos.eqb w 1 && is_one_const_expr 1 nt && is_zero_const_expr 1 nf) eqn:Es10.
        -- rewrite !andb_true_iff in Es10; destruct Es10 as ([Ew1 _] & _);
             apply Pos.eqb_eq in Ew1; rewrite Ew1.
           repeat split; [exact Hwc | exact Htc | exact Hlc | apply incl_appl, incl_refl].
        -- destruct (Pos.eqb w 1 && is_zero_const_expr 1 nt && is_one_const_expr 1 nf) eqn:Es01.
           ++ rewrite !andb_true_iff in Es01; destruct Es01 as ([Ew1 _] & _);
                apply Pos.eqb_eq in Ew1; rewrite Ew1.
              cbn - [Pos.eqb]; rewrite Htc, Hwc, Hlc, app_nil_r; cbn; repeat split; apply incl_appl, incl_refl.
           ++ destruct (extract_not_expr 1 nc) as [c0 |] eqn:Enc; [| exact Hdef_out].
              destruct (ub_free_expr nt && ub_free_expr nf); [| exact Hdef_out].
              pose proof (extract_not_expr_inv 1 nc c0 Enc) as Heqc; subst nc.
              cbn [wt_cert_expr cert_expr_bit_width] in Htc; cbn in Hlc; rewrite !andb_true_iff in Htc; rewrite !andb_true_iff in Hlc.
              destruct Htc as ((((_ & Htc0) & _) & Hwc0) & _); destruct Hlc as [Hlc0 _].
              apply Pos.eqb_eq in Hwc0.
              cbn - [Pos.eqb]; rewrite Htc0, Htf, Htt, Hwc0, Hwf0, Hwt0, !Pos.eqb_refl, Hlc0, Hlf, Hlt, app_nil_r.
              cbn; repeat split.
              intros x Hx; apply in_app_iff in Hx as [Hxc | Hxft]; apply in_app_iff;
                [left; exact Hxc | right; apply in_app_iff; apply in_app_iff in Hxft as [Hxf | Hxt];
                                   [right; exact Hxf | left; exact Hxt]].
Qed.

Lemma norm_select_step_eval :
  forall {Pa : Params} ctx w nc nt nf (penv : param_env Pa) foracle,
    cert_expr_bit_width nc = 1%positive ->
    cert_expr_bit_width nt = w ->
    cert_expr_bit_width nf = w ->
    wt_cert_expr [] nc = true ->
    wt_cert_expr [] nt = true ->
    wt_cert_expr [] nf = true ->
    wf_param_env_for
      (collect_free_vars [] nc ++ collect_free_vars [] nt ++ collect_free_vars [] nf) penv ->
    ub_ctx_holds penv foracle ctx ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_Select w nc nt nf))
      (eval_closed_cert_expr penv foracle (norm_select_step ctx w nc nt nf)).
Proof.
  intros Pa ctx w nc nt nf penv foracle Hwc Hwt0 Hwf0 Htc Htt Htf Hpenv Hctx.
  assert (Hpc : wf_param_env_for (collect_free_vars [] nc) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
  assert (Hpt : wf_param_env_for (collect_free_vars [] nt) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; left; exact Hx).
  assert (Hpf : wf_param_env_for (collect_free_vars [] nf) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; right; exact Hx).
  unfold norm_select_step.
  destruct (is_one_const_expr 1 nc && ub_free_expr nf) eqn:Ec1.
  - apply andb_true_iff in Ec1 as [Eo1 Eubf]; rewrite (is_one_const_expr_inv 1 nc Eo1).
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
    destruct (eval_cert_expr_totality nt [] penv [] foracle Htt wf_let_val_env_nil Hpt)
      as [[msgt ->] | [vt [-> _]]]; [cbn; exact I | cbn [eou_bind]].
    destruct (ub_free_expr_eval_ret nf [] penv [] foracle Eubf Htf wf_let_val_env_nil Hpf)
      as [vf [-> _]]; cbn [eou_bind].
    rewrite repr_one_N; cbn; rewrite (@Integers.unsigned_one 1); cbn; reflexivity.
  - destruct (is_zero_const_expr 1 nc && ub_free_expr nt) eqn:Ec0.
    + apply andb_true_iff in Ec0 as [Ez0 Eubt]; rewrite (is_zero_const_expr_inv 1 nc Ez0).
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
      destruct (ub_free_expr_eval_ret nt [] penv [] foracle Eubt Htt wf_let_val_env_nil Hpt)
        as [vt [-> _]]; cbn [eou_bind].
      destruct (eval_cert_expr_totality nf [] penv [] foracle Htf wf_let_val_env_nil Hpf)
        as [[msgf ->] | [vf [-> _]]]; [cbn; exact I | cbn [eou_bind]].
      rewrite repr_zero_N; cbn; rewrite (@Integers.unsigned_zero 1); cbn; reflexivity.
    + destruct (cert_expr_eqb nt nf && expr_guaranteed_defined ctx nc) eqn:Esame.
      * apply andb_true_iff in Esame as [Eeq Edefc].
        apply cert_expr_eqb_eq in Eeq; subst nf.
        destruct (expr_guaranteed_defined_sound ctx nc penv foracle Edefc Htc Hpc Hctx)
          as [_ [ic Hic]].
        revert ic Hic; rewrite Hwc; intros ic Hic.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hic; cbn [eou_bind].
        destruct (eval_cert_expr_totality nt [] penv [] foracle Htt wf_let_val_env_nil Hpt)
          as [[msgt ->] | [vt [-> _]]]; [cbn; exact I | cbn [eou_bind]].
        cbn; destruct (@Integers.unsigned 1 ic =? 1)%Z; reflexivity.
      * destruct (Pos.eqb w 1 && is_one_const_expr 1 nt && is_zero_const_expr 1 nf) eqn:Es10.
        -- rewrite !andb_true_iff in Es10; destruct Es10 as ([Ew1 Et1] & Ef0);
             apply Pos.eqb_eq in Ew1; subst w.
           rewrite (is_one_const_expr_inv 1 nt Et1), (is_zero_const_expr_inv 1 nf Ef0).
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
           destruct (eval_cert_expr_totality nc [] penv [] foracle Htc wf_let_val_env_nil Hpc)
             as [[msgc ->] | [vc [-> Hwfvc]]]; cbn [eou_bind]; [exact I |].
           rewrite Hwc in Hwfvc; destruct Hwfvc as [-> | [ic ->]]; cbn; [reflexivity |].
           destruct (alg_i1_cases ic) as [-> | ->];
             rewrite repr_one_N, repr_zero_N,
                     ?(@Integers.unsigned_zero 1), ?(@Integers.unsigned_one 1); cbn; reflexivity.
        -- destruct (Pos.eqb w 1 && is_zero_const_expr 1 nt && is_one_const_expr 1 nf) eqn:Es01.
           ++ rewrite !andb_true_iff in Es01; destruct Es01 as ([Ew1 Et0] & Ef1);
                apply Pos.eqb_eq in Ew1; subst w.
              rewrite (is_zero_const_expr_inv 1 nt Et0), (is_one_const_expr_inv 1 nf Ef1).
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
              destruct (eval_cert_expr_totality nc [] penv [] foracle Htc wf_let_val_env_nil Hpc)
                as [[msgc ->] | [vc [-> Hwfvc]]]; cbn [eou_bind]; [exact I |].
              rewrite Hwc in Hwfvc; destruct Hwfvc as [-> | [ic ->]]; [cbn; reflexivity | cbn [eou_bind]].
              unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_one_N, repr_zero_N; cbn.
              destruct (alg_i1_cases ic) as [-> | ->];
                rewrite ?(@Integers.unsigned_zero 1), ?(@Integers.unsigned_one 1),
                        ?(@Integers.xor_zero_l 1), ?(@Integers.xor_idem 1); cbn; reflexivity.
           ++ destruct (extract_not_expr 1 nc) as [c0 |] eqn:Enc; [| apply equiv_eou_dvalue_refl].
              destruct (ub_free_expr nt && ub_free_expr nf) eqn:Eubtf; [| apply equiv_eou_dvalue_refl].
              apply andb_true_iff in Eubtf as [Eubt Eubf].
              pose proof (extract_not_expr_inv 1 nc c0 Enc) as Heqc; subst nc.
              cbn [wt_cert_expr cert_expr_bit_width] in Htc; cbn in Hpc;
                rewrite !andb_true_iff in Htc; rewrite app_nil_r in Hpc.
              destruct Htc as ((((_ & Htc0) & _) & Hwc0) & _); apply Pos.eqb_eq in Hwc0.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
              destruct (eval_cert_expr_totality c0 [] penv [] foracle Htc0 wf_let_val_env_nil Hpc)
                as [[msgc ->] | [vc0 [-> Hwfvc0]]]; cbn [eou_bind]; [exact I |].
              destruct (ub_free_expr_eval_ret nt [] penv [] foracle Eubt Htt wf_let_val_env_nil Hpt)
                as [vt [Evt _]].
              destruct (ub_free_expr_eval_ret nf [] penv [] foracle Eubf Htf wf_let_val_env_nil Hpf)
                as [vf [Evf _]].
              rewrite Hwc0 in Hwfvc0; destruct Hwfvc0 as [-> | [ic0 ->]]; cbn [eou_bind].
              ** cbn [eval_iop]; rewrite Evt, Evf; cbn; reflexivity.
              ** unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N; cbn [eou_bind].
                 rewrite Evt, Evf; cbn [eou_bind].
                 assert (Hm1 : @Integers.mone 1 = @Integers.one 1)
                   by (destruct (alg_i1_cases (@Integers.mone 1)) as [Hz | Hm1];
                       [apply (f_equal (@Integers.unsigned 1)) in Hz; cbv in Hz; discriminate | exact Hm1]).
                 cbn; rewrite Hm1.
                 destruct (alg_i1_cases ic0) as [-> | ->];
                   rewrite ?(@Integers.xor_zero_l 1), ?(@Integers.xor_idem 1); cbn;
                   rewrite ?(@Integers.unsigned_zero 1), ?(@Integers.unsigned_one 1); cbn; reflexivity.
Qed.

Fixpoint normalize_cert_expr (ctx : ub_ctx) (e : cert_expr) {struct e} : cert_expr :=
  match e with
  | CE_BvConst w val => mk_bv_const w (@Integers.repr w (Z.of_N val))
  | CE_Poison w => CE_Poison w
  | CE_Var nm w => CE_Var nm w
  | CE_BinOp op w fl l r =>
      norm_binop_step ctx op w fl (normalize_cert_expr ctx l) (normalize_cert_expr ctx r)
  | CE_ICmp pr ss w l r =>
      norm_icmp_step ctx pr ss w (normalize_cert_expr ctx l) (normalize_cert_expr ctx r)
  | CE_Cast k fw tw fl o =>
      norm_cast_step k fw tw fl (normalize_cert_expr ctx o)
  | CE_Select w c t f =>
      norm_select_step ctx w
        (normalize_cert_expr ctx c)
        (normalize_cert_expr ctx t)
        (normalize_cert_expr ctx f)
  | CE_Freeze w o =>
      if expr_guaranteed_defined ctx o
      then normalize_cert_expr ctx o
      else
        match o with
        | CE_Freeze w' inner =>
            if Pos.eqb w' w then CE_Freeze w inner else CE_Freeze w o
        | _ => CE_Freeze w o
        end
  | CE_Let bs body => CE_Let bs body
  end.

Lemma normalize_cert_expr_typing :
  forall ctx e,
    wt_cert_expr [] e = true ->
    is_let_free_expr e = true ->
    let ne := normalize_cert_expr ctx e in
    cert_expr_bit_width ne = cert_expr_bit_width e /\
    wt_cert_expr [] ne = true /\
    is_let_free_expr ne = true /\
    incl (collect_free_vars [] ne) (collect_free_vars [] e).
Proof.
  intros ctx e.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hwt Hlf; cbn zeta; try discriminate Hlf.
  - unfold normalize_cert_expr, mk_bv_const; cbn; repeat split; apply incl_refl.
  - cbn; repeat split; apply incl_refl.
  - cbn [normalize_cert_expr cert_expr_bit_width]; repeat split;
      [exact Hwt | apply incl_refl].
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars normalize_cert_expr cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
    destruct Hwt as ((((Hfl & Hwtl) & Hwtr) & Hwl) & Hwr); destruct Hlf as [Hlfl Hlfr].
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    destruct (IHl Hwtl Hlfl) as (Hbl & Htl & Hfl_l & Hinc_l).
    destruct (IHr Hwtr Hlfr) as (Hbr & Htr & Hfl_r & Hinc_r).
    rewrite Hwl in Hbl; rewrite Hwr in Hbr.
    destruct (norm_binop_step_typing ctx op w fl _ _ Hfl Hbl Hbr Htl Htr Hfl_l Hfl_r)
      as (Hb & Ht & Hfl_o & Hinc_o).
    repeat split; [exact Hb | exact Ht | exact Hfl_o |].
    intros x Hx; apply Hinc_o in Hx; apply in_app_iff in Hx as [Hxl | Hxr];
      apply in_app_iff; [left; exact (Hinc_l x Hxl) | right; exact (Hinc_r x Hxr)].
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars normalize_cert_expr cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
    destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr); destruct Hlf as [Hlfl Hlfr].
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    destruct (IHl Hwtl Hlfl) as (Hbl & Htl & Hfl_l & Hinc_l).
    destruct (IHr Hwtr Hlfr) as (Hbr & Htr & Hfl_r & Hinc_r).
    rewrite Hwl in Hbl; rewrite Hwr in Hbr.
    destruct (norm_icmp_step_typing ctx pr ss w _ _ Hbl Hbr Htl Htr Hfl_l Hfl_r)
      as (Hb & Ht & Hfl_o & Hinc_o).
    repeat split; [exact Hb | exact Ht | exact Hfl_o |].
    intros x Hx; apply Hinc_o in Hx; apply in_app_iff in Hx as [Hxl | Hxr];
      apply in_app_iff; [left; exact (Hinc_l x Hxl) | right; exact (Hinc_r x Hxr)].
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars normalize_cert_expr cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((Hk & Hwto) & Hwo).
    apply Pos.eqb_eq in Hwo.
    destruct (IHo Hwto Hlf) as (Hbo & Hto & Hfl_o & Hinc_o).
    rewrite Hwo in Hbo.
    destruct (norm_cast_step_typing k fw tw fl _ Hk Hbo Hto Hfl_o)
      as (Hb & Ht & Hfl_out & Hinc_out).
    repeat split; [exact Hb | exact Ht | exact Hfl_out | exact (incl_tran Hinc_out Hinc_o)].
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars normalize_cert_expr cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hwc) & Hwt0) & Hwf0).
    destruct Hlf as ([Hlfc Hlft] & Hlff).
    apply Pos.eqb_eq in Hwc; apply Pos.eqb_eq in Hwt0; apply Pos.eqb_eq in Hwf0.
    destruct (IHc Hwtc Hlfc) as (Hbc & Htc & Hfl_c & Hinc_c).
    destruct (IHt Hwtt Hlft) as (Hbt & Htt & Hfl_t & Hinc_t).
    destruct (IHf Hwtf Hlff) as (Hbf & Htf & Hfl_f & Hinc_f).
    rewrite Hwc in Hbc; rewrite Hwt0 in Hbt; rewrite Hwf0 in Hbf.
    destruct (norm_select_step_typing ctx w _ _ _ Hbc Hbt Hbf Htc Htt Htf Hfl_c Hfl_t Hfl_f)
      as (Hb & Ht & Hfl_o & Hinc_o).
    repeat split; [exact Hb | exact Ht | exact Hfl_o |].
    intros x Hx; apply Hinc_o in Hx.
    apply in_app_iff in Hx as [Hxc | Hxtf];
      [apply in_app_iff; left; exact (Hinc_c x Hxc) |].
    apply in_app_iff in Hxtf as [Hxt | Hxf]; apply in_app_iff; right; apply in_app_iff;
      [left; exact (Hinc_t x Hxt) | right; exact (Hinc_f x Hxf)].
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars normalize_cert_expr cert_expr_bit_width] in *.
    apply andb_true_iff in Hwt as [Hwto Hwo]; apply Pos.eqb_eq in Hwo.
    destruct (expr_guaranteed_defined ctx o).
    + destruct (IHo Hwto Hlf) as (Hbo & Hto & Hfl_o & Hinc_o).
      rewrite Hwo in Hbo; repeat split; assumption.
    + assert (Hunch :
        cert_expr_bit_width (CE_Freeze w o) = w /\
        wt_cert_expr [] (CE_Freeze w o) = true /\
        is_let_free_expr (CE_Freeze w o) = true /\
        incl (collect_free_vars [] (CE_Freeze w o)) (collect_free_vars [] o)).
      { change (wt_cert_expr [] (CE_Freeze w o)) with (wt_cert_expr [] o && Pos.eqb (cert_expr_bit_width o) w).
        change (is_let_free_expr (CE_Freeze w o)) with (is_let_free_expr o).
        change (collect_free_vars [] (CE_Freeze w o)) with (collect_free_vars [] o).
        rewrite Hwto, Hwo, Pos.eqb_refl, Hlf; repeat split; apply incl_refl. }
      destruct o as [| | | | | | | w' inner |]; try exact Hunch.
      destruct (Pos.eqb w' w) eqn:Eww'; [| exact Hunch].
      apply Pos.eqb_eq in Eww'; subst w'.
      cbn [wt_cert_expr is_let_free_expr collect_free_vars cert_expr_bit_width] in Hwto, Hlf |- *.
      rewrite Hwto, Hlf; repeat split; apply incl_refl.
Qed.

Lemma normalize_cert_expr_eval :
  forall {Pa : Params} ctx e (penv : param_env Pa) foracle,
    wt_cert_expr [] e = true ->
    is_let_free_expr e = true ->
    wf_param_env_for (collect_free_vars [] e) penv ->
    ub_ctx_holds penv foracle ctx ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle e)
      (eval_closed_cert_expr penv foracle (normalize_cert_expr ctx e)).
Proof.
  intros Pa ctx e.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros penv foracle Hwt Hlf Hpenv Hctx;
    try discriminate Hlf.
  - unfold normalize_cert_expr, mk_bv_const, eval_closed_cert_expr; cbn.
    rewrite repr_of_N_to_N_unsigned; reflexivity.
  - apply equiv_eou_dvalue_refl.
  - apply equiv_eou_dvalue_refl.
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars normalize_cert_expr] in *.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
    destruct Hwt as ((((Hfl & Hwtl) & Hwtr) & Hwl) & Hwr); destruct Hlf as [Hlfl Hlfr].
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    assert (Hpl : wf_param_env_for (collect_free_vars [] l) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars [] r) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
    destruct (normalize_cert_expr_typing ctx l Hwtl Hlfl) as (Hbl & Htl & _ & Hinc_l).
    destruct (normalize_cert_expr_typing ctx r Hwtr Hlfr) as (Hbr & Htr & _ & Hinc_r).
    rewrite Hwl in Hbl; rewrite Hwr in Hbr.
    assert (Hcong : equiv_eou_dvalue
                      (eval_closed_cert_expr penv foracle (CE_BinOp op w fl l r))
                      (eval_closed_cert_expr penv foracle
                         (CE_BinOp op w fl (normalize_cert_expr ctx l) (normalize_cert_expr ctx r)))).
    { unfold eval_closed_cert_expr; cbn [eval_cert_expr].
      apply eou_bind_equiv_cong; [exact (IHl penv foracle Hwtl Hlfl Hpl Hctx) | intros vl].
      apply eou_bind_equiv_cong; [exact (IHr penv foracle Hwtr Hlfr Hpr Hctx) | intros vr].
      apply equiv_eou_dvalue_refl. }
    apply (equiv_eou_dvalue_trans _ _ _ Hcong).
    refine (norm_binop_step_eval ctx op w fl _ _ penv foracle Hfl Hbl Hbr Htl Htr _ Hctx).
    intros x wx Hx; apply in_app_iff in Hx as [Hxl | Hxr];
      [exact (Hpl x wx (Hinc_l _ Hxl)) | exact (Hpr x wx (Hinc_r _ Hxr))].
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars normalize_cert_expr] in *.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
    destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr); destruct Hlf as [Hlfl Hlfr].
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    assert (Hpl : wf_param_env_for (collect_free_vars [] l) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars [] r) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
    destruct (normalize_cert_expr_typing ctx l Hwtl Hlfl) as (Hbl & Htl & _ & Hinc_l).
    destruct (normalize_cert_expr_typing ctx r Hwtr Hlfr) as (Hbr & Htr & _ & Hinc_r).
    rewrite Hwl in Hbl; rewrite Hwr in Hbr.
    assert (Hcong : equiv_eou_dvalue
                      (eval_closed_cert_expr penv foracle (CE_ICmp pr ss w l r))
                      (eval_closed_cert_expr penv foracle
                         (CE_ICmp pr ss w (normalize_cert_expr ctx l) (normalize_cert_expr ctx r)))).
    { unfold eval_closed_cert_expr; cbn [eval_cert_expr].
      apply eou_bind_equiv_cong; [exact (IHl penv foracle Hwtl Hlfl Hpl Hctx) | intros vl].
      apply eou_bind_equiv_cong; [exact (IHr penv foracle Hwtr Hlfr Hpr Hctx) | intros vr].
      apply equiv_eou_dvalue_refl. }
    apply (equiv_eou_dvalue_trans _ _ _ Hcong).
    refine (norm_icmp_step_eval ctx pr ss w _ _ penv foracle Hbl Hbr Htl Htr _ Hctx).
    intros x wx Hx; apply in_app_iff in Hx as [Hxl | Hxr];
      [exact (Hpl x wx (Hinc_l _ Hxl)) | exact (Hpr x wx (Hinc_r _ Hxr))].
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars normalize_cert_expr] in *.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((Hk & Hwto) & _).
    destruct (normalize_cert_expr_typing ctx o Hwto Hlf) as (_ & Hto & _ & Hinc_o).
    assert (Hcong : equiv_eou_dvalue
                      (eval_closed_cert_expr penv foracle (CE_Cast k fw tw fl o))
                      (eval_closed_cert_expr penv foracle
                         (CE_Cast k fw tw fl (normalize_cert_expr ctx o)))).
    { unfold eval_closed_cert_expr; cbn [eval_cert_expr].
      apply eou_bind_equiv_cong;
        [exact (IHo penv foracle Hwto Hlf Hpenv Hctx) | intros vo; apply equiv_eou_dvalue_refl]. }
    apply (equiv_eou_dvalue_trans _ _ _ Hcong).
    apply (norm_cast_step_eval k fw tw fl _ penv foracle Hk Hto).
    intros x wx Hx; exact (Hpenv x wx (Hinc_o _ Hx)).
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars normalize_cert_expr] in *.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hwc) & Hwt0) & Hwf0).
    destruct Hlf as ([Hlfc Hlft] & Hlff).
    apply Pos.eqb_eq in Hwc; apply Pos.eqb_eq in Hwt0; apply Pos.eqb_eq in Hwf0.
    assert (Hpc : wf_param_env_for (collect_free_vars [] c) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpt : wf_param_env_for (collect_free_vars [] t) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; left; exact Hx).
    assert (Hpf : wf_param_env_for (collect_free_vars [] f) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; right; exact Hx).
    destruct (normalize_cert_expr_typing ctx c Hwtc Hlfc) as (Hbc & Htc & _ & Hinc_c).
    destruct (normalize_cert_expr_typing ctx t Hwtt Hlft) as (Hbt & Htt & _ & Hinc_t).
    destruct (normalize_cert_expr_typing ctx f Hwtf Hlff) as (Hbf & Htf & _ & Hinc_f).
    rewrite Hwc in Hbc; rewrite Hwt0 in Hbt; rewrite Hwf0 in Hbf.
    assert (Hcong : equiv_eou_dvalue
                      (eval_closed_cert_expr penv foracle (CE_Select w c t f))
                      (eval_closed_cert_expr penv foracle
                         (CE_Select w (normalize_cert_expr ctx c)
                                      (normalize_cert_expr ctx t)
                                      (normalize_cert_expr ctx f)))).
    { unfold eval_closed_cert_expr; cbn [eval_cert_expr].
      apply eou_bind_equiv_cong; [exact (IHc penv foracle Hwtc Hlfc Hpc Hctx) | intros vc].
      apply eou_bind_equiv_cong; [exact (IHt penv foracle Hwtt Hlft Hpt Hctx) | intros vt].
      apply eou_bind_equiv_cong; [exact (IHf penv foracle Hwtf Hlff Hpf Hctx) | intros vf].
      apply equiv_eou_dvalue_refl. }
    apply (equiv_eou_dvalue_trans _ _ _ Hcong).
    refine (norm_select_step_eval ctx w _ _ _ penv foracle Hbc Hbt Hbf Htc Htt Htf _ Hctx).
    intros x wx Hx; apply in_app_iff in Hx as [Hxc | Hxtf];
      [exact (Hpc x wx (Hinc_c _ Hxc)) |].
    apply in_app_iff in Hxtf as [Hxt | Hxf];
      [exact (Hpt x wx (Hinc_t _ Hxt)) | exact (Hpf x wx (Hinc_f _ Hxf))].
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars normalize_cert_expr] in *.
    apply andb_true_iff in Hwt as [Hwto Hwo]; apply Pos.eqb_eq in Hwo.
    destruct (expr_guaranteed_defined ctx o) eqn:Edefo.
    + destruct (expr_guaranteed_defined_sound ctx o penv foracle Edefo Hwto Hpenv Hctx)
        as [_ [io Hio]].
      revert io Hio; rewrite Hwo; intros io Hio.
      pose proof (IHo penv foracle Hwto Hlf Hpenv Hctx) as Heqo.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hio in Heqo |- *.
      exact Heqo.
    + destruct o as [| | | | | | | w' inner |]; try apply equiv_eou_dvalue_refl.
      destruct (Pos.eqb w' w) eqn:Eww'; [| apply equiv_eou_dvalue_refl].
      apply Pos.eqb_eq in Eww'; subst w'.
      cbn [wt_cert_expr collect_free_vars] in Hwto, Hpenv.
      apply andb_true_iff in Hwto as [Hwti Hwi]; apply Pos.eqb_eq in Hwi.
      unfold eval_closed_cert_expr; cbn [eval_cert_expr].
      destruct (eval_cert_expr_totality inner [] penv [] foracle Hwti wf_let_val_env_nil Hpenv)
        as [[msgi ->] | [vi [-> Hwf_vi]]]; [cbn; exact I | cbn [eou_bind]].
      rewrite Hwi in Hwf_vi.
      destruct Hwf_vi as [-> | [ii ->]]; cbn; reflexivity.
Qed.

(** *** 6.3 Directional Refinement Checker ([check_expr_refines]) & Soundness *)

Definition binop_flags_weaken (fl_src fl_tgt : cert_binop_flags) : bool :=
  implb (cbf_nuw fl_tgt) (cbf_nuw fl_src) &&
  implb (cbf_nsw fl_tgt) (cbf_nsw fl_src) &&
  implb (cbf_exact fl_tgt) (cbf_exact fl_src) &&
  implb (cbf_disjoint fl_tgt) (cbf_disjoint fl_src).

Definition cast_flags_weaken (fl_src fl_tgt : cert_cast_flags) : bool :=
  implb (ccf_nneg fl_tgt) (ccf_nneg fl_src) &&
  implb (ccf_nuw fl_tgt) (ccf_nuw fl_src) &&
  implb (ccf_nsw fl_tgt) (ccf_nsw fl_src).

Definition expr_divisor_nonzero (ctx : ub_ctx) (e : cert_expr) : bool :=
  match e with
  | CE_BvConst w val =>
      negb ((@Integers.unsigned w (@Integers.repr w (Z.of_N val)) =? 0)%Z)
  | _ => false
  end || ctx_has_divisor_nonzero ctx e.

Lemma expr_divisor_nonzero_sound :
  forall {Pa : Params} ctx e (penv : param_env Pa) foracle,
    wt_cert_expr [] e = true ->
    expr_divisor_nonzero ctx e = true ->
    ub_ctx_holds penv foracle ctx ->
    exists i : @Integers.bit_int (cert_expr_bit_width e),
      eval_closed_cert_expr penv foracle e =
      raise_ret (DVALUE_Base (@DVALUE_I Pa (cert_expr_bit_width e) i)) /\
      (@Integers.unsigned (cert_expr_bit_width e) i <> 0)%Z.
Proof.
  intros Pa ctx e penv foracle Hwt Hnz Hctx.
  unfold expr_divisor_nonzero in Hnz.
  apply orb_true_iff in Hnz as [Hcst | Hctx_nz].
  - destruct e as [w val | | | | | | | |]; try discriminate Hcst.
    apply negb_true_iff in Hcst; apply Z.eqb_neq in Hcst.
    cbn [cert_expr_bit_width]; exists (@Integers.repr w (Z.of_N val)).
    split; [reflexivity | exact Hcst].
  - destruct (ctx_has_divisor_nonzero_sound penv foracle ctx e Hctx_nz Hctx)
      as [w0 [i0 [Hev Hnz0]]].
    pose proof (eval_cert_expr_ret_wf_scalar e [] penv [] foracle _ Hwt Hev) as Hwf.
    destruct Hwf as [Hpsn | [i' Hi']]; [discriminate Hpsn |].
    injection Hi' as Hw_eq _.
    subst w0; exists i0; split; assumption.
Qed.

Lemma alg_unsigned_nz_signed_nz : forall w (i : @Integers.bit_int w),
  (@Integers.unsigned w i <> 0)%Z -> (@Integers.signed w i <> 0)%Z.
Proof.
  intros w i Huns Hsgn; apply Huns.
  assert (Hz : i = @Integers.zero w).
  { rewrite <- (@Integers.repr_signed w i), Hsgn; reflexivity. }
  rewrite Hz; apply @Integers.unsigned_zero.
Qed.

Lemma eou_bind_refine_typed :
  forall {Pa : Params} w (m1 m2 : EOU (@dvalue Pa))
         (k1 k2 : @dvalue Pa -> EOU (@dvalue Pa)),
    (forall v1, m1 = raise_ret v1 -> wf_scalar_dvalue w v1) ->
    (forall v2, m2 = raise_ret v2 -> wf_scalar_dvalue w v2) ->
    refine_eou_dvalue m1 m2 ->
    (forall v1 v2,
       wf_scalar_dvalue w v1 ->
       wf_scalar_dvalue w v2 ->
       dvalue_refines v1 v2 ->
       refine_eou_dvalue (k1 v1) (k2 v2)) ->
    refine_eou_dvalue (eou_bind m1 k1) (eou_bind m2 k2).
Proof.
  intros Pa w m1 m2 k1 k2 Hw1 Hw2 Hm Hk.
  destruct m1, m2; cbn in Hm |- *; try contradiction; trivial.
  exact (Hk _ _ (Hw1 _ eq_refl) (Hw2 _ eq_refl) Hm).
Qed.

Lemma binop_flags_weaken_no_flags : forall fl,
  binop_flags_weaken fl no_binop_flags = true.
Proof.
  intros fl; reflexivity.
Qed.

Lemma eval_iop_non_div_rem_monotone :
  forall {Pa : Params} op fl1 fl2 w (vl1 vl2 vr1 vr2 : @dvalue Pa),
    is_div_or_rem_op op = false ->
    binop_flags_weaken fl1 fl2 = true ->
    wf_scalar_dvalue w vl1 ->
    wf_scalar_dvalue w vl2 ->
    wf_scalar_dvalue w vr1 ->
    wf_scalar_dvalue w vr2 ->
    dvalue_refines vl1 vl2 ->
    dvalue_refines vr1 vr2 ->
    refine_eou_dvalue
      (@eval_iop Pa (cert_to_ibinop op fl1) vl1 vr1)
      (@eval_iop Pa (cert_to_ibinop op fl2) vl2 vr2).
Proof.
  intros Pa op fl1 fl2 w vl1 vl2 vr1 vr2 Hop Hfl Hwfl1 Hwfl2 Hwfr1 Hwfr2 Hrefl Hrefr.
  destruct Hrefl as [-> | ->].
  - assert (Hsrc : @eval_iop Pa (cert_to_ibinop op fl1) (DVALUE_Base DVALUE_Poison) vr1 =
                   raise_ret (DVALUE_Base DVALUE_Poison)).
    { destruct Hwfr1 as [-> | [ir1 ->]]; destruct op; cbn in Hop; try discriminate; reflexivity. }
    rewrite Hsrc.
    destruct (eval_iop_non_div_rem_no_ub op fl2 w vl2 vr2 Hop Hwfl2 Hwfr2) as [vout2 [-> _]].
    cbn; apply dvalue_refines_poison_l.
  - destruct Hrefr as [-> | ->].
    + assert (Hsrc : @eval_iop Pa (cert_to_ibinop op fl1) vl1 (DVALUE_Base DVALUE_Poison) =
                     raise_ret (DVALUE_Base DVALUE_Poison)).
      { destruct Hwfl1 as [-> | [il1 ->]]; destruct op; cbn in Hop; try discriminate; reflexivity. }
      rewrite Hsrc.
      destruct (eval_iop_non_div_rem_no_ub op fl2 w vl1 vr2 Hop Hwfl1 Hwfr2) as [vout2 [-> _]].
      cbn; apply dvalue_refines_poison_l.
    + destruct Hwfl1 as [-> | [il ->]].
      * destruct Hwfr1 as [-> | [ir ->]]; destruct op; cbn in Hop; try discriminate;
          cbn; apply dvalue_refines_refl.
      * destruct Hwfr1 as [-> | [ir ->]];
          [destruct op; cbn in Hop; try discriminate; cbn; apply dvalue_refines_refl |].
        unfold binop_flags_weaken in Hfl; rewrite !andb_true_iff in Hfl.
        destruct Hfl as (((Hnuw & Hnsw) & Hex) & Hdisj).
        unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
        destruct op; cbn in Hop; try discriminate;
          unfold cert_to_ibinop, eval_int_op, dvp; cbn - [andb orb negb]; rewrite ?andb_true_r.
        -- destruct (cbf_nuw fl1), (cbf_nuw fl2), (cbf_nsw fl1), (cbf_nsw fl2);
             cbn in Hnuw, Hnsw; try discriminate;
             split_bool_ifs;
             cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
        -- destruct (cbf_nuw fl1), (cbf_nuw fl2), (cbf_nsw fl1), (cbf_nsw fl2);
             cbn in Hnuw, Hnsw; try discriminate;
             split_bool_ifs;
             cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
        -- destruct (Pos.eqb w 1); [cbn; apply dvalue_refines_refl |].
           destruct (cbf_nuw fl1), (cbf_nuw fl2), (cbf_nsw fl1), (cbf_nsw fl2);
             cbn in Hnuw, Hnsw; try discriminate;
             split_bool_ifs;
             cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
        -- destruct (@Integers.unsigned w ir >=? Z.pos w)%Z; [cbn; apply dvalue_refines_refl |].
           destruct (cbf_nuw fl1), (cbf_nuw fl2), (cbf_nsw fl1), (cbf_nsw fl2);
             cbn in Hnuw, Hnsw; try discriminate;
             split_bool_ifs;
             cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
        -- destruct (@Integers.unsigned w ir >=? Z.pos w)%Z; [cbn; apply dvalue_refines_refl |].
           destruct (cbf_exact fl1), (cbf_exact fl2);
             cbn in Hex; try discriminate;
             split_bool_ifs;
             cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
        -- destruct (@Integers.unsigned w ir >=? Z.pos w)%Z; [cbn; apply dvalue_refines_refl |].
           destruct (cbf_exact fl1), (cbf_exact fl2);
             cbn in Hex; try discriminate;
             split_bool_ifs;
             cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
        -- apply dvalue_refines_refl.
        -- destruct (cbf_disjoint fl1), (cbf_disjoint fl2);
             cbn in Hdisj; try discriminate;
             split_bool_ifs;
             cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
        -- apply dvalue_refines_refl.
Qed.

Lemma eval_iop_div_rem_same_lhs :
  forall {Pa : Params} op fl1 fl2 w (vl vr1 vr2 : @dvalue Pa),
    is_div_or_rem_op op = true ->
    binop_flags_weaken fl1 fl2 = true ->
    wf_scalar_dvalue w vl ->
    wf_scalar_dvalue w vr1 ->
    wf_scalar_dvalue w vr2 ->
    dvalue_refines vr1 vr2 ->
    refine_eou_dvalue
      (@eval_iop Pa (cert_to_ibinop op fl1) vl vr1)
      (@eval_iop Pa (cert_to_ibinop op fl2) vl vr2).
Proof.
  intros Pa op fl1 fl2 w vl vr1 vr2 Hop Hfl Hwfl Hwfr1 _ [-> | ->].
  - destruct Hwfl as [-> | [il ->]]; destruct op; cbn in Hop; try discriminate; cbn; exact I.
  - destruct Hwfr1 as [-> | [ir ->]].
    + destruct Hwfl as [-> | [il ->]]; destruct op; cbn in Hop; try discriminate; cbn; exact I.
    + destruct Hwfl as [-> | [il ->]].
      * destruct op; cbn in Hop; try discriminate; cbn;
          try apply dvalue_refines_refl;
          (destruct (Z.eq_dec (@Integers.signed w ir) (-1)%Z); cbn;
           [exact I | apply dvalue_refines_refl]).
      * unfold binop_flags_weaken in Hfl; rewrite !andb_true_iff in Hfl.
        destruct Hfl as (((_ & _) & Hex) & _).
        unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
        destruct op; cbn in Hop; try discriminate;
          unfold cert_to_ibinop, eval_int_op, dvp; cbn - [andb orb negb]; rewrite ?andb_true_r;
          destruct (cbf_exact fl1), (cbf_exact fl2);
          cbn in Hex; try discriminate;
          split_bool_ifs;
          cbn; first [exact I | apply dvalue_refines_poison_l | apply dvalue_refines_refl].
Qed.

Lemma eval_iop_sdiv_poison_l : forall {Pa : Params} ex w (ir : @Integers.bit_int w),
  @eval_iop Pa (LLVMAst.SDiv ex) (DVALUE_Base DVALUE_Poison) (DVALUE_Base (@DVALUE_I Pa w ir)) =
  if Z.eq_dec (@Integers.signed w ir) (-1)%Z
  then raise_ub "Signed division/remainder poison overflow"
  else raise_ret (DVALUE_Base DVALUE_Poison).
Proof.
  intros Pa ex w ir; cbn.
  destruct (Z.eq_dec (@Integers.signed w ir) (-1)%Z); reflexivity.
Qed.

Lemma eval_iop_srem_poison_l : forall {Pa : Params} w (ir : @Integers.bit_int w),
  @eval_iop Pa LLVMAst.SRem (DVALUE_Base DVALUE_Poison) (DVALUE_Base (@DVALUE_I Pa w ir)) =
  if Z.eq_dec (@Integers.signed w ir) (-1)%Z
  then raise_ub "Signed division/remainder poison overflow"
  else raise_ret (DVALUE_Base DVALUE_Poison).
Proof.
  intros Pa w ir; cbn.
  destruct (Z.eq_dec (@Integers.signed w ir) (-1)%Z); reflexivity.
Qed.

Lemma eval_iop_div_rem_nonzero_div :
  forall {Pa : Params} op fl1 fl2 w (ir : @Integers.bit_int w) (vl1 vl2 : @dvalue Pa),
    is_div_or_rem_op op = true ->
    binop_flags_weaken fl1 fl2 = true ->
    (@Integers.unsigned w ir <> 0)%Z ->
    wf_scalar_dvalue w vl1 ->
    wf_scalar_dvalue w vl2 ->
    dvalue_refines vl1 vl2 ->
    refine_eou_dvalue
      (@eval_iop Pa (cert_to_ibinop op fl1) vl1 (DVALUE_Base (@DVALUE_I Pa w ir)))
      (@eval_iop Pa (cert_to_ibinop op fl2) vl2 (DVALUE_Base (@DVALUE_I Pa w ir))).
Proof.
  intros Pa op fl1 fl2 w ir vl1 vl2 Hop Hfl Hnz Hwfl1 Hwfl2 [-> | ->].
  - destruct Hwfl2 as [-> | [il2 ->]].
    + exact (eval_iop_div_rem_same_lhs op fl1 fl2 w
               (DVALUE_Base DVALUE_Poison) _ _ Hop Hfl (or_introl eq_refl)
               (or_intror (ex_intro _ ir eq_refl))
               (or_intror (ex_intro _ ir eq_refl))
               (dvalue_refines_refl _)).
    + assert (Hu0 : (@Integers.unsigned w ir =? 0)%Z = false) by (apply Z.eqb_neq; exact Hnz).
      assert (Hs0 : (@Integers.signed w ir =? 0)%Z = false)
        by (apply Z.eqb_neq; exact (alg_unsigned_nz_signed_nz w ir Hnz)).
      destruct op; cbn in Hop; try discriminate.
      * change (@eval_iop Pa (cert_to_ibinop CB_UDiv fl1) (DVALUE_Base DVALUE_Poison)
                  (DVALUE_Base (@DVALUE_I Pa w ir))) with
          (@raise_ret (@dvalue Pa) (DVALUE_Base DVALUE_Poison)).
        unfold eval_iop; rewrite eval_iop_integer_base_same_width.
        unfold cert_to_ibinop, eval_int_op; cbn; rewrite Hu0; cbn.
        destruct (cbf_exact fl2 && _); cbn; apply dvalue_refines_poison_l.
      * cbn [cert_to_ibinop]; rewrite eval_iop_sdiv_poison_l.
        destruct (Z.eq_dec (@Integers.signed w ir) (-1)%Z) as [_ | Hnm1]; [cbn; exact I |].
        assert (Hsm1 : (@Integers.signed w ir =? -1)%Z = false) by (apply Z.eqb_neq; exact Hnm1).
        unfold eval_iop; rewrite eval_iop_integer_base_same_width.
        unfold eval_int_op; cbn; rewrite Hs0, Hsm1, andb_false_r; cbn.
        destruct (cbf_exact fl2 && _); cbn; apply dvalue_refines_poison_l.
      * change (@eval_iop Pa (cert_to_ibinop CB_URem fl1) (DVALUE_Base DVALUE_Poison)
                  (DVALUE_Base (@DVALUE_I Pa w ir))) with
          (@raise_ret (@dvalue Pa) (DVALUE_Base DVALUE_Poison)).
        unfold eval_iop; rewrite eval_iop_integer_base_same_width.
        unfold cert_to_ibinop, eval_int_op; cbn; rewrite Hu0; cbn; apply dvalue_refines_poison_l.
      * cbn [cert_to_ibinop]; rewrite eval_iop_srem_poison_l.
        destruct (Z.eq_dec (@Integers.signed w ir) (-1)%Z) as [_ | Hnm1]; [cbn; exact I |].
        assert (Hsm1 : (@Integers.signed w ir =? -1)%Z = false) by (apply Z.eqb_neq; exact Hnm1).
        unfold eval_iop; rewrite eval_iop_integer_base_same_width.
        unfold eval_int_op; cbn; rewrite Hs0, Hsm1, andb_false_r; cbn; apply dvalue_refines_poison_l.
  - exact (eval_iop_div_rem_same_lhs op fl1 fl2 w vl1 _ _ Hop Hfl Hwfl1
             (or_intror (ex_intro _ ir eq_refl))
             (or_intror (ex_intro _ ir eq_refl))
             (dvalue_refines_refl _)).
Qed.

Lemma alg_msamesign_sym : forall w (x y : @Integers.bit_int w),
  @msamesign (@Integers.bit_int w) (@VIntVMemInt (@Integers.bit_int w) (@VInt_Bounded w)) x y =
  @msamesign (@Integers.bit_int w) (@VIntVMemInt (@Integers.bit_int w) (@VInt_Bounded w)) y x.
Proof.
  intros w x y; cbn [msamesign VIntVMemInt samesign VInt_Bounded].
  rewrite (andb_comm (@Integers.cmp w Cge x (@Integers.zero w))),
          (andb_comm (@Integers.cmp w Clt x (@Integers.zero w))).
  reflexivity.
Qed.

Lemma eval_icmp_swap :
  forall {Pa : Params} ss pr w (vl vr : @dvalue Pa),
    wf_scalar_dvalue w vl ->
    wf_scalar_dvalue w vr ->
    @eval_icmp Pa ss (cert_to_icmp pr) vl vr =
    @eval_icmp Pa ss (cert_to_icmp (swap_cert_icmp pr)) vr vl.
Proof.
  intros Pa ss pr w vl vr [-> | [il ->]] [-> | [ir ->]]; try reflexivity.
  unfold eval_icmp; rewrite !eval_icmp_base_same_width.
  unfold eval_int_icmp; rewrite alg_msamesign_sym.
  destruct pr; unfold swap_cert_icmp, cert_to_icmp; cbn;
    try rewrite (@Integers.eq_sym w il ir);
    reflexivity.
Qed.

Lemma eval_icmp_monotone :
  forall {Pa : Params} ss1 ss2 pr w (vl1 vl2 vr1 vr2 : @dvalue Pa),
    implb ss2 ss1 = true ->
    wf_scalar_dvalue w vl1 ->
    wf_scalar_dvalue w vl2 ->
    wf_scalar_dvalue w vr1 ->
    wf_scalar_dvalue w vr2 ->
    dvalue_refines vl1 vl2 ->
    dvalue_refines vr1 vr2 ->
    refine_eou_dvalue
      (@eval_icmp Pa ss1 (cert_to_icmp pr) vl1 vr1)
      (@eval_icmp Pa ss2 (cert_to_icmp pr) vl2 vr2).
Proof.
  intros Pa ss1 ss2 pr w vl1 vl2 vr1 vr2 Hss Hwfl1 Hwfl2 Hwfr1 Hwfr2 [-> | ->].
  - intros _; assert (Hsrc : @eval_icmp Pa ss1 (cert_to_icmp pr) (DVALUE_Base DVALUE_Poison) vr1 =
                   raise_ret (DVALUE_Base DVALUE_Poison))
      by (destruct Hwfr1 as [-> | [ir1 ->]]; reflexivity).
    rewrite Hsrc.
    destruct (eval_icmp_wf_scalar ss2 pr w vl2 vr2 Hwfl2 Hwfr2) as [vout2 [-> _]].
    cbn; apply dvalue_refines_poison_l.
  - intros [-> | ->].
    + assert (Hsrc : @eval_icmp Pa ss1 (cert_to_icmp pr) vl1 (DVALUE_Base DVALUE_Poison) =
                     raise_ret (DVALUE_Base DVALUE_Poison))
        by (destruct Hwfl1 as [-> | [il1 ->]]; reflexivity).
      rewrite Hsrc.
      destruct (eval_icmp_wf_scalar ss2 pr w vl1 vr2 Hwfl1 Hwfr2) as [vout2 [-> _]].
      cbn; apply dvalue_refines_poison_l.
    + destruct Hwfl1 as [-> | [il ->]];
        [destruct Hwfr1 as [-> | [ir ->]]; cbn; apply dvalue_refines_refl |].
      destruct Hwfr1 as [-> | [ir ->]]; [cbn; apply dvalue_refines_refl |].
      unfold eval_icmp; rewrite !eval_icmp_base_same_width.
      destruct ss1, ss2; cbn in Hss; try discriminate;
        [apply refine_eou_dvalue_refl | | apply refine_eou_dvalue_refl].
      destruct pr; unfold cert_to_icmp, eval_int_icmp, dvp; cbn - [andb orb negb]; rewrite ?andb_true_r;
        split_bool_ifs;
        cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
Qed.

Lemma eval_cast_monotone :
  forall {Pa : Params} k fw tw fl1 fl2 (vo1 vo2 : @dvalue Pa),
    match k with
    | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw fl1) && negb (ccf_nsw fl1)
    | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg fl1) && negb (ccf_nuw fl1) && negb (ccf_nsw fl1)
    | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg fl1)
    end = true ->
    match k with
    | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw fl2) && negb (ccf_nsw fl2)
    | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg fl2) && negb (ccf_nuw fl2) && negb (ccf_nsw fl2)
    | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg fl2)
    end = true ->
    cast_flags_weaken fl1 fl2 = true ->
    wf_scalar_dvalue fw vo1 ->
    wf_scalar_dvalue fw vo2 ->
    dvalue_refines vo1 vo2 ->
    refine_eou_dvalue
      (@convert_pure Pa (cert_to_pure_conv k fl1)
         (DTYPE_Base (DTYPE_I fw)) vo1 (DTYPE_Base (DTYPE_I tw)))
      (@convert_pure Pa (cert_to_pure_conv k fl2)
         (DTYPE_Base (DTYPE_I fw)) vo2 (DTYPE_Base (DTYPE_I tw))).
Proof.
  intros Pa k fw tw fl1 fl2 vo1 vo2 Hk1 Hk2 Hfl Hwfo1 Hwfo2 [-> | ->].
  - assert (Hsrc : @convert_pure Pa (cert_to_pure_conv k fl1)
                     (DTYPE_Base (DTYPE_I fw)) (DVALUE_Base DVALUE_Poison)
                     (DTYPE_Base (DTYPE_I tw)) = raise_ret (DVALUE_Base DVALUE_Poison))
      by (destruct k; reflexivity).
    rewrite Hsrc.
    destruct (eval_cast_wf_scalar k fw tw fl2 vo2 Hk2 Hwfo2) as [vout2 [-> _]].
    cbn; apply dvalue_refines_poison_l.
  - destruct Hwfo1 as [-> | [io ->]]; [destruct k; cbn; apply dvalue_refines_refl |].
    unfold cast_flags_weaken in Hfl; rewrite !andb_true_iff in Hfl.
    destruct Hfl as ([Hnneg Hnuw] & Hnsw).
    unfold dvp; destruct k; cbn - [andb orb negb Pos.ltb Pos.eqb] in Hk1 |- *; rewrite !andb_true_iff in Hk1.
    + destruct Hk1 as ([Hlt _] & _); rewrite Pos.eqb_refl, Hlt; cbn - [andb orb negb].
      destruct (ccf_nneg fl1), (ccf_nneg fl2); cbn in Hnneg; try discriminate;
        split_bool_ifs;
        cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
    + destruct Hk1 as (([Hlt _] & _) & _); rewrite Pos.eqb_refl, Hlt; cbn.
      apply dvalue_refines_refl.
    + destruct Hk1 as [Hlt _]; rewrite Pos.eqb_refl, Hlt; cbn - [andb orb negb].
      destruct (ccf_nuw fl1), (ccf_nuw fl2), (ccf_nsw fl1), (ccf_nsw fl2);
        cbn in Hnuw, Hnsw; try discriminate;
        split_bool_ifs;
        cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
Qed.

Lemma eval_select_monotone :
  forall {Pa : Params} w (vc1 vc2 vt1 vt2 vf1 vf2 : @dvalue Pa),
    wf_scalar_dvalue 1%positive vc1 ->
    wf_scalar_dvalue 1%positive vc2 ->
    wf_scalar_dvalue w vt1 ->
    wf_scalar_dvalue w vt2 ->
    wf_scalar_dvalue w vf1 ->
    wf_scalar_dvalue w vf2 ->
    dvalue_refines vc1 vc2 ->
    dvalue_refines vt1 vt2 ->
    dvalue_refines vf1 vf2 ->
    refine_eou_dvalue
      (@eval_select Pa vc1 (DTYPE_Base (DTYPE_I w)) vt1 vf1)
      (@eval_select Pa vc2 (DTYPE_Base (DTYPE_I w)) vt2 vf2).
Proof.
  intros Pa w vc1 vc2 vt1 vt2 vf1 vf2 Hwc1 Hwc2 Hwt1 Hwt2 Hwf1 Hwf2 [-> | ->] Hrt Hrf.
  - destruct (eval_select_wf_scalar w vc2 vt2 vf2 Hwc2 Hwt2 Hwf2) as [vout2 [-> _]].
    cbn; apply dvalue_refines_poison_l.
  - destruct Hwc1 as [-> | [ic ->]]; cbn; [apply dvalue_refines_refl |].
    destruct (@Integers.unsigned 1 ic =? 1)%Z; [exact Hrt | exact Hrf].
Qed.

Fixpoint expr_size (e : cert_expr) : nat :=
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ => 1%nat
  | CE_BinOp _ _ _ l r | CE_ICmp _ _ _ l r =>
      S (expr_size l + expr_size r)
  | CE_Cast _ _ _ _ o | CE_Freeze _ o =>
      S (expr_size o)
  | CE_Select _ c t f =>
      S (expr_size c + expr_size t + expr_size f)
  | CE_Let _ body =>
      S (expr_size body)
  end.

Definition match_inner_binop (op_in : cert_binop) (e : cert_expr)
  : option (cert_binop_flags * cert_expr * cert_expr) :=
  match e with
  | CE_BinOp op0 _ fl0 a b =>
      if cert_binop_eqb op0 op_in then Some (fl0, a, b) else None
  | _ => None
  end.

Lemma match_inner_binop_inv : forall op_in e fl0 a b,
  match_inner_binop op_in e = Some (fl0, a, b) ->
  exists w0, e = CE_BinOp op_in w0 fl0 a b.
Proof.
  intros op_in [| | | op0 w0 f0 x y | | | | |] fl0 a b H; cbn in H; try discriminate.
  destruct (cert_binop_eqb op0 op_in) eqn:E; [| discriminate].
  apply cert_binop_eqb_eq in E; inversion H; subst; exists w0; reflexivity.
Qed.

Definition check_cancel_binop_lhs
  (op_in : cert_binop) (comm_in : bool)
  (rec : cert_expr -> cert_expr -> bool) (l r tgt : cert_expr) : bool :=
  match match_inner_binop op_in l with
  | Some (_, a, b) =>
      (cert_expr_eqb b r && ub_free_expr r && rec a tgt) ||
      (comm_in && cert_expr_eqb a r && ub_free_expr r && rec b tgt)
  | None => false
  end.

Definition check_cancel_binop_rhs
  (op_in : cert_binop) (comm_in : bool)
  (rec : cert_expr -> cert_expr -> bool) (l r tgt : cert_expr) : bool :=
  match match_inner_binop op_in r with
  | Some (_, a, b) =>
      (cert_expr_eqb b l && ub_free_expr l && rec a tgt) ||
      (comm_in && cert_expr_eqb a l && ub_free_expr l && rec b tgt)
  | None => false
  end.

Definition check_absorb_binop_rhs
  (op_in : cert_binop) (rec : cert_expr -> cert_expr -> bool)
  (l r tgt : cert_expr) : bool :=
  match match_inner_binop op_in r with
  | Some (_, a, b) =>
      (cert_expr_eqb a l && ub_free_expr b && rec l tgt) ||
      (cert_expr_eqb b l && ub_free_expr a && rec l tgt)
  | None => false
  end.

Definition check_absorb_binop_lhs
  (op_in : cert_binop) (rec : cert_expr -> cert_expr -> bool)
  (l r tgt : cert_expr) : bool :=
  match match_inner_binop op_in l with
  | Some (_, a, b) =>
      (cert_expr_eqb a r && ub_free_expr b && rec r tgt) ||
      (cert_expr_eqb b r && ub_free_expr a && rec r tgt)
  | None => false
  end.

Definition check_src_elim_step
  (rec : cert_expr -> cert_expr -> bool) (ctx : ub_ctx)
  (src tgt : cert_expr) : bool :=
  match src with
  | CE_Poison _ => ub_free_expr tgt
  | CE_BinOp op w _ l r =>
      match op with
      | CB_Add =>
          (is_zero_const_expr w r && rec l tgt) ||
          (is_zero_const_expr w l && rec r tgt) ||
          check_cancel_binop_lhs CB_Sub false rec l r tgt ||
          check_cancel_binop_rhs CB_Sub false rec l r tgt
      | CB_Sub =>
          (is_zero_const_expr w r && rec l tgt) ||
          (cert_expr_eqb l r && is_zero_const_expr w tgt) ||
          check_cancel_binop_lhs CB_Add true rec l r tgt
      | CB_Mul =>
          (is_one_const_expr w r && rec l tgt) ||
          (is_one_const_expr w l && rec r tgt) ||
          (is_zero_const_expr w r && is_zero_const_expr w tgt) ||
          (is_zero_const_expr w l && is_zero_const_expr w tgt)
      | CB_UDiv =>
          (is_one_const_expr w r && rec l tgt) ||
          (is_zero_const_expr w l && is_zero_const_expr w tgt)
      | CB_URem =>
          (is_one_const_expr w r && is_zero_const_expr w tgt) ||
          (is_zero_const_expr w l && is_zero_const_expr w tgt)
      | CB_SDiv | CB_SRem =>
          is_zero_const_expr w l && is_zero_const_expr w tgt
      | CB_And =>
          (is_all_ones_const_expr w r && rec l tgt) ||
          (is_all_ones_const_expr w l && rec r tgt) ||
          (cert_expr_eqb l r && rec l tgt) ||
          (is_zero_const_expr w r && is_zero_const_expr w tgt) ||
          (is_zero_const_expr w l && is_zero_const_expr w tgt) ||
          check_absorb_binop_rhs CB_Or rec l r tgt ||
          check_absorb_binop_lhs CB_Or rec l r tgt
      | CB_Or =>
          (is_zero_const_expr w r && rec l tgt) ||
          (is_zero_const_expr w l && rec r tgt) ||
          (cert_expr_eqb l r && rec l tgt) ||
          (is_all_ones_const_expr w r && is_all_ones_const_expr w tgt) ||
          (is_all_ones_const_expr w l && is_all_ones_const_expr w tgt) ||
          check_absorb_binop_rhs CB_And rec l r tgt ||
          check_absorb_binop_lhs CB_And rec l r tgt
      | CB_Xor =>
          (is_zero_const_expr w r && rec l tgt) ||
          (is_zero_const_expr w l && rec r tgt) ||
          (cert_expr_eqb l r && is_zero_const_expr w tgt) ||
          check_cancel_binop_lhs CB_Xor true rec l r tgt ||
          check_cancel_binop_rhs CB_Xor true rec l r tgt
      | CB_Shl | CB_LShr | CB_AShr =>
          is_zero_const_expr w r && rec l tgt
      end
  | CE_ICmp pr _ _ l r =>
      cert_expr_eqb l r &&
      (if is_refl_true_icmp pr
       then is_one_const_expr 1%positive tgt
       else is_zero_const_expr 1%positive tgt)
  | CE_Select _ _ t f =>
      rec t tgt && rec f tgt
  | CE_Freeze _ o =>
      expr_guaranteed_defined ctx o && rec o tgt
  | _ => false
  end.

Definition check_tgt_intro_step
  (rec : cert_expr -> cert_expr -> bool) (src tgt : cert_expr) : bool :=
  match tgt with
  | CE_Freeze _ o2 => rec src o2
  | _ => false
  end.

Definition neg_cert_icmp (pr : cert_icmp_pred) : cert_icmp_pred :=
  match pr with
  | CIP_Eq  => CIP_Ne
  | CIP_Ne  => CIP_Eq
  | CIP_Ult => CIP_Uge
  | CIP_Ule => CIP_Ugt
  | CIP_Ugt => CIP_Ule
  | CIP_Uge => CIP_Ult
  | CIP_Slt => CIP_Sge
  | CIP_Sle => CIP_Sgt
  | CIP_Sgt => CIP_Sle
  | CIP_Sge => CIP_Slt
  end.

Lemma swap_neg_cert_icmp : forall pr,
  swap_cert_icmp (neg_cert_icmp pr) = neg_cert_icmp (swap_cert_icmp pr).
Proof.
  destruct pr; reflexivity.
Qed.

Lemma eval_int_icmp_neg :
  forall {Pa : Params} ss1 ss2 pr w (il ir : @Integers.bit_int w),
    implb ss2 ss1 = true ->
    (eval_int_icmp ss1 (cert_to_icmp pr) il ir = raise_ret (@DVALUE_Poison Pa)) \/
    (exists b : bool,
       eval_int_icmp ss1 (cert_to_icmp pr) il ir =
         raise_ret (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)) /\
       eval_int_icmp ss2 (cert_to_icmp (neg_cert_icmp pr)) il ir =
         raise_ret (@DVALUE_I Pa 1%positive (if negb b then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa ss1 ss2 pr w il ir Hss.
  set (ms := @msamesign (@Integers.bit_int w) (@VIntVMemInt (@Integers.bit_int w) (@VInt_Bounded w)) il ir).
  destruct ss1, ss2; cbn in Hss; try discriminate Hss; destruct ms eqn:Ems;
    [| left; destruct pr; unfold cert_to_icmp, eval_int_icmp, dvp; cbn [andb orb negb]; fold ms; rewrite ?Ems; reflexivity
     | | left; destruct pr; unfold cert_to_icmp, eval_int_icmp, dvp; cbn [andb orb negb]; fold ms; rewrite ?Ems; reflexivity | |];
    right; destruct pr; unfold cert_to_icmp, neg_cert_icmp, eval_int_icmp;
    cbn [andb orb negb bind ret EOU_monad mcmp mcmpu cmp cmpu mdtyp_of_int VIntVMemInt VInt_Bounded];
    fold ms; rewrite ?Ems;
    repeat match goal with
           | |- context [if dtyp_base_eq_dec ?a ?b then _ else _] =>
               destruct (dtyp_base_eq_dec a b); try discriminate
           end;
    cbn [andb orb negb bind ret EOU_monad]; unfold Integers.cmp, Integers.cmpu;
    repeat match goal with
           | |- context [if @Integers.eq ?sz ?a ?b then _ else _] => destruct (@Integers.eq sz a b)
           | |- context [if @Integers.ltu ?sz ?a ?b then _ else _] => destruct (@Integers.ltu sz a b)
           | |- context [if @Integers.lt ?sz ?a ?b then _ else _] => destruct (@Integers.lt sz a b)
           end;
    cbn [negb]; ((exists true; split; reflexivity) || (exists false; split; reflexivity)).
Qed.

Lemma eval_icmp_neg_select :
  forall {Pa : Params} ss1 ss2 pr w sw
         (vl1 vl2 vr1 vr2 vt1 vt2 vf1 vf2 : @dvalue Pa),
    implb ss2 ss1 = true ->
    wf_scalar_dvalue w vl1 ->
    wf_scalar_dvalue w vl2 ->
    wf_scalar_dvalue w vr1 ->
    wf_scalar_dvalue w vr2 ->
    wf_scalar_dvalue sw vt1 ->
    wf_scalar_dvalue sw vt2 ->
    wf_scalar_dvalue sw vf1 ->
    wf_scalar_dvalue sw vf2 ->
    dvalue_refines vl1 vl2 ->
    dvalue_refines vr1 vr2 ->
    dvalue_refines vt1 vf2 ->
    dvalue_refines vf1 vt2 ->
    refine_eou_dvalue
      (vc1 <- @eval_icmp Pa ss1 (cert_to_icmp pr) vl1 vr1;;
       @eval_select Pa vc1 (DTYPE_Base (DTYPE_I sw)) vt1 vf1)
      (vc2 <- @eval_icmp Pa ss2 (cert_to_icmp (neg_cert_icmp pr)) vl2 vr2;;
       @eval_select Pa vc2 (DTYPE_Base (DTYPE_I sw)) vt2 vf2).
Proof.
  intros Pa ss1 ss2 pr w sw vl1 vl2 vr1 vr2 vt1 vt2 vf1 vf2
         Hss Hwl1 Hwl2 Hwr1 Hwr2 Hwt1 Hwt2 Hwf1 Hwf2 [-> | Hvl_eq] Hrr Hrt Hrf.
  - assert (Hsrc : @eval_icmp Pa ss1 (cert_to_icmp pr) (DVALUE_Base DVALUE_Poison) vr1 =
                   raise_ret (DVALUE_Base DVALUE_Poison))
      by (destruct Hwr1 as [-> | [ir1 ->]]; reflexivity).
    rewrite Hsrc; cbn [bind EOU_monad eou_bind eval_select].
    destruct (eval_icmp_wf_scalar ss2 (neg_cert_icmp pr) w vl2 vr2 Hwl2 Hwr2) as [vc2 [Hvc2 Hwc2]].
    rewrite Hvc2; cbn [bind EOU_monad eou_bind].
    destruct (eval_select_wf_scalar sw vc2 vt2 vf2 Hwc2 Hwt2 Hwf2) as [vs2 [Hvs2 _]].
    rewrite Hvs2; cbn; apply dvalue_refines_poison_l.
  - subst vl2; destruct Hrr as [-> | Hvr_eq].
    + assert (Hsrc : @eval_icmp Pa ss1 (cert_to_icmp pr) vl1 (DVALUE_Base DVALUE_Poison) =
                     raise_ret (DVALUE_Base DVALUE_Poison))
        by (destruct Hwl1 as [-> | [il1 ->]]; reflexivity).
      rewrite Hsrc; cbn [bind EOU_monad eou_bind eval_select].
      destruct (eval_icmp_wf_scalar ss2 (neg_cert_icmp pr) w vl1 vr2 Hwl1 Hwr2) as [vc2 [Hvc2 Hwc2]].
      rewrite Hvc2; cbn [bind EOU_monad eou_bind].
      destruct (eval_select_wf_scalar sw vc2 vt2 vf2 Hwc2 Hwt2 Hwf2) as [vs2 [Hvs2 _]].
      rewrite Hvs2; cbn; apply dvalue_refines_poison_l.
    + subst vr2; destruct Hwl1 as [-> | [il ->]];
        [destruct Hwr1 as [-> | [ir ->]]; unfold eval_icmp; cbn; apply dvalue_refines_refl |].
      destruct Hwr1 as [-> | [ir ->]]; [unfold eval_icmp; cbn; apply dvalue_refines_refl |].
      unfold eval_icmp; rewrite !eval_icmp_base_same_width.
      assert (Hsel_psn :
        refine_eou_dvalue
          (vc1 <- raise_ret (DVALUE_Base DVALUE_Poison);;
           @eval_select Pa vc1 (DTYPE_Base (DTYPE_I sw)) vt1 vf1)
          (vc2 <- DVALUE_Base <$> eval_int_icmp ss2 (cert_to_icmp (neg_cert_icmp pr)) il ir;;
           @eval_select Pa vc2 (DTYPE_Base (DTYPE_I sw)) vt2 vf2)).
      { destruct (eval_icmp_wf_scalar ss2 (neg_cert_icmp pr) w
                    (DVALUE_Base (@DVALUE_I Pa w il)) (DVALUE_Base (@DVALUE_I Pa w ir))
                    (or_intror (ex_intro _ il eq_refl))
                    (or_intror (ex_intro _ ir eq_refl))) as [vc2 [Hvc2 Hwc2]].
        unfold eval_icmp in Hvc2; rewrite eval_icmp_base_same_width in Hvc2; rewrite Hvc2.
        destruct (eval_select_wf_scalar sw vc2 vt2 vf2 Hwc2 Hwt2 Hwf2) as [vs2 [Hvs2 _]].
        cbn [bind EOU_monad eou_bind] in *; rewrite Hvs2; cbn; apply dvalue_refines_poison_l. }
      destruct (eval_int_icmp_neg ss1 ss2 pr w il ir Hss) as [Hpsn | [b [Hb1 Hb2]]].
      * rewrite Hpsn; unfold fmap; cbn [liftM bind ret Functor_Monad EOU_monad]; exact Hsel_psn.
      * rewrite Hb1, Hb2; destruct b;
          unfold fmap; cbn [negb liftM bind ret Functor_Monad EOU_monad eou_bind eval_select];
          rewrite ?(@Integers.unsigned_one 1%positive), ?(@Integers.unsigned_zero 1%positive);
          cbn; [exact Hrt | exact Hrf].
Qed.

Definition check_struct_cong_step
  (rec : cert_expr -> cert_expr -> bool) (ctx : ub_ctx)
  (src tgt : cert_expr) : bool :=
  match src, tgt with
  | CE_BinOp op1 w1 fl1 l1 r1, CE_BinOp op2 w2 fl2 l2 r2 =>
      cert_binop_eqb op1 op2 &&
      Pos.eqb w1 w2 &&
      binop_flags_weaken fl1 fl2 &&
      (if is_div_or_rem_op op1 then
         (cert_expr_eqb l1 l2 && rec r1 r2) ||
         (expr_divisor_nonzero ctx r1 && rec l1 l2 && rec r1 r2)
       else
         (rec l1 l2 && rec r1 r2) ||
         (is_commutative_binop op1 && rec l1 r2 && rec r1 l2))
  | CE_ICmp pr1 ss1 w1 l1 r1, CE_ICmp pr2 ss2 w2 l2 r2 =>
      Pos.eqb w1 w2 &&
      implb ss2 ss1 &&
      ((cert_icmp_pred_eqb pr1 pr2 && rec l1 l2 && rec r1 r2) ||
       (cert_icmp_pred_eqb (swap_cert_icmp pr1) pr2 && rec l1 r2 && rec r1 l2))
  | CE_Cast k1 fw1 tw1 fl1 o1, CE_Cast k2 fw2 tw2 fl2 o2 =>
      cert_cast_kind_eqb k1 k2 &&
      Pos.eqb fw1 fw2 &&
      Pos.eqb tw1 tw2 &&
      cast_flags_weaken fl1 fl2 &&
      rec o1 o2
  | CE_Select w1 c1 t1 f1, CE_Select w2 c2 t2 f2 =>
      Pos.eqb w1 w2 &&
      ((rec c1 c2 && rec t1 t2 && rec f1 f2) ||
       match c1, c2 with
       | CE_ICmp pr1 ss1 wc1 l1 r1, CE_ICmp pr2 ss2 wc2 l2 r2 =>
           Pos.eqb wc1 wc2 && implb ss2 ss1 && rec t1 f2 && rec f1 t2 &&
           ((cert_icmp_pred_eqb pr2 (neg_cert_icmp pr1) && rec l1 l2 && rec r1 r2) ||
            (cert_icmp_pred_eqb pr2 (swap_cert_icmp (neg_cert_icmp pr1)) && rec l1 r2 && rec r1 l2))
       | _, _ => false
       end)
  | _, _ => false
  end.

Fixpoint check_norm_refines_fuel
  (fuel : nat) (ctx : ub_ctx) (src tgt : cert_expr) {struct fuel} : bool :=
  if ctx_has_unreachable ctx then true
  else if cert_expr_eqb src tgt then true
  else
    match fuel with
    | O => false
    | S fuel' =>
        let rec := check_norm_refines_fuel fuel' ctx in
        check_src_elim_step rec ctx src tgt ||
        check_tgt_intro_step rec src tgt ||
        check_struct_cong_step rec ctx src tgt
    end.

Lemma alg_divu_zero_l : forall w (d : @Integers.bit_int w),
  @Integers.divu w (@Integers.zero w) d = @Integers.zero w.
Proof.
  intros w d; unfold Integers.divu; rewrite (@Integers.unsigned_zero w); reflexivity.
Qed.

Lemma alg_modu_zero_l : forall w (d : @Integers.bit_int w),
  @Integers.modu w (@Integers.zero w) d = @Integers.zero w.
Proof.
  intros w d; unfold Integers.modu; rewrite (@Integers.unsigned_zero w); reflexivity.
Qed.

Lemma alg_divs_zero_l : forall w (d : @Integers.bit_int w),
  @Integers.divs w (@Integers.zero w) d = @Integers.zero w.
Proof.
  intros w d; unfold Integers.divs; rewrite (@Integers.signed_zero w); reflexivity.
Qed.

Lemma alg_mods_zero_l : forall w (d : @Integers.bit_int w),
  @Integers.mods w (@Integers.zero w) d = @Integers.zero w.
Proof.
  intros w d; unfold Integers.mods; rewrite (@Integers.signed_zero w); reflexivity.
Qed.

Lemma alg_sub_add_cancel : forall w (a b : @Integers.bit_int w),
  @Integers.add w (@Integers.sub w a b) b = a.
Proof.
  intros w a b.
  rewrite Integers.sub_add_opp, Integers.add_assoc, (Integers.add_commut (Integers.neg b) b),
          Integers.add_neg_zero, Integers.add_zero; reflexivity.
Qed.

Lemma alg_sub_add_cancel_l : forall w (b a : @Integers.bit_int w),
  @Integers.add w b (@Integers.sub w a b) = a.
Proof.
  intros w b a; rewrite Integers.add_commut; exact (alg_sub_add_cancel w a b).
Qed.

Lemma alg_add_sub_cancel : forall w (a b : @Integers.bit_int w),
  @Integers.sub w (@Integers.add w a b) b = a.
Proof.
  intros w a b.
  rewrite Integers.sub_add_opp, Integers.add_assoc, Integers.add_neg_zero, Integers.add_zero;
    reflexivity.
Qed.

Lemma alg_xor_cancel : forall w (a b : @Integers.bit_int w),
  @Integers.xor w (@Integers.xor w a b) b = a.
Proof.
  intros w a b.
  rewrite Integers.xor_assoc, Integers.xor_idem, Integers.xor_zero; reflexivity.
Qed.

Lemma alg_xor_cancel_l : forall w (b a : @Integers.bit_int w),
  @Integers.xor w b (@Integers.xor w a b) = a.
Proof.
  intros w b a; rewrite Integers.xor_commut; exact (alg_xor_cancel w a b).
Qed.

Lemma alg_and_or_absorb : forall w (a b : @Integers.bit_int w),
  @Integers.and w a (@Integers.or w a b) = a.
Proof.
  intros w a b; apply Integers.same_bits_eq; intros k Hk.
  rewrite Integers.bits_and, Integers.bits_or by exact Hk.
  destruct (Integers.testbit a k), (Integers.testbit b k); reflexivity.
Qed.

Lemma alg_or_and_absorb : forall w (a b : @Integers.bit_int w),
  @Integers.or w a (@Integers.and w a b) = a.
Proof.
  intros w a b; apply Integers.same_bits_eq; intros k Hk.
  rewrite Integers.bits_or, Integers.bits_and by exact Hk.
  destruct (Integers.testbit a k), (Integers.testbit b k); reflexivity.
Qed.

Lemma eval_iop_no_flags_poison_any :
  forall {Pa : Params} op w (v1 v2 : @dvalue Pa),
    is_div_or_rem_op op = false ->
    wf_scalar_dvalue w v1 ->
    wf_scalar_dvalue w v2 ->
    (v1 = DVALUE_Base DVALUE_Poison \/ v2 = DVALUE_Base DVALUE_Poison) ->
    @eval_iop Pa (cert_to_ibinop op no_binop_flags) v1 v2 =
    raise_ret (DVALUE_Base DVALUE_Poison).
Proof.
  intros Pa op w v1 v2 Hndiv [-> | [i1 ->]] [-> | [i2 ->]] Hp;
    destruct op; cbn in Hndiv; try discriminate;
    try reflexivity;
    destruct Hp as [Hp | Hp]; discriminate Hp.
Qed.

Lemma eval_iop_nested_weaken_l :
  forall {Pa : Params} op_in op_out fl_in fl_out w (va vb vc vtgt : @dvalue Pa)
         (iop_in iop_out : @Integers.bit_int w -> @Integers.bit_int w -> @Integers.bit_int w),
    is_div_or_rem_op op_in = false ->
    is_div_or_rem_op op_out = false ->
    wf_scalar_dvalue w va ->
    wf_scalar_dvalue w vb ->
    wf_scalar_dvalue w vc ->
    (forall x y, eval_int_op (cert_to_ibinop op_in no_binop_flags) x y =
                 raise_ret (@DVALUE_I Pa w (iop_in x y))) ->
    (forall x y, eval_int_op (cert_to_ibinop op_out no_binop_flags) x y =
                 raise_ret (@DVALUE_I Pa w (iop_out x y))) ->
    (forall ia ib ic,
       va = DVALUE_Base (@DVALUE_I Pa w ia) ->
       vb = DVALUE_Base (@DVALUE_I Pa w ib) ->
       vc = DVALUE_Base (@DVALUE_I Pa w ic) ->
       dvalue_refines (DVALUE_Base (@DVALUE_I Pa w (iop_out (iop_in ia ib) ic))) vtgt) ->
    refine_eou_dvalue
      (eou_bind (@eval_iop Pa (cert_to_ibinop op_in fl_in) va vb)
                (fun vin => @eval_iop Pa (cert_to_ibinop op_out fl_out) vin vc))
      (raise_ret vtgt).
Proof.
  intros Pa op_in op_out fl_in fl_out w va vb vc vtgt iop_in iop_out
         Hnin Hnout Hwfa Hwfb Hwfc Hiop_in Hiop_out Hres.
  destruct (eval_iop_non_div_rem_no_ub op_in fl_in w va vb Hnin Hwfa Hwfb) as [vin [Evin Hwfvin]].
  destruct (eval_iop_non_div_rem_no_ub op_in no_binop_flags w va vb Hnin Hwfa Hwfb) as [vin0 [Evin0 Hwfvin0]].
  pose proof (eval_iop_non_div_rem_monotone op_in fl_in no_binop_flags w va va vb vb
                Hnin (binop_flags_weaken_no_flags fl_in) Hwfa Hwfa Hwfb Hwfb
                (dvalue_refines_refl _) (dvalue_refines_refl _)) as Hrin.
  rewrite Evin, Evin0 in Hrin; cbn in Hrin; rewrite Evin; cbn [eou_bind].
  apply (refine_eou_dvalue_trans _ (@eval_iop Pa (cert_to_ibinop op_out no_binop_flags) vin0 vc) _).
  - exact (eval_iop_non_div_rem_monotone op_out fl_out no_binop_flags w vin vin0 vc vc
             Hnout (binop_flags_weaken_no_flags fl_out) Hwfvin Hwfvin0 Hwfc Hwfc
             Hrin (dvalue_refines_refl _)).
  - destruct Hwfa as [Hpa | [ia Hia]];
      [rewrite (eval_iop_no_flags_poison_any op_in w va vb Hnin
                  (or_introl Hpa) Hwfb (or_introl Hpa)) in Evin0;
       inversion Evin0; subst vin0;
       rewrite (eval_iop_no_flags_poison_any op_out w _ vc Hnout
                  (or_introl eq_refl) Hwfc (or_introl eq_refl));
       cbn; apply dvalue_refines_poison_l |].
    destruct Hwfb as [Hpb | [ib Hib]];
      [rewrite (eval_iop_no_flags_poison_any op_in w va vb Hnin
                  (or_intror (ex_intro _ ia Hia)) (or_introl Hpb) (or_intror Hpb)) in Evin0;
       inversion Evin0; subst vin0;
       rewrite (eval_iop_no_flags_poison_any op_out w _ vc Hnout
                  (or_introl eq_refl) Hwfc (or_introl eq_refl));
       cbn; apply dvalue_refines_poison_l |].
    destruct Hwfc as [Hpc | [ic Hic]];
      [rewrite (eval_iop_no_flags_poison_any op_out w vin0 vc Hnout
                  Hwfvin0 (or_introl Hpc) (or_intror Hpc));
       cbn; apply dvalue_refines_poison_l |].
    subst va vb vc.
    unfold eval_iop in Evin0 |- *;
      rewrite eval_iop_integer_base_same_width, Hiop_in in Evin0;
      inversion Evin0; subst vin0.
    rewrite eval_iop_integer_base_same_width, Hiop_out; cbn.
    exact (Hres ia ib ic eq_refl eq_refl eq_refl).
Qed.

Lemma eval_iop_nested_weaken_r :
  forall {Pa : Params} op_in op_out fl_in fl_out w (va vb vc vtgt : @dvalue Pa)
         (iop_in iop_out : @Integers.bit_int w -> @Integers.bit_int w -> @Integers.bit_int w),
    is_div_or_rem_op op_in = false ->
    is_div_or_rem_op op_out = false ->
    wf_scalar_dvalue w va ->
    wf_scalar_dvalue w vb ->
    wf_scalar_dvalue w vc ->
    (forall x y, eval_int_op (cert_to_ibinop op_in no_binop_flags) x y =
                 raise_ret (@DVALUE_I Pa w (iop_in x y))) ->
    (forall x y, eval_int_op (cert_to_ibinop op_out no_binop_flags) x y =
                 raise_ret (@DVALUE_I Pa w (iop_out x y))) ->
    (forall ia ib ic,
       va = DVALUE_Base (@DVALUE_I Pa w ia) ->
       vb = DVALUE_Base (@DVALUE_I Pa w ib) ->
       vc = DVALUE_Base (@DVALUE_I Pa w ic) ->
       dvalue_refines (DVALUE_Base (@DVALUE_I Pa w (iop_out ia (iop_in ib ic)))) vtgt) ->
    refine_eou_dvalue
      (eou_bind (@eval_iop Pa (cert_to_ibinop op_in fl_in) vb vc)
                (fun vin => @eval_iop Pa (cert_to_ibinop op_out fl_out) va vin))
      (raise_ret vtgt).
Proof.
  intros Pa op_in op_out fl_in fl_out w va vb vc vtgt iop_in iop_out
         Hnin Hnout Hwfa Hwfb Hwfc Hiop_in Hiop_out Hres.
  destruct (eval_iop_non_div_rem_no_ub op_in fl_in w vb vc Hnin Hwfb Hwfc) as [vin [Evin Hwfvin]].
  destruct (eval_iop_non_div_rem_no_ub op_in no_binop_flags w vb vc Hnin Hwfb Hwfc) as [vin0 [Evin0 Hwfvin0]].
  pose proof (eval_iop_non_div_rem_monotone op_in fl_in no_binop_flags w vb vb vc vc
                Hnin (binop_flags_weaken_no_flags fl_in) Hwfb Hwfb Hwfc Hwfc
                (dvalue_refines_refl _) (dvalue_refines_refl _)) as Hrin.
  rewrite Evin, Evin0 in Hrin; cbn in Hrin; rewrite Evin; cbn [eou_bind].
  apply (refine_eou_dvalue_trans _ (@eval_iop Pa (cert_to_ibinop op_out no_binop_flags) va vin0) _).
  - exact (eval_iop_non_div_rem_monotone op_out fl_out no_binop_flags w va va vin vin0
             Hnout (binop_flags_weaken_no_flags fl_out) Hwfa Hwfa Hwfvin Hwfvin0
             (dvalue_refines_refl _) Hrin).
  - destruct Hwfa as [Hpa | [ia Hia]];
      [rewrite (eval_iop_no_flags_poison_any op_out w va vin0 Hnout
                  (or_introl Hpa) Hwfvin0 (or_introl Hpa));
       cbn; apply dvalue_refines_poison_l |].
    destruct Hwfb as [Hpb | [ib Hib]];
      [rewrite (eval_iop_no_flags_poison_any op_in w vb vc Hnin
                  (or_introl Hpb) Hwfc (or_introl Hpb)) in Evin0;
       inversion Evin0; subst vin0;
       rewrite (eval_iop_no_flags_poison_any op_out w va _ Hnout
                  (or_intror (ex_intro _ ia Hia)) (or_introl eq_refl) (or_intror eq_refl));
       cbn; apply dvalue_refines_poison_l |].
    destruct Hwfc as [Hpc | [ic Hic]];
      [rewrite (eval_iop_no_flags_poison_any op_in w vb vc Hnin
                  (or_intror (ex_intro _ ib Hib)) (or_introl Hpc) (or_intror Hpc)) in Evin0;
       inversion Evin0; subst vin0;
       rewrite (eval_iop_no_flags_poison_any op_out w va _ Hnout
                  (or_intror (ex_intro _ ia Hia)) (or_introl eq_refl) (or_intror eq_refl));
       cbn; apply dvalue_refines_poison_l |].
    subst va vb vc.
    unfold eval_iop in Evin0 |- *;
      rewrite eval_iop_integer_base_same_width, Hiop_in in Evin0;
      inversion Evin0; subst vin0.
    rewrite eval_iop_integer_base_same_width, Hiop_out; cbn.
    exact (Hres ia ib ic eq_refl eq_refl eq_refl).
Qed.

Lemma dvalue_i_inj : forall {Pa : Params} w (x y : @Integers.bit_int w),
  (@DVALUE_Base Pa (@DVALUE_I Pa w x)) = (@DVALUE_Base Pa (@DVALUE_I Pa w y)) ->
  x = y.
Proof.
  intros Pa w x y H.
  apply (f_equal (fun dv : @dvalue Pa =>
           match dv with
           | DVALUE_Base (@DVALUE_I _ sz i) => @Integers.unsigned sz i
           | _ => 0%Z
           end)) in H.
  rewrite <- (@Integers.repr_unsigned w x), <- (@Integers.repr_unsigned w y), H; reflexivity.
Qed.

Lemma check_src_elim_step_sound :
  forall {Pa : Params} (rec : cert_expr -> cert_expr -> bool)
         (ctx : ub_ctx) (src tgt : cert_expr)
         (penv : param_env Pa) (foracle : freeze_oracle),
    (forall s t,
       rec s t = true ->
       cert_expr_bit_width s = cert_expr_bit_width t ->
       wt_cert_expr [] s = true ->
       wt_cert_expr [] t = true ->
       wf_param_env_for (collect_free_vars [] s) penv ->
       wf_param_env_for (collect_free_vars [] t) penv ->
       refine_eou_dvalue
         (eval_closed_cert_expr penv foracle s)
         (eval_closed_cert_expr penv foracle t)) ->
    check_src_elim_step rec ctx src tgt = true ->
    cert_expr_bit_width src = cert_expr_bit_width tgt ->
    wt_cert_expr [] src = true ->
    wt_cert_expr [] tgt = true ->
    wf_param_env_for (collect_free_vars [] src) penv ->
    wf_param_env_for (collect_free_vars [] tgt) penv ->
    ub_ctx_holds penv foracle ctx ->
    refine_eou_dvalue
      (eval_closed_cert_expr penv foracle src)
      (eval_closed_cert_expr penv foracle tgt).
Proof.
  intros Pa rec ctx src tgt penv foracle IH Hstep Hbw Hwts Hwtt Hps Hpt Hctx.
  destruct src as
    [ w val | w | nm w
    | op w fl l r
    | pr ss w l r
    | k fw tw fl o
    | w c t f
    | w o
    | bs body ];
    cbn [check_src_elim_step] in Hstep; try discriminate Hstep.
  - (* CE_Poison *)
    destruct (ub_free_expr_eval_ret tgt [] penv [] foracle Hstep Hwtt wf_let_val_env_nil Hpt)
      as [vtgt [Hvtgt _]].
    unfold eval_closed_cert_expr; rewrite Hvtgt; cbn; apply dvalue_refines_poison_l.
  - (* CE_BinOp *)
    cbn [wt_cert_expr collect_free_vars cert_expr_bit_width] in Hwts, Hps, Hbw.
    rewrite !andb_true_iff in Hwts.
    destruct Hwts as ((((_ & Hwtl) & Hwtr) & Hwl) & Hwr).
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    assert (Hpl : wf_param_env_for (collect_free_vars [] l) penv)
      by (intros x wx Hx; apply Hps, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars [] r) penv)
      by (intros x wx Hx; apply Hps, in_app_iff; right; exact Hx).
    assert (Htot_l :
      (exists msg, eval_closed_cert_expr penv foracle l = raise_ub msg) \/
      (exists vl, eval_closed_cert_expr penv foracle l = raise_ret vl /\ wf_scalar_dvalue w vl)).
    { destruct (eval_cert_expr_totality l [] penv [] foracle Hwtl wf_let_val_env_nil Hpl)
        as [[msg H] | [v [H Hwf]]];
        [left; exists msg; exact H | right; rewrite Hwl in Hwf; exists v; exact (conj H Hwf)]. }
    assert (Htot_r :
      (exists msg, eval_closed_cert_expr penv foracle r = raise_ub msg) \/
      (exists vr, eval_closed_cert_expr penv foracle r = raise_ret vr /\ wf_scalar_dvalue w vr)).
    { destruct (eval_cert_expr_totality r [] penv [] foracle Hwtr wf_let_val_env_nil Hpr)
        as [[msg H] | [v [H Hwf]]];
        [left; exists msg; exact H | right; rewrite Hwr in Hwf; exists v; exact (conj H Hwf)]. }
    assert (Hid_r : forall cval,
      is_div_or_rem_op op = false ->
      r = CE_BvConst w cval ->
      rec l tgt = true ->
      (forall il : @Integers.bit_int w,
         @eval_iop Pa (cert_to_ibinop op no_binop_flags)
           (DVALUE_Base (@DVALUE_I Pa w il))
           (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N cval)))) =
         raise_ret (DVALUE_Base (@DVALUE_I Pa w il))) ->
      refine_eou_dvalue
        (eval_closed_cert_expr penv foracle (CE_BinOp op w fl l r))
        (eval_closed_cert_expr penv foracle tgt)).
    { intros cval Hndiv -> Hrec Hiop.
      pose proof (IH l tgt Hrec (eq_trans Hwl Hbw) Hwtl Hwtt Hpl Hpt) as Hlt.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
      destruct Htot_l as [[msgl Evl] | [vl [Evl Hwfvl]]];
        [rewrite Evl; cbn; exact I | rewrite Evl; cbn [eou_bind] in *].
      apply (refine_eou_dvalue_trans _
               (@eval_iop Pa (cert_to_ibinop op no_binop_flags) vl
                  (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N cval))))) _).
      - exact (eval_iop_non_div_rem_monotone op fl no_binop_flags w vl vl _ _
                 Hndiv (binop_flags_weaken_no_flags fl) Hwfvl Hwfvl
                 (or_intror (ex_intro _ _ eq_refl)) (or_intror (ex_intro _ _ eq_refl))
                 (dvalue_refines_refl _) (dvalue_refines_refl _)).
      - destruct Hwfvl as [-> | [il ->]].
        + assert (Hp : @eval_iop Pa (cert_to_ibinop op no_binop_flags)
                         (DVALUE_Base DVALUE_Poison)
                         (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N cval)))) =
                       raise_ret (DVALUE_Base DVALUE_Poison))
            by (destruct op; cbn in Hndiv; try discriminate; reflexivity).
          rewrite Hp, <- Evl; exact Hlt.
        + rewrite Hiop, <- Evl; exact Hlt. }
    assert (Hid_l : forall cval,
      is_div_or_rem_op op = false ->
      l = CE_BvConst w cval ->
      rec r tgt = true ->
      (forall ir : @Integers.bit_int w,
         @eval_iop Pa (cert_to_ibinop op no_binop_flags)
           (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N cval))))
           (DVALUE_Base (@DVALUE_I Pa w ir)) =
         raise_ret (DVALUE_Base (@DVALUE_I Pa w ir))) ->
      refine_eou_dvalue
        (eval_closed_cert_expr penv foracle (CE_BinOp op w fl l r))
        (eval_closed_cert_expr penv foracle tgt)).
    { intros cval Hndiv -> Hrec Hiop.
      pose proof (IH r tgt Hrec (eq_trans Hwr Hbw) Hwtr Hwtt Hpr Hpt) as Hrt.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
      destruct Htot_r as [[msgr Evr] | [vr [Evr Hwfvr]]];
        [rewrite Evr; cbn; exact I | rewrite Evr; cbn [eou_bind] in *].
      apply (refine_eou_dvalue_trans _
               (@eval_iop Pa (cert_to_ibinop op no_binop_flags)
                  (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N cval)))) vr) _).
      - exact (eval_iop_non_div_rem_monotone op fl no_binop_flags w _ _ vr vr
                 Hndiv (binop_flags_weaken_no_flags fl)
                 (or_intror (ex_intro _ _ eq_refl)) (or_intror (ex_intro _ _ eq_refl))
                 Hwfvr Hwfvr (dvalue_refines_refl _) (dvalue_refines_refl _)).
      - destruct Hwfvr as [-> | [ir ->]].
        + assert (Hp : @eval_iop Pa (cert_to_ibinop op no_binop_flags)
                         (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N cval))))
                         (DVALUE_Base DVALUE_Poison) =
                       raise_ret (DVALUE_Base DVALUE_Poison))
            by (destruct op; cbn in Hndiv; try discriminate; reflexivity).
          rewrite Hp, <- Evr; exact Hrt.
        + rewrite Hiop, <- Evr; exact Hrt. }
    assert (Hcan_lhs : forall op_in comm_in
              (iop_in iop_out : @Integers.bit_int w -> @Integers.bit_int w -> @Integers.bit_int w),
      is_div_or_rem_op op = false ->
      is_div_or_rem_op op_in = false ->
      check_cancel_binop_lhs op_in comm_in rec l r tgt = true ->
      (forall x y, eval_int_op (cert_to_ibinop op_in no_binop_flags) x y =
                   raise_ret (@DVALUE_I Pa w (iop_in x y))) ->
      (forall x y, eval_int_op (cert_to_ibinop op no_binop_flags) x y =
                   raise_ret (@DVALUE_I Pa w (iop_out x y))) ->
      (forall x y, iop_out (iop_in x y) y = x) ->
      (comm_in = true -> forall x y, iop_in x y = iop_in y x) ->
      refine_eou_dvalue
        (eval_closed_cert_expr penv foracle (CE_BinOp op w fl l r))
        (eval_closed_cert_expr penv foracle tgt)).
    { intros op_in comm_in iop_in iop_out Hndiv_out Hndiv_in Hchk0 Hiop_in Hiop_out Hcan Hcomm_in.
      unfold check_cancel_binop_lhs in Hchk0.
      destruct (match_inner_binop op_in l) as [[[fl_in a] b] |] eqn:Em; [| discriminate Hchk0].
      destruct (match_inner_binop_inv op_in l fl_in a b Em) as [wl Heql]; subst l.
      cbn [cert_expr_bit_width] in Hwl; subst wl.
      cbn [wt_cert_expr collect_free_vars] in Hwtl, Hpl; rewrite !andb_true_iff in Hwtl.
      destruct Hwtl as ((((_ & Hta) & Htb) & Hwa) & Hwb).
      apply Pos.eqb_eq in Hwa; apply Pos.eqb_eq in Hwb.
      assert (Hpa : wf_param_env_for (collect_free_vars [] a) penv)
        by (intros x wx Hx; apply Hpl, in_app_iff; left; exact Hx).
      assert (Hpb : wf_param_env_for (collect_free_vars [] b) penv)
        by (intros x wx Hx; apply Hpl, in_app_iff; right; exact Hx).
      apply orb_true_iff in Hchk0 as [Hbr | Har].
      - rewrite !andb_true_iff in Hbr; destruct Hbr as ([Heqbr Hubr] & Hrec).
        apply cert_expr_eqb_eq in Heqbr; subst b.
        pose proof (IH a tgt Hrec (eq_trans Hwa Hbw) Hta Hwtt Hpa Hpt) as Hat.
        destruct (ub_free_expr_eval_ret r [] penv [] foracle Hubr Hwtr wf_let_val_env_nil Hpr)
          as [vr [Evr Hwfvr]]; rewrite Hwr in Hwfvr.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpa)
          as [[msga ->] | [va [Eva Hwfva]]]; [cbn; exact I | rewrite Eva in Hat |- *; cbn [eou_bind]].
        rewrite Hwa in Hwfva; rewrite Evr; cbn [eou_bind].
        destruct (eval_cert_expr penv [] foracle tgt) as [| | | vtgt];
          cbn in Hat; try contradiction.
        exact (eval_iop_nested_weaken_l op_in op fl_in fl w va vr vr vtgt iop_in iop_out
                 Hndiv_in Hndiv_out Hwfva Hwfvr Hwfvr Hiop_in Hiop_out
                 (fun ia ib ic Hia Hib Hic =>
                    ltac:(rewrite Hib in Hic; apply dvalue_i_inj in Hic; subst ic;
                          rewrite Hcan, <- Hia; exact Hat))).
      - rewrite !andb_true_iff in Har; destruct Har as (((Hc_in & Heqar) & Hubr) & Hrec).
        apply cert_expr_eqb_eq in Heqar; subst a.
        pose proof (IH b tgt Hrec (eq_trans Hwb Hbw) Htb Hwtt Hpb Hpt) as Hbt.
        destruct (ub_free_expr_eval_ret r [] penv [] foracle Hubr Hwtr wf_let_val_env_nil Hpr)
          as [vr [Evr Hwfvr]]; rewrite Hwr in Hwfvr.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Evr; cbn [eou_bind].
        destruct (eval_cert_expr_totality b [] penv [] foracle Htb wf_let_val_env_nil Hpb)
          as [[msgb ->] | [vb [Evb Hwfvb]]]; [cbn; exact I | rewrite Evb in Hbt |- *; cbn [eou_bind]].
        rewrite Hwb in Hwfvb; rewrite ?Evr; cbn [eou_bind].
        destruct (eval_cert_expr penv [] foracle tgt) as [| | | vtgt];
          cbn in Hbt; try contradiction.
        exact (eval_iop_nested_weaken_l op_in op fl_in fl w vr vb vr vtgt iop_in iop_out
                 Hndiv_in Hndiv_out Hwfvr Hwfvb Hwfvr Hiop_in Hiop_out
                 (fun ia ib ic Hia Hib Hic =>
                    ltac:(rewrite Hia in Hic; apply dvalue_i_inj in Hic; subst ic;
                          rewrite (Hcomm_in Hc_in ia ib), Hcan, <- Hib; exact Hbt))). }
    assert (Hcan_rhs : forall op_in comm_in
              (iop_in iop_out : @Integers.bit_int w -> @Integers.bit_int w -> @Integers.bit_int w),
      is_div_or_rem_op op = false ->
      is_div_or_rem_op op_in = false ->
      check_cancel_binop_rhs op_in comm_in rec l r tgt = true ->
      (forall x y, eval_int_op (cert_to_ibinop op_in no_binop_flags) x y =
                   raise_ret (@DVALUE_I Pa w (iop_in x y))) ->
      (forall x y, eval_int_op (cert_to_ibinop op no_binop_flags) x y =
                   raise_ret (@DVALUE_I Pa w (iop_out x y))) ->
      (forall x y, iop_out y (iop_in x y) = x) ->
      (comm_in = true -> forall x y, iop_in x y = iop_in y x) ->
      refine_eou_dvalue
        (eval_closed_cert_expr penv foracle (CE_BinOp op w fl l r))
        (eval_closed_cert_expr penv foracle tgt)).
    { intros op_in comm_in iop_in iop_out Hndiv_out Hndiv_in Hchk0 Hiop_in Hiop_out Hcan Hcomm_in.
      unfold check_cancel_binop_rhs in Hchk0.
      destruct (match_inner_binop op_in r) as [[[fl_in a] b] |] eqn:Em; [| discriminate Hchk0].
      destruct (match_inner_binop_inv op_in r fl_in a b Em) as [wr Heqr]; subst r.
      cbn [cert_expr_bit_width] in Hwr; subst wr.
      cbn [wt_cert_expr collect_free_vars] in Hwtr, Hpr; rewrite !andb_true_iff in Hwtr.
      destruct Hwtr as ((((_ & Hta) & Htb) & Hwa) & Hwb).
      apply Pos.eqb_eq in Hwa; apply Pos.eqb_eq in Hwb.
      assert (Hpa : wf_param_env_for (collect_free_vars [] a) penv)
        by (intros x wx Hx; apply Hpr, in_app_iff; left; exact Hx).
      assert (Hpb : wf_param_env_for (collect_free_vars [] b) penv)
        by (intros x wx Hx; apply Hpr, in_app_iff; right; exact Hx).
      apply orb_true_iff in Hchk0 as [Hbl | Hal].
      - rewrite !andb_true_iff in Hbl; destruct Hbl as ([Heqbl Hubl] & Hrec).
        apply cert_expr_eqb_eq in Heqbl; subst b.
        pose proof (IH a tgt Hrec (eq_trans Hwa Hbw) Hta Hwtt Hpa Hpt) as Hat.
        destruct (ub_free_expr_eval_ret l [] penv [] foracle Hubl Hwtl wf_let_val_env_nil Hpl)
          as [vl [Evl Hwfvl]]; rewrite Hwl in Hwfvl.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Evl; cbn [eou_bind].
        destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpa)
          as [[msga ->] | [va [Eva Hwfva]]]; [cbn; exact I | rewrite Eva in Hat |- *; cbn [eou_bind]].
        rewrite Hwa in Hwfva; rewrite ?Evl; cbn [eou_bind].
        destruct (eval_cert_expr penv [] foracle tgt) as [| | | vtgt];
          cbn in Hat; try contradiction.
        exact (eval_iop_nested_weaken_r op_in op fl_in fl w vl va vl vtgt iop_in iop_out
                 Hndiv_in Hndiv_out Hwfvl Hwfva Hwfvl Hiop_in Hiop_out
                 (fun ia ib ic Hia Hib Hic =>
                    ltac:(rewrite Hia in Hic; apply dvalue_i_inj in Hic; subst ic;
                          rewrite Hcan, <- Hib; exact Hat))).
      - rewrite !andb_true_iff in Hal; destruct Hal as (((Hc_in & Heqal) & Hubl) & Hrec).
        apply cert_expr_eqb_eq in Heqal; subst a.
        pose proof (IH b tgt Hrec (eq_trans Hwb Hbw) Htb Hwtt Hpb Hpt) as Hbt.
        destruct (ub_free_expr_eval_ret l [] penv [] foracle Hubl Hwtl wf_let_val_env_nil Hpl)
          as [vl [Evl Hwfvl]]; rewrite Hwl in Hwfvl.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite !Evl; cbn [eou_bind].
        destruct (eval_cert_expr_totality b [] penv [] foracle Htb wf_let_val_env_nil Hpb)
          as [[msgb ->] | [vb [Evb Hwfvb]]]; [cbn; exact I | rewrite Evb in Hbt |- *; cbn [eou_bind]].
        rewrite Hwb in Hwfvb.
        destruct (eval_cert_expr penv [] foracle tgt) as [| | | vtgt];
          cbn in Hbt; try contradiction.
        exact (eval_iop_nested_weaken_r op_in op fl_in fl w vl vl vb vtgt iop_in iop_out
                 Hndiv_in Hndiv_out Hwfvl Hwfvl Hwfvb Hiop_in Hiop_out
                 (fun ia ib ic Hia Hib Hic =>
                    ltac:(rewrite Hia in Hib; apply dvalue_i_inj in Hib; subst ib;
                          rewrite (Hcomm_in Hc_in ia ic), Hcan, <- Hic; exact Hbt))). }
    assert (Habs_rhs : forall op_in
              (iop_in iop_out : @Integers.bit_int w -> @Integers.bit_int w -> @Integers.bit_int w),
      is_div_or_rem_op op = false ->
      is_div_or_rem_op op_in = false ->
      check_absorb_binop_rhs op_in rec l r tgt = true ->
      (forall x y, eval_int_op (cert_to_ibinop op_in no_binop_flags) x y =
                   raise_ret (@DVALUE_I Pa w (iop_in x y))) ->
      (forall x y, eval_int_op (cert_to_ibinop op no_binop_flags) x y =
                   raise_ret (@DVALUE_I Pa w (iop_out x y))) ->
      (forall x y, iop_out x (iop_in x y) = x) ->
      (forall x y, iop_in x y = iop_in y x) ->
      refine_eou_dvalue
        (eval_closed_cert_expr penv foracle (CE_BinOp op w fl l r))
        (eval_closed_cert_expr penv foracle tgt)).
    { intros op_in iop_in iop_out Hndiv_out Hndiv_in Hchk0 Hiop_in Hiop_out Habs Hcomm_in.
      unfold check_absorb_binop_rhs in Hchk0.
      destruct (match_inner_binop op_in r) as [[[fl_in a] b] |] eqn:Em; [| discriminate Hchk0].
      destruct (match_inner_binop_inv op_in r fl_in a b Em) as [wr Heqr]; subst r.
      cbn [cert_expr_bit_width] in Hwr; subst wr.
      cbn [wt_cert_expr collect_free_vars] in Hwtr, Hpr; rewrite !andb_true_iff in Hwtr.
      destruct Hwtr as ((((_ & Hta) & Htb) & Hwa) & Hwb).
      apply Pos.eqb_eq in Hwa; apply Pos.eqb_eq in Hwb.
      assert (Hpa : wf_param_env_for (collect_free_vars [] a) penv)
        by (intros x wx Hx; apply Hpr, in_app_iff; left; exact Hx).
      assert (Hpb : wf_param_env_for (collect_free_vars [] b) penv)
        by (intros x wx Hx; apply Hpr, in_app_iff; right; exact Hx).
      apply orb_true_iff in Hchk0 as [Hal | Hbl];
        [rewrite !andb_true_iff in Hal | rewrite !andb_true_iff in Hbl].
      - destruct Hal as ([Heqal Hubb] & Hrec); apply cert_expr_eqb_eq in Heqal; subst a.
        pose proof (IH l tgt Hrec (eq_trans Hwl Hbw) Hwtl Hwtt Hpl Hpt) as Hlt.
        destruct (ub_free_expr_eval_ret b [] penv [] foracle Hubb Htb wf_let_val_env_nil Hpb)
          as [vb [Evb Hwfvb]]; rewrite Hwb in Hwfvb.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [Evl Hwfvl]]]; [cbn; exact I | rewrite ?Evl in Hlt; rewrite !Evl; cbn [eou_bind]].
        rewrite Evb; cbn [eou_bind].
        destruct (eval_cert_expr penv [] foracle tgt) as [| | | vtgt];
          cbn in Hlt; try contradiction.
        exact (eval_iop_nested_weaken_r op_in op fl_in fl w vl vl vb vtgt iop_in iop_out
                 Hndiv_in Hndiv_out Hwfvl Hwfvl Hwfvb Hiop_in Hiop_out
                 (fun ia ib ic Hia Hib _ =>
                    ltac:(rewrite Hia in Hib; apply dvalue_i_inj in Hib; subst ib;
                          rewrite Habs, <- Hia; exact Hlt))).
      - destruct Hbl as ([Heqbl Huba] & Hrec); apply cert_expr_eqb_eq in Heqbl; subst b.
        pose proof (IH l tgt Hrec (eq_trans Hwl Hbw) Hwtl Hwtt Hpl Hpt) as Hlt.
        destruct (ub_free_expr_eval_ret a [] penv [] foracle Huba Hta wf_let_val_env_nil Hpa)
          as [va [Eva Hwfva]]; rewrite Hwa in Hwfva.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [Evl Hwfvl]]]; [cbn; exact I | rewrite Evl in Hlt |- *; cbn [eou_bind]].
        rewrite Eva, ?Evl; cbn [eou_bind].
        destruct (eval_cert_expr penv [] foracle tgt) as [| | | vtgt];
          cbn in Hlt; try contradiction.
        exact (eval_iop_nested_weaken_r op_in op fl_in fl w vl va vl vtgt iop_in iop_out
                 Hndiv_in Hndiv_out Hwfvl Hwfva Hwfvl Hiop_in Hiop_out
                 (fun ia ib ic Hia _ Hic =>
                    ltac:(rewrite Hia in Hic; apply dvalue_i_inj in Hic; subst ic;
                          rewrite (Hcomm_in ib ia), Habs, <- Hia; exact Hlt))). }
    assert (Habs_lhs : forall op_in
              (iop_in iop_out : @Integers.bit_int w -> @Integers.bit_int w -> @Integers.bit_int w),
      is_div_or_rem_op op = false ->
      is_div_or_rem_op op_in = false ->
      check_absorb_binop_lhs op_in rec l r tgt = true ->
      (forall x y, eval_int_op (cert_to_ibinop op_in no_binop_flags) x y =
                   raise_ret (@DVALUE_I Pa w (iop_in x y))) ->
      (forall x y, eval_int_op (cert_to_ibinop op no_binop_flags) x y =
                   raise_ret (@DVALUE_I Pa w (iop_out x y))) ->
      (forall x y, iop_out (iop_in x y) x = x) ->
      (forall x y, iop_in x y = iop_in y x) ->
      refine_eou_dvalue
        (eval_closed_cert_expr penv foracle (CE_BinOp op w fl l r))
        (eval_closed_cert_expr penv foracle tgt)).
    { intros op_in iop_in iop_out Hndiv_out Hndiv_in Hchk0 Hiop_in Hiop_out Habs Hcomm_in.
      unfold check_absorb_binop_lhs in Hchk0.
      destruct (match_inner_binop op_in l) as [[[fl_in a] b] |] eqn:Em; [| discriminate Hchk0].
      destruct (match_inner_binop_inv op_in l fl_in a b Em) as [wl Heql]; subst l.
      cbn [cert_expr_bit_width] in Hwl; subst wl.
      cbn [wt_cert_expr collect_free_vars] in Hwtl, Hpl; rewrite !andb_true_iff in Hwtl.
      destruct Hwtl as ((((_ & Hta) & Htb) & Hwa) & Hwb).
      apply Pos.eqb_eq in Hwa; apply Pos.eqb_eq in Hwb.
      assert (Hpa : wf_param_env_for (collect_free_vars [] a) penv)
        by (intros x wx Hx; apply Hpl, in_app_iff; left; exact Hx).
      assert (Hpb : wf_param_env_for (collect_free_vars [] b) penv)
        by (intros x wx Hx; apply Hpl, in_app_iff; right; exact Hx).
      apply orb_true_iff in Hchk0 as [Har | Hbr];
        [rewrite !andb_true_iff in Har | rewrite !andb_true_iff in Hbr].
      - destruct Har as ([Heqar Hubb] & Hrec); apply cert_expr_eqb_eq in Heqar; subst a.
        pose proof (IH r tgt Hrec (eq_trans Hwr Hbw) Hwtr Hwtt Hpr Hpt) as Hrt.
        destruct (ub_free_expr_eval_ret b [] penv [] foracle Hubb Htb wf_let_val_env_nil Hpb)
          as [vb [Evb Hwfvb]]; rewrite Hwb in Hwfvb.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_r as [[msgr ->] | [vr [Evr Hwfvr]]]; [cbn; exact I | rewrite Evr in Hrt |- *; cbn [eou_bind]].
        rewrite Evb, ?Evr; cbn [eou_bind].
        destruct (eval_cert_expr penv [] foracle tgt) as [| | | vtgt];
          cbn in Hrt; try contradiction.
        exact (eval_iop_nested_weaken_l op_in op fl_in fl w vr vb vr vtgt iop_in iop_out
                 Hndiv_in Hndiv_out Hwfvr Hwfvb Hwfvr Hiop_in Hiop_out
                 (fun ia ib ic Hia _ Hic =>
                    ltac:(rewrite Hia in Hic; apply dvalue_i_inj in Hic; subst ic;
                          rewrite Habs, <- Hia; exact Hrt))).
      - destruct Hbr as ([Heqbr Huba] & Hrec); apply cert_expr_eqb_eq in Heqbr; subst b.
        pose proof (IH r tgt Hrec (eq_trans Hwr Hbw) Hwtr Hwtt Hpr Hpt) as Hrt.
        destruct (ub_free_expr_eval_ret a [] penv [] foracle Huba Hta wf_let_val_env_nil Hpa)
          as [va [Eva Hwfva]]; rewrite Hwa in Hwfva.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Eva; cbn [eou_bind].
        destruct Htot_r as [[msgr ->] | [vr [Evr Hwfvr]]]; [cbn; exact I | rewrite ?Evr in Hrt; rewrite !Evr; cbn [eou_bind]].
        destruct (eval_cert_expr penv [] foracle tgt) as [| | | vtgt];
          cbn in Hrt; try contradiction.
        exact (eval_iop_nested_weaken_l op_in op fl_in fl w va vr vr vtgt iop_in iop_out
                 Hndiv_in Hndiv_out Hwfva Hwfvr Hwfvr Hiop_in Hiop_out
                 (fun ia ib ic _ Hib Hic =>
                    ltac:(rewrite Hib in Hic; apply dvalue_i_inj in Hic; subst ic;
                          rewrite (Hcomm_in ia ib), Habs, <- Hib; exact Hrt))). }
    destruct op.
    + (* CB_Add *)
      rewrite !orb_true_iff in Hstep; destruct Hstep as [[[Hc | Hc] | Hc] | Hc].
      * apply andb_true_iff in Hc as [Hz Hrec].
        apply (Hid_r 0%N eq_refl (is_zero_const_expr_inv w r Hz) Hrec).
        intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.add_zero; reflexivity.
      * apply andb_true_iff in Hc as [Hz Hrec].
        apply (Hid_l 0%N eq_refl (is_zero_const_expr_inv w l Hz) Hrec).
        intros ir; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.add_zero_l; reflexivity.
      * exact (Hcan_lhs CB_Sub false (@Integers.sub w) (@Integers.add w) eq_refl eq_refl Hc
                 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (alg_sub_add_cancel w)
                 (fun H => False_ind _ (Bool.diff_false_true H))).
      * exact (Hcan_rhs CB_Sub false (@Integers.sub w) (@Integers.add w) eq_refl eq_refl Hc
                 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun x y => alg_sub_add_cancel_l w y x)
                 (fun H => False_ind _ (Bool.diff_false_true H))).
    + (* CB_Sub *)
      rewrite !orb_true_iff in Hstep; destruct Hstep as [[Hc | Hc] | Hc].
      * apply andb_true_iff in Hc as [H1 H2].
        apply (Hid_r 0%N eq_refl (is_zero_const_expr_inv w r H1) H2).
        intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.sub_zero_l; reflexivity.
      * apply andb_true_iff in Hc as [H1 H2].
        apply cert_expr_eqb_eq in H1; subst r.
        rewrite (is_zero_const_expr_inv w tgt H2).
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [-> Hwfvl]]]; [cbn; exact I | cbn [eou_bind]].
        apply (refine_eou_dvalue_trans _
                 (@eval_iop Pa (cert_to_ibinop CB_Sub no_binop_flags) vl vl) _).
        -- exact (eval_iop_non_div_rem_monotone CB_Sub fl no_binop_flags w vl vl vl vl
                    eq_refl (binop_flags_weaken_no_flags fl) Hwfvl Hwfvl Hwfvl Hwfvl
                    (dvalue_refines_refl _) (dvalue_refines_refl _)).
        -- destruct Hwfvl as [-> | [il ->]]; [cbn; apply dvalue_refines_poison_l |].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
           rewrite Integers.sub_idem; apply dvalue_refines_refl.
      * exact (Hcan_lhs CB_Add true (@Integers.add w) (@Integers.sub w) eq_refl eq_refl Hc
                 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (alg_add_sub_cancel w)
                 (fun _ => @Integers.add_commut w)).
    + (* CB_Mul *)
      rewrite !orb_true_iff in Hstep; destruct Hstep as [[[Hc | Hc] | Hc] | Hc];
        apply andb_true_iff in Hc as [H1 H2].
      * apply (Hid_r 1%N eq_refl (is_one_const_expr_inv w r H1) H2).
        intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_one_N; cbn.
        destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_one; reflexivity.
      * apply (Hid_l 1%N eq_refl (is_one_const_expr_inv w l H1) H2).
        intros ir; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_one_N; cbn.
        destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_commut, Integers.mul_one; reflexivity.
      * rewrite (is_zero_const_expr_inv w r H1), (is_zero_const_expr_inv w tgt H2).
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [-> Hwfvl]]]; [cbn; exact I | cbn [eou_bind]].
        apply (refine_eou_dvalue_trans _
                 (@eval_iop Pa (cert_to_ibinop CB_Mul no_binop_flags) vl
                    (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N 0))))) _).
        -- exact (eval_iop_non_div_rem_monotone CB_Mul fl no_binop_flags w vl vl _ _
                    eq_refl (binop_flags_weaken_no_flags fl) Hwfvl Hwfvl
                    (or_intror (ex_intro _ _ eq_refl)) (or_intror (ex_intro _ _ eq_refl))
                    (dvalue_refines_refl _) (dvalue_refines_refl _)).
        -- destruct Hwfvl as [-> | [il ->]]; [cbn; apply dvalue_refines_poison_l |].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
           destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_zero; apply dvalue_refines_refl.
      * rewrite (is_zero_const_expr_inv w l H1), (is_zero_const_expr_inv w tgt H2).
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
        destruct Htot_r as [[msgr ->] | [vr [-> Hwfvr]]]; [cbn; exact I | cbn [eou_bind]].
        apply (refine_eou_dvalue_trans _
                 (@eval_iop Pa (cert_to_ibinop CB_Mul no_binop_flags)
                    (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N 0)))) vr) _).
        -- exact (eval_iop_non_div_rem_monotone CB_Mul fl no_binop_flags w _ _ vr vr
                    eq_refl (binop_flags_weaken_no_flags fl)
                    (or_intror (ex_intro _ _ eq_refl)) (or_intror (ex_intro _ _ eq_refl))
                    Hwfvr Hwfvr (dvalue_refines_refl _) (dvalue_refines_refl _)).
        -- destruct Hwfvr as [-> | [ir ->]]; [cbn; apply dvalue_refines_poison_l |].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
           destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_commut, Integers.mul_zero;
             apply dvalue_refines_refl.
    + (* CB_UDiv *)
      apply orb_true_iff in Hstep as [Hc | Hc]; apply andb_true_iff in Hc as [H1 H2].
      * rewrite (is_one_const_expr_inv w r H1).
        pose proof (IH l tgt H2 (eq_trans Hwl Hbw) Hwtl Hwtt Hpl Hpt) as Hlt.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [Evl Hwfvl]]];
          [cbn; exact I | rewrite Evl in Hlt |- *; cbn [eou_bind]].
        apply (refine_eou_dvalue_trans _
                 (@eval_iop Pa (cert_to_ibinop CB_UDiv no_binop_flags) vl
                    (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N 1))))) _).
        -- exact (eval_iop_div_rem_same_lhs CB_UDiv fl no_binop_flags w vl _ _
                    eq_refl (binop_flags_weaken_no_flags fl) Hwfvl
                    (or_intror (ex_intro _ _ eq_refl)) (or_intror (ex_intro _ _ eq_refl))
                    (dvalue_refines_refl _)).
        -- destruct Hwfvl as [-> | [il ->]]; [exact Hlt |].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_one_N; cbn.
           rewrite (@Integers.unsigned_one w); cbn; rewrite (@Integers.divu_one w il); exact Hlt.
      * rewrite (is_zero_const_expr_inv w l H1), (is_zero_const_expr_inv w tgt H2).
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
        destruct Htot_r as [[msgr ->] | [vr [-> [-> | [ir ->]]]]]; [cbn; exact I | cbn; exact I |].
        cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
        unfold cert_to_ibinop, eval_int_op; cbn.
        destruct (@Integers.unsigned w ir =? 0)%Z; cbn; [exact I |].
        destruct (cbf_exact fl && _); cbn;
          [apply dvalue_refines_poison_l | rewrite alg_divu_zero_l; apply dvalue_refines_refl].
    + (* CB_SDiv *)
      apply andb_true_iff in Hstep as [H1 H2].
      rewrite (is_zero_const_expr_inv w l H1), (is_zero_const_expr_inv w tgt H2).
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
      destruct Htot_r as [[msgr ->] | [vr [-> [-> | [ir ->]]]]]; [cbn; exact I | cbn; exact I |].
      cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
      unfold cert_to_ibinop, eval_int_op; cbn.
      destruct (@Integers.signed w ir =? 0)%Z; cbn; [exact I |].
      destruct ((@Integers.min_signed w =? @Integers.signed w (@Integers.zero w))%Z && _);
        cbn; [exact I |].
      destruct (cbf_exact fl && _); cbn;
        [apply dvalue_refines_poison_l | rewrite alg_divs_zero_l; apply dvalue_refines_refl].
    + (* CB_URem *)
      apply orb_true_iff in Hstep as [Hc | Hc]; apply andb_true_iff in Hc as [H1 H2].
      * rewrite (is_one_const_expr_inv w r H1), (is_zero_const_expr_inv w tgt H2).
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]];
          [cbn; exact I | cbn; apply dvalue_refines_poison_l |].
        cbn [eou_bind]; unfold eval_iop;
          rewrite eval_iop_integer_base_same_width, repr_one_N, repr_zero_N; cbn.
        rewrite (@Integers.unsigned_one w); cbn; rewrite (@Integers.modu_one w il).
        apply dvalue_refines_refl.
      * rewrite (is_zero_const_expr_inv w l H1), (is_zero_const_expr_inv w tgt H2).
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
        destruct Htot_r as [[msgr ->] | [vr [-> [-> | [ir ->]]]]]; [cbn; exact I | cbn; exact I |].
        cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        destruct (@Integers.unsigned w ir =? 0)%Z; cbn; [exact I |].
        rewrite alg_modu_zero_l; apply dvalue_refines_refl.
    + (* CB_SRem *)
      apply andb_true_iff in Hstep as [H1 H2].
      rewrite (is_zero_const_expr_inv w l H1), (is_zero_const_expr_inv w tgt H2).
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
      destruct Htot_r as [[msgr ->] | [vr [-> [-> | [ir ->]]]]]; [cbn; exact I | cbn; exact I |].
      cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
      unfold cert_to_ibinop, eval_int_op; cbn.
      destruct (@Integers.signed w ir =? 0)%Z; cbn; [exact I |].
      destruct ((@Integers.min_signed w =? @Integers.signed w (@Integers.zero w))%Z && _);
        cbn; [exact I |].
      rewrite alg_mods_zero_l; cbn; apply dvalue_refines_refl.
    + (* CB_Shl *)
      apply andb_true_iff in Hstep as [H1 H2].
      apply (Hid_r 0%N eq_refl (is_zero_const_expr_inv w r H1) H2).
      intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
      rewrite (@Integers.unsigned_zero w); cbn; rewrite alg_shl_zero; reflexivity.
    + (* CB_LShr *)
      apply andb_true_iff in Hstep as [H1 H2].
      apply (Hid_r 0%N eq_refl (is_zero_const_expr_inv w r H1) H2).
      intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
      rewrite (@Integers.unsigned_zero w); cbn; rewrite alg_shru_zero; reflexivity.
    + (* CB_AShr *)
      apply andb_true_iff in Hstep as [H1 H2].
      apply (Hid_r 0%N eq_refl (is_zero_const_expr_inv w r H1) H2).
      intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
      rewrite (@Integers.unsigned_zero w); cbn; rewrite alg_shr_zero; reflexivity.
    + (* CB_And *)
      rewrite !orb_true_iff in Hstep.
      destruct Hstep as [[[[[[Hc | Hc] | Hc] | Hc] | Hc] | Habs_r] | Habs_l].
      * apply andb_true_iff in Hc as [H1 H2].
        apply (Hid_r (all_ones_N w) eq_refl (is_all_ones_const_expr_inv w r H1) H2).
        intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
        rewrite Integers.and_mone; reflexivity.
      * apply andb_true_iff in Hc as [H1 H2].
        apply (Hid_l (all_ones_N w) eq_refl (is_all_ones_const_expr_inv w l H1) H2).
        intros ir; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
        rewrite Integers.and_mone_l; reflexivity.
      * apply andb_true_iff in Hc as [H1 H2]; apply cert_expr_eqb_eq in H1; subst r.
        pose proof (IH l tgt H2 (eq_trans Hwl Hbw) Hwtl Hwtt Hpl Hpt) as Hlt.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [Evl Hwfvl]]];
          [cbn; exact I | rewrite !Evl; rewrite Evl in Hlt; cbn [eou_bind]].
        destruct Hwfvl as [-> | [il ->]]; [exact Hlt |].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn.
        rewrite Integers.and_idem; exact Hlt.
      * apply andb_true_iff in Hc as [H1 H2].
        rewrite (is_zero_const_expr_inv w r H1), (is_zero_const_expr_inv w tgt H2).
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]];
          [cbn; exact I | cbn; apply dvalue_refines_poison_l | cbn [eou_bind]].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.and_zero; apply dvalue_refines_refl.
      * apply andb_true_iff in Hc as [H1 H2].
        rewrite (is_zero_const_expr_inv w l H1), (is_zero_const_expr_inv w tgt H2).
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
        destruct Htot_r as [[msgr ->] | [vr [-> [-> | [ir ->]]]]];
          [cbn; exact I | cbn; apply dvalue_refines_poison_l | cbn [eou_bind]].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.and_zero_l; apply dvalue_refines_refl.
      * exact (Habs_rhs CB_Or (@Integers.or w) (@Integers.and w) eq_refl eq_refl Habs_r
                 (fun _ _ => eq_refl) (fun _ _ => eq_refl)
                 (alg_and_or_absorb w) (@Integers.or_commut w)).
      * exact (Habs_lhs CB_Or (@Integers.or w) (@Integers.and w) eq_refl eq_refl Habs_l
                 (fun _ _ => eq_refl) (fun _ _ => eq_refl)
                 (fun x y => eq_trans (@Integers.and_commut w _ x) (alg_and_or_absorb w x y))
                 (@Integers.or_commut w)).
    + (* CB_Or *)
      rewrite !orb_true_iff in Hstep.
      destruct Hstep as [[[[[[Hc | Hc] | Hc] | Hc] | Hc] | Habs_r] | Habs_l].
      * apply andb_true_iff in Hc as [H1 H2].
        apply (Hid_r 0%N eq_refl (is_zero_const_expr_inv w r H1) H2).
        intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.or_zero; reflexivity.
      * apply andb_true_iff in Hc as [H1 H2].
        apply (Hid_l 0%N eq_refl (is_zero_const_expr_inv w l H1) H2).
        intros ir; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.or_zero_l; reflexivity.
      * apply andb_true_iff in Hc as [H1 H2]; apply cert_expr_eqb_eq in H1; subst r.
        pose proof (IH l tgt H2 (eq_trans Hwl Hbw) Hwtl Hwtt Hpl Hpt) as Hlt.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [Evl Hwfvl]]];
          [cbn; exact I | rewrite !Evl; rewrite Evl in Hlt; cbn [eou_bind]].
        apply (refine_eou_dvalue_trans _
                 (@eval_iop Pa (cert_to_ibinop CB_Or no_binop_flags) vl vl) _).
        -- exact (eval_iop_non_div_rem_monotone CB_Or fl no_binop_flags w vl vl vl vl
                    eq_refl (binop_flags_weaken_no_flags fl) Hwfvl Hwfvl Hwfvl Hwfvl
                    (dvalue_refines_refl _) (dvalue_refines_refl _)).
        -- destruct Hwfvl as [-> | [il ->]]; [exact Hlt |].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn.
           rewrite Integers.or_idem; exact Hlt.
      * apply andb_true_iff in Hc as [H1 H2].
        rewrite (is_all_ones_const_expr_inv w r H1), (is_all_ones_const_expr_inv w tgt H2).
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [-> Hwfvl]]]; [cbn; exact I | cbn [eou_bind]].
        apply (refine_eou_dvalue_trans _
                 (@eval_iop Pa (cert_to_ibinop CB_Or no_binop_flags) vl
                    (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N (all_ones_N w)))))) _).
        -- exact (eval_iop_non_div_rem_monotone CB_Or fl no_binop_flags w vl vl _ _
                    eq_refl (binop_flags_weaken_no_flags fl) Hwfvl Hwfvl
                    (or_intror (ex_intro _ _ eq_refl)) (or_intror (ex_intro _ _ eq_refl))
                    (dvalue_refines_refl _) (dvalue_refines_refl _)).
        -- destruct Hwfvl as [-> | [il ->]]; [cbn; apply dvalue_refines_poison_l |].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
           rewrite Integers.or_mone; apply dvalue_refines_refl.
      * apply andb_true_iff in Hc as [H1 H2].
        rewrite (is_all_ones_const_expr_inv w l H1), (is_all_ones_const_expr_inv w tgt H2).
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
        destruct Htot_r as [[msgr ->] | [vr [-> Hwfvr]]]; [cbn; exact I | cbn [eou_bind]].
        apply (refine_eou_dvalue_trans _
                 (@eval_iop Pa (cert_to_ibinop CB_Or no_binop_flags)
                    (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N (all_ones_N w))))) vr) _).
        -- exact (eval_iop_non_div_rem_monotone CB_Or fl no_binop_flags w _ _ vr vr
                    eq_refl (binop_flags_weaken_no_flags fl)
                    (or_intror (ex_intro _ _ eq_refl)) (or_intror (ex_intro _ _ eq_refl))
                    Hwfvr Hwfvr (dvalue_refines_refl _) (dvalue_refines_refl _)).
        -- destruct Hwfvr as [-> | [ir ->]]; [cbn; apply dvalue_refines_poison_l |].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
           rewrite Integers.or_commut, Integers.or_mone; apply dvalue_refines_refl.
      * exact (Habs_rhs CB_And (@Integers.and w) (@Integers.or w) eq_refl eq_refl Habs_r
                 (fun _ _ => eq_refl) (fun _ _ => eq_refl)
                 (alg_or_and_absorb w) (@Integers.and_commut w)).
      * exact (Habs_lhs CB_And (@Integers.and w) (@Integers.or w) eq_refl eq_refl Habs_l
                 (fun _ _ => eq_refl) (fun _ _ => eq_refl)
                 (fun x y => eq_trans (@Integers.or_commut w _ x) (alg_or_and_absorb w x y))
                 (@Integers.and_commut w)).
    + (* CB_Xor *)
      rewrite !orb_true_iff in Hstep.
      destruct Hstep as [[[[Hc | Hc] | Hc] | Hcl] | Hcr].
      * apply andb_true_iff in Hc as [H1 H2].
        apply (Hid_r 0%N eq_refl (is_zero_const_expr_inv w r H1) H2).
        intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.xor_zero; reflexivity.
      * apply andb_true_iff in Hc as [H1 H2].
        apply (Hid_l 0%N eq_refl (is_zero_const_expr_inv w l H1) H2).
        intros ir; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.xor_zero_l; reflexivity.
      * apply andb_true_iff in Hc as [H1 H2].
        apply cert_expr_eqb_eq in H1; subst r; rewrite (is_zero_const_expr_inv w tgt H2).
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]];
          [cbn; exact I | cbn; apply dvalue_refines_poison_l | cbn [eou_bind]].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.xor_idem; apply dvalue_refines_refl.
      * exact (Hcan_lhs CB_Xor true (@Integers.xor w) (@Integers.xor w) eq_refl eq_refl Hcl
                 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (alg_xor_cancel w)
                 (fun _ => @Integers.xor_commut w)).
      * exact (Hcan_rhs CB_Xor true (@Integers.xor w) (@Integers.xor w) eq_refl eq_refl Hcr
                 (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun x y => alg_xor_cancel_l w y x)
                 (fun _ => @Integers.xor_commut w)).
  - (* CE_ICmp *)
    cbn [wt_cert_expr collect_free_vars] in Hwts, Hps.
    rewrite !andb_true_iff in Hwts; rewrite !andb_true_iff in Hstep.
    destruct Hwts as (((Hwtl & _) & Hwl) & _); destruct Hstep as [Heq Hcst].
    apply Pos.eqb_eq in Hwl; apply cert_expr_eqb_eq in Heq; subst r.
    assert (Hpl : wf_param_env_for (collect_free_vars [] l) penv)
      by (intros x wx Hx; apply Hps, in_app_iff; left; exact Hx).
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    destruct (eval_cert_expr_totality l [] penv [] foracle Hwtl wf_let_val_env_nil Hpl)
      as [[msgl ->] | [vl [-> Hwfvl]]]; [cbn; exact I | cbn [eou_bind]].
    rewrite Hwl in Hwfvl.
    apply (refine_eou_dvalue_trans _ (@eval_icmp Pa false (cert_to_icmp pr) vl vl) _).
    + exact (eval_icmp_monotone ss false pr w vl vl vl vl
               eq_refl Hwfvl Hwfvl Hwfvl Hwfvl
               (dvalue_refines_refl _) (dvalue_refines_refl _)).
    + destruct (is_refl_true_icmp pr) eqn:Ert.
      * rewrite (is_one_const_expr_inv 1 tgt Hcst); cbn [eval_cert_expr].
        destruct Hwfvl as [-> | [il ->]]; [cbn; apply dvalue_refines_poison_l |].
        rewrite alg_eval_icmp_refl, Ert, repr_one_N; apply dvalue_refines_refl.
      * rewrite (is_zero_const_expr_inv 1 tgt Hcst); cbn [eval_cert_expr].
        destruct Hwfvl as [-> | [il ->]]; [cbn; apply dvalue_refines_poison_l |].
        rewrite alg_eval_icmp_refl, Ert, repr_zero_N; apply dvalue_refines_refl.
  - (* CE_Select *)
    cbn [wt_cert_expr collect_free_vars cert_expr_bit_width] in Hwts, Hps, Hbw.
    rewrite !andb_true_iff in Hwts; rewrite !andb_true_iff in Hstep.
    destruct Hwts as (((((Hwtc & Hwtt1) & Hwtf1) & Hwc) & Hwt0) & Hwf0).
    destruct Hstep as [Hrt Hrf].
    apply Pos.eqb_eq in Hwc; apply Pos.eqb_eq in Hwt0; apply Pos.eqb_eq in Hwf0.
    assert (Hpc : wf_param_env_for (collect_free_vars [] c) penv)
      by (intros x wx Hx; apply Hps, in_app_iff; left; exact Hx).
    assert (Hpt1 : wf_param_env_for (collect_free_vars [] t) penv)
      by (intros x wx Hx; apply Hps, in_app_iff; right; apply in_app_iff; left; exact Hx).
    assert (Hpf1 : wf_param_env_for (collect_free_vars [] f) penv)
      by (intros x wx Hx; apply Hps, in_app_iff; right; apply in_app_iff; right; exact Hx).
    pose proof (IH t tgt Hrt (eq_trans Hwt0 Hbw) Hwtt1 Hwtt Hpt1 Hpt) as IHt.
    pose proof (IH f tgt Hrf (eq_trans Hwf0 Hbw) Hwtf1 Hwtt Hpf1 Hpt) as IHf.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    destruct (eval_cert_expr_totality c [] penv [] foracle Hwtc wf_let_val_env_nil Hpc)
      as [[msgc ->] | [vc [-> Hwfvc]]]; [cbn; exact I | cbn [eou_bind]].
    destruct (eval_cert_expr_totality t [] penv [] foracle Hwtt1 wf_let_val_env_nil Hpt1)
      as [[msgt ->] | [vt [Evt _]]]; [cbn; exact I | rewrite Evt in IHt |- *; cbn [eou_bind]].
    destruct (eval_cert_expr_totality f [] penv [] foracle Hwtf1 wf_let_val_env_nil Hpf1)
      as [[msgf ->] | [vf [Evf _]]]; [cbn; exact I | rewrite Evf in IHf |- *; cbn [eou_bind]].
    destruct (eval_cert_expr penv [] foracle tgt) as [| | | vtgt];
      cbn in IHt, IHf; try contradiction.
    rewrite Hwc in Hwfvc; destruct Hwfvc as [-> | [ic ->]]; cbn;
      [apply dvalue_refines_poison_l | destruct (@Integers.unsigned 1 ic =? 1)%Z; assumption].
  - (* CE_Freeze *)
    cbn [wt_cert_expr collect_free_vars cert_expr_bit_width] in Hwts, Hps, Hbw.
    apply andb_true_iff in Hwts as [Hwto Hwo]; apply Pos.eqb_eq in Hwo.
    apply andb_true_iff in Hstep as [Hdefo Hrec].
    destruct (expr_guaranteed_defined_sound ctx o penv foracle Hdefo Hwto Hps Hctx)
      as [_ [io Hio]].
    revert io Hio; rewrite Hwo; intros io Hio.
    pose proof (IH o tgt Hrec (eq_trans Hwo Hbw) Hwto Hwtt Hps Hpt) as IHo.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hio in IHo |- *.
    exact IHo.
Qed.

Lemma check_norm_refines_fuel_sound :
  forall {Pa : Params} (fuel : nat) (ctx : ub_ctx) (src tgt : cert_expr)
         (penv : param_env Pa) (foracle : freeze_oracle),
    check_norm_refines_fuel fuel ctx src tgt = true ->
    cert_expr_bit_width src = cert_expr_bit_width tgt ->
    wt_cert_expr [] src = true ->
    wt_cert_expr [] tgt = true ->
    wf_param_env_for (collect_free_vars [] src) penv ->
    wf_param_env_for (collect_free_vars [] tgt) penv ->
    ub_ctx_holds penv foracle ctx ->
    refine_eou_dvalue
      (eval_closed_cert_expr penv foracle src)
      (eval_closed_cert_expr penv foracle tgt).
Proof.
  intros Pa fuel ctx.
  induction fuel as [| fuel' IH];
    intros src tgt penv foracle Hchk Hbw Hwts Hwtt Hps Hpt Hctx;
    cbn [check_norm_refines_fuel] in Hchk.
  - destruct (ctx_has_unreachable ctx) eqn:Eunr;
      [exfalso; exact (ctx_has_unreachable_sound penv foracle ctx Eunr Hctx) |].
    destruct (cert_expr_eqb src tgt) eqn:Eeq; [| discriminate Hchk].
    apply cert_expr_eqb_eq in Eeq; subst tgt; apply refine_eou_dvalue_refl.
  - destruct (ctx_has_unreachable ctx) eqn:Eunr;
      [exfalso; exact (ctx_has_unreachable_sound penv foracle ctx Eunr Hctx) |].
    destruct (cert_expr_eqb src tgt) eqn:Eeq;
      [apply cert_expr_eqb_eq in Eeq; subst tgt; apply refine_eou_dvalue_refl |].
    rewrite !orb_true_iff in Hchk; destruct Hchk as [[Helim | Hintro] | Hcong].
    + apply (check_src_elim_step_sound (check_norm_refines_fuel fuel' ctx)
               ctx src tgt penv foracle
               (fun s t Hs Hbs Hts Htt Hps' Hpt' =>
                  IH s t penv foracle Hs Hbs Hts Htt Hps' Hpt' Hctx)
               Helim Hbw Hwts Hwtt Hps Hpt Hctx).
    + destruct tgt as [| | | | | | | w2 o2 |]; cbn in Hintro; try discriminate Hintro.
      cbn [wt_cert_expr collect_free_vars cert_expr_bit_width] in Hwtt, Hpt, Hbw.
      apply andb_true_iff in Hwtt as [Hwto2 Hwo2]; apply Pos.eqb_eq in Hwo2.
      pose proof (IH src o2 penv foracle Hintro (eq_trans Hbw (eq_sym Hwo2))
                     Hwts Hwto2 Hps Hpt Hctx) as IHo.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
      destruct (eval_cert_expr_totality src [] penv [] foracle Hwts wf_let_val_env_nil Hps)
        as [[msgs ->] | [vs [Evs _]]]; [cbn; exact I | rewrite Evs in IHo |- *].
      destruct (eval_cert_expr penv [] foracle o2) as [| | | vo2] eqn:Evo2;
        cbn in IHo; try contradiction.
      pose proof (eval_cert_expr_ret_wf_scalar o2 [] penv [] foracle vo2 Hwto2 Evo2) as Hwfvo2.
      rewrite Hwo2 in Hwfvo2; cbn [eou_bind].
      destruct IHo as [-> | ->].
      * destruct Hwfvo2 as [-> | [io2 ->]]; cbn; apply dvalue_refines_poison_l.
      * destruct Hwfvo2 as [-> | [io2 ->]]; cbn;
          [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
    + destruct src as
        [| | | op1 w1 fl1 l1 r1 | pr1 ss1 w1 l1 r1 | k1 fw1 tw1 fl1 o1 | w1 c1 t1 f1 | |];
        destruct tgt as
        [| | | op2 w2 fl2 l2 r2 | pr2 ss2 w2 l2 r2 | k2 fw2 tw2 fl2 o2 | w2 c2 t2 f2 | |];
        cbn [check_struct_cong_step] in Hcong; try discriminate Hcong.
      * (* CE_BinOp *)
        rewrite !andb_true_iff in Hcong.
        destruct Hcong as (((Hop & Hww) & Hfl) & Hargs).
        apply cert_binop_eqb_eq in Hop; apply Pos.eqb_eq in Hww; subst op2 w2.
        cbn [wt_cert_expr collect_free_vars] in Hwts, Hwtt, Hps, Hpt.
        rewrite !andb_true_iff in Hwts; rewrite !andb_true_iff in Hwtt.
        destruct Hwts as ((((_ & Htl1) & Htr1) & Hwl1) & Hwr1).
        destruct Hwtt as ((((_ & Htl2) & Htr2) & Hwl2) & Hwr2).
        apply Pos.eqb_eq in Hwl1; apply Pos.eqb_eq in Hwr1.
        apply Pos.eqb_eq in Hwl2; apply Pos.eqb_eq in Hwr2.
        assert (Hpl1 : wf_param_env_for (collect_free_vars [] l1) penv)
          by (intros x wx Hx; apply Hps, in_app_iff; left; exact Hx).
        assert (Hpr1 : wf_param_env_for (collect_free_vars [] r1) penv)
          by (intros x wx Hx; apply Hps, in_app_iff; right; exact Hx).
        assert (Hpl2 : wf_param_env_for (collect_free_vars [] l2) penv)
          by (intros x wx Hx; apply Hpt, in_app_iff; left; exact Hx).
        assert (Hpr2 : wf_param_env_for (collect_free_vars [] r2) penv)
          by (intros x wx Hx; apply Hpt, in_app_iff; right; exact Hx).
        destruct (is_div_or_rem_op op1) eqn:Ediv.
        -- apply orb_true_iff in Hargs as [Hsame | Hnzdiv].
           ++ apply andb_true_iff in Hsame as [Heql Hrr].
              apply cert_expr_eqb_eq in Heql; subst l2.
              pose proof (IH r1 r2 penv foracle Hrr (eq_trans Hwr1 (eq_sym Hwr2))
                             Htr1 Htr2 Hpr1 Hpr2 Hctx) as IHr.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
              destruct (eval_cert_expr_totality l1 [] penv [] foracle Htl1 wf_let_val_env_nil Hpl1)
                as [[msgl ->] | [vl [-> Hwfvl]]]; [cbn; exact I | cbn [eou_bind]].
              rewrite Hwl1 in Hwfvl.
              apply (eou_bind_refine_typed w1 _ _ _ _
                       (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                      (eval_cert_expr_ret_wf_scalar r1 [] penv [] foracle v Htr1 Hv) _ Hwr1)
                       (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                      (eval_cert_expr_ret_wf_scalar r2 [] penv [] foracle v Htr2 Hv) _ Hwr2)
                       IHr).
              intros vr1 vr2 Hwfr1 Hwfr2 Hrr_val.
              exact (eval_iop_div_rem_same_lhs op1 fl1 fl2 w1 vl vr1 vr2
                       Ediv Hfl Hwfvl Hwfr1 Hwfr2 Hrr_val).
           ++ rewrite !andb_true_iff in Hnzdiv; destruct Hnzdiv as ([Hnz Hll] & Hrr).
              destruct (expr_divisor_nonzero_sound ctx r1 penv foracle Htr1 Hnz Hctx)
                as [ir1 [Hir1 Hnz1]].
              revert ir1 Hir1 Hnz1; rewrite Hwr1; intros ir1 Hir1 Hnz1.
              pose proof (IH l1 l2 penv foracle Hll (eq_trans Hwl1 (eq_sym Hwl2))
                             Htl1 Htl2 Hpl1 Hpl2 Hctx) as IHl.
              pose proof (IH r1 r2 penv foracle Hrr (eq_trans Hwr1 (eq_sym Hwr2))
                             Htr1 Htr2 Hpr1 Hpr2 Hctx) as IHr.
              rewrite Hir1 in IHr.
              destruct (eval_closed_cert_expr penv foracle r2) as [| | | vr2] eqn:Evr2;
                cbn in IHr; try contradiction.
              destruct IHr as [Hpsn | ->]; [discriminate Hpsn |].
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
              rewrite Hir1, Evr2.
              apply (eou_bind_refine_typed w1 _ _ _ _
                       (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                      (eval_cert_expr_ret_wf_scalar l1 [] penv [] foracle v Htl1 Hv) _ Hwl1)
                       (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                      (eval_cert_expr_ret_wf_scalar l2 [] penv [] foracle v Htl2 Hv) _ Hwl2)
                       IHl).
              intros vl1 vl2 Hwfl1 Hwfl2 Hll_val; cbn [eou_bind].
              exact (eval_iop_div_rem_nonzero_div op1 fl1 fl2 w1 ir1 vl1 vl2
                       Ediv Hfl Hnz1 Hwfl1 Hwfl2 Hll_val).
        -- apply orb_true_iff in Hargs as [Hdir | Hswp].
           ++ apply andb_true_iff in Hdir as [Hll Hrr].
              pose proof (IH l1 l2 penv foracle Hll (eq_trans Hwl1 (eq_sym Hwl2))
                             Htl1 Htl2 Hpl1 Hpl2 Hctx) as IHl.
              pose proof (IH r1 r2 penv foracle Hrr (eq_trans Hwr1 (eq_sym Hwr2))
                             Htr1 Htr2 Hpr1 Hpr2 Hctx) as IHr.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
              apply (eou_bind_refine_typed w1 _ _ _ _
                       (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                      (eval_cert_expr_ret_wf_scalar l1 [] penv [] foracle v Htl1 Hv) _ Hwl1)
                       (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                      (eval_cert_expr_ret_wf_scalar l2 [] penv [] foracle v Htl2 Hv) _ Hwl2)
                       IHl).
              intros vl1 vl2 Hwfl1 Hwfl2 Hll_val.
              apply (eou_bind_refine_typed w1 _ _ _ _
                       (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                      (eval_cert_expr_ret_wf_scalar r1 [] penv [] foracle v Htr1 Hv) _ Hwr1)
                       (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                      (eval_cert_expr_ret_wf_scalar r2 [] penv [] foracle v Htr2 Hv) _ Hwr2)
                       IHr).
              intros vr1 vr2 Hwfr1 Hwfr2 Hrr_val.
              exact (eval_iop_non_div_rem_monotone op1 fl1 fl2 w1 vl1 vl2 vr1 vr2
                       Ediv Hfl Hwfl1 Hwfl2 Hwfr1 Hwfr2 Hll_val Hrr_val).
           ++ rewrite !andb_true_iff in Hswp; destruct Hswp as ([Hcomm Hlr] & Hrl).
              pose proof (IH l1 r2 penv foracle Hlr (eq_trans Hwl1 (eq_sym Hwr2))
                             Htl1 Htr2 Hpl1 Hpr2 Hctx) as IHlr.
              pose proof (IH r1 l2 penv foracle Hrl (eq_trans Hwr1 (eq_sym Hwl2))
                             Htr1 Htl2 Hpr1 Hpl2 Hctx) as IHrl.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
              destruct (eval_cert_expr_totality l1 [] penv [] foracle Htl1 wf_let_val_env_nil Hpl1)
                as [[msgl ->] | [vl1 [Evl1 Hwfl1]]]; [cbn; exact I | rewrite Evl1 in IHlr |- *; cbn [eou_bind]].
              destruct (eval_cert_expr_totality r1 [] penv [] foracle Htr1 wf_let_val_env_nil Hpr1)
                as [[msgr ->] | [vr1 [Evr1 Hwfr1]]]; [cbn; exact I | rewrite Evr1 in IHrl |- *; cbn [eou_bind]].
              destruct (eval_cert_expr penv [] foracle r2) as [| | | vr2] eqn:Evr2;
                cbn in IHlr; try contradiction.
              destruct (eval_cert_expr penv [] foracle l2) as [| | | vl2] eqn:Evl2;
                cbn in IHrl; try contradiction.
              cbn [eou_bind].
              pose proof (eval_cert_expr_ret_wf_scalar l2 [] penv [] foracle vl2 Htl2 Evl2) as Hwfl2.
              pose proof (eval_cert_expr_ret_wf_scalar r2 [] penv [] foracle vr2 Htr2 Evr2) as Hwfr2.
              rewrite Hwl1 in Hwfl1; rewrite Hwr1 in Hwfr1;
                rewrite Hwl2 in Hwfl2; rewrite Hwr2 in Hwfr2.
              rewrite (eval_iop_commut op1 fl2 w1 vl2 vr2 Hcomm Hwfl2 Hwfr2).
              exact (eval_iop_non_div_rem_monotone op1 fl1 fl2 w1 vl1 vr2 vr1 vl2
                       Ediv Hfl Hwfl1 Hwfr2 Hwfr1 Hwfl2 IHlr IHrl).
      * (* CE_ICmp *)
        rewrite !andb_true_iff in Hcong; destruct Hcong as ([Hww Hss] & Hargs).
        apply Pos.eqb_eq in Hww; subst w2.
        cbn [wt_cert_expr collect_free_vars] in Hwts, Hwtt, Hps, Hpt.
        rewrite !andb_true_iff in Hwts; rewrite !andb_true_iff in Hwtt.
        destruct Hwts as (((Htl1 & Htr1) & Hwl1) & Hwr1).
        destruct Hwtt as (((Htl2 & Htr2) & Hwl2) & Hwr2).
        apply Pos.eqb_eq in Hwl1; apply Pos.eqb_eq in Hwr1.
        apply Pos.eqb_eq in Hwl2; apply Pos.eqb_eq in Hwr2.
        assert (Hpl1 : wf_param_env_for (collect_free_vars [] l1) penv)
          by (intros x wx Hx; apply Hps, in_app_iff; left; exact Hx).
        assert (Hpr1 : wf_param_env_for (collect_free_vars [] r1) penv)
          by (intros x wx Hx; apply Hps, in_app_iff; right; exact Hx).
        assert (Hpl2 : wf_param_env_for (collect_free_vars [] l2) penv)
          by (intros x wx Hx; apply Hpt, in_app_iff; left; exact Hx).
        assert (Hpr2 : wf_param_env_for (collect_free_vars [] r2) penv)
          by (intros x wx Hx; apply Hpt, in_app_iff; right; exact Hx).
        apply orb_true_iff in Hargs as [Hdir | Hswp].
        -- rewrite !andb_true_iff in Hdir; destruct Hdir as ([Hpr Hll] & Hrr);
           apply cert_icmp_pred_eqb_eq in Hpr; subst pr2.
           pose proof (IH l1 l2 penv foracle Hll (eq_trans Hwl1 (eq_sym Hwl2))
                          Htl1 Htl2 Hpl1 Hpl2 Hctx) as IHl.
           pose proof (IH r1 r2 penv foracle Hrr (eq_trans Hwr1 (eq_sym Hwr2))
                          Htr1 Htr2 Hpr1 Hpr2 Hctx) as IHr.
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
           apply (eou_bind_refine_typed w1 _ _ _ _
                    (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                   (eval_cert_expr_ret_wf_scalar l1 [] penv [] foracle v Htl1 Hv) _ Hwl1)
                    (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                   (eval_cert_expr_ret_wf_scalar l2 [] penv [] foracle v Htl2 Hv) _ Hwl2)
                    IHl).
           intros vl1 vl2 Hwfl1 Hwfl2 Hll_val.
           apply (eou_bind_refine_typed w1 _ _ _ _
                    (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                   (eval_cert_expr_ret_wf_scalar r1 [] penv [] foracle v Htr1 Hv) _ Hwr1)
                    (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                   (eval_cert_expr_ret_wf_scalar r2 [] penv [] foracle v Htr2 Hv) _ Hwr2)
                    IHr).
           intros vr1 vr2 Hwfr1 Hwfr2 Hrr_val.
           exact (eval_icmp_monotone ss1 ss2 pr1 w1 vl1 vl2 vr1 vr2
                    Hss Hwfl1 Hwfl2 Hwfr1 Hwfr2 Hll_val Hrr_val).
        -- rewrite !andb_true_iff in Hswp; destruct Hswp as ([Hpr Hlr] & Hrl);
           apply cert_icmp_pred_eqb_eq in Hpr; subst pr2.
           pose proof (IH l1 r2 penv foracle Hlr (eq_trans Hwl1 (eq_sym Hwr2))
                          Htl1 Htr2 Hpl1 Hpr2 Hctx) as IHlr.
           pose proof (IH r1 l2 penv foracle Hrl (eq_trans Hwr1 (eq_sym Hwl2))
                          Htr1 Htl2 Hpr1 Hpl2 Hctx) as IHrl.
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
           destruct (eval_cert_expr_totality l1 [] penv [] foracle Htl1 wf_let_val_env_nil Hpl1)
             as [[msgl ->] | [vl1 [Evl1 Hwfl1]]]; [cbn; exact I | rewrite Evl1 in IHlr |- *; cbn [eou_bind]].
           destruct (eval_cert_expr_totality r1 [] penv [] foracle Htr1 wf_let_val_env_nil Hpr1)
             as [[msgr ->] | [vr1 [Evr1 Hwfr1]]]; [cbn; exact I | rewrite Evr1 in IHrl |- *; cbn [eou_bind]].
           destruct (eval_cert_expr penv [] foracle r2) as [| | | vr2] eqn:Evr2;
             cbn in IHlr; try contradiction.
           destruct (eval_cert_expr penv [] foracle l2) as [| | | vl2] eqn:Evl2;
             cbn in IHrl; try contradiction.
           cbn [eou_bind].
           pose proof (eval_cert_expr_ret_wf_scalar l2 [] penv [] foracle vl2 Htl2 Evl2) as Hwfl2.
           pose proof (eval_cert_expr_ret_wf_scalar r2 [] penv [] foracle vr2 Htr2 Evr2) as Hwfr2.
           rewrite Hwl1 in Hwfl1; rewrite Hwr1 in Hwfr1;
             rewrite Hwl2 in Hwfl2; rewrite Hwr2 in Hwfr2.
           rewrite (eval_icmp_swap ss1 pr1 w1 vl1 vr1 Hwfl1 Hwfr1).
           exact (eval_icmp_monotone ss1 ss2 (swap_cert_icmp pr1) w1 vr1 vl2 vl1 vr2
                    Hss Hwfr1 Hwfl2 Hwfl1 Hwfr2 IHrl IHlr).
      * (* CE_Cast *)
        rewrite !andb_true_iff in Hcong.
        destruct Hcong as ((((Hk & Hfw) & Htw) & Hfl) & Hoo).
        apply cert_cast_kind_eqb_eq in Hk; apply Pos.eqb_eq in Hfw; apply Pos.eqb_eq in Htw.
        subst k2 fw2 tw2.
        cbn [wt_cert_expr collect_free_vars] in Hwts, Hwtt, Hps, Hpt.
        rewrite !andb_true_iff in Hwts; rewrite !andb_true_iff in Hwtt.
        destruct Hwts as ((Hk1 & Hto1) & Hwo1); destruct Hwtt as ((Hk2 & Hto2) & Hwo2).
        apply Pos.eqb_eq in Hwo1; apply Pos.eqb_eq in Hwo2.
        pose proof (IH o1 o2 penv foracle Hoo (eq_trans Hwo1 (eq_sym Hwo2))
                       Hto1 Hto2 Hps Hpt Hctx) as IHo.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        apply (eou_bind_refine_typed fw1 _ _ _ _
                 (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                (eval_cert_expr_ret_wf_scalar o1 [] penv [] foracle v Hto1 Hv) _ Hwo1)
                 (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                (eval_cert_expr_ret_wf_scalar o2 [] penv [] foracle v Hto2 Hv) _ Hwo2)
                 IHo).
        intros vo1 vo2 Hwfo1 Hwfo2 Hoo_val.
        exact (eval_cast_monotone k1 fw1 tw1 fl1 fl2 vo1 vo2 Hk1 Hk2 Hfl Hwfo1 Hwfo2 Hoo_val).
      * (* CE_Select *)
        apply andb_true_iff in Hcong as [Hww Hor].
        apply Pos.eqb_eq in Hww; subst w2.
        cbn [wt_cert_expr collect_free_vars] in Hwts, Hwtt, Hps, Hpt.
        rewrite !andb_true_iff in Hwts; rewrite !andb_true_iff in Hwtt.
        destruct Hwts as (((((Htc1 & Htt1) & Htf1) & Hwc1) & Hwt1) & Hwf1).
        destruct Hwtt as (((((Htc2 & Htt2) & Htf2) & Hwc2) & Hwt2) & Hwf2).
        apply Pos.eqb_eq in Hwc1; apply Pos.eqb_eq in Hwt1; apply Pos.eqb_eq in Hwf1.
        apply Pos.eqb_eq in Hwc2; apply Pos.eqb_eq in Hwt2; apply Pos.eqb_eq in Hwf2.
        assert (Hpc1 : wf_param_env_for (collect_free_vars [] c1) penv)
          by (intros x wx Hx; apply Hps, in_app_iff; left; exact Hx).
        assert (Hpt1 : wf_param_env_for (collect_free_vars [] t1) penv)
          by (intros x wx Hx; apply Hps, in_app_iff; right; apply in_app_iff; left; exact Hx).
        assert (Hpf1 : wf_param_env_for (collect_free_vars [] f1) penv)
          by (intros x wx Hx; apply Hps, in_app_iff; right; apply in_app_iff; right; exact Hx).
        assert (Hpc2 : wf_param_env_for (collect_free_vars [] c2) penv)
          by (intros x wx Hx; apply Hpt, in_app_iff; left; exact Hx).
        assert (Hpt2 : wf_param_env_for (collect_free_vars [] t2) penv)
          by (intros x wx Hx; apply Hpt, in_app_iff; right; apply in_app_iff; left; exact Hx).
        assert (Hpf2 : wf_param_env_for (collect_free_vars [] f2) penv)
          by (intros x wx Hx; apply Hpt, in_app_iff; right; apply in_app_iff; right; exact Hx).
        apply orb_true_iff in Hor as [Hdir | Hneg].
        -- rewrite !andb_true_iff in Hdir; destruct Hdir as ([Hcc Htt0] & Hff0).
           pose proof (IH c1 c2 penv foracle Hcc (eq_trans Hwc1 (eq_sym Hwc2))
                          Htc1 Htc2 Hpc1 Hpc2 Hctx) as IHc.
           pose proof (IH t1 t2 penv foracle Htt0 (eq_trans Hwt1 (eq_sym Hwt2))
                          Htt1 Htt2 Hpt1 Hpt2 Hctx) as IHt.
           pose proof (IH f1 f2 penv foracle Hff0 (eq_trans Hwf1 (eq_sym Hwf2))
                          Htf1 Htf2 Hpf1 Hpf2 Hctx) as IHf.
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
           apply (eou_bind_refine_typed 1%positive _ _ _ _
                    (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                   (eval_cert_expr_ret_wf_scalar c1 [] penv [] foracle v Htc1 Hv) _ Hwc1)
                    (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                   (eval_cert_expr_ret_wf_scalar c2 [] penv [] foracle v Htc2 Hv) _ Hwc2)
                    IHc).
           intros vc1 vc2 Hwfc1 Hwfc2 Hcc_val.
           apply (eou_bind_refine_typed w1 _ _ _ _
                    (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                   (eval_cert_expr_ret_wf_scalar t1 [] penv [] foracle v Htt1 Hv) _ Hwt1)
                    (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                   (eval_cert_expr_ret_wf_scalar t2 [] penv [] foracle v Htt2 Hv) _ Hwt2)
                    IHt).
           intros vt1 vt2 Hwft1 Hwft2 Htt_val.
           apply (eou_bind_refine_typed w1 _ _ _ _
                    (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                   (eval_cert_expr_ret_wf_scalar f1 [] penv [] foracle v Htf1 Hv) _ Hwf1)
                    (fun v Hv => eq_ind _ (fun z => wf_scalar_dvalue z v)
                                   (eval_cert_expr_ret_wf_scalar f2 [] penv [] foracle v Htf2 Hv) _ Hwf2)
                    IHf).
           intros vf1 vf2 Hwff1 Hwff2 Hff_val.
           exact (eval_select_monotone w1 vc1 vc2 vt1 vt2 vf1 vf2
                    Hwfc1 Hwfc2 Hwft1 Hwft2 Hwff1 Hwff2 Hcc_val Htt_val Hff_val).
        -- destruct c1 as [| | | | pr1 ss1 wc1 l1 r1 | | | |]; try discriminate Hneg.
           destruct c2 as [| | | | pr2 ss2 wc2 l2 r2 | | | |]; try discriminate Hneg.
           rewrite !andb_true_iff in Hneg;
             destruct Hneg as ((((Hwc & Hss) & Htf0) & Hft0) & Horp).
           apply Pos.eqb_eq in Hwc; subst wc2.
           cbn [wt_cert_expr collect_free_vars] in Htc1, Htc2, Hpc1, Hpc2;
             rewrite !andb_true_iff in Htc1; rewrite !andb_true_iff in Htc2.
           destruct Htc1 as (((Htl1 & Htr1) & Hwl1) & Hwr1);
             destruct Htc2 as (((Htl2 & Htr2) & Hwl2) & Hwr2);
             apply Pos.eqb_eq in Hwl1; apply Pos.eqb_eq in Hwr1;
             apply Pos.eqb_eq in Hwl2; apply Pos.eqb_eq in Hwr2.
           assert (Hpl1 : wf_param_env_for (collect_free_vars [] l1) penv)
             by (intros x wx Hx; apply Hpc1, in_app_iff; left; exact Hx).
           assert (Hpr1 : wf_param_env_for (collect_free_vars [] r1) penv)
             by (intros x wx Hx; apply Hpc1, in_app_iff; right; exact Hx).
           assert (Hpl2 : wf_param_env_for (collect_free_vars [] l2) penv)
             by (intros x wx Hx; apply Hpc2, in_app_iff; left; exact Hx).
           assert (Hpr2 : wf_param_env_for (collect_free_vars [] r2) penv)
             by (intros x wx Hx; apply Hpc2, in_app_iff; right; exact Hx).
           pose proof (IH t1 f2 penv foracle Htf0 (eq_trans Hwt1 (eq_sym Hwf2))
                          Htt1 Htf2 Hpt1 Hpf2 Hctx) as IHtf.
           pose proof (IH f1 t2 penv foracle Hft0 (eq_trans Hwf1 (eq_sym Hwt2))
                          Htf1 Htt2 Hpf1 Hpt2 Hctx) as IHft.
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
           destruct (eval_cert_expr_totality l1 [] penv [] foracle Htl1 wf_let_val_env_nil Hpl1)
             as [[msgl ->] | [vl1 [Evl1 Hwfl1]]]; [cbn [eou_bind]; exact I | rewrite ?Evl1; cbn [eou_bind]].
           destruct (eval_cert_expr_totality r1 [] penv [] foracle Htr1 wf_let_val_env_nil Hpr1)
             as [[msgr ->] | [vr1 [Evr1 Hwfr1]]]; [cbn [eou_bind]; exact I | rewrite ?Evr1; cbn [eou_bind]].
           rewrite Hwl1 in Hwfl1; rewrite Hwr1 in Hwfr1.
           destruct (eval_icmp_wf_scalar ss1 pr1 wc1 vl1 vr1 Hwfl1 Hwfr1) as [vc1 [Hvc1 _]].
           pose proof Hvc1 as Hvc1_rw; rewrite Hvc1_rw; cbn [eou_bind].
           destruct (eval_cert_expr_totality t1 [] penv [] foracle Htt1 wf_let_val_env_nil Hpt1)
             as [[msgt ->] | [vt1 [Evt1 Hwft1]]]; [cbn [eou_bind]; exact I | rewrite Evt1 in IHtf |- *; cbn [eou_bind]].
           destruct (eval_cert_expr_totality f1 [] penv [] foracle Htf1 wf_let_val_env_nil Hpf1)
             as [[msgf ->] | [vf1 [Evf1 Hwff1]]]; [cbn [eou_bind]; exact I | rewrite Evf1 in IHft |- *; cbn [eou_bind]].
           rewrite Hwt1 in Hwft1; rewrite Hwf1 in Hwff1.
           destruct (eval_cert_expr penv [] foracle f2) as [| | | vf2] eqn:Evf2;
             cbn in IHtf; try contradiction.
           destruct (eval_cert_expr penv [] foracle t2) as [| | | vt2] eqn:Evt2;
             cbn in IHft; try contradiction.
           pose proof (eval_cert_expr_ret_wf_scalar f2 [] penv [] foracle vf2 Htf2 Evf2) as Hwff2;
             rewrite Hwf2 in Hwff2.
           pose proof (eval_cert_expr_ret_wf_scalar t2 [] penv [] foracle vt2 Htt2 Evt2) as Hwft2;
             rewrite Hwt2 in Hwft2.
           apply orb_true_iff in Horp as [Hdirp | Hswpp].
           ++ rewrite !andb_true_iff in Hdirp; destruct Hdirp as ((Hpr & Hll) & Hrr).
              apply cert_icmp_pred_eqb_eq in Hpr; subst pr2.
              pose proof (IH l1 l2 penv foracle Hll (eq_trans Hwl1 (eq_sym Hwl2))
                             Htl1 Htl2 Hpl1 Hpl2 Hctx) as IHll.
              pose proof (IH r1 r2 penv foracle Hrr (eq_trans Hwr1 (eq_sym Hwr2))
                             Htr1 Htr2 Hpr1 Hpr2 Hctx) as IHrr.
              rewrite Evl1 in IHll; rewrite Evr1 in IHrr.
              destruct (eval_cert_expr penv [] foracle l2) as [| | | vl2] eqn:Evl2;
                cbn in IHll; try contradiction.
              destruct (eval_cert_expr penv [] foracle r2) as [| | | vr2] eqn:Evr2;
                cbn in IHrr; try contradiction.
              pose proof (eval_cert_expr_ret_wf_scalar l2 [] penv [] foracle vl2 Htl2 Evl2) as Hwfl2;
                rewrite Hwl2 in Hwfl2.
              pose proof (eval_cert_expr_ret_wf_scalar r2 [] penv [] foracle vr2 Htr2 Evr2) as Hwfr2;
                rewrite Hwr2 in Hwfr2.
              cbn [eou_bind].
              pose proof (eval_icmp_neg_select ss1 ss2 pr1 wc1 w1 vl1 vl2 vr1 vr2 vt1 vt2 vf1 vf2
                            Hss Hwfl1 Hwfl2 Hwfr1 Hwfr2 Hwft1 Hwft2 Hwff1 Hwff2 IHll IHrr IHtf IHft)
                as Hneg_sel.
              rewrite Hvc1 in Hneg_sel; cbn [eou_bind] in Hneg_sel.
              destruct (eval_icmp_wf_scalar ss2 (neg_cert_icmp pr1) wc1 vl2 vr2 Hwfl2 Hwfr2) as [vc2 [Hvc2 _]].
              rewrite Hvc2 in *; cbn [eou_bind] in *; exact Hneg_sel.
           ++ rewrite !andb_true_iff in Hswpp; destruct Hswpp as ((Hpr & Hlr) & Hrl).
              apply cert_icmp_pred_eqb_eq in Hpr; subst pr2.
              pose proof (IH l1 r2 penv foracle Hlr (eq_trans Hwl1 (eq_sym Hwr2))
                             Htl1 Htr2 Hpl1 Hpr2 Hctx) as IHlr.
              pose proof (IH r1 l2 penv foracle Hrl (eq_trans Hwr1 (eq_sym Hwl2))
                             Htr1 Htl2 Hpr1 Hpl2 Hctx) as IHrl.
              rewrite Evl1 in IHlr; rewrite Evr1 in IHrl.
              destruct (eval_cert_expr penv [] foracle l2) as [| | | vl2] eqn:Evl2;
                cbn in IHrl; try contradiction.
              destruct (eval_cert_expr penv [] foracle r2) as [| | | vr2] eqn:Evr2;
                cbn in IHlr; try contradiction.
              pose proof (eval_cert_expr_ret_wf_scalar l2 [] penv [] foracle vl2 Htl2 Evl2) as Hwfl2;
                rewrite Hwl2 in Hwfl2.
              pose proof (eval_cert_expr_ret_wf_scalar r2 [] penv [] foracle vr2 Htr2 Evr2) as Hwfr2;
                rewrite Hwr2 in Hwfr2.
              cbn [eou_bind].
              rewrite swap_neg_cert_icmp.
              pose proof (eval_icmp_neg_select ss1 ss2 (swap_cert_icmp pr1) wc1 w1
                            vr1 vl2 vl1 vr2 vt1 vt2 vf1 vf2
                            Hss Hwfr1 Hwfl2 Hwfl1 Hwfr2 Hwft1 Hwft2 Hwff1 Hwff2 IHrl IHlr IHtf IHft)
                as Hneg_sel.
              rewrite <- (eval_icmp_swap ss1 pr1 wc1 vl1 vr1 Hwfl1 Hwfr1), Hvc1 in Hneg_sel.
              destruct (eval_icmp_wf_scalar ss2 (neg_cert_icmp (swap_cert_icmp pr1)) wc1 vl2 vr2 Hwfl2 Hwfr2)
                as [vc2 [Hvc2 _]].
              rewrite Hvc2 in *; cbn [eou_bind] in *; exact Hneg_sel.
Qed.

Definition check_expr_refines (ctx : ub_ctx) (src tgt : cert_expr) : bool :=
  Pos.eqb (cert_expr_bit_width src) (cert_expr_bit_width tgt) &&
  wt_cert_expr [] src &&
  wt_cert_expr [] tgt &&
  check_wf_let_dag_fast default_let_expand_budget src &&
  check_wf_let_dag_fast default_let_expand_budget tgt &&
  if ctx_has_unreachable ctx then true
  else if cert_expr_eqb src tgt then true
  else
    match expand_lets_fueled norm_let_expand_budget src,
          expand_lets_fueled norm_let_expand_budget tgt with
    | Some es, Some et =>
        let ns := normalize_cert_expr ctx es in
        let nt := normalize_cert_expr ctx et in
        check_norm_refines_fuel (Nat.min 128%nat (S (expr_size ns + expr_size nt))) ctx ns nt
    | _, _ => false
    end.

Theorem check_expr_refines_sound :
  forall {Pa : Params} (ctx : ub_ctx) (src tgt : cert_expr)
         (penv : param_env Pa) (foracle : freeze_oracle),
    check_expr_refines ctx src tgt = true ->
    wf_param_env_for (collect_free_vars [] src) penv ->
    wf_param_env_for (collect_free_vars [] tgt) penv ->
    ub_ctx_holds penv foracle ctx ->
    refine_eou_dvalue
      (eval_closed_cert_expr penv foracle src)
      (eval_closed_cert_expr penv foracle tgt).
Proof.
  intros Pa ctx src tgt penv foracle Hchk Hps Hpt Hctx.
  unfold check_expr_refines in Hchk.
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as (((((Hbw & Hwts) & Hwtt) & Hdags_f) & Hdagt_f) & Hbody).
  apply Pos.eqb_eq in Hbw.
  pose proof (check_wf_let_dag_fast_sound default_let_expand_budget src Hdags_f) as Hdags.
  pose proof (check_wf_let_dag_fast_sound default_let_expand_budget tgt Hdagt_f) as Hdagt.
  destruct (ctx_has_unreachable ctx) eqn:Eunr;
    [exfalso; exact (ctx_has_unreachable_sound penv foracle ctx Eunr Hctx) |].
  destruct (cert_expr_eqb src tgt) eqn:Eeq;
    [apply cert_expr_eqb_eq in Eeq; subst tgt; apply refine_eou_dvalue_refl |].
  destruct (expand_lets_fueled norm_let_expand_budget src) as [es |] eqn:Ees;
    [| discriminate Hbody].
  destruct (expand_lets_fueled norm_let_expand_budget tgt) as [et |] eqn:Eet;
    [| discriminate Hbody].
  pose proof (expand_lets_fueled_eq norm_let_expand_budget src es Ees) as Hes_eq.
  pose proof (expand_lets_fueled_eq norm_let_expand_budget tgt et Eet) as Het_eq.
  subst es et; cbn zeta in Hbody.
  destruct (expand_lets_with_typing src [] [] Hwts wf_let_subst_nil)
    as (Hb_es & Hwt_es & Hlf_es).
  destruct (expand_lets_with_typing tgt [] [] Hwtt wf_let_subst_nil)
    as (Hb_et & Hwt_et & Hlf_et).
  pose proof (expand_lets_with_wf_param_env src [] penv
                (fun k ce H => False_ind _ H) Hps) as Hp_es.
  pose proof (expand_lets_with_wf_param_env tgt [] penv
                (fun k ce H => False_ind _ H) Hpt) as Hp_et.
  destruct (normalize_cert_expr_typing ctx (expand_lets src) Hwt_es Hlf_es)
    as (Hb_ns & Hwt_ns & _ & Hinc_ns).
  destruct (normalize_cert_expr_typing ctx (expand_lets tgt) Hwt_et Hlf_et)
    as (Hb_nt & Hwt_nt & _ & Hinc_nt).
  assert (Hp_ns : wf_param_env_for (collect_free_vars [] (normalize_cert_expr ctx (expand_lets src))) penv)
    by (intros x wx Hx; exact (Hp_es x wx (Hinc_ns _ Hx))).
  assert (Hp_nt : wf_param_env_for (collect_free_vars [] (normalize_cert_expr ctx (expand_lets tgt))) penv)
    by (intros x wx Hx; exact (Hp_et x wx (Hinc_nt _ Hx))).
  assert (Heq_src : equiv_eou_dvalue
                      (eval_closed_cert_expr penv foracle src)
                      (eval_closed_cert_expr penv foracle (normalize_cert_expr ctx (expand_lets src)))).
  { apply (equiv_eou_dvalue_trans _ (eval_closed_cert_expr penv foracle (expand_lets src))).
    - exact (eval_expand_lets_equiv src penv foracle Hwts Hdags Hps).
    - exact (normalize_cert_expr_eval ctx (expand_lets src) penv foracle Hwt_es Hlf_es Hp_es Hctx). }
  assert (Heq_tgt : equiv_eou_dvalue
                      (eval_closed_cert_expr penv foracle tgt)
                      (eval_closed_cert_expr penv foracle (normalize_cert_expr ctx (expand_lets tgt)))).
  { apply (equiv_eou_dvalue_trans _ (eval_closed_cert_expr penv foracle (expand_lets tgt))).
    - exact (eval_expand_lets_equiv tgt penv foracle Hwtt Hdagt Hpt).
    - exact (normalize_cert_expr_eval ctx (expand_lets tgt) penv foracle Hwt_et Hlf_et Hp_et Hctx). }
  assert (Hbw_norm :
            cert_expr_bit_width (normalize_cert_expr ctx (expand_lets src)) =
            cert_expr_bit_width (normalize_cert_expr ctx (expand_lets tgt)))
    by (rewrite Hb_ns, Hb_nt; unfold expand_lets; rewrite Hb_es, Hb_et; exact Hbw).
  apply (refine_eou_compat _ _ _ _ Heq_src Heq_tgt).
  exact (check_norm_refines_fuel_sound _ ctx _ _ penv foracle
           Hbody Hbw_norm Hwt_ns Hwt_nt Hp_ns Hp_nt Hctx).
Qed.


