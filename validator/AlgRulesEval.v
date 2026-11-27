(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * [CertValidator.AlgRulesEval] Verified Symbolic [(val, poison)] DAG Evaluator

    Defines:
    1. Vanilla-CIC Hedberg proof-irrelevance for [Pos.eq_dec] and bitvector
       constant characterizations ([all_ones_N], [repr_all_ones_N]) over
       Vellvm's [@Integers.bit_int sz].
    2. Exact bijections between canonical [cert-v1] operators and Vellvm's
       [ibinop], [icmp], and [pure_conversion] AST operators.
    3. Relational scalar value refinement ([dvalue_refines]) and [EOU]
       outcome equivalence/refinement ([equiv_eou_dvalue], [refine_eou_dvalue]).
    4. The relational [(val, poison)] symbolic DAG evaluator [eval_cert_expr]
       over [param_env] + [let_env] + [freeze_oracle], supporting closed
       [$n0..] [CE_Let] DAG bindings ([E-10]), constants, arbitrary bitwidths
       [sz : positive], all 13 integer binary operators, [icmp], [select],
       [zext]/[sext]/[trunc] (with [nneg]/[nuw]/[nsw]), and [freeze].
    5. Closed [CE_Let] DAG expansion ([expand_lets]) and its exact evaluation
       equivalence ([eval_expand_lets_equiv]). *)

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
  CertFormatAst.
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

(** ** 1. Vanilla-CIC Hedberg & Bitvector Foundations *)

Lemma alg_eq_trans_sym_l {A : Type} {x y : A} (p : x = y) :
  Logic.eq_trans (Logic.eq_sym p) p = Logic.eq_refl.
Proof.
  destruct p; reflexivity.
Qed.

Definition alg_pos_nu {x y : positive} (p : x = y) : x = y :=
  match Pos.eq_dec x y with
  | left q => q
  | right Hne => False_rect (x = y) (Hne p)
  end.

Lemma alg_pos_nu_const {x y : positive} (p q : x = y) :
  alg_pos_nu p = alg_pos_nu q.
Proof.
  unfold alg_pos_nu.
  destruct (Pos.eq_dec x y) as [Heq | Hne]; [reflexivity | contradiction (Hne p)].
Qed.

Lemma alg_pos_nu_left_inv {x y : positive} (p : x = y) :
  Logic.eq_trans (Logic.eq_sym (alg_pos_nu Logic.eq_refl)) (alg_pos_nu p) = p.
Proof.
  destruct p; apply alg_eq_trans_sym_l.
Qed.

Lemma alg_pos_uip_refl (x : positive) (p : x = x) :
  p = Logic.eq_refl.
Proof.
  rewrite <- (alg_pos_nu_left_inv p), (alg_pos_nu_const p Logic.eq_refl);
    apply alg_pos_nu_left_inv.
Qed.

Lemma alg_pos_eq_dec_refl (sz : positive) :
  Pos.eq_dec sz sz = left Logic.eq_refl.
Proof.
  destruct (Pos.eq_dec sz sz) as [Heq | Hne].
  - f_equal; apply alg_pos_uip_refl.
  - contradiction (Hne Logic.eq_refl).
Qed.

Lemma alg_bit_int_unsigned_inj (sz : positive) (x y : @Integers.bit_int sz) :
  @Integers.unsigned sz x = @Integers.unsigned sz y -> x = y.
Proof.
  intros H.
  rewrite <- (@Integers.repr_unsigned sz x), <- (@Integers.repr_unsigned sz y), H.
  reflexivity.
Qed.

Lemma dvalue_I_same_sz_inj : forall {Pa : Params} (sz : positive)
                                    (i1 i2 : @Integers.bit_int sz),
  @DVALUE_I Pa sz i1 = @DVALUE_I Pa sz i2 -> i1 = i2.
Proof.
  intros Pa sz i1 i2 H.
  apply alg_bit_int_unsigned_inj.
  exact (f_equal (@dvalue_base_int_unsigned Pa) H).
Qed.

Definition dvalue_base_int_width {Pa : Params} (dv : @dvalue_base Pa) : option positive :=
  match dv with
  | DVALUE_I sz _ => Some sz
  | _ => None
  end.

Lemma dvalue_I_width_eq : forall {Pa : Params} (sz1 sz2 : positive)
                                 (i1 : @Integers.bit_int sz1)
                                 (i2 : @Integers.bit_int sz2),
  @DVALUE_I Pa sz1 i1 = @DVALUE_I Pa sz2 i2 -> sz1 = sz2.
Proof.
  intros Pa sz1 sz2 i1 i2 H.
  pose proof (f_equal (@dvalue_base_int_width Pa) H) as Hw; cbn in Hw.
  inversion Hw; reflexivity.
Qed.

Lemma alg_bit_int_1_cases (val : @Integers.bit_int 1) :
  if (@Integers.unsigned 1 val =? 1)%Z
  then val = @Integers.one 1
  else val = @Integers.zero 1.
Proof.
  pose proof (@Integers.unsigned_range 1 val) as Hrng.
  change (@Integers.modulus 1) with 2%Z in Hrng.
  destruct (@Integers.unsigned 1 val =? 1)%Z eqn:E.
  - apply Z.eqb_eq in E.
    apply alg_bit_int_unsigned_inj.
    rewrite E, (@Integers.unsigned_one 1); reflexivity.
  - apply Z.eqb_neq in E.
    apply alg_bit_int_unsigned_inj.
    rewrite (@Integers.unsigned_zero 1); lia.
Qed.

Lemma eval_iop_integer_base_same_width :
  forall {Pa : Params} (iop : LLVMAst.ibinop) (sz : positive)
         (i1 i2 : @Integers.bit_int sz),
    @eval_iop_integer_base Pa iop (@DVALUE_I Pa sz i1) (@DVALUE_I Pa sz i2) =
    eval_int_op iop i1 i2.
Proof.
  intros Pa iop sz i1 i2.
  unfold eval_iop_integer_base.
  rewrite (alg_pos_eq_dec_refl sz).
  reflexivity.
Qed.

Lemma eval_icmp_base_same_width :
  forall {Pa : Params} (ss : bool) (pr : LLVMAst.icmp) (sz : positive)
         (i1 i2 : @Integers.bit_int sz),
    @eval_icmp_base Pa ss pr (@DVALUE_I Pa sz i1) (@DVALUE_I Pa sz i2) =
    eval_int_icmp ss pr i1 i2.
Proof.
  intros Pa ss pr sz i1 i2.
  unfold eval_icmp_base.
  rewrite (alg_pos_eq_dec_refl sz).
  reflexivity.
Qed.

Definition all_ones_N (sz : positive) : N :=
  Z.to_N (Z.ones (Z.pos sz)).

Lemma repr_zero_N : forall (sz : positive),
  @Integers.repr sz (Z.of_N 0%N) = @Integers.zero sz.
Proof.
  intros sz; unfold Integers.zero; reflexivity.
Qed.

Lemma repr_one_N : forall (sz : positive),
  @Integers.repr sz (Z.of_N 1%N) = @Integers.one sz.
Proof.
  intros sz; unfold Integers.one; reflexivity.
Qed.

Lemma repr_all_ones_N : forall (sz : positive),
  @Integers.repr sz (Z.of_N (all_ones_N sz)) = @Integers.mone sz.
Proof.
  intros sz; unfold all_ones_N.
  assert (Hpos : (0 <= Z.ones (Z.pos sz))%Z).
  { rewrite Z.ones_equiv.
    assert (Hp : (0 < 2 ^ Z.pos sz)%Z) by (apply Z.pow_pos_nonneg; lia).
    lia. }
  rewrite (Z2N.id _ Hpos).
  apply @Integers.same_bits_eq; intros i Hi.
  rewrite (@Integers.testbit_repr sz _ i Hi), (@Integers.bits_mone sz i Hi).
  unfold Integers.zwordsize in Hi.
  exact (Z.ones_spec_low (Z.pos sz) i Hi).
Qed.

Definition is_zero_const_expr (w : positive) (e : cert_expr) : bool :=
  match e with
  | CE_BvConst w' v => Pos.eqb w' w && N.eqb v 0%N
  | _ => false
  end.

Definition is_one_const_expr (w : positive) (e : cert_expr) : bool :=
  match e with
  | CE_BvConst w' v => Pos.eqb w' w && N.eqb v 1%N
  | _ => false
  end.

Definition is_all_ones_const_expr (w : positive) (e : cert_expr) : bool :=
  match e with
  | CE_BvConst w' v => Pos.eqb w' w && N.eqb v (all_ones_N w)
  | _ => false
  end.

Lemma is_zero_const_expr_inv : forall w e,
  is_zero_const_expr w e = true -> e = CE_BvConst w 0%N.
Proof.
  intros w [w' v | | | | | | | |] H; cbn in H; try discriminate.
  apply andb_true_iff in H as [Hw Hv].
  apply Pos.eqb_eq in Hw; apply N.eqb_eq in Hv; subst; reflexivity.
Qed.

Lemma is_one_const_expr_inv : forall w e,
  is_one_const_expr w e = true -> e = CE_BvConst w 1%N.
Proof.
  intros w [w' v | | | | | | | |] H; cbn in H; try discriminate.
  apply andb_true_iff in H as [Hw Hv].
  apply Pos.eqb_eq in Hw; apply N.eqb_eq in Hv; subst; reflexivity.
Qed.

Lemma is_all_ones_const_expr_inv : forall w e,
  is_all_ones_const_expr w e = true -> e = CE_BvConst w (all_ones_N w).
Proof.
  intros w [w' v | | | | | | | |] H; cbn in H; try discriminate.
  apply andb_true_iff in H as [Hw Hv].
  apply Pos.eqb_eq in Hw; apply N.eqb_eq in Hv; subst; reflexivity.
Qed.

(** ** 2. Exact Bijections Between [cert-v1] Operators and Vellvm AST Operators *)

Definition cert_to_ibinop (op : cert_binop) (fl : cert_binop_flags) : LLVMAst.ibinop :=
  match op with
  | CB_Add  => LLVMAst.Add (cbf_nuw fl) (cbf_nsw fl)
  | CB_Sub  => LLVMAst.Sub (cbf_nuw fl) (cbf_nsw fl)
  | CB_Mul  => LLVMAst.Mul (cbf_nuw fl) (cbf_nsw fl)
  | CB_Shl  => LLVMAst.Shl (cbf_nuw fl) (cbf_nsw fl)
  | CB_UDiv => LLVMAst.UDiv (cbf_exact fl)
  | CB_SDiv => LLVMAst.SDiv (cbf_exact fl)
  | CB_LShr => LLVMAst.LShr (cbf_exact fl)
  | CB_AShr => LLVMAst.AShr (cbf_exact fl)
  | CB_URem => LLVMAst.URem
  | CB_SRem => LLVMAst.SRem
  | CB_And  => LLVMAst.And
  | CB_Or   => LLVMAst.Or (cbf_disjoint fl)
  | CB_Xor  => LLVMAst.Xor
  end.

Definition ibinop_to_cert (iop : LLVMAst.ibinop) : cert_binop * cert_binop_flags :=
  match iop with
  | LLVMAst.Add nuw nsw => (CB_Add, mk_cert_binop_flags nuw nsw false false)
  | LLVMAst.Sub nuw nsw => (CB_Sub, mk_cert_binop_flags nuw nsw false false)
  | LLVMAst.Mul nuw nsw => (CB_Mul, mk_cert_binop_flags nuw nsw false false)
  | LLVMAst.Shl nuw nsw => (CB_Shl, mk_cert_binop_flags nuw nsw false false)
  | LLVMAst.UDiv ex     => (CB_UDiv, mk_cert_binop_flags false false ex false)
  | LLVMAst.SDiv ex     => (CB_SDiv, mk_cert_binop_flags false false ex false)
  | LLVMAst.LShr ex     => (CB_LShr, mk_cert_binop_flags false false ex false)
  | LLVMAst.AShr ex     => (CB_AShr, mk_cert_binop_flags false false ex false)
  | LLVMAst.URem        => (CB_URem, no_binop_flags)
  | LLVMAst.SRem        => (CB_SRem, no_binop_flags)
  | LLVMAst.And         => (CB_And, no_binop_flags)
  | LLVMAst.Or dj       => (CB_Or, mk_cert_binop_flags false false false dj)
  | LLVMAst.Xor         => (CB_Xor, no_binop_flags)
  end.

Lemma ibinop_to_cert_roundtrip : forall iop op fl,
  ibinop_to_cert iop = (op, fl) ->
  cert_to_ibinop op fl = iop /\ wf_binop_flags_for op fl = true.
Proof.
  intros iop op fl H; destruct iop; inversion H; subst; cbn; auto.
Qed.

Definition cert_to_icmp (pr : cert_icmp_pred) : LLVMAst.icmp :=
  match pr with
  | CIP_Eq  => LLVMAst.Eq
  | CIP_Ne  => LLVMAst.Ne
  | CIP_Ult => LLVMAst.Ult
  | CIP_Ule => LLVMAst.Ule
  | CIP_Ugt => LLVMAst.Ugt
  | CIP_Uge => LLVMAst.Uge
  | CIP_Slt => LLVMAst.Slt
  | CIP_Sle => LLVMAst.Sle
  | CIP_Sgt => LLVMAst.Sgt
  | CIP_Sge => LLVMAst.Sge
  end.

Definition icmp_to_cert (pr : LLVMAst.icmp) : cert_icmp_pred :=
  match pr with
  | LLVMAst.Eq  => CIP_Eq
  | LLVMAst.Ne  => CIP_Ne
  | LLVMAst.Ult => CIP_Ult
  | LLVMAst.Ule => CIP_Ule
  | LLVMAst.Ugt => CIP_Ugt
  | LLVMAst.Uge => CIP_Uge
  | LLVMAst.Slt => CIP_Slt
  | LLVMAst.Sle => CIP_Sle
  | LLVMAst.Sgt => CIP_Sgt
  | LLVMAst.Sge => CIP_Sge
  end.

Lemma icmp_to_cert_roundtrip : forall pr,
  cert_to_icmp (icmp_to_cert pr) = pr.
Proof.
  intros []; reflexivity.
Qed.

Definition cert_to_pure_conv (k : cert_cast_kind) (fl : cert_cast_flags)
  : LLVMAst.pure_conversion :=
  match k with
  | CCK_ZExt  => LLVMAst.Zext (ccf_nneg fl)
  | CCK_SExt  => LLVMAst.Sext
  | CCK_Trunc => LLVMAst.Trunc (ccf_nuw fl) (ccf_nsw fl)
  end.

Definition pure_conv_to_cert (pc : LLVMAst.pure_conversion)
  : option (cert_cast_kind * cert_cast_flags) :=
  match pc with
  | LLVMAst.Zext nn => Some (CCK_ZExt, mk_cert_cast_flags nn false false)
  | LLVMAst.Sext => Some (CCK_SExt, no_cast_flags)
  | LLVMAst.Trunc nuw nsw => Some (CCK_Trunc, mk_cert_cast_flags false nuw nsw)
  | _ => None
  end.

Lemma pure_conv_to_cert_roundtrip : forall pc k fl,
  pure_conv_to_cert pc = Some (k, fl) ->
  cert_to_pure_conv k fl = pc.
Proof.
  intros pc k fl H; destruct pc; cbn in H; try discriminate;
    inversion H; subst; reflexivity.
Qed.

(** ** 3. Scalar Value Typing, [dvalue_refines], and [EOU] Outcome Relations *)

Definition wf_scalar_dvalue {Pa : Params} (sz : positive) (v : @dvalue Pa) : Prop :=
  v = DVALUE_Base DVALUE_Poison \/
  exists i : @Integers.bit_int sz, v = DVALUE_Base (@DVALUE_I Pa sz i).

Definition dvalue_refines {Pa : Params} (v_src v_tgt : @dvalue Pa) : Prop :=
  v_src = DVALUE_Base DVALUE_Poison \/ v_tgt = v_src.

Lemma dvalue_refines_refl : forall {Pa : Params} (v : @dvalue Pa),
  dvalue_refines v v.
Proof.
  intros Pa v; right; reflexivity.
Qed.

Lemma dvalue_refines_trans : forall {Pa : Params} (v1 v2 v3 : @dvalue Pa),
  dvalue_refines v1 v2 -> dvalue_refines v2 v3 -> dvalue_refines v1 v3.
Proof.
  intros Pa v1 v2 v3 [-> | ->] [-> | ->];
    try (left; reflexivity); right; reflexivity.
Qed.

Lemma dvalue_refines_poison_l : forall {Pa : Params} (v : @dvalue Pa),
  dvalue_refines (DVALUE_Base DVALUE_Poison) v.
Proof.
  intros Pa v; left; reflexivity.
Qed.

Definition equiv_eou_dvalue {Pa : Params} (r1 r2 : EOU (@dvalue Pa)) : Prop :=
  match r1, r2 with
  | raise_ub _, raise_ub _ => True
  | raise_oom _, raise_oom _ => True
  | raise_error _, raise_error _ => True
  | raise_ret v1, raise_ret v2 => v1 = v2
  | _, _ => False
  end.

Lemma equiv_eou_dvalue_refl : forall {Pa : Params} (r : EOU (@dvalue Pa)),
  equiv_eou_dvalue r r.
Proof.
  intros Pa []; cbn; trivial.
Qed.

Lemma equiv_eou_dvalue_sym : forall {Pa : Params} (r1 r2 : EOU (@dvalue Pa)),
  equiv_eou_dvalue r1 r2 -> equiv_eou_dvalue r2 r1.
Proof.
  intros Pa [] [] H; cbn in *; auto.
Qed.

Lemma equiv_eou_dvalue_trans : forall {Pa : Params} (r1 r2 r3 : EOU (@dvalue Pa)),
  equiv_eou_dvalue r1 r2 -> equiv_eou_dvalue r2 r3 -> equiv_eou_dvalue r1 r3.
Proof.
  intros Pa [] [] [] H12 H23; cbn in *; try contradiction; trivial; congruence.
Qed.

Definition refine_eou_dvalue {Pa : Params} (r_src r_tgt : EOU (@dvalue Pa)) : Prop :=
  match r_src with
  | raise_ub _ => True
  | raise_error _ =>
      match r_tgt with
      | raise_error _ => True
      | _ => False
      end
  | raise_oom _ =>
      match r_tgt with
      | raise_oom _ => True
      | _ => False
      end
  | raise_ret v_src =>
      match r_tgt with
      | raise_ret v_tgt => dvalue_refines v_src v_tgt
      | _ => False
      end
  end.

Lemma refine_eou_dvalue_refl : forall {Pa : Params} (r : EOU (@dvalue Pa)),
  refine_eou_dvalue r r.
Proof.
  intros Pa []; cbn; trivial; apply dvalue_refines_refl.
Qed.

Lemma refine_eou_dvalue_trans : forall {Pa : Params} (r1 r2 r3 : EOU (@dvalue Pa)),
  refine_eou_dvalue r1 r2 -> refine_eou_dvalue r2 r3 -> refine_eou_dvalue r1 r3.
Proof.
  intros Pa [] [] [] H12 H23; cbn in *; try contradiction; trivial.
  exact (dvalue_refines_trans _ _ _ H12 H23).
Qed.

Lemma equiv_implies_refine_eou : forall {Pa : Params} (r1 r2 : EOU (@dvalue Pa)),
  equiv_eou_dvalue r1 r2 -> refine_eou_dvalue r1 r2.
Proof.
  intros Pa [] [] H; cbn in *; try contradiction; trivial.
  subst; apply dvalue_refines_refl.
Qed.

Lemma refine_eou_compat :
  forall {Pa : Params} (s s' t t' : EOU (@dvalue Pa)),
    equiv_eou_dvalue s s' ->
    equiv_eou_dvalue t t' ->
    refine_eou_dvalue s' t' ->
    refine_eou_dvalue s t.
Proof.
  intros Pa [] [] [] [] Hs Ht Href; cbn in *;
    try contradiction; trivial; subst; exact Href.
Qed.

(** ** 4. Closed [CE_Let] Expansion & Symbolic [(val, poison)] DAG Evaluator *)

Fixpoint lookup_let_expr (m : list (string * cert_expr)) (nm : string)
  {struct m} : option cert_expr :=
  match m with
  | [] => None
  | (k, v) :: rest => if String.eqb k nm then Some v else lookup_let_expr rest nm
  end.

Section ExpandLetBinds.
  Variable exp_e : list (string * cert_expr) -> cert_expr -> cert_expr.

  Fixpoint expand_let_binds (cur_m : list (string * cert_expr))
                            (xs : list (string * cert_expr))
    {struct xs} : list (string * cert_expr) :=
    match xs with
    | [] => cur_m
    | (bnm, be) :: rest =>
        let exp_be := exp_e cur_m be in
        expand_let_binds ((bnm, exp_be) :: cur_m) rest
    end.
End ExpandLetBinds.

Fixpoint expand_lets_with (m : list (string * cert_expr)) (e : cert_expr)
  {struct e} : cert_expr :=
  match e with
  | CE_BvConst w v => CE_BvConst w v
  | CE_Poison w => CE_Poison w
  | CE_Var nm w =>
      match lookup_let_expr m nm with
      | Some rep => rep
      | None => CE_Var nm w
      end
  | CE_BinOp op w fl l r =>
      CE_BinOp op w fl (expand_lets_with m l) (expand_lets_with m r)
  | CE_ICmp pr ss w l r =>
      CE_ICmp pr ss w (expand_lets_with m l) (expand_lets_with m r)
  | CE_Cast k fw tw fl o =>
      CE_Cast k fw tw fl (expand_lets_with m o)
  | CE_Select w c t f =>
      CE_Select w (expand_lets_with m c) (expand_lets_with m t) (expand_lets_with m f)
  | CE_Freeze w o =>
      CE_Freeze w (expand_lets_with m o)
  | CE_Let bs body =>
      expand_lets_with (expand_let_binds expand_lets_with m bs) body
  end.

Definition expand_lets (e : cert_expr) : cert_expr :=
  expand_lets_with [] e.

(** *** Bounded-Node [CE_Let] Expansion ([F-63] DoS Protection) *)

Definition default_let_expand_budget : nat := N.to_nat 8192%N.
Definition norm_let_expand_budget : nat := N.to_nat 4096%N.
#[local] Opaque default_let_expand_budget norm_let_expand_budget.

Fixpoint consume_fuel (cost fuel : nat) {struct cost} : option nat :=
  match cost with
  | O => Some fuel
  | S c' =>
      match fuel with
      | O => None
      | S f' => consume_fuel c' f'
      end
  end.

Definition sized_let_map : Type := list (string * (cert_expr * nat)).

Definition strip_let_sizes (ms : sized_let_map) : list (string * cert_expr) :=
  List.map (fun '(k, (ce, _)) => (k, ce)) ms.

Fixpoint lookup_let_sized (ms : sized_let_map) (nm : string)
  {struct ms} : option (cert_expr * nat) :=
  match ms with
  | [] => None
  | (k, vp) :: rest =>
      if String.eqb k nm then Some vp else lookup_let_sized rest nm
  end.

Lemma lookup_let_sized_strip : forall ms nm,
  option_map fst (lookup_let_sized ms nm) = lookup_let_expr (strip_let_sizes ms) nm.
Proof.
  induction ms as [| [k [ce sz]] rest IH]; intros nm; [reflexivity |].
  cbn; destruct (String.eqb k nm); [reflexivity | exact (IH nm)].
Qed.

Section ExpandLetBindsFueled.
  Variable exp_f : sized_let_map -> cert_expr -> nat -> option (cert_expr * nat * nat).

  Fixpoint expand_let_binds_fueled
    (cur_ms : sized_let_map) (xs : list (string * cert_expr)) (fuel : nat)
    {struct xs} : option (sized_let_map * nat) :=
    match xs with
    | [] => Some (cur_ms, fuel)
    | (bnm, be) :: rest =>
        match exp_f cur_ms be fuel with
        | Some (ebe, bsz, f1) =>
            expand_let_binds_fueled ((bnm, (ebe, bsz)) :: cur_ms) rest f1
        | None => None
        end
    end.
End ExpandLetBindsFueled.

Fixpoint expand_lets_fueled_with
  (ms : sized_let_map) (e : cert_expr) (fuel : nat)
  {struct e} : option (cert_expr * nat * nat) :=
  match e with
  | CE_BvConst w v =>
      match fuel with
      | O => None
      | S f1 => Some (CE_BvConst w v, 1%nat, f1)
      end
  | CE_Poison w =>
      match fuel with
      | O => None
      | S f1 => Some (CE_Poison w, 1%nat, f1)
      end
  | CE_Var nm w =>
      match lookup_let_sized ms nm with
      | Some (rep, rsz) =>
          match consume_fuel rsz fuel with
          | Some f1 => Some (rep, rsz, f1)
          | None => None
          end
      | None =>
          match fuel with
          | O => None
          | S f1 => Some (CE_Var nm w, 1%nat, f1)
          end
      end
  | CE_BinOp op w fl l r =>
      match fuel with
      | O => None
      | S f1 =>
          match expand_lets_fueled_with ms l f1 with
          | Some (el, sl, f2) =>
              match expand_lets_fueled_with ms r f2 with
              | Some (er, sr, f3) =>
                  Some (CE_BinOp op w fl el er, S (sl + sr), f3)
              | None => None
              end
          | None => None
          end
      end
  | CE_ICmp pr ss w l r =>
      match fuel with
      | O => None
      | S f1 =>
          match expand_lets_fueled_with ms l f1 with
          | Some (el, sl, f2) =>
              match expand_lets_fueled_with ms r f2 with
              | Some (er, sr, f3) =>
                  Some (CE_ICmp pr ss w el er, S (sl + sr), f3)
              | None => None
              end
          | None => None
          end
      end
  | CE_Cast k fw tw fl o =>
      match fuel with
      | O => None
      | S f1 =>
          match expand_lets_fueled_with ms o f1 with
          | Some (eo, so, f2) =>
              Some (CE_Cast k fw tw fl eo, S so, f2)
          | None => None
          end
      end
  | CE_Select w c t f =>
      match fuel with
      | O => None
      | S f1 =>
          match expand_lets_fueled_with ms c f1 with
          | Some (ec, sc, f2) =>
              match expand_lets_fueled_with ms t f2 with
              | Some (et, st, f3) =>
                  match expand_lets_fueled_with ms f f3 with
                  | Some (ef, sf, f4) =>
                      Some (CE_Select w ec et ef, S (sc + st + sf), f4)
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      end
  | CE_Freeze w o =>
      match fuel with
      | O => None
      | S f1 =>
          match expand_lets_fueled_with ms o f1 with
          | Some (eo, so, f2) =>
              Some (CE_Freeze w eo, S so, f2)
          | None => None
          end
      end
  | CE_Let bs body =>
      match expand_let_binds_fueled expand_lets_fueled_with ms bs fuel with
      | Some (ms', f1) => expand_lets_fueled_with ms' body f1
      | None => None
      end
  end.

Definition expand_lets_fueled (budget : nat) (e : cert_expr) : option cert_expr :=
  match expand_lets_fueled_with [] e budget with
  | Some (out, _, _) => Some out
  | None => None
  end.

Lemma expand_lets_fueled_with_eq :
  forall e ms fuel out sz fuel',
    expand_lets_fueled_with ms e fuel = Some (out, sz, fuel') ->
    out = expand_lets_with (strip_let_sizes ms) e.
Proof.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body IHbs IHb ] using cert_expr_ind_nested;
    intros ms fuel out sz fuel' Hexp; cbn [expand_lets_fueled_with expand_lets_with] in Hexp |- *.
  - destruct fuel; [discriminate Hexp | inversion Hexp; reflexivity].
  - destruct fuel; [discriminate Hexp | inversion Hexp; reflexivity].
  - pose proof (lookup_let_sized_strip ms nm) as Hlk.
    destruct (lookup_let_sized ms nm) as [[rep rsz] |]; cbn in Hlk; rewrite <- Hlk.
    + destruct (consume_fuel rsz fuel); [inversion Hexp; reflexivity | discriminate Hexp].
    + destruct fuel; [discriminate Hexp | inversion Hexp; reflexivity].
  - destruct fuel as [| f1]; [discriminate Hexp |].
    destruct (expand_lets_fueled_with ms l f1) as [[[el sl] f2] |] eqn:El; [| discriminate Hexp].
    destruct (expand_lets_fueled_with ms r f2) as [[[er sr] f3] |] eqn:Er; [| discriminate Hexp].
    inversion Hexp; subst; f_equal; [exact (IHl _ _ _ _ _ El) | exact (IHr _ _ _ _ _ Er)].
  - destruct fuel as [| f1]; [discriminate Hexp |].
    destruct (expand_lets_fueled_with ms l f1) as [[[el sl] f2] |] eqn:El; [| discriminate Hexp].
    destruct (expand_lets_fueled_with ms r f2) as [[[er sr] f3] |] eqn:Er; [| discriminate Hexp].
    inversion Hexp; subst; f_equal; [exact (IHl _ _ _ _ _ El) | exact (IHr _ _ _ _ _ Er)].
  - destruct fuel as [| f1]; [discriminate Hexp |].
    destruct (expand_lets_fueled_with ms o f1) as [[[eo so] f2] |] eqn:Eo; [| discriminate Hexp].
    inversion Hexp; subst; f_equal; exact (IHo _ _ _ _ _ Eo).
  - destruct fuel as [| f1]; [discriminate Hexp |].
    destruct (expand_lets_fueled_with ms c f1) as [[[ec sc] f2] |] eqn:Ec; [| discriminate Hexp].
    destruct (expand_lets_fueled_with ms t f2) as [[[et st] f3] |] eqn:Et; [| discriminate Hexp].
    destruct (expand_lets_fueled_with ms f f3) as [[[ef sf] f4] |] eqn:Ef; [| discriminate Hexp].
    inversion Hexp; subst; f_equal;
      [exact (IHc _ _ _ _ _ Ec) | exact (IHt _ _ _ _ _ Et) | exact (IHf _ _ _ _ _ Ef)].
  - destruct fuel as [| f1]; [discriminate Hexp |].
    destruct (expand_lets_fueled_with ms o f1) as [[[eo so] f2] |] eqn:Eo; [| discriminate Hexp].
    inversion Hexp; subst; f_equal; exact (IHo _ _ _ _ _ Eo).
  - destruct (expand_let_binds_fueled expand_lets_fueled_with ms bs fuel)
      as [[ms' f1] |] eqn:Ebs; [| discriminate Hexp].
    assert (Hbs_eq : strip_let_sizes ms' = expand_let_binds expand_lets_with (strip_let_sizes ms) bs).
    { clear Hexp; revert ms fuel ms' f1 Ebs; induction IHbs as [| [bnm be] rest Hbe _ IHrest];
        intros cur_ms f ms_out f_out Ebs; cbn in Ebs |- *.
      - inversion Ebs; reflexivity.
      - destruct (expand_lets_fueled_with cur_ms be f) as [[[ebe bsz] f_mid] |] eqn:Ebe;
          [| discriminate Ebs].
        pose proof (Hbe _ _ _ _ _ Ebe) as Hebe; subst ebe.
        exact (IHrest ((bnm, (expand_lets_with (strip_let_sizes cur_ms) be, bsz)) :: cur_ms)
                      f_mid ms_out f_out Ebs). }
    rewrite <- Hbs_eq; exact (IHb _ _ _ _ _ Hexp).
Qed.

Lemma expand_lets_fueled_eq :
  forall budget e out,
    expand_lets_fueled budget e = Some out ->
    out = expand_lets e.
Proof.
  intros budget e out H; unfold expand_lets_fueled in H.
  destruct (expand_lets_fueled_with [] e budget) as [[[o sz] f'] |] eqn:Eo; [| discriminate H].
  inversion H; subst o; exact (expand_lets_fueled_with_eq e [] budget out sz f' Eo).
Qed.

(** Non-dependent [freeze] choice oracle keyed by bitwidth and closed operand
    expression, yielding an integer representative mapped via [@Integers.repr]. *)
Definition freeze_oracle : Type := positive -> cert_expr -> Z.

Definition default_freeze_oracle : freeze_oracle :=
  fun _ _ => 0%Z.

Definition param_env (Pa : Params) : Type := string -> option (@dvalue Pa).

Definition let_val_env (Pa : Params) : Type :=
  list (string * (@dvalue Pa * cert_expr)).

Fixpoint lookup_let_val {Pa : Params} (lenv : let_val_env Pa) (nm : string)
  {struct lenv} : option (@dvalue Pa) :=
  match lenv with
  | [] => None
  | (k, (dv, _)) :: rest =>
      if String.eqb k nm then Some dv else lookup_let_val rest nm
  end.

Definition let_val_exprs {Pa : Params} (lenv : let_val_env Pa)
  : list (string * cert_expr) :=
  List.map (fun '(k, (_, ce)) => (k, ce)) lenv.

Definition check_scalar_width {Pa : Params} (w : positive) (dv : @dvalue Pa)
  : EOU (@dvalue Pa) :=
  match dv with
  | DVALUE_Base (@DVALUE_I _ sz _) =>
      if Pos.eqb sz w then raise_ret dv
      else raise_error "scalar width mismatch"
  | DVALUE_Base DVALUE_Poison =>
      raise_ret (DVALUE_Base DVALUE_Poison)
  | _ =>
      raise_error "non-integer scalar value"
  end.

Lemma check_scalar_width_ok : forall {Pa : Params} w (dv : @dvalue Pa),
  wf_scalar_dvalue w dv -> check_scalar_width w dv = raise_ret dv.
Proof.
  intros Pa w dv [-> | [i ->]]; cbn; [reflexivity |].
  rewrite Pos.eqb_refl; reflexivity.
Qed.

Lemma check_scalar_width_inv : forall {Pa : Params} w (dv out : @dvalue Pa),
  check_scalar_width w dv = raise_ret out ->
  out = dv /\ wf_scalar_dvalue w out.
Proof.
  intros Pa w [db | | ] out H; cbn in H; try discriminate.
  destruct db as [| sz i | | | | | |]; try discriminate.
  - destruct (Pos.eqb sz w) eqn:E; [| discriminate].
    apply Pos.eqb_eq in E; subst sz.
    inversion H; subst; split; [reflexivity | right; exists i; reflexivity].
  - inversion H; subst; split; [reflexivity | left; reflexivity].
Qed.

Definition eou_bind {A B : Type} (m : EOU A) (k : A -> EOU B) : EOU B :=
  match m with
  | raise_oom s => raise_oom s
  | raise_ub s => raise_ub s
  | raise_error s => raise_error s
  | raise_ret x => k x
  end.

Section EvalLetBinds.
  Context {Pa : Params}.
  Variable ev_e : let_val_env Pa -> cert_expr -> EOU (@dvalue Pa).

  Fixpoint eval_let_binds (cur_env : let_val_env Pa)
                          (xs : list (string * cert_expr))
    {struct xs} : EOU (let_val_env Pa) :=
    match xs with
    | [] => raise_ret cur_env
    | (bnm, be) :: rest =>
        let exp_be := expand_lets_with (let_val_exprs cur_env) be in
        eou_bind (ev_e cur_env be) (fun dv =>
        eval_let_binds ((bnm, (dv, exp_be)) :: cur_env) rest)
    end.
End EvalLetBinds.

Fixpoint eval_cert_expr {Pa : Params}
  (penv : param_env Pa) (lenv : let_val_env Pa) (foracle : freeze_oracle)
  (e : cert_expr) {struct e} : EOU (@dvalue Pa) :=
  match e with
  | CE_BvConst w val =>
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N val))))
  | CE_Poison _ =>
      raise_ret (DVALUE_Base DVALUE_Poison)
  | CE_Var nm w =>
      match lookup_let_val lenv nm with
      | Some dv => check_scalar_width w dv
      | None =>
          match penv nm with
          | Some dv => check_scalar_width w dv
          | None => raise_error ("unbound variable: " ++ nm)%string
          end
      end
  | CE_BinOp op _ fl l r =>
      eou_bind (eval_cert_expr penv lenv foracle l) (fun vl =>
      eou_bind (eval_cert_expr penv lenv foracle r) (fun vr =>
      @eval_iop Pa (cert_to_ibinop op fl) vl vr))
  | CE_ICmp pr ss _ l r =>
      eou_bind (eval_cert_expr penv lenv foracle l) (fun vl =>
      eou_bind (eval_cert_expr penv lenv foracle r) (fun vr =>
      @eval_icmp Pa ss (cert_to_icmp pr) vl vr))
  | CE_Cast k fw tw fl o =>
      eou_bind (eval_cert_expr penv lenv foracle o) (fun vo =>
      @convert_pure Pa (cert_to_pure_conv k fl)
        (DTYPE_Base (DTYPE_I fw)) vo (DTYPE_Base (DTYPE_I tw)))
  | CE_Select w c t f =>
      eou_bind (eval_cert_expr penv lenv foracle c) (fun vc =>
      eou_bind (eval_cert_expr penv lenv foracle t) (fun vt =>
      eou_bind (eval_cert_expr penv lenv foracle f) (fun vf =>
      @eval_select Pa vc (DTYPE_Base (DTYPE_I w)) vt vf)))
  | CE_Freeze w o =>
      let key := expand_lets_with (let_val_exprs lenv) o in
      eou_bind (eval_cert_expr penv lenv foracle o) (fun vo =>
      match vo with
      | DVALUE_Base DVALUE_Poison =>
          raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (foracle w key))))
      | _ => raise_ret vo
      end)
  | CE_Let bs body =>
      eou_bind
        (eval_let_binds (fun ce x => eval_cert_expr penv ce foracle x) lenv bs)
        (fun lenv' => eval_cert_expr penv lenv' foracle body)
  end.

Definition eval_closed_cert_expr {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle) (e : cert_expr)
  : EOU (@dvalue Pa) :=
  eval_cert_expr penv [] foracle e.

(** *** 4.1 Explicit Poison-Divisor UB and Out-of-Bounds Shift Poison Theorems *)

Definition is_div_or_rem_op (op : cert_binop) : bool :=
  match op with
  | CB_UDiv | CB_SDiv | CB_URem | CB_SRem => true
  | _ => false
  end.

Theorem eval_cert_div_rem_poison_rhs_ub :
  forall {Pa : Params} penv lenv foracle op w fl lhs rhs vl,
    is_div_or_rem_op op = true ->
    wf_scalar_dvalue w vl ->
    eval_cert_expr penv lenv foracle lhs = raise_ret vl ->
    eval_cert_expr penv lenv foracle rhs = raise_ret (DVALUE_Base DVALUE_Poison) ->
    exists msg, eval_cert_expr penv lenv foracle (CE_BinOp op w fl lhs rhs) = raise_ub msg.
Proof.
  intros Pa penv lenv foracle op w fl lhs rhs vl Hop Hvl Hl Hr.
  cbn [eval_cert_expr]; rewrite Hl, Hr; cbn [eou_bind].
  destruct Hvl as [-> | [i1 ->]];
    destruct op; cbn in Hop; try discriminate;
    cbn; eexists; reflexivity.
Qed.

Definition is_shift_op (op : cert_binop) : bool :=
  match op with
  | CB_Shl | CB_LShr | CB_AShr => true
  | _ => false
  end.

Theorem eval_cert_shift_oob_poison :
  forall {Pa : Params} penv lenv foracle op w fl lhs rhs
         (i1 i2 : @Integers.bit_int w),
    is_shift_op op = true ->
    (@Integers.unsigned w i2 >= Z.pos w)%Z ->
    eval_cert_expr penv lenv foracle lhs = raise_ret (DVALUE_Base (@DVALUE_I Pa w i1)) ->
    eval_cert_expr penv lenv foracle rhs = raise_ret (DVALUE_Base (@DVALUE_I Pa w i2)) ->
    eval_cert_expr penv lenv foracle (CE_BinOp op w fl lhs rhs) =
    raise_ret (DVALUE_Base DVALUE_Poison).
Proof.
  intros Pa penv lenv foracle op w fl lhs rhs i1 i2 Hsh Hoob Hl Hr.
  cbn [eval_cert_expr]; rewrite Hl, Hr; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  assert (Hge : (@Integers.unsigned w i2 >=? Z.pos w)%Z = true)
    by (apply Z.geb_le; lia).
  destruct op; cbn in Hsh; try discriminate;
    unfold cert_to_ibinop, eval_int_op; cbn;
    rewrite Hge; cbn; reflexivity.
Qed.

(** *** 4.2 Semantic Width-Typing & Totality on Well-Typed Environments *)

Fixpoint wt_cert_expr (let_env : list (string * positive)) (e : cert_expr)
  {struct e} : bool :=
  match e with
  | CE_BvConst _ _ => true
  | CE_Poison _ => true
  | CE_Var nm w =>
      match lookup_let_width let_env nm with
      | Some bw => Pos.eqb bw w
      | None => negb (starts_with_dollar nm)
      end
  | CE_BinOp op w fl l r =>
      wf_binop_flags_for op fl &&
      wt_cert_expr let_env l &&
      wt_cert_expr let_env r &&
      Pos.eqb (cert_expr_bit_width l) w &&
      Pos.eqb (cert_expr_bit_width r) w
  | CE_ICmp _ _ w l r =>
      wt_cert_expr let_env l &&
      wt_cert_expr let_env r &&
      Pos.eqb (cert_expr_bit_width l) w &&
      Pos.eqb (cert_expr_bit_width r) w
  | CE_Cast k fw tw fl o =>
      match k with
      | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw fl) && negb (ccf_nsw fl)
      | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg fl) && negb (ccf_nuw fl) && negb (ccf_nsw fl)
      | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg fl)
      end &&
      wt_cert_expr let_env o &&
      Pos.eqb (cert_expr_bit_width o) fw
  | CE_Select w c t f =>
      wt_cert_expr let_env c &&
      wt_cert_expr let_env t &&
      wt_cert_expr let_env f &&
      Pos.eqb (cert_expr_bit_width c) 1%positive &&
      Pos.eqb (cert_expr_bit_width t) w &&
      Pos.eqb (cert_expr_bit_width f) w
  | CE_Freeze w o =>
      wt_cert_expr let_env o &&
      Pos.eqb (cert_expr_bit_width o) w
  | CE_Let bs body =>
      match wf_let_binds_step wt_cert_expr let_env [] bs with
      | Some env' => wt_cert_expr env' body
      | None => false
      end
  end.

Lemma wf_implies_wt_cert_expr : forall e let_env,
  wf_cert_expr let_env e = true -> wt_cert_expr let_env e = true.
Proof.
  induction e as
    [ w v
    | w
    | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body IHbs IHb ] using cert_expr_ind_nested;
    intros let_env Hwf; cbn [wf_cert_expr wt_cert_expr] in Hwf |- *; auto.
  - rewrite !andb_true_iff in Hwf; destruct Hwf as ([_ _] & Hlk); exact Hlk.
  - rewrite !andb_true_iff in Hwf; rewrite !andb_true_iff.
    destruct Hwf as (((((_ & Hfl) & Hl) & Hr) & Hwl) & Hwr).
    repeat split; auto.
  - rewrite !andb_true_iff in Hwf; rewrite !andb_true_iff.
    destruct Hwf as ((((_ & Hl) & Hr) & Hwl) & Hwr).
    repeat split; auto.
  - rewrite !andb_true_iff in Hwf; rewrite !andb_true_iff.
    destruct Hwf as ((Hsp & Ho) & Hwo).
    unfold wf_cast_spec in Hsp; rewrite !andb_true_iff in Hsp.
    destruct Hsp as ([_ _] & Hk).
    repeat split; auto.
  - rewrite !andb_true_iff in Hwf; rewrite !andb_true_iff.
    destruct Hwf as ((((((_ & Hc) & Ht) & Hf) & Hwc) & Hwt) & Hwf0).
    repeat split; auto.
  - rewrite !andb_true_iff in Hwf; rewrite !andb_true_iff.
    destruct Hwf as ((_ & Ho) & Hwo); split; auto.
  - destruct bs as [| b0 br]; [discriminate |]; cbn [wf_cert_expr] in Hwf.
    assert (Hstep :
      forall xs env seen env',
        Forall (fun p => forall le, wf_cert_expr le (snd p) = true ->
                                    wt_cert_expr le (snd p) = true) xs ->
        wf_let_binds_step wf_cert_expr env seen xs = Some env' ->
        wf_let_binds_step wt_cert_expr env seen xs = Some env').
    { induction xs as [| [bnm be] rx IHrx]; intros env seen env' HF Hs;
        cbn [wf_let_binds_step] in Hs |- *; [exact Hs |].
      inversion HF as [| ? ? Hbe HFrx]; subst; cbn [snd] in Hbe.
      destruct (is_dollar_let_name bnm && negb (string_in_list bnm seen)) eqn:Hpre;
        cbn [wf_let_binds_step] in Hs |- *; [| discriminate].
      destruct (wf_cert_expr env be) eqn:Hwf_be; [| discriminate].
      rewrite (Hbe env Hwf_be); exact (IHrx _ _ _ HFrx Hs). }
    destruct (wf_let_binds_step wf_cert_expr let_env [] (b0 :: br)) as [env' |] eqn:Hs;
      [| discriminate].
    rewrite (Hstep (b0 :: br) let_env [] env' IHbs Hs).
    exact (IHb env' Hwf).
Qed.

Lemma eval_iop_wf_scalar :
  forall {Pa : Params} op fl w (vl vr : @dvalue Pa),
    wf_scalar_dvalue w vl ->
    wf_scalar_dvalue w vr ->
    (exists msg, @eval_iop Pa (cert_to_ibinop op fl) vl vr = raise_ub msg) \/
    (exists vout, @eval_iop Pa (cert_to_ibinop op fl) vl vr = raise_ret vout /\
                  wf_scalar_dvalue w vout).
Proof.
  intros Pa op fl w vl vr [-> | [il ->]] [-> | [ir ->]].
  - destruct op; cbn;
      try (left; eexists; reflexivity);
      (right; exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | left; reflexivity]).
  - destruct op; cbn;
      try (right; exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | left; reflexivity]);
      (destruct (Z.eq_dec (@Integers.signed w ir) (-1)%Z); cbn;
       [left; eexists; reflexivity | right; exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | left; reflexivity]]).
  - destruct op; cbn;
      try (left; eexists; reflexivity);
      (right; exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | left; reflexivity]).
  - unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct op; unfold cert_to_ibinop, eval_int_op; cbn;
      repeat match goal with
             | |- context [if ?b then _ else _] => destruct b
             end;
      cbn;
      try (left; eexists; reflexivity);
      (right; eexists; split; [reflexivity | first [left; reflexivity | right; eexists; reflexivity]]).
Qed.

Lemma eval_icmp_wf_scalar :
  forall {Pa : Params} ss pr w (vl vr : @dvalue Pa),
    wf_scalar_dvalue w vl ->
    wf_scalar_dvalue w vr ->
    exists vout,
      @eval_icmp Pa ss (cert_to_icmp pr) vl vr = raise_ret vout /\
      wf_scalar_dvalue 1%positive vout.
Proof.
  intros Pa ss pr w vl vr [-> | [il ->]] [-> | [ir ->]].
  - exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | left; reflexivity].
  - exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | left; reflexivity].
  - exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | left; reflexivity].
  - unfold eval_icmp; rewrite eval_icmp_base_same_width.
    destruct pr; unfold cert_to_icmp, eval_int_icmp;
      cbn - [andb negb msamesign mcmp mcmpu];
      repeat match goal with
             | |- context [if ?b then _ else _] => destruct b
             end;
      cbn; (eexists; split; [reflexivity | first [left; reflexivity | right; eexists; reflexivity]]).
Qed.

Lemma eval_cast_wf_scalar :
  forall {Pa : Params} k fw tw fl (vo : @dvalue Pa),
    match k with
    | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg fl) && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg fl)
    end = true ->
    wf_scalar_dvalue fw vo ->
    exists vout,
      @convert_pure Pa (cert_to_pure_conv k fl)
        (DTYPE_Base (DTYPE_I fw)) vo (DTYPE_Base (DTYPE_I tw)) = raise_ret vout /\
      wf_scalar_dvalue tw vout.
Proof.
  intros Pa k fw tw fl vo Hk [-> | [io ->]].
  - destruct k; cbn; exists (DVALUE_Base DVALUE_Poison);
      (split; [reflexivity | left; reflexivity]).
  - destruct k; cbn - [andb Pos.ltb Pos.eqb] in Hk |- *; rewrite !andb_true_iff in Hk.
    + destruct Hk as ([Hlt _] & _); rewrite Pos.eqb_refl, Hlt; cbn.
      destruct (ccf_nneg fl && (@Integers.signed fw io <? 0)%Z); cbn;
        [eexists; split; [reflexivity | left; reflexivity]
        | eexists; split; [reflexivity | right; eexists; reflexivity]].
    + destruct Hk as (([Hlt _] & _) & _); rewrite Pos.eqb_refl, Hlt; cbn.
      eexists; split; [reflexivity | right; eexists; reflexivity].
    + destruct Hk as [Hlt _]; rewrite Pos.eqb_refl, Hlt; cbn.
      match goal with |- context [if ?b then _ else _] => destruct b end; cbn;
        [eexists; split; [reflexivity | left; reflexivity]
        | eexists; split; [reflexivity | right; eexists; reflexivity]].
Qed.

Lemma eval_select_wf_scalar :
  forall {Pa : Params} w (vc vt vf : @dvalue Pa),
    wf_scalar_dvalue 1%positive vc ->
    wf_scalar_dvalue w vt ->
    wf_scalar_dvalue w vf ->
    exists vout,
      @eval_select Pa vc (DTYPE_Base (DTYPE_I w)) vt vf = raise_ret vout /\
      wf_scalar_dvalue w vout.
Proof.
  intros Pa w vc vt vf [-> | [ic ->]] Hvt Hvf; cbn.
  - exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | left; reflexivity].
  - destruct (@Integers.unsigned 1 ic =? 1)%Z;
      [exists vt; split; [reflexivity | exact Hvt]
      | exists vf; split; [reflexivity | exact Hvf]].
Qed.

Definition wf_let_val_env {Pa : Params}
  (let_widths : list (string * positive)) (lenv : let_val_env Pa) : Prop :=
  forall nm,
    match lookup_let_width let_widths nm, lookup_let_val lenv nm with
    | Some bw, Some dv => wf_scalar_dvalue bw dv
    | None, None => True
    | _, _ => False
    end.

Section CollectBindVars.
  Variable cfv : list string -> cert_expr -> list (string * positive).

  Fixpoint collect_bind_vars (cur_b : list string) (xs : list (string * cert_expr))
    {struct xs} : list string * list (string * positive) :=
    match xs with
    | [] => (cur_b, [])
    | (bnm, be) :: rest =>
        let vs_be := cfv cur_b be in
        let '(final_b, vs_rest) := collect_bind_vars (bnm :: cur_b) rest in
        (final_b, vs_be ++ vs_rest)
    end.
End CollectBindVars.

Fixpoint collect_free_vars (bound : list string) (e : cert_expr)
  {struct e} : list (string * positive) :=
  match e with
  | CE_BvConst _ _ | CE_Poison _ => []
  | CE_Var nm w =>
      if string_in_list nm bound then [] else [(nm, w)]
  | CE_BinOp _ _ _ l r | CE_ICmp _ _ _ l r =>
      collect_free_vars bound l ++ collect_free_vars bound r
  | CE_Cast _ _ _ _ o | CE_Freeze _ o =>
      collect_free_vars bound o
  | CE_Select _ c t f =>
      collect_free_vars bound c ++ collect_free_vars bound t ++ collect_free_vars bound f
  | CE_Let bs body =>
      let '(bound', vs_bs) := collect_bind_vars collect_free_vars bound bs in
      vs_bs ++ collect_free_vars bound' body
  end.

Definition wf_param_env_for {Pa : Params}
  (vars : list (string * positive)) (penv : param_env Pa) : Prop :=
  forall nm w,
    In (nm, w) vars ->
    exists dv, penv nm = Some dv /\ wf_scalar_dvalue w dv.

Lemma string_in_list_spec : forall s xs,
  string_in_list s xs = true <-> In s xs.
Proof.
  intros s xs; induction xs as [| x rest IH]; cbn; [split; [discriminate | contradiction] |].
  destruct (String.eqb s x) eqn:E.
  - apply String.eqb_eq in E; subst; split; [intros _; left; reflexivity | intros _; reflexivity].
  - apply String.eqb_neq in E; destruct IH as [IH1 IH2]; split.
    + intros H; right; exact (IH1 H).
    + intros [Hx | H]; [exfalso; apply E; symmetry; exact Hx | exact (IH2 H)].
Qed.

Lemma lookup_let_width_in_dom : forall le nm,
  lookup_let_width le nm = None <-> ~ In nm (List.map fst le).
Proof.
  induction le as [| [k w] rest IH]; intros nm; cbn.
  - split; [intros _ [] | intros _; reflexivity].
  - destruct (String.eqb k nm) eqn:E.
    + apply String.eqb_eq in E; subst; split;
        [discriminate | intros H; exfalso; apply H; left; reflexivity].
    + apply String.eqb_neq in E; destruct (IH nm) as [IH1 IH2]; split.
      * intros Hnot [Hk | Hr]; [apply E, Hk | exact (IH1 Hnot Hr)].
      * intros Hnot; apply IH2; intros Hr; apply Hnot; right; exact Hr.
Qed.

Theorem eval_cert_expr_totality :
  forall {Pa : Params} (e : cert_expr) (let_widths : list (string * positive))
         (penv : param_env Pa) (lenv : let_val_env Pa) (foracle : freeze_oracle),
    wt_cert_expr let_widths e = true ->
    wf_let_val_env let_widths lenv ->
    wf_param_env_for (collect_free_vars (List.map fst let_widths) e) penv ->
    (exists msg, eval_cert_expr penv lenv foracle e = raise_ub msg) \/
    (exists vout, eval_cert_expr penv lenv foracle e = raise_ret vout /\
                  wf_scalar_dvalue (cert_expr_bit_width e) vout).
Proof.
  intros Pa e.
  induction e as
    [ w val
    | w
    | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body IHbs IHb ] using cert_expr_ind_nested;
    intros let_widths penv lenv foracle Hwt Hlenv Hpenv.
  - right; eexists; split; [reflexivity | right; eexists; reflexivity].
  - right; eexists; split; [reflexivity | left; reflexivity].
  - cbn [wt_cert_expr eval_cert_expr cert_expr_bit_width] in *.
    pose proof (Hlenv nm) as Hlnm.
    destruct (lookup_let_width let_widths nm) as [bw |] eqn:Hlw.
    + apply Pos.eqb_eq in Hwt; subst bw.
      destruct (lookup_let_val lenv nm) as [dv |]; [| contradiction].
      right; exists dv; split; [exact (check_scalar_width_ok w dv Hlnm) | exact Hlnm].
    + destruct (lookup_let_val lenv nm) as [dv |]; [contradiction |].
      cbn [collect_free_vars] in Hpenv.
      assert (Hnin : string_in_list nm (List.map fst let_widths) = false).
      { destruct (string_in_list nm (List.map fst let_widths)) eqn:Ein; [| reflexivity].
        apply string_in_list_spec in Ein.
        apply lookup_let_width_in_dom in Hlw; contradiction. }
      rewrite Hnin in Hpenv.
      destruct (Hpenv nm w (or_introl eq_refl)) as [dv [Hpm Hwfv]].
      rewrite Hpm; right; exists dv; split;
        [exact (check_scalar_width_ok w dv Hwfv) | exact Hwfv].
  - cbn [wt_cert_expr collect_free_vars eval_cert_expr cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hwt.
    destruct Hwt as ((((Hfl & Hwtl) & Hwtr) & Hwl) & Hwr).
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    assert (Hpl : wf_param_env_for (collect_free_vars (List.map fst let_widths) l) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars (List.map fst let_widths) r) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
    destruct (IHl _ penv lenv foracle Hwtl Hlenv Hpl) as [[msgl ->] | [vl [-> Hwfl]]];
      [left; exists msgl; reflexivity | cbn [eou_bind]].
    destruct (IHr _ penv lenv foracle Hwtr Hlenv Hpr) as [[msgr ->] | [vr [-> Hwfr]]];
      [left; exists msgr; reflexivity | cbn [eou_bind]].
    rewrite Hwl in Hwfl; rewrite Hwr in Hwfr.
    exact (eval_iop_wf_scalar op fl w vl vr Hwfl Hwfr).
  - cbn [wt_cert_expr collect_free_vars eval_cert_expr cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hwt.
    destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr).
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    assert (Hpl : wf_param_env_for (collect_free_vars (List.map fst let_widths) l) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars (List.map fst let_widths) r) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
    destruct (IHl _ penv lenv foracle Hwtl Hlenv Hpl) as [[msgl ->] | [vl [-> Hwfl]]];
      [left; exists msgl; reflexivity | cbn [eou_bind]].
    destruct (IHr _ penv lenv foracle Hwtr Hlenv Hpr) as [[msgr ->] | [vr [-> Hwfr]]];
      [left; exists msgr; reflexivity | cbn [eou_bind]].
    rewrite Hwl in Hwfl; rewrite Hwr in Hwfr.
    right; exact (eval_icmp_wf_scalar ss pr w vl vr Hwfl Hwfr).
  - cbn [wt_cert_expr collect_free_vars eval_cert_expr cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hwt.
    destruct Hwt as ((Hk & Hwto) & Hwo).
    apply Pos.eqb_eq in Hwo.
    destruct (IHo _ penv lenv foracle Hwto Hlenv Hpenv) as [[msgo ->] | [vo [-> Hwfo]]];
      [left; exists msgo; reflexivity | cbn [eou_bind]].
    rewrite Hwo in Hwfo.
    right; exact (eval_cast_wf_scalar k fw tw fl vo Hk Hwfo).
  - cbn [wt_cert_expr collect_free_vars eval_cert_expr cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hwt.
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hwc) & Hwt0) & Hwf0).
    apply Pos.eqb_eq in Hwc; apply Pos.eqb_eq in Hwt0; apply Pos.eqb_eq in Hwf0.
    assert (Hpc : wf_param_env_for (collect_free_vars (List.map fst let_widths) c) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpt : wf_param_env_for (collect_free_vars (List.map fst let_widths) t) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; left; exact Hx).
    assert (Hpf : wf_param_env_for (collect_free_vars (List.map fst let_widths) f) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; right; exact Hx).
    destruct (IHc _ penv lenv foracle Hwtc Hlenv Hpc) as [[msgc ->] | [vc [-> Hwfc]]];
      [left; exists msgc; reflexivity | cbn [eou_bind]].
    destruct (IHt _ penv lenv foracle Hwtt Hlenv Hpt) as [[msgt ->] | [vt [-> Hwft]]];
      [left; exists msgt; reflexivity | cbn [eou_bind]].
    destruct (IHf _ penv lenv foracle Hwtf Hlenv Hpf) as [[msgf ->] | [vf [-> Hwff]]];
      [left; exists msgf; reflexivity | cbn [eou_bind]].
    rewrite Hwc in Hwfc; rewrite Hwt0 in Hwft; rewrite Hwf0 in Hwff.
    right; exact (eval_select_wf_scalar w vc vt vf Hwfc Hwft Hwff).
  - cbn [wt_cert_expr collect_free_vars eval_cert_expr cert_expr_bit_width] in *.
    apply andb_true_iff in Hwt as [Hwto Hwo].
    apply Pos.eqb_eq in Hwo.
    destruct (IHo _ penv lenv foracle Hwto Hlenv Hpenv) as [[msgo ->] | [vo [-> Hwfo]]];
      [left; exists msgo; reflexivity | cbn [eou_bind]].
    rewrite Hwo in Hwfo.
    destruct Hwfo as [-> | [io ->]];
      (right; eexists; split; [reflexivity | right; eexists; reflexivity]).
  - cbn [wt_cert_expr collect_free_vars eval_cert_expr cert_expr_bit_width] in *.
    destruct (wf_let_binds_step wt_cert_expr let_widths [] bs) as [env' |] eqn:Hbs;
      [| discriminate].
    assert (Hstep :
      forall cur_lw seen cur_le,
        wf_let_binds_step wt_cert_expr cur_lw seen bs = Some env' ->
        wf_let_val_env cur_lw cur_le ->
        wf_param_env_for
          (let '(b', vs_xs) := collect_bind_vars collect_free_vars (List.map fst cur_lw) bs in
           vs_xs ++ collect_free_vars b' body) penv ->
        (exists msg,
           eval_let_binds (fun ce x => eval_cert_expr penv ce foracle x) cur_le bs =
           raise_ub msg) \/
        (exists lenv',
           eval_let_binds (fun ce x => eval_cert_expr penv ce foracle x) cur_le bs =
           raise_ret lenv' /\
           wf_let_val_env env' lenv' /\
           wf_param_env_for (collect_free_vars (List.map fst env') body) penv)).
    { clear Hbs Hpenv; induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_lw seen cur_le Hs Hcle Hcp; cbn [wf_let_binds_step] in Hs.
      - inversion Hs; subst cur_lw; cbn in Hcp.
        right; exists cur_le; repeat split; assumption.
      - cbn in IHbe.
        destruct (is_dollar_let_name bnm && negb (string_in_list bnm seen) &&
                  wt_cert_expr cur_lw be) eqn:Hok; [| discriminate].
        rewrite !andb_true_iff in Hok; destruct Hok as ([_ _] & Hwt_be).
        cbn [collect_bind_vars] in Hcp.
        destruct (collect_bind_vars collect_free_vars (bnm :: List.map fst cur_lw) rx)
          as [b_end vs_rx] eqn:Hbv.
        assert (Hp_be : wf_param_env_for (collect_free_vars (List.map fst cur_lw) be) penv).
        { intros x wx Hx; apply Hcp; rewrite <- app_assoc; apply in_app_iff; left; exact Hx. }
        cbn [eval_let_binds].
        destruct (IHbe cur_lw penv cur_le foracle Hwt_be Hcle Hp_be)
          as [[msg_be ->] | [dv_be [-> Hwf_dv]]];
          [left; exists msg_be; reflexivity | cbn [eou_bind]].
        apply (IHrx ((bnm, cert_expr_bit_width be) :: cur_lw) (bnm :: seen)
                    ((bnm, (dv_be, expand_lets_with (let_val_exprs cur_le) be)) :: cur_le) Hs).
        + intros q; cbn [lookup_let_width lookup_let_val].
          destruct (String.eqb bnm q); [exact Hwf_dv | exact (Hcle q)].
        + cbn [List.map fst]; rewrite Hbv.
          intros x wx Hx; apply Hcp; rewrite <- app_assoc; apply in_app_iff; right; exact Hx. }
    destruct (Hstep let_widths [] lenv Hbs Hlenv Hpenv)
      as [[msg ->] | [lenv' [-> [Hlenv' Hpenv']]]];
      [left; exists msg; reflexivity | cbn [eou_bind]].
    exact (IHb env' penv lenv' foracle Hwt Hlenv' Hpenv').
Qed.

Lemma eval_cert_expr_ret_wf_scalar :
  forall {Pa : Params} e let_widths penv lenv foracle vout,
    wt_cert_expr let_widths e = true ->
    eval_cert_expr penv lenv foracle e = raise_ret vout ->
    wf_scalar_dvalue (cert_expr_bit_width e) vout.
Proof.
  intros Pa e.
  induction e as
    [ w val
    | w
    | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ IHb ] using cert_expr_ind_nested;
    intros let_widths penv lenv foracle vout Hwt Hev.
  - cbn in Hev; inversion Hev; right; eexists; reflexivity.
  - cbn in Hev; inversion Hev; left; reflexivity.
  - cbn in Hev; destruct (lookup_let_val lenv nm) as [dv |].
    + exact (proj2 (check_scalar_width_inv w dv vout Hev)).
    + destruct (penv nm) as [dv |]; [| discriminate].
      exact (proj2 (check_scalar_width_inv w dv vout Hev)).
  - cbn [wt_cert_expr eval_cert_expr cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((((Hfl & Hwtl) & Hwtr) & Hwl) & Hwr).
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    destruct (eval_cert_expr penv lenv foracle l) as [| | | vl] eqn:El; [discriminate.. |].
    cbn [eou_bind] in Hev.
    destruct (eval_cert_expr penv lenv foracle r) as [| | | vr] eqn:Er; [discriminate.. |].
    cbn [eou_bind] in Hev.
    pose proof (IHl _ _ _ _ _ Hwtl El) as Hwfl; rewrite Hwl in Hwfl.
    pose proof (IHr _ _ _ _ _ Hwtr Er) as Hwfr; rewrite Hwr in Hwfr.
    destruct (eval_iop_wf_scalar op fl w vl vr Hwfl Hwfr)
      as [[msg Hub] | [v' [Hv' Hwf']]]; [congruence | congruence].
  - cbn [wt_cert_expr eval_cert_expr cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hwt; destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr).
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    destruct (eval_cert_expr penv lenv foracle l) as [| | | vl] eqn:El; [discriminate.. |].
    cbn [eou_bind] in Hev.
    destruct (eval_cert_expr penv lenv foracle r) as [| | | vr] eqn:Er; [discriminate.. |].
    cbn [eou_bind] in Hev.
    pose proof (IHl _ _ _ _ _ Hwtl El) as Hwfl; rewrite Hwl in Hwfl.
    pose proof (IHr _ _ _ _ _ Hwtr Er) as Hwfr; rewrite Hwr in Hwfr.
    destruct (eval_icmp_wf_scalar ss pr w vl vr Hwfl Hwfr) as [v' [Hv' Hwf']]; congruence.
  - cbn [wt_cert_expr eval_cert_expr cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((Hk & Hwto) & Hwo).
    apply Pos.eqb_eq in Hwo.
    destruct (eval_cert_expr penv lenv foracle o) as [| | | vo] eqn:Eo; [discriminate.. |].
    cbn [eou_bind] in Hev.
    pose proof (IHo _ _ _ _ _ Hwto Eo) as Hwfo; rewrite Hwo in Hwfo.
    destruct (eval_cast_wf_scalar k fw tw fl vo Hk Hwfo) as [v' [Hv' Hwf']]; congruence.
  - cbn [wt_cert_expr eval_cert_expr cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hwt.
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hwc) & Hwt0) & Hwf0).
    apply Pos.eqb_eq in Hwc; apply Pos.eqb_eq in Hwt0; apply Pos.eqb_eq in Hwf0.
    destruct (eval_cert_expr penv lenv foracle c) as [| | | vc] eqn:Ec; [discriminate.. |].
    cbn [eou_bind] in Hev.
    destruct (eval_cert_expr penv lenv foracle t) as [| | | vt] eqn:Et; [discriminate.. |].
    cbn [eou_bind] in Hev.
    destruct (eval_cert_expr penv lenv foracle f) as [| | | vf] eqn:Ef; [discriminate.. |].
    cbn [eou_bind] in Hev.
    pose proof (IHc _ _ _ _ _ Hwtc Ec) as Hwfc; rewrite Hwc in Hwfc.
    pose proof (IHt _ _ _ _ _ Hwtt Et) as Hwft; rewrite Hwt0 in Hwft.
    pose proof (IHf _ _ _ _ _ Hwtf Ef) as Hwff; rewrite Hwf0 in Hwff.
    destruct (eval_select_wf_scalar w vc vt vf Hwfc Hwft Hwff) as [v' [Hv' Hwf']]; congruence.
  - cbn [wt_cert_expr eval_cert_expr cert_expr_bit_width] in *.
    apply andb_true_iff in Hwt as [Hwto Hwo]; apply Pos.eqb_eq in Hwo.
    destruct (eval_cert_expr penv lenv foracle o) as [| | | vo] eqn:Eo; [discriminate.. |].
    cbn [eou_bind] in Hev.
    pose proof (IHo _ _ _ _ _ Hwto Eo) as Hwfo; rewrite Hwo in Hwfo.
    destruct Hwfo as [-> | [io ->]]; inversion Hev; subst; right; eexists; reflexivity.
  - cbn [wt_cert_expr eval_cert_expr cert_expr_bit_width] in *.
    destruct (wf_let_binds_step wt_cert_expr let_widths [] bs) as [env' |] eqn:Hbs;
      [| discriminate].
    destruct (eval_let_binds (fun ce x => eval_cert_expr penv ce foracle x) lenv bs)
      as [| | | lenv']; [discriminate.. |].
    cbn [eou_bind] in Hev.
    exact (IHb env' penv lenv' foracle vout Hwt Hev).
Qed.


(** ** 5. Closed [CE_Let] DAG Expansion & Exact Evaluation Equivalence *)

Fixpoint is_let_free_expr (e : cert_expr) : bool :=
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ => true
  | CE_BinOp _ _ _ l r | CE_ICmp _ _ _ l r =>
      is_let_free_expr l && is_let_free_expr r
  | CE_Cast _ _ _ _ o | CE_Freeze _ o =>
      is_let_free_expr o
  | CE_Select _ c t f =>
      is_let_free_expr c && is_let_free_expr t && is_let_free_expr f
  | CE_Let _ _ => false
  end.

Lemma expand_lets_with_nil_let_free : forall e,
  is_let_free_expr e = true -> expand_lets_with [] e = e.
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

Section UbFreeBinds.
  Variable ubf : cert_expr -> bool.

  Fixpoint ub_free_let_binds (xs : list (string * cert_expr)) : bool :=
    match xs with
    | [] => true
    | (_, be) :: rest => ubf be && ub_free_let_binds rest
    end.
End UbFreeBinds.

Fixpoint ub_free_expr (e : cert_expr) : bool :=
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ => true
  | CE_BinOp op _ _ l r =>
      negb (is_div_or_rem_op op) && ub_free_expr l && ub_free_expr r
  | CE_ICmp _ _ _ l r =>
      ub_free_expr l && ub_free_expr r
  | CE_Cast _ _ _ _ o | CE_Freeze _ o =>
      ub_free_expr o
  | CE_Select _ c t f =>
      ub_free_expr c && ub_free_expr t && ub_free_expr f
  | CE_Let bs body =>
      ub_free_let_binds ub_free_expr bs && ub_free_expr body
  end.

Lemma eval_iop_non_div_rem_no_ub :
  forall {Pa : Params} op fl w (vl vr : @dvalue Pa),
    is_div_or_rem_op op = false ->
    wf_scalar_dvalue w vl ->
    wf_scalar_dvalue w vr ->
    exists vout,
      @eval_iop Pa (cert_to_ibinop op fl) vl vr = raise_ret vout /\
      wf_scalar_dvalue w vout.
Proof.
  intros Pa op fl w vl vr Hop [-> | [il ->]] [-> | [ir ->]].
  - destruct op; cbn in Hop; try discriminate; cbn;
      exists (DVALUE_Base DVALUE_Poison); (split; [reflexivity | left; reflexivity]).
  - destruct op; cbn in Hop; try discriminate; cbn;
      exists (DVALUE_Base DVALUE_Poison); (split; [reflexivity | left; reflexivity]).
  - destruct op; cbn in Hop; try discriminate; cbn;
      exists (DVALUE_Base DVALUE_Poison); (split; [reflexivity | left; reflexivity]).
  - unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct op; cbn in Hop; try discriminate;
      unfold cert_to_ibinop, eval_int_op; cbn;
      repeat match goal with
             | |- context [if ?b then _ else _] => destruct b
             end;
      cbn; (eexists; split; [reflexivity | first [left; reflexivity | right; eexists; reflexivity]]).
Qed.

Lemma check_scalar_width_not_ub :
  forall {Pa : Params} w (dv : @dvalue Pa) msg,
    check_scalar_width w dv <> raise_ub msg.
Proof.
  intros Pa w [db | |] msg; cbn; try discriminate.
  destruct db as [| sz i | | | | | |]; try discriminate.
  destruct (Pos.eqb sz w); discriminate.
Qed.

Lemma ub_free_expr_no_ub :
  forall {Pa : Params} e let_widths penv lenv foracle msg,
    ub_free_expr e = true ->
    wt_cert_expr let_widths e = true ->
    eval_cert_expr penv lenv foracle e <> raise_ub msg.
Proof.
  intros Pa e.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body IHbs IHb ] using cert_expr_ind_nested;
    intros let_widths penv lenv foracle msg Hubf Hwt Hev.
  - discriminate Hev.
  - discriminate Hev.
  - cbn in Hev; destruct (lookup_let_val lenv nm) as [dv |].
    + exact (check_scalar_width_not_ub w dv msg Hev).
    + destruct (penv nm) as [dv |]; [| discriminate Hev].
      exact (check_scalar_width_not_ub w dv msg Hev).
  - cbn [ub_free_expr wt_cert_expr eval_cert_expr] in *.
    rewrite !andb_true_iff in Hubf; rewrite !andb_true_iff in Hwt.
    destruct Hubf as ([Hop Hubl] & Hubr).
    destruct Hwt as ((((_ & Hwtl) & Hwtr) & Hwl) & Hwr).
    apply negb_true_iff in Hop; apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    destruct (eval_cert_expr penv lenv foracle l) as [| s | | vl] eqn:El;
      cbn [eou_bind] in Hev; try discriminate.
    + inversion Hev; subst s; exact (IHl _ _ _ _ msg Hubl Hwtl El).
    + destruct (eval_cert_expr penv lenv foracle r) as [| s | | vr] eqn:Er;
        cbn [eou_bind] in Hev; try discriminate.
      * inversion Hev; subst s; exact (IHr _ _ _ _ msg Hubr Hwtr Er).
      * pose proof (eval_cert_expr_ret_wf_scalar l _ _ _ _ _ Hwtl El) as Hwfl.
        pose proof (eval_cert_expr_ret_wf_scalar r _ _ _ _ _ Hwtr Er) as Hwfr.
        rewrite Hwl in Hwfl; rewrite Hwr in Hwfr.
        destruct (eval_iop_non_div_rem_no_ub op fl w vl vr Hop Hwfl Hwfr) as [v' [Hv' _]].
        congruence.
  - cbn [ub_free_expr wt_cert_expr eval_cert_expr] in *.
    rewrite !andb_true_iff in Hubf; rewrite !andb_true_iff in Hwt.
    destruct Hubf as [Hubl Hubr]; destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr).
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    destruct (eval_cert_expr penv lenv foracle l) as [| s | | vl] eqn:El;
      cbn [eou_bind] in Hev; try discriminate.
    + inversion Hev; subst s; exact (IHl _ _ _ _ msg Hubl Hwtl El).
    + destruct (eval_cert_expr penv lenv foracle r) as [| s | | vr] eqn:Er;
        cbn [eou_bind] in Hev; try discriminate.
      * inversion Hev; subst s; exact (IHr _ _ _ _ msg Hubr Hwtr Er).
      * pose proof (eval_cert_expr_ret_wf_scalar l _ _ _ _ _ Hwtl El) as Hwfl.
        pose proof (eval_cert_expr_ret_wf_scalar r _ _ _ _ _ Hwtr Er) as Hwfr.
        rewrite Hwl in Hwfl; rewrite Hwr in Hwfr.
        destruct (eval_icmp_wf_scalar ss pr w vl vr Hwfl Hwfr) as [v' [Hv' _]]; congruence.
  - cbn [ub_free_expr wt_cert_expr eval_cert_expr] in *.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((Hk & Hwto) & Hwo).
    apply Pos.eqb_eq in Hwo.
    destruct (eval_cert_expr penv lenv foracle o) as [| s | | vo] eqn:Eo;
      cbn [eou_bind] in Hev; try discriminate.
    + inversion Hev; subst s; exact (IHo _ _ _ _ msg Hubf Hwto Eo).
    + pose proof (eval_cert_expr_ret_wf_scalar o _ _ _ _ _ Hwto Eo) as Hwfo.
      rewrite Hwo in Hwfo.
      destruct (eval_cast_wf_scalar k fw tw fl vo Hk Hwfo) as [v' [Hv' _]]; congruence.
  - cbn [ub_free_expr wt_cert_expr eval_cert_expr] in *.
    rewrite !andb_true_iff in Hubf; rewrite !andb_true_iff in Hwt.
    destruct Hubf as ([Hubc Hubt] & Hubf0).
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hwc) & Hwt0) & Hwf0).
    apply Pos.eqb_eq in Hwc; apply Pos.eqb_eq in Hwt0; apply Pos.eqb_eq in Hwf0.
    destruct (eval_cert_expr penv lenv foracle c) as [| s | | vc] eqn:Ec;
      cbn [eou_bind] in Hev; try discriminate.
    + inversion Hev; subst s; exact (IHc _ _ _ _ msg Hubc Hwtc Ec).
    + destruct (eval_cert_expr penv lenv foracle t) as [| s | | vt] eqn:Et;
        cbn [eou_bind] in Hev; try discriminate.
      * inversion Hev; subst s; exact (IHt _ _ _ _ msg Hubt Hwtt Et).
      * destruct (eval_cert_expr penv lenv foracle f) as [| s | | vf] eqn:Ef;
          cbn [eou_bind] in Hev; try discriminate.
        -- inversion Hev; subst s; exact (IHf _ _ _ _ msg Hubf0 Hwtf Ef).
        -- pose proof (eval_cert_expr_ret_wf_scalar c _ _ _ _ _ Hwtc Ec) as Hwfc.
           pose proof (eval_cert_expr_ret_wf_scalar t _ _ _ _ _ Hwtt Et) as Hwft.
           pose proof (eval_cert_expr_ret_wf_scalar f _ _ _ _ _ Hwtf Ef) as Hwff.
           rewrite Hwc in Hwfc; rewrite Hwt0 in Hwft; rewrite Hwf0 in Hwff.
           destruct (eval_select_wf_scalar w vc vt vf Hwfc Hwft Hwff) as [v' [Hv' _]];
             congruence.
  - cbn [ub_free_expr wt_cert_expr eval_cert_expr] in *.
    apply andb_true_iff in Hwt as [Hwto _].
    destruct (eval_cert_expr penv lenv foracle o) as [| s | | vo] eqn:Eo;
      cbn [eou_bind] in Hev; try discriminate.
    + inversion Hev; subst s; exact (IHo _ _ _ _ msg Hubf Hwto Eo).
    + destruct vo as [[| | | | | | |] | |]; discriminate Hev.
  - cbn [ub_free_expr wt_cert_expr eval_cert_expr] in *.
    apply andb_true_iff in Hubf as [Hub_bs Hub_body].
    destruct (wf_let_binds_step wt_cert_expr let_widths [] bs) as [env' |] eqn:Hbs;
      [| discriminate].
    assert (Hstep :
      forall cur_lw seen cur_le s,
        ub_free_let_binds ub_free_expr bs = true ->
        wf_let_binds_step wt_cert_expr cur_lw seen bs = Some env' ->
        eval_let_binds (fun ce x => eval_cert_expr penv ce foracle x) cur_le bs <> raise_ub s).
    { clear Hub_bs Hbs Hev; induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_lw seen cur_le s Hub_xs Hs Hev_xs;
        cbn [ub_free_let_binds wf_let_binds_step eval_let_binds] in Hub_xs, Hs, Hev_xs; cbn [snd] in *.
      - discriminate Hev_xs.
      - apply andb_true_iff in Hub_xs as [Hub_be Hub_rx].
        destruct (is_dollar_let_name bnm && negb (string_in_list bnm seen) &&
                  wt_cert_expr cur_lw be) eqn:Hok; [| discriminate].
        rewrite !andb_true_iff in Hok; destruct Hok as (_ & Hwt_be).
        destruct (eval_cert_expr penv cur_le foracle be) as [| s0 | | dv] eqn:Ebe;
          cbn [eou_bind] in Hev_xs; try discriminate.
        + inversion Hev_xs; subst s0; exact (IHbe _ _ _ _ s Hub_be Hwt_be Ebe).
        + exact (IHrx _ _ _ s Hub_rx Hs Hev_xs). }
    destruct (eval_let_binds (fun ce x => eval_cert_expr penv ce foracle x) lenv bs)
      as [| s | | lenv'] eqn:Ebs; cbn [eou_bind] in Hev; try discriminate.
    + inversion Hev; subst s; exact (Hstep let_widths [] lenv msg Hub_bs Hbs Ebs).
    + exact (IHb env' penv lenv' foracle msg Hub_body Hwt Hev).
Qed.

Lemma ub_free_expr_eval_ret :
  forall {Pa : Params} e let_widths penv lenv foracle,
    ub_free_expr e = true ->
    wt_cert_expr let_widths e = true ->
    wf_let_val_env let_widths lenv ->
    wf_param_env_for (collect_free_vars (List.map fst let_widths) e) penv ->
    exists vout,
      eval_cert_expr penv lenv foracle e = raise_ret vout /\
      wf_scalar_dvalue (cert_expr_bit_width e) vout.
Proof.
  intros Pa e let_widths penv lenv foracle Hubf Hwt Hle Hpe.
  destruct (eval_cert_expr_totality e let_widths penv lenv foracle Hwt Hle Hpe)
    as [[msg Hub] | Hret].
  - exfalso; exact (ub_free_expr_no_ub e let_widths penv lenv foracle msg Hubf Hwt Hub).
  - exact Hret.
Qed.

Fixpoint is_syntactic_subexpr (sub big : cert_expr) {struct big} : bool :=
  cert_expr_eqb sub big ||
  match big with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ | CE_Let _ _ => false
  | CE_BinOp _ _ _ l r | CE_ICmp _ _ _ l r =>
      is_syntactic_subexpr sub l || is_syntactic_subexpr sub r
  | CE_Cast _ _ _ _ o | CE_Freeze _ o =>
      is_syntactic_subexpr sub o
  | CE_Select _ c t f =>
      is_syntactic_subexpr sub c || is_syntactic_subexpr sub t || is_syntactic_subexpr sub f
  end.

Lemma is_syntactic_subexpr_eval_ret :
  forall {Pa : Params} sub big penv lenv foracle vbig,
    is_syntactic_subexpr sub big = true ->
    eval_cert_expr penv lenv foracle big = raise_ret vbig ->
    exists vsub, eval_cert_expr penv lenv foracle sub = raise_ret vsub.
Proof.
  intros Pa sub big.
  induction big as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros penv lenv foracle vbig Hsub Hbig;
    cbn [is_syntactic_subexpr] in Hsub;
    destruct (cert_expr_eqb sub _) eqn:Heq;
    try (apply cert_expr_eqb_eq in Heq; subst sub; exists vbig; exact Hbig);
    cbn [orb] in Hsub; try discriminate Hsub.
  - cbn [eval_cert_expr] in Hbig.
    destruct (eval_cert_expr penv lenv foracle l) as [| | | vl] eqn:El; [discriminate.. |].
    cbn [eou_bind] in Hbig.
    destruct (eval_cert_expr penv lenv foracle r) as [| | | vr] eqn:Er; [discriminate.. |].
    apply orb_true_iff in Hsub as [Hsl | Hsr];
      [exact (IHl _ _ _ vl Hsl El) | exact (IHr _ _ _ vr Hsr Er)].
  - cbn [eval_cert_expr] in Hbig.
    destruct (eval_cert_expr penv lenv foracle l) as [| | | vl] eqn:El; [discriminate.. |].
    cbn [eou_bind] in Hbig.
    destruct (eval_cert_expr penv lenv foracle r) as [| | | vr] eqn:Er; [discriminate.. |].
    apply orb_true_iff in Hsub as [Hsl | Hsr];
      [exact (IHl _ _ _ vl Hsl El) | exact (IHr _ _ _ vr Hsr Er)].
  - cbn [eval_cert_expr] in Hbig.
    destruct (eval_cert_expr penv lenv foracle o) as [| | | vo] eqn:Eo; [discriminate.. |].
    exact (IHo _ _ _ vo Hsub Eo).
  - cbn [eval_cert_expr] in Hbig.
    destruct (eval_cert_expr penv lenv foracle c) as [| | | vc] eqn:Ec; [discriminate.. |].
    cbn [eou_bind] in Hbig.
    destruct (eval_cert_expr penv lenv foracle t) as [| | | vt] eqn:Et; [discriminate.. |].
    cbn [eou_bind] in Hbig.
    destruct (eval_cert_expr penv lenv foracle f) as [| | | vf] eqn:Ef; [discriminate.. |].
    rewrite !orb_true_iff in Hsub; destruct Hsub as [[Hsc | Hst] | Hsf];
      [exact (IHc _ _ _ vc Hsc Ec)
      | exact (IHt _ _ _ vt Hst Et)
      | exact (IHf _ _ _ vf Hsf Ef)].
  - cbn [eval_cert_expr] in Hbig.
    destruct (eval_cert_expr penv lenv foracle o) as [| | | vo] eqn:Eo; [discriminate.. |].
    exact (IHo _ _ _ vo Hsub Eo).
Qed.

Section WfLetDagBinds.
  Variable wld : list (string * cert_expr) -> cert_expr -> bool.

  Fixpoint wf_let_dag_binds (exp_body : cert_expr)
                            (cur_m : list (string * cert_expr))
                            (xs : list (string * cert_expr)) {struct xs} : bool :=
    match xs with
    | [] => true
    | (bnm, be) :: rest =>
        let exp_be := expand_lets_with cur_m be in
        wld cur_m be &&
        (ub_free_expr exp_be || is_syntactic_subexpr exp_be exp_body) &&
        wf_let_dag_binds exp_body ((bnm, exp_be) :: cur_m) rest
    end.
End WfLetDagBinds.

Fixpoint wf_let_dag (m : list (string * cert_expr)) (e : cert_expr)
  {struct e} : bool :=
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ => true
  | CE_BinOp _ _ _ l r | CE_ICmp _ _ _ l r =>
      wf_let_dag m l && wf_let_dag m r
  | CE_Cast _ _ _ _ o | CE_Freeze _ o =>
      wf_let_dag m o
  | CE_Select _ c t f =>
      wf_let_dag m c && wf_let_dag m t && wf_let_dag m f
  | CE_Let bs body =>
      let m' := expand_let_binds expand_lets_with m bs in
      let exp_body := expand_lets_with m' body in
      wf_let_dag_binds wf_let_dag exp_body m bs && wf_let_dag m' body
  end.

Definition wf_let_subst (lw : list (string * positive))
                        (m : list (string * cert_expr)) : Prop :=
  List.map fst m = List.map fst lw /\
  forall nm,
    match lookup_let_width lw nm, lookup_let_expr m nm with
    | Some bw, Some ce =>
        cert_expr_bit_width ce = bw /\
        wt_cert_expr [] ce = true /\
        is_let_free_expr ce = true
    | None, None => True
    | _, _ => False
    end.

Lemma expand_lets_with_typing :
  forall e lw m,
    wt_cert_expr lw e = true ->
    wf_let_subst lw m ->
    cert_expr_bit_width (expand_lets_with m e) = cert_expr_bit_width e /\
    wt_cert_expr [] (expand_lets_with m e) = true /\
    is_let_free_expr (expand_lets_with m e) = true.
Proof.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body IHbs IHb ] using cert_expr_ind_nested;
    intros lw m Hwt [Hdom Hsub].
  - cbn; repeat split; reflexivity.
  - cbn; repeat split; reflexivity.
  - cbn [wt_cert_expr expand_lets_with] in *.
    pose proof (Hsub nm) as Hnm.
    destruct (lookup_let_width lw nm) as [bw |].
    + apply Pos.eqb_eq in Hwt; subst bw.
      destruct (lookup_let_expr m nm) as [ce |]; [| contradiction].
      exact Hnm.
    + destruct (lookup_let_expr m nm) as [ce |]; [contradiction |].
      cbn; repeat split; exact Hwt.
  - cbn [wt_cert_expr expand_lets_with cert_expr_bit_width is_let_free_expr] in *.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((((Hfl & Hwtl) & Hwtr) & Hwl) & Hwr).
    destruct (IHl lw m Hwtl (conj Hdom Hsub)) as (Hbl & Htl & Hfl_l).
    destruct (IHr lw m Hwtr (conj Hdom Hsub)) as (Hbr & Htr & Hfl_r).
    rewrite Hbl, Hbr, Htl, Htr, Hfl_l, Hfl_r, Hfl, Hwl, Hwr; repeat split; reflexivity.
  - cbn [wt_cert_expr expand_lets_with cert_expr_bit_width is_let_free_expr] in *.
    rewrite !andb_true_iff in Hwt; destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr).
    destruct (IHl lw m Hwtl (conj Hdom Hsub)) as (Hbl & Htl & Hfl_l).
    destruct (IHr lw m Hwtr (conj Hdom Hsub)) as (Hbr & Htr & Hfl_r).
    rewrite Hbl, Hbr, Htl, Htr, Hfl_l, Hfl_r, Hwl, Hwr; repeat split; reflexivity.
  - cbn [wt_cert_expr expand_lets_with cert_expr_bit_width is_let_free_expr] in *.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((Hk & Hwto) & Hwo).
    destruct (IHo lw m Hwto (conj Hdom Hsub)) as (Hbo & Hto & Hfl_o).
    rewrite Hbo, Hto, Hfl_o, Hk, Hwo; repeat split; reflexivity.
  - cbn [wt_cert_expr expand_lets_with cert_expr_bit_width is_let_free_expr] in *.
    rewrite !andb_true_iff in Hwt.
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hwc) & Hwt0) & Hwf0).
    destruct (IHc lw m Hwtc (conj Hdom Hsub)) as (Hbc & Htc & Hfl_c).
    destruct (IHt lw m Hwtt (conj Hdom Hsub)) as (Hbt & Htt & Hfl_t).
    destruct (IHf lw m Hwtf (conj Hdom Hsub)) as (Hbf & Htf & Hfl_f).
    rewrite Hbc, Hbt, Hbf, Htc, Htt, Htf, Hfl_c, Hfl_t, Hfl_f, Hwc, Hwt0, Hwf0.
    repeat split; reflexivity.
  - cbn [wt_cert_expr expand_lets_with cert_expr_bit_width is_let_free_expr] in *.
    apply andb_true_iff in Hwt as [Hwto Hwo].
    destruct (IHo lw m Hwto (conj Hdom Hsub)) as (Hbo & Hto & Hfl_o).
    rewrite Hbo, Hto, Hfl_o, Hwo; repeat split; reflexivity.
  - cbn [wt_cert_expr expand_lets_with cert_expr_bit_width] in *.
    destruct (wf_let_binds_step wt_cert_expr lw [] bs) as [env' |] eqn:Hbs; [| discriminate].
    assert (Hstep :
      forall cur_lw seen cur_m,
        wf_let_binds_step wt_cert_expr cur_lw seen bs = Some env' ->
        wf_let_subst cur_lw cur_m ->
        wf_let_subst env' (expand_let_binds expand_lets_with cur_m bs)).
    { clear Hbs; induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_lw seen cur_m Hs Hcs;
        cbn [wf_let_binds_step expand_let_binds] in Hs |- *; cbn [snd] in *.
      - inversion Hs; subst cur_lw; exact Hcs.
      - destruct (is_dollar_let_name bnm && negb (string_in_list bnm seen) &&
                  wt_cert_expr cur_lw be) eqn:Hok; [| discriminate].
        rewrite !andb_true_iff in Hok; destruct Hok as (_ & Hwt_be).
        destruct (IHbe cur_lw cur_m Hwt_be Hcs) as (Hb_be & Ht_be & Hlf_be).
        apply (IHrx ((bnm, cert_expr_bit_width be) :: cur_lw) (bnm :: seen)
                    ((bnm, expand_lets_with cur_m be) :: cur_m) Hs).
        destruct Hcs as [Hcd Hcl]; split; [cbn; congruence |].
        intros q; cbn [lookup_let_width lookup_let_expr].
        destruct (String.eqb bnm q); [repeat split; assumption | exact (Hcl q)]. }
    exact (IHb env' (expand_let_binds expand_lets_with m bs)
               Hwt (Hstep lw [] m Hbs (conj Hdom Hsub))).
Qed.

Lemma lookup_let_expr_in : forall m nm ce,
  lookup_let_expr m nm = Some ce -> exists k, In (k, ce) m.
Proof.
  induction m as [| [k v] rest IH]; intros nm ce H; cbn in H; [discriminate |].
  destruct (String.eqb k nm).
  - inversion H; subst; exists k; left; reflexivity.
  - destruct (IH nm ce H) as [k' Hk']; exists k'; right; exact Hk'.
Qed.

Lemma ub_free_expr_expand_lets_with :
  forall e m,
    (forall k ce, In (k, ce) m -> ub_free_expr ce = true) ->
    ub_free_expr e = true ->
    ub_free_expr (expand_lets_with m e) = true.
Proof.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body IHbs IHb ] using cert_expr_ind_nested;
    intros m Hm Hub; cbn [expand_lets_with ub_free_expr] in Hub |- *.
  - reflexivity.
  - reflexivity.
  - destruct (lookup_let_expr m nm) as [ce |] eqn:Hlk.
    + destruct (lookup_let_expr_in m nm ce Hlk) as [k Hk]; exact (Hm k ce Hk).
    + reflexivity.
  - cbn [ub_free_expr]; rewrite !andb_true_iff in Hub; rewrite !andb_true_iff.
    destruct Hub as ([Hop Hl] & Hr).
    split; [split; [exact Hop | exact (IHl m Hm Hl)] | exact (IHr m Hm Hr)].
  - cbn [ub_free_expr]; rewrite !andb_true_iff in Hub; rewrite !andb_true_iff.
    destruct Hub as [Hl Hr]; split; [exact (IHl m Hm Hl) | exact (IHr m Hm Hr)].
  - cbn [ub_free_expr]; exact (IHo m Hm Hub).
  - cbn [ub_free_expr]; rewrite !andb_true_iff in Hub; rewrite !andb_true_iff.
    destruct Hub as ([Hc Ht] & Hf).
    split; [split; [exact (IHc m Hm Hc) | exact (IHt m Hm Ht)] | exact (IHf m Hm Hf)].
  - cbn [ub_free_expr]; exact (IHo m Hm Hub).
  - apply andb_true_iff in Hub as [Hbs Hbody].
    assert (Hstep :
      forall cur_m,
        (forall k ce, In (k, ce) cur_m -> ub_free_expr ce = true) ->
        ub_free_let_binds ub_free_expr bs = true ->
        forall k ce, In (k, ce) (expand_let_binds expand_lets_with cur_m bs) ->
                     ub_free_expr ce = true).
    { clear Hbs; induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_m Hcm Hxs; cbn in Hxs |- *.
      - exact Hcm.
      - apply andb_true_iff in Hxs as [Hbe Hrx].
        pose proof (IHbe cur_m Hcm Hbe) as Hub_exp.
        apply IHrx; [| exact Hrx].
        intros k ce [Heq | Hin]; [inversion Heq; subst; exact Hub_exp | exact (Hcm k ce Hin)]. }
    exact (IHb (expand_let_binds expand_lets_with m bs) (Hstep m Hm Hbs) Hbody).
Qed.

Lemma ub_free_expr_wf_let_dag :
  forall e m,
    (forall k ce, In (k, ce) m -> ub_free_expr ce = true) ->
    ub_free_expr e = true ->
    wf_let_dag m e = true.
Proof.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body IHbs IHb ] using cert_expr_ind_nested;
    intros m Hm Hub; cbn [wf_let_dag ub_free_expr] in Hub |- *.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite !andb_true_iff in Hub; rewrite !andb_true_iff.
    destruct Hub as ([_ Hl] & Hr); split; [exact (IHl m Hm Hl) | exact (IHr m Hm Hr)].
  - rewrite !andb_true_iff in Hub; rewrite !andb_true_iff.
    destruct Hub as [Hl Hr]; split; [exact (IHl m Hm Hl) | exact (IHr m Hm Hr)].
  - exact (IHo m Hm Hub).
  - rewrite !andb_true_iff in Hub; rewrite !andb_true_iff.
    destruct Hub as ([Hc Ht] & Hf).
    split; [split; [exact (IHc m Hm Hc) | exact (IHt m Hm Ht)] | exact (IHf m Hm Hf)].
  - exact (IHo m Hm Hub).
  - apply andb_true_iff in Hub as [Hbs Hbody].
    assert (Hstep :
      forall exp_body cur_m,
        (forall k ce, In (k, ce) cur_m -> ub_free_expr ce = true) ->
        ub_free_let_binds ub_free_expr bs = true ->
        wf_let_dag_binds wf_let_dag exp_body cur_m bs = true /\
        (forall k ce, In (k, ce) (expand_let_binds expand_lets_with cur_m bs) ->
                      ub_free_expr ce = true)).
    { clear Hbs; intros exp_body; induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_m Hcm Hxs; cbn in Hxs |- *; cbn [snd] in *.
      - split; [reflexivity | exact Hcm].
      - apply andb_true_iff in Hxs as [Hbe Hrx].
        pose proof (IHbe cur_m Hcm Hbe) as Hwf_be.
        pose proof (ub_free_expr_expand_lets_with be cur_m Hcm Hbe) as Hub_exp.
        assert (Hcm' : forall k ce,
                  In (k, ce) ((bnm, expand_lets_with cur_m be) :: cur_m) ->
                  ub_free_expr ce = true)
          by (intros k ce [Heq | Hin]; [inversion Heq; subst; exact Hub_exp | exact (Hcm k ce Hin)]).
        destruct (IHrx _ Hcm' Hrx) as [Hwf_rx Hcm_end].
        split; [rewrite Hwf_be, Hub_exp, Hwf_rx; reflexivity | exact Hcm_end]. }
    destruct (Hstep (expand_lets_with (expand_let_binds expand_lets_with m bs) body)
                    m Hm Hbs) as [Hwf_bs Hm'].
    rewrite Hwf_bs, (IHb _ Hm' Hbody); reflexivity.
Qed.

Section WfLetDagFueledBinds.
  Variable wldf : sized_let_map -> cert_expr -> nat -> option nat.

  Fixpoint wf_let_dag_binds_fueled
    (exp_body : cert_expr) (cur_ms : sized_let_map)
    (xs : list (string * cert_expr)) (fuel : nat) {struct xs} : option nat :=
    match xs with
    | [] => Some fuel
    | (bnm, be) :: rest =>
        match wldf cur_ms be fuel with
        | Some f1 =>
            match expand_lets_fueled_with cur_ms be f1 with
            | Some (exp_be, bsz, f2) =>
                if ub_free_expr exp_be || is_syntactic_subexpr exp_be exp_body
                then wf_let_dag_binds_fueled exp_body ((bnm, (exp_be, bsz)) :: cur_ms) rest f2
                else None
            | None => None
            end
        | None => None
        end
    end.
End WfLetDagFueledBinds.

Fixpoint wf_let_dag_fueled_with
  (ms : sized_let_map) (e : cert_expr) (fuel : nat) {struct e} : option nat :=
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ => Some fuel
  | CE_BinOp _ _ _ l r | CE_ICmp _ _ _ l r =>
      match wf_let_dag_fueled_with ms l fuel with
      | Some f1 => wf_let_dag_fueled_with ms r f1
      | None => None
      end
  | CE_Cast _ _ _ _ o | CE_Freeze _ o =>
      wf_let_dag_fueled_with ms o fuel
  | CE_Select _ c t f =>
      match wf_let_dag_fueled_with ms c fuel with
      | Some f1 =>
          match wf_let_dag_fueled_with ms t f1 with
          | Some f2 => wf_let_dag_fueled_with ms f f2
          | None => None
          end
      | None => None
      end
  | CE_Let bs body =>
      match expand_let_binds_fueled expand_lets_fueled_with ms bs fuel with
      | Some (ms', f1) =>
          match expand_lets_fueled_with ms' body f1 with
          | Some (exp_body, _, f2) =>
              match wf_let_dag_binds_fueled wf_let_dag_fueled_with exp_body ms bs f2 with
              | Some f3 => wf_let_dag_fueled_with ms' body f3
              | None => None
              end
          | None => None
          end
      | None => None
      end
  end.

Definition wf_let_dag_fueled (budget : nat) (e : cert_expr) : bool :=
  match wf_let_dag_fueled_with [] e budget with
  | Some _ => true
  | None => false
  end.

Definition check_wf_let_dag_fast (budget : nat) (e : cert_expr) : bool :=
  ub_free_expr e || wf_let_dag_fueled budget e.

Lemma expand_let_binds_fueled_strip :
  forall xs cur_ms fuel ms' f1,
    expand_let_binds_fueled expand_lets_fueled_with cur_ms xs fuel = Some (ms', f1) ->
    strip_let_sizes ms' = expand_let_binds expand_lets_with (strip_let_sizes cur_ms) xs.
Proof.
  induction xs as [| [bnm be] rest IH]; intros cur_ms fuel ms' f1 Hexp; cbn in Hexp |- *.
  - inversion Hexp; reflexivity.
  - destruct (expand_lets_fueled_with cur_ms be fuel) as [[[ebe bsz] f_mid] |] eqn:Ebe;
      [| discriminate Hexp].
    pose proof (expand_lets_fueled_with_eq be cur_ms fuel ebe bsz f_mid Ebe) as Hebe.
    subst ebe.
    exact (IH ((bnm, (expand_lets_with (strip_let_sizes cur_ms) be, bsz)) :: cur_ms)
              f_mid ms' f1 Hexp).
Qed.

Lemma wf_let_dag_fueled_with_sound :
  forall e ms fuel fuel',
    wf_let_dag_fueled_with ms e fuel = Some fuel' ->
    wf_let_dag (strip_let_sizes ms) e = true.
Proof.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body IHbs IHb ] using cert_expr_ind_nested;
    intros ms fuel fuel' Hwf; cbn [wf_let_dag_fueled_with wf_let_dag] in Hwf |- *.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (wf_let_dag_fueled_with ms l fuel) as [f1 |] eqn:El; [| discriminate Hwf].
    rewrite (IHl _ _ _ El), (IHr _ _ _ Hwf); reflexivity.
  - destruct (wf_let_dag_fueled_with ms l fuel) as [f1 |] eqn:El; [| discriminate Hwf].
    rewrite (IHl _ _ _ El), (IHr _ _ _ Hwf); reflexivity.
  - exact (IHo _ _ _ Hwf).
  - destruct (wf_let_dag_fueled_with ms c fuel) as [f1 |] eqn:Ec; [| discriminate Hwf].
    destruct (wf_let_dag_fueled_with ms t f1) as [f2 |] eqn:Et; [| discriminate Hwf].
    rewrite (IHc _ _ _ Ec), (IHt _ _ _ Et), (IHf _ _ _ Hwf); reflexivity.
  - exact (IHo _ _ _ Hwf).
  - destruct (expand_let_binds_fueled expand_lets_fueled_with ms bs fuel)
      as [[ms' f1] |] eqn:Ebs; [| discriminate Hwf].
    destruct (expand_lets_fueled_with ms' body f1) as [[[exp_body sz_b] f2] |] eqn:Eb;
      [| discriminate Hwf].
    destruct (wf_let_dag_binds_fueled wf_let_dag_fueled_with exp_body ms bs f2)
      as [f3 |] eqn:Ewbs; [| discriminate Hwf].
    pose proof (expand_let_binds_fueled_strip bs ms fuel ms' f1 Ebs) as Hms'.
    pose proof (expand_lets_fueled_with_eq body ms' f1 exp_body sz_b f2 Eb) as Hexp_b.
    rewrite Hms' in Hexp_b; subst exp_body.
    set (exp_b := expand_lets_with (expand_let_binds expand_lets_with (strip_let_sizes ms) bs) body)
      in Ewbs |- *.
    assert (Hstep :
      forall cur_ms f_in f_out,
        wf_let_dag_binds_fueled wf_let_dag_fueled_with exp_b cur_ms bs f_in = Some f_out ->
        wf_let_dag_binds wf_let_dag exp_b (strip_let_sizes cur_ms) bs = true).
    { clearbody exp_b; clear Ebs Eb Ewbs Hms' Hwf;
      induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_ms f_in f_out H; cbn [wf_let_dag_binds_fueled wf_let_dag_binds] in H |- *; cbn [snd] in *.
      - reflexivity.
      - destruct (wf_let_dag_fueled_with cur_ms be f_in) as [fa |] eqn:Ebe1; [| discriminate H].
        destruct (expand_lets_fueled_with cur_ms be fa) as [[[exp_be bsz] fb] |] eqn:Ebe2;
          [| discriminate H].
        destruct (ub_free_expr exp_be || is_syntactic_subexpr exp_be exp_b) eqn:Esub;
          [| discriminate H].
        pose proof (expand_lets_fueled_with_eq be cur_ms fa exp_be bsz fb Ebe2) as Hebe.
        subst exp_be.
        change ((bnm, expand_lets_with (strip_let_sizes cur_ms) be) :: strip_let_sizes cur_ms)
          with (strip_let_sizes ((bnm, (expand_lets_with (strip_let_sizes cur_ms) be, bsz)) :: cur_ms)).
        rewrite (IHbe _ _ _ Ebe1), Esub,
                (IHrx ((bnm, (expand_lets_with (strip_let_sizes cur_ms) be, bsz)) :: cur_ms) _ _ H).
        reflexivity. }
    rewrite (Hstep ms f2 f3 Ewbs), <- Hms', (IHb ms' f3 fuel' Hwf); reflexivity.
Qed.

Lemma wf_let_dag_fueled_sound :
  forall budget e,
    wf_let_dag_fueled budget e = true ->
    wf_let_dag [] e = true.
Proof.
  intros budget e H; unfold wf_let_dag_fueled in H.
  destruct (wf_let_dag_fueled_with [] e budget) as [f' |] eqn:E; [| discriminate H].
  exact (wf_let_dag_fueled_with_sound e [] budget f' E).
Qed.

Lemma check_wf_let_dag_fast_sound :
  forall budget e,
    check_wf_let_dag_fast budget e = true ->
    wf_let_dag [] e = true.
Proof.
  intros budget e H; unfold check_wf_let_dag_fast in H.
  apply orb_true_iff in H as [Hub | Hwf].
  - exact (ub_free_expr_wf_let_dag e [] (fun k ce H => False_ind _ H) Hub).
  - exact (wf_let_dag_fueled_sound budget e Hwf).
Qed.

Lemma lookup_let_expr_none_dom : forall m nm,
  lookup_let_expr m nm = None -> ~ In nm (List.map fst m).
Proof.
  induction m as [| [k v] rest IH]; intros nm H; cbn in *.
  - intros [].
  - destruct (String.eqb k nm) eqn:E; [discriminate |].
    apply String.eqb_neq in E; intros [Hk | Hr];
      [exact (E Hk) | exact (IH nm H Hr)].
Qed.

Lemma expand_lets_with_free_vars :
  forall e m V,
    (forall k ce, In (k, ce) m -> incl (collect_free_vars [] ce) V) ->
    incl (collect_free_vars (List.map fst m) e) V ->
    incl (collect_free_vars [] (expand_lets_with m e)) V.
Proof.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body IHbs IHb ] using cert_expr_ind_nested;
    intros m V Hm He; cbn [expand_lets_with collect_free_vars] in *.
  - intros x [].
  - intros x [].
  - destruct (lookup_let_expr m nm) as [ce |] eqn:Hlk.
    + destruct (lookup_let_expr_in m nm ce Hlk) as [k Hk]; exact (Hm k ce Hk).
    + cbn [collect_free_vars].
      assert (Hnin : string_in_list nm (List.map fst m) = false).
      { destruct (string_in_list nm (List.map fst m)) eqn:Ein; [| reflexivity].
        apply string_in_list_spec in Ein.
        exfalso; exact (lookup_let_expr_none_dom m nm Hlk Ein). }
      rewrite Hnin in He; exact He.
  - apply incl_app;
      [apply (IHl m V Hm); intros x Hx; apply He, in_app_iff; left; exact Hx
      | apply (IHr m V Hm); intros x Hx; apply He, in_app_iff; right; exact Hx].
  - apply incl_app;
      [apply (IHl m V Hm); intros x Hx; apply He, in_app_iff; left; exact Hx
      | apply (IHr m V Hm); intros x Hx; apply He, in_app_iff; right; exact Hx].
  - exact (IHo m V Hm He).
  - apply incl_app; [| apply incl_app].
    + apply (IHc m V Hm); intros x Hx; apply He, in_app_iff; left; exact Hx.
    + apply (IHt m V Hm); intros x Hx; apply He, in_app_iff; right; apply in_app_iff; left; exact Hx.
    + apply (IHf m V Hm); intros x Hx; apply He, in_app_iff; right; apply in_app_iff; right; exact Hx.
  - exact (IHo m V Hm He).
  - assert (Hstep :
      forall cur_m,
        (forall k ce, In (k, ce) cur_m -> incl (collect_free_vars [] ce) V) ->
        incl (let '(b', vs_xs) := collect_bind_vars collect_free_vars (List.map fst cur_m) bs in
              vs_xs ++ collect_free_vars b' body) V ->
        (forall k ce, In (k, ce) (expand_let_binds expand_lets_with cur_m bs) ->
                      incl (collect_free_vars [] ce) V) /\
        incl (collect_free_vars (List.map fst (expand_let_binds expand_lets_with cur_m bs)) body) V).
    { clear He; induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_m Hcm Hce; cbn in *.
      - split; assumption.
      - destruct (collect_bind_vars collect_free_vars (bnm :: List.map fst cur_m) rx)
          as [b_end vs_rx] eqn:Hbv.
        assert (Hbe_incl : incl (collect_free_vars (List.map fst cur_m) be) V).
        { intros x Hx; apply Hce; rewrite <- app_assoc; apply in_app_iff; left; exact Hx. }
        pose proof (IHbe cur_m V Hcm Hbe_incl) as Hexp_be.
        apply (IHrx ((bnm, expand_lets_with cur_m be) :: cur_m)).
        + intros k ce [Heq | Hin]; [inversion Heq; subst; exact Hexp_be | exact (Hcm k ce Hin)].
        + cbn [List.map fst]; rewrite Hbv.
          intros x Hx; apply Hce; rewrite <- app_assoc; apply in_app_iff; right; exact Hx. }
    destruct (collect_bind_vars collect_free_vars (List.map fst m) bs) as [b' vs_bs] eqn:Hbv.
    assert (He' : incl (let '(b0, vs0) := collect_bind_vars collect_free_vars (List.map fst m) bs in
                        vs0 ++ collect_free_vars b0 body) V)
      by (rewrite Hbv; exact He).
    destruct (Hstep m Hm He') as [Hm' Hbody'].
    exact (IHb (expand_let_binds expand_lets_with m bs) V Hm' Hbody').
Qed.

Lemma expand_lets_with_wf_param_env :
  forall {Pa : Params} e m (penv : param_env Pa),
    (forall k ce, In (k, ce) m -> wf_param_env_for (collect_free_vars [] ce) penv) ->
    wf_param_env_for (collect_free_vars (List.map fst m) e) penv ->
    wf_param_env_for (collect_free_vars [] (expand_lets_with m e)) penv.
Proof.
  intros Pa e m penv Hm He nm w Hin.
  set (V := List.flat_map (fun p => collect_free_vars [] (snd p)) m ++
            collect_free_vars (List.map fst m) e).
  assert (HinV : In (nm, w) V).
  { apply (expand_lets_with_free_vars e m V); [| apply incl_appr, incl_refl | exact Hin].
    intros k ce Hk x Hx; apply in_app_iff; left; apply in_flat_map.
    exists (k, ce); split; [exact Hk | exact Hx]. }
  apply in_app_iff in HinV as [Hfm | Hef].
  - apply in_flat_map in Hfm as [[k ce] [Hk Hce]]; cbn in Hce.
    exact (Hm k ce Hk nm w Hce).
  - exact (He nm w Hef).
Qed.

Lemma wf_let_val_env_nil : forall {Pa : Params}, @wf_let_val_env Pa [] [].
Proof.
  intros Pa nm; cbn; exact I.
Qed.

Lemma wf_let_subst_nil : wf_let_subst [] [].
Proof.
  split; [reflexivity | intros nm; cbn; exact I].
Qed.

Definition wf_let_eval_sync {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (lw : list (string * positive)) (lenv : let_val_env Pa) : Prop :=
  wf_let_val_env lw lenv /\
  wf_let_subst lw (let_val_exprs lenv) /\
  (forall nm,
     match lookup_let_val lenv nm, lookup_let_expr (let_val_exprs lenv) nm with
     | Some dv, Some ce => eval_cert_expr penv [] foracle ce = raise_ret dv
     | None, None => True
     | _, _ => False
     end) /\
  (forall k ce,
     In (k, ce) (let_val_exprs lenv) ->
     wf_param_env_for (collect_free_vars [] ce) penv).

Lemma wf_let_eval_sync_nil :
  forall {Pa : Params} (penv : param_env Pa) (foracle : freeze_oracle),
    wf_let_eval_sync penv foracle [] [].
Proof.
  intros Pa penv foracle; unfold wf_let_eval_sync.
  split; [apply wf_let_val_env_nil |].
  split; [apply wf_let_subst_nil |].
  split; [intros nm; exact I | intros k ce []].
Qed.

Lemma eou_bind_equiv_cong :
  forall {Pa : Params} (m1 m2 : EOU (@dvalue Pa))
         (k1 k2 : @dvalue Pa -> EOU (@dvalue Pa)),
    equiv_eou_dvalue m1 m2 ->
    (forall v, equiv_eou_dvalue (k1 v) (k2 v)) ->
    equiv_eou_dvalue (eou_bind m1 k1) (eou_bind m2 k2).
Proof.
  intros Pa [] [] k1 k2 Hm Hk; cbn in *; try contradiction; trivial.
  subst; exact (Hk _).
Qed.

Lemma eval_expand_lets_with_equiv :
  forall {Pa : Params} (e : cert_expr) (lw : list (string * positive))
         (penv : param_env Pa) (lenv : let_val_env Pa) (foracle : freeze_oracle),
    wt_cert_expr lw e = true ->
    wf_let_dag (let_val_exprs lenv) e = true ->
    wf_let_eval_sync penv foracle lw lenv ->
    wf_param_env_for (collect_free_vars (List.map fst lw) e) penv ->
    equiv_eou_dvalue
      (eval_cert_expr penv lenv foracle e)
      (eval_cert_expr penv [] foracle (expand_lets_with (let_val_exprs lenv) e)).
Proof.
  intros Pa e.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body IHbs IHb ] using cert_expr_ind_nested;
    intros lw penv lenv foracle Hwt Hdag Hsync Hpenv.
  - apply equiv_eou_dvalue_refl.
  - apply equiv_eou_dvalue_refl.
  - destruct Hsync as (Hval & [_ Hsub] & Heval & _).
    cbn [wt_cert_expr eval_cert_expr expand_lets_with] in *.
    pose proof (Hval nm) as Hvnm; pose proof (Hsub nm) as Hsnm; pose proof (Heval nm) as Henm.
    destruct (lookup_let_width lw nm) as [bw |].
    + apply Pos.eqb_eq in Hwt; subst bw.
      destruct (lookup_let_val lenv nm) as [dv |]; [| contradiction].
      destruct (lookup_let_expr (let_val_exprs lenv) nm) as [ce |]; [| contradiction].
      rewrite (check_scalar_width_ok w dv Hvnm), Henm; cbn; reflexivity.
    + destruct (lookup_let_val lenv nm) as [dv |]; [contradiction |].
      destruct (lookup_let_expr (let_val_exprs lenv) nm) as [ce |]; [contradiction |].
      cbn [eval_cert_expr lookup_let_val]; apply equiv_eou_dvalue_refl.
  - cbn [wt_cert_expr wf_let_dag collect_free_vars eval_cert_expr expand_lets_with] in *.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hdag.
    destruct Hwt as ((((_ & Hwtl) & Hwtr) & _) & _); destruct Hdag as [Hdl Hdr].
    assert (Hpl : wf_param_env_for (collect_free_vars (List.map fst lw) l) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars (List.map fst lw) r) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
    apply eou_bind_equiv_cong; [exact (IHl lw penv lenv foracle Hwtl Hdl Hsync Hpl) | intros vl].
    apply eou_bind_equiv_cong; [exact (IHr lw penv lenv foracle Hwtr Hdr Hsync Hpr) | intros vr].
    apply equiv_eou_dvalue_refl.
  - cbn [wt_cert_expr wf_let_dag collect_free_vars eval_cert_expr expand_lets_with] in *.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hdag.
    destruct Hwt as (((Hwtl & Hwtr) & _) & _); destruct Hdag as [Hdl Hdr].
    assert (Hpl : wf_param_env_for (collect_free_vars (List.map fst lw) l) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars (List.map fst lw) r) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
    apply eou_bind_equiv_cong; [exact (IHl lw penv lenv foracle Hwtl Hdl Hsync Hpl) | intros vl].
    apply eou_bind_equiv_cong; [exact (IHr lw penv lenv foracle Hwtr Hdr Hsync Hpr) | intros vr].
    apply equiv_eou_dvalue_refl.
  - cbn [wt_cert_expr wf_let_dag collect_free_vars eval_cert_expr expand_lets_with] in *.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((_ & Hwto) & _).
    apply eou_bind_equiv_cong;
      [exact (IHo lw penv lenv foracle Hwto Hdag Hsync Hpenv) | intros vo; apply equiv_eou_dvalue_refl].
  - cbn [wt_cert_expr wf_let_dag collect_free_vars eval_cert_expr expand_lets_with] in *.
    rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hdag.
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & _) & _) & _).
    destruct Hdag as ([Hdc Hdt] & Hdf).
    assert (Hpc : wf_param_env_for (collect_free_vars (List.map fst lw) c) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpt : wf_param_env_for (collect_free_vars (List.map fst lw) t) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; left; exact Hx).
    assert (Hpf : wf_param_env_for (collect_free_vars (List.map fst lw) f) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; right; exact Hx).
    apply eou_bind_equiv_cong; [exact (IHc lw penv lenv foracle Hwtc Hdc Hsync Hpc) | intros vc].
    apply eou_bind_equiv_cong; [exact (IHt lw penv lenv foracle Hwtt Hdt Hsync Hpt) | intros vt].
    apply eou_bind_equiv_cong; [exact (IHf lw penv lenv foracle Hwtf Hdf Hsync Hpf) | intros vf].
    apply equiv_eou_dvalue_refl.
  - cbn [wt_cert_expr wf_let_dag collect_free_vars eval_cert_expr expand_lets_with] in *.
    apply andb_true_iff in Hwt as [Hwto _].
    destruct Hsync as (Hval & Hsub & Heval & Hfv_m).
    destruct (expand_lets_with_typing o lw (let_val_exprs lenv) Hwto Hsub)
      as (_ & _ & Hlf_o).
    cbn [let_val_exprs List.map].
    rewrite (expand_lets_with_nil_let_free _ Hlf_o).
    apply eou_bind_equiv_cong;
      [exact (IHo lw penv lenv foracle Hwto Hdag (conj Hval (conj Hsub (conj Heval Hfv_m))) Hpenv)
      | intros vo; apply equiv_eou_dvalue_refl].
  - assert (Hpenv_exp_body :
      wf_param_env_for
        (collect_free_vars []
           (expand_lets_with (expand_let_binds expand_lets_with (let_val_exprs lenv) bs) body)) penv).
    { destruct Hsync as (_ & [Hdom_l _] & _ & Hfv_m).
      pose proof (expand_lets_with_wf_param_env (CE_Let bs body) (let_val_exprs lenv) penv Hfv_m) as Hfv.
      rewrite Hdom_l in Hfv; exact (Hfv Hpenv). }
    cbn [wt_cert_expr wf_let_dag collect_free_vars eval_cert_expr expand_lets_with] in *.
    destruct (wf_let_binds_step wt_cert_expr lw [] bs) as [env' |] eqn:Hbs; [| discriminate].
    apply andb_true_iff in Hdag as [Hdag_bs Hdag_body].
    set (exp_body := expand_lets_with (expand_let_binds expand_lets_with (let_val_exprs lenv) bs) body) in *.
    assert (Hwt_exp_body : wt_cert_expr [] exp_body = true).
    { destruct Hsync as (_ & Hsub & _).
      assert (Hg : forall xs cur_lw seen cur_m,
                     wf_let_binds_step wt_cert_expr cur_lw seen xs = Some env' ->
                     wf_let_subst cur_lw cur_m ->
                     wf_let_subst env' (expand_let_binds expand_lets_with cur_m xs)).
      { clear Hdag_bs Hdag_body exp_body Hpenv_exp_body Hbs Hsub Hpenv.
        induction xs as [| [bnm be] rx IHrx]; intros cur_lw seen cur_m Hs Hcs;
          cbn [wf_let_binds_step expand_let_binds] in Hs |- *.
        - inversion Hs; subst; exact Hcs.
        - destruct (is_dollar_let_name bnm && negb (string_in_list bnm seen) &&
                    wt_cert_expr cur_lw be) eqn:Hok; [| discriminate].
          rewrite !andb_true_iff in Hok; destruct Hok as (_ & Hwt_be).
          destruct (expand_lets_with_typing be cur_lw cur_m Hwt_be Hcs)
            as (Hb_be & Ht_be & Hlf_be).
          apply (IHrx ((bnm, cert_expr_bit_width be) :: cur_lw) (bnm :: seen)
                      ((bnm, expand_lets_with cur_m be) :: cur_m) Hs).
          destruct Hcs as [Hcd Hcl]; split; [cbn; congruence |].
          intros q; cbn [lookup_let_width lookup_let_expr].
          destruct (String.eqb bnm q); [repeat split; assumption | exact (Hcl q)]. }
      exact (proj1 (proj2 (expand_lets_with_typing body env' _ Hwt (Hg bs lw [] (let_val_exprs lenv) Hbs Hsub)))). }
    assert (Hstep :
      forall cur_lw seen cur_le,
        wf_let_binds_step wt_cert_expr cur_lw seen bs = Some env' ->
        wf_let_dag_binds wf_let_dag exp_body (let_val_exprs cur_le) bs = true ->
        wf_let_eval_sync penv foracle cur_lw cur_le ->
        wf_param_env_for
          (let '(b', vs_xs) := collect_bind_vars collect_free_vars (List.map fst cur_lw) bs in
           vs_xs ++ collect_free_vars b' body) penv ->
        (exists msg_l msg_r,
           eval_let_binds (fun ce x => eval_cert_expr penv ce foracle x) cur_le bs = raise_ub msg_l /\
           eval_cert_expr penv [] foracle exp_body = raise_ub msg_r) \/
        (exists lenv',
           eval_let_binds (fun ce x => eval_cert_expr penv ce foracle x) cur_le bs = raise_ret lenv' /\
           let_val_exprs lenv' = expand_let_binds expand_lets_with (let_val_exprs cur_le) bs /\
           wf_let_eval_sync penv foracle env' lenv' /\
           wf_param_env_for (collect_free_vars (List.map fst env') body) penv)).
    { fold exp_body in Hpenv_exp_body; clearbody exp_body; clear Hbs Hdag_bs Hdag_body Hpenv;
      induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_lw seen cur_le Hs Hd Hsy Hcp;
        cbn [wf_let_binds_step] in Hs; cbn [wf_let_dag_binds] in Hd.
      - inversion Hs; subst cur_lw; cbn in Hcp.
        right; exists cur_le; split; [reflexivity | split; [reflexivity | split; [exact Hsy | exact Hcp]]].
      - cbn in IHbe.
        destruct (is_dollar_let_name bnm && negb (string_in_list bnm seen) &&
                  wt_cert_expr cur_lw be) eqn:Hok; [| discriminate].
        rewrite !andb_true_iff in Hok; rewrite !andb_true_iff in Hd.
        destruct Hok as (_ & Hwt_be); destruct Hd as ([Hd_be Hub_or_sub] & Hd_rx).
        cbn [collect_bind_vars] in Hcp.
        destruct (collect_bind_vars collect_free_vars (bnm :: List.map fst cur_lw) rx)
          as [b_end vs_rx] eqn:Hbv.
        assert (Hp_be : wf_param_env_for (collect_free_vars (List.map fst cur_lw) be) penv).
        { intros x wx Hx; apply Hcp; rewrite <- app_assoc; apply in_app_iff; left; exact Hx. }
        pose proof (IHbe cur_lw penv cur_le foracle Hwt_be Hd_be Hsy Hp_be) as Heq_be.
        destruct Hsy as (Hval_c & Hsub_c & Hev_c & Hfv_c).
        destruct (expand_lets_with_typing be cur_lw (let_val_exprs cur_le) Hwt_be Hsub_c)
          as (Hb_exp_be & Hwt_exp_be & Hlf_exp_be).
        cbn [eval_let_binds].
        destruct (eval_cert_expr_totality be cur_lw penv cur_le foracle Hwt_be Hval_c Hp_be)
          as [[msg_be Hbe_ub] | [dv_be [Hbe_ret Hwf_dv]]].
        + rewrite Hbe_ub in Heq_be |- *; cbn [eou_bind].
          destruct (eval_cert_expr penv [] foracle (expand_lets_with (let_val_exprs cur_le) be))
            as [| | msg_exp |] eqn:Eexp_be; cbn in Heq_be; try contradiction.
          destruct (ub_free_expr (expand_lets_with (let_val_exprs cur_le) be)) eqn:Eubf;
            cbn [orb] in Hub_or_sub.
          * exfalso; exact (ub_free_expr_no_ub _ [] penv [] foracle msg_exp Eubf Hwt_exp_be Eexp_be).
          * destruct (eval_cert_expr_totality exp_body [] penv [] foracle
                        Hwt_exp_body wf_let_val_env_nil Hpenv_exp_body)
              as [[msg_body Hbody_ub] | [vbody [Hbody_ret _]]].
            -- left; exists msg_be, msg_body; split; [reflexivity | exact Hbody_ub].
            -- destruct (is_syntactic_subexpr_eval_ret _ _ penv [] foracle vbody Hub_or_sub Hbody_ret)
                 as [vsub Hvsub].
               congruence.
        + rewrite Hbe_ret in Heq_be |- *; cbn [eou_bind].
          destruct (eval_cert_expr penv [] foracle (expand_lets_with (let_val_exprs cur_le) be))
            as [| | | dv_exp] eqn:Eexp_be; cbn in Heq_be; try contradiction.
          subst dv_exp.
          set (exp_be := expand_lets_with (let_val_exprs cur_le) be) in *.
          apply (IHrx ((bnm, cert_expr_bit_width be) :: cur_lw) (bnm :: seen)
                      ((bnm, (dv_be, exp_be)) :: cur_le) Hs Hd_rx).
          * repeat split.
            -- intros q; cbn [lookup_let_width lookup_let_val].
               destruct (String.eqb bnm q); [exact Hwf_dv | exact (Hval_c q)].
            -- cbn; f_equal; exact (proj1 Hsub_c).
            -- intros q; cbn [lookup_let_width let_val_exprs List.map lookup_let_expr].
               destruct (String.eqb bnm q);
                 [repeat split; assumption | exact (proj2 Hsub_c q)].
            -- intros q; cbn [lookup_let_val let_val_exprs List.map lookup_let_expr].
               destruct (String.eqb bnm q); [exact Eexp_be | exact (Hev_c q)].
            -- intros k ce [Heq_k | Hin_k].
               ++ inversion Heq_k; subst k ce.
                  unfold exp_be; apply expand_lets_with_wf_param_env; [exact Hfv_c |].
                  rewrite (proj1 Hsub_c); exact Hp_be.
               ++ exact (Hfv_c k ce Hin_k).
          * cbn [List.map fst]; rewrite Hbv.
            intros x wx Hx; apply Hcp; rewrite <- app_assoc; apply in_app_iff; right; exact Hx. }
    destruct (Hstep lw [] lenv Hbs Hdag_bs Hsync Hpenv)
      as [[msg_l [msg_r [-> ->]]] | [lenv' [-> [Hle_exprs [Hsync' Hpenv']]]]].
    + cbn; exact I.
    + cbn [eou_bind]; unfold exp_body; rewrite <- Hle_exprs.
      apply (IHb env' penv lenv' foracle Hwt); [rewrite Hle_exprs; exact Hdag_body | exact Hsync' | exact Hpenv'].
Qed.

Theorem eval_expand_lets_equiv :
  forall {Pa : Params} (e : cert_expr) (penv : param_env Pa) (foracle : freeze_oracle),
    wt_cert_expr [] e = true ->
    wf_let_dag [] e = true ->
    wf_param_env_for (collect_free_vars [] e) penv ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle e)
      (eval_closed_cert_expr penv foracle (expand_lets e)).
Proof.
  intros Pa e penv foracle Hwt Hdag Hpenv.
  exact (eval_expand_lets_with_equiv e [] penv [] foracle
           Hwt Hdag (wf_let_eval_sync_nil penv foracle) Hpenv).
Qed.


