(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Symbolic [(val, poison)] DAG Evaluator & Algebraic Refinement Rules

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
       [sz : positive], all 13 integer binary operators (proving poison-divisor
       UB on [udiv]/[urem]/[sdiv]/[srem] and out-of-bounds shift [>= sz] poison
       on [shl]/[lshr]/[ashr]), [icmp], [select], [zext]/[sext]/[trunc] (with
       [nneg]/[nuw]/[nsw]), and [freeze].
    5. Closed [CE_Let] DAG expansion ([expand_lets]) and its exact evaluation
       equivalence ([eval_expand_lets_equiv]), source UB assumption semantics
       ([ub_ctx_holds]), algebraic normalization ([normalize_cert_expr]),
       directional poison/flag/identity refinement ([check_expr_refines]),
       and a verified 2-rail [LRAT] fallback ([check_expr_refines_with_lrat]),
       backed by [check_expr_refines_sound] and
       [check_expr_refines_with_lrat_sound]. *)

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
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.Operations.Compare
  Semantics.Operations.Conversion
  Semantics.Operations.Select.

From CertValidator Require Import
  CertFormat
  AigLrat.

Unset Implicit Arguments.
Unset Strict Implicit.
Set Default Goal Selector "!".

Local Open Scope bool_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.

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
  destruct (Pos.eq_dec x y) as [_ | Hne]; [reflexivity | contradiction (Hne p)].
Qed.

Lemma alg_pos_nu_left_inv {x y : positive} (p : x = y) :
  Logic.eq_trans (Logic.eq_sym (alg_pos_nu Logic.eq_refl)) (alg_pos_nu p) = p.
Proof.
  destruct p; apply alg_eq_trans_sym_l.
Qed.

Lemma alg_pos_uip_refl (x : positive) (p : x = x) :
  p = Logic.eq_refl.
Proof.
  rewrite <- (alg_pos_nu_left_inv p), <- (alg_pos_nu_left_inv Logic.eq_refl).
  rewrite (alg_pos_nu_const p Logic.eq_refl).
  reflexivity.
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
  rewrite (@Integers.modulus_two_power_nat 1), (@Integers.natwordsize_def 1) in Hrng.
  cbn in Hrng.
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
  intros sz; unfold all_ones_N, Integers.mone.
  assert (Hpos : (0 <= Z.ones (Z.pos sz))%Z).
  { rewrite Z.ones_equiv.
    assert (Hp : (0 < 2 ^ Z.pos sz)%Z) by (apply Z.pow_pos_nonneg; lia).
    lia. }
  rewrite (Z2N.id _ Hpos).
  apply @Integers.same_bits_eq; intros i Hi.
  rewrite !@Integers.testbit_repr by exact Hi.
  unfold Integers.zwordsize in Hi.
  rewrite (Z.ones_spec_low (Z.pos sz) i Hi), (Z.bits_m1 i (proj1 Hi)).
  reflexivity.
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
  : option cert_expr :=
  match m with
  | [] => None
  | (k, v) :: rest => if String.eqb k nm then Some v else lookup_let_expr rest nm
  end.

Section ExpandLetBinds.
  Variable exp_e : list (string * cert_expr) -> cert_expr -> cert_expr.

  Fixpoint expand_let_binds (cur_m : list (string * cert_expr))
                            (xs : list (string * cert_expr))
    : list (string * cert_expr) :=
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

(** Non-dependent [freeze] choice oracle keyed by bitwidth and closed operand
    expression, yielding an integer representative mapped via [@Integers.repr]. *)
Definition freeze_oracle : Type := positive -> cert_expr -> Z.

Definition default_freeze_oracle : freeze_oracle :=
  fun _ _ => 0%Z.

Definition param_env (Pa : Params) : Type := string -> option (@dvalue Pa).

Definition let_val_env (Pa : Params) : Type :=
  list (string * (@dvalue Pa * cert_expr)).

Fixpoint lookup_let_val {Pa : Params} (lenv : let_val_env Pa) (nm : string)
  : option (@dvalue Pa) :=
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
    : EOU (let_val_env Pa) :=
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
          | None => raise_error ("unbound variable: " ++ nm)
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
    intros let_env Hwf; cbn in Hwf |- *; auto.
  - rewrite !andb_true_iff in Hwf; destruct Hwf as ([_ _] & Hlk); exact Hlk.
  - rewrite !andb_true_iff in Hwf |- *.
    destruct Hwf as (((((_ & Hfl) & Hl) & Hr) & Hwl) & Hwr).
    repeat split; auto.
  - rewrite !andb_true_iff in Hwf |- *.
    destruct Hwf as ((((_ & Hl) & Hr) & Hwl) & Hwr).
    repeat split; auto.
  - rewrite !andb_true_iff in Hwf |- *.
    destruct Hwf as ((Hsp & Ho) & Hwo).
    unfold wf_cast_spec in Hsp; rewrite !andb_true_iff in Hsp.
    destruct Hsp as ([_ _] & Hk).
    repeat split; auto.
  - rewrite !andb_true_iff in Hwf |- *.
    destruct Hwf as ((((((_ & Hc) & Ht) & Hf) & Hwc) & Hwt) & Hwf0).
    repeat split; auto.
  - rewrite !andb_true_iff in Hwf |- *.
    destruct Hwf as ((_ & Ho) & Hwo); split; auto.
  - destruct bs as [| b0 br]; [discriminate |].
    assert (Hstep :
      forall xs env seen env',
        Forall (fun p => forall le, wf_cert_expr le (snd p) = true ->
                                    wt_cert_expr le (snd p) = true) xs ->
        wf_let_binds_step wf_cert_expr env seen xs = Some env' ->
        wf_let_binds_step wt_cert_expr env seen xs = Some env').
    { induction xs as [| [bnm be] rx IHrx]; intros env seen env' HF Hs; cbn in Hs |- *; [exact Hs |].
      inversion HF as [| ? ? Hbe HFrx]; subst; cbn in Hbe.
      destruct (is_dollar_let_name bnm && negb (string_in_list bnm seen)) eqn:Hpre;
        cbn in Hs |- *; [| discriminate].
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
      right; exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | left; reflexivity].
  - destruct op; cbn;
      try (right; exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | left; reflexivity]);
      destruct (Z.eq_dec (@Integers.signed w ir) (-1)%Z); cbn;
      [left; eexists; reflexivity | right; exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | left; reflexivity]].
  - destruct op; cbn;
      try (left; eexists; reflexivity);
      right; exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | left; reflexivity].
  - unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct op; unfold cert_to_ibinop, eval_int_op; cbn;
      repeat match goal with
             | |- context [if ?b then _ else _] => destruct b
             end;
      cbn;
      try (left; eexists; reflexivity);
      right; eexists; split; [reflexivity |];
      try (left; reflexivity);
      right; eexists; reflexivity.
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
      cbn [mdtyp_of_int VIntVMemInt VInt_Bounded bitwidth dtyp_base_eq_dec dvp];
      repeat match goal with
             | |- context [if ?b then _ else _] => destruct b
             end;
      cbn; eexists; split; [reflexivity |];
      first [left; reflexivity | right; eexists; reflexivity].
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
      split; [reflexivity | left; reflexivity].
  - destruct k; cbn in Hk |- *; rewrite !andb_true_iff in Hk.
    + destruct Hk as ([Hlt _] & _); rewrite Pos.eqb_refl, Hlt; cbn.
      destruct (ccf_nneg fl && (@Integers.signed fw io <? 0)%Z); cbn;
        eexists; split; [reflexivity |];
        [left; reflexivity | right; eexists; reflexivity].
    + destruct Hk as (([Hlt _] & _) & _); rewrite Pos.eqb_refl, Hlt; cbn.
      eexists; split; [reflexivity | right; eexists; reflexivity].
    + destruct Hk as [Hlt _]; rewrite Pos.eqb_refl, Hlt; cbn.
      match goal with |- context [if ?b then _ else _] => destruct b end; cbn;
        eexists; split; [reflexivity |];
        [left; reflexivity | right; eexists; reflexivity].
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
    : list string * list (string * positive) :=
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
      right; eexists; split; [reflexivity | right; eexists; reflexivity].
  - cbn [wt_cert_expr collect_free_vars eval_cert_expr cert_expr_bit_width] in *.
    destruct (wf_let_binds_step wt_cert_expr let_widths [] bs) as [env' |] eqn:Hbs;
      [| discriminate].
    assert (Hstep :
      forall xs cur_lw seen cur_le,
        wf_let_binds_step wt_cert_expr cur_lw seen xs = Some env' ->
        wf_let_val_env cur_lw cur_le ->
        wf_param_env_for
          (let '(b', vs_xs) := collect_bind_vars collect_free_vars (List.map fst cur_lw) xs in
           vs_xs ++ collect_free_vars b' body) penv ->
        (exists msg,
           eval_let_binds (fun ce x => eval_cert_expr penv ce foracle x) cur_le xs =
           raise_ub msg) \/
        (exists lenv',
           eval_let_binds (fun ce x => eval_cert_expr penv ce foracle x) cur_le xs =
           raise_ret lenv' /\
           wf_let_val_env env' lenv' /\
           wf_param_env_for (collect_free_vars (List.map fst env') body) penv)).
    { induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_lw seen cur_le Hs Hcle Hcp; cbn in Hs.
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
    destruct (Hstep bs let_widths [] lenv Hbs Hlenv Hpenv)
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
      exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | left; reflexivity].
  - destruct op; cbn in Hop; try discriminate; cbn;
      exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | left; reflexivity].
  - destruct op; cbn in Hop; try discriminate; cbn;
      exists (DVALUE_Base DVALUE_Poison); split; [reflexivity | left; reflexivity].
  - unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct op; cbn in Hop; try discriminate;
      unfold cert_to_ibinop, eval_int_op; cbn;
      repeat match goal with
             | |- context [if ?b then _ else _] => destruct b
             end;
      cbn; eexists; split; [reflexivity |];
      first [left; reflexivity | right; eexists; reflexivity].
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
    rewrite !andb_true_iff in Hubf, Hwt.
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
    rewrite !andb_true_iff in Hubf, Hwt.
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
    rewrite !andb_true_iff in Hubf, Hwt.
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
      forall xs cur_lw seen cur_le s,
        ub_free_let_binds ub_free_expr xs = true ->
        wf_let_binds_step wt_cert_expr cur_lw seen xs = Some env' ->
        eval_let_binds (fun ce x => eval_cert_expr penv ce foracle x) cur_le xs <> raise_ub s).
    { induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_lw seen cur_le s Hub_xs Hs Hev_xs; cbn in *.
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
    + inversion Hev; subst s; exact (Hstep bs let_widths [] lenv msg Hub_bs Hbs Ebs).
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
                            (xs : list (string * cert_expr)) : bool :=
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
      cbn; repeat split; [exact Hwt | reflexivity].
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
      forall xs cur_lw seen cur_m,
        wf_let_binds_step wt_cert_expr cur_lw seen xs = Some env' ->
        wf_let_subst cur_lw cur_m ->
        wf_let_subst env' (expand_let_binds expand_lets_with cur_m xs)).
    { induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_lw seen cur_m Hs Hcs; cbn in *.
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
               Hwt (Hstep bs lw [] m Hbs (conj Hdom Hsub))).
Qed.

Lemma lookup_let_expr_in : forall m nm ce,
  lookup_let_expr m nm = Some ce -> exists k, In (k, ce) m.
Proof.
  induction m as [| [k v] rest IH]; intros nm ce H; cbn in H; [discriminate |].
  destruct (String.eqb k nm).
  - inversion H; subst; exists k; left; reflexivity.
  - destruct (IH nm ce H) as [k' Hk']; exists k'; right; exact Hk'.
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
      forall xs cur_m,
        (forall k ce, In (k, ce) cur_m -> incl (collect_free_vars [] ce) V) ->
        incl (let '(b', vs_xs) := collect_bind_vars collect_free_vars (List.map fst cur_m) xs in
              vs_xs ++ collect_free_vars b' body) V ->
        (forall k ce, In (k, ce) (expand_let_binds expand_lets_with cur_m xs) ->
                      incl (collect_free_vars [] ce) V) /\
        incl (collect_free_vars (List.map fst (expand_let_binds expand_lets_with cur_m xs)) body) V).
    { induction IHbs as [| [bnm be] rx IHbe _ IHrx];
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
    destruct (Hstep bs m Hm He') as [Hm' Hbody'].
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
  intros Pa penv foracle; repeat split.
  - apply wf_let_val_env_nil.
  - intros nm; cbn; exact I.
  - intros nm; cbn; exact I.
  - intros k ce [].
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
    rewrite !andb_true_iff in Hwt, Hdag.
    destruct Hwt as ((((_ & Hwtl) & Hwtr) & _) & _); destruct Hdag as [Hdl Hdr].
    assert (Hpl : wf_param_env_for (collect_free_vars (List.map fst lw) l) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars (List.map fst lw) r) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
    apply eou_bind_equiv_cong; [exact (IHl lw penv lenv foracle Hwtl Hdl Hsync Hpl) | intros vl].
    apply eou_bind_equiv_cong; [exact (IHr lw penv lenv foracle Hwtr Hdr Hsync Hpr) | intros vr].
    apply equiv_eou_dvalue_refl.
  - cbn [wt_cert_expr wf_let_dag collect_free_vars eval_cert_expr expand_lets_with] in *.
    rewrite !andb_true_iff in Hwt, Hdag.
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
    rewrite !andb_true_iff in Hwt, Hdag.
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
        induction xs as [| [bnm be] rx IHrx]; intros cur_lw seen cur_m Hs Hcs; cbn in *.
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
      forall xs cur_lw seen cur_le,
        wf_let_binds_step wt_cert_expr cur_lw seen xs = Some env' ->
        wf_let_dag_binds wf_let_dag exp_body (let_val_exprs cur_le) xs = true ->
        wf_let_eval_sync penv foracle cur_lw cur_le ->
        wf_param_env_for
          (let '(b', vs_xs) := collect_bind_vars collect_free_vars (List.map fst cur_lw) xs in
           vs_xs ++ collect_free_vars b' body) penv ->
        (exists msg_l msg_r,
           eval_let_binds (fun ce x => eval_cert_expr penv ce foracle x) cur_le xs = raise_ub msg_l /\
           eval_cert_expr penv [] foracle exp_body = raise_ub msg_r) \/
        (exists lenv',
           eval_let_binds (fun ce x => eval_cert_expr penv ce foracle x) cur_le xs = raise_ret lenv' /\
           let_val_exprs lenv' = expand_let_binds expand_lets_with (let_val_exprs cur_le) xs /\
           wf_let_eval_sync penv foracle env' lenv' /\
           wf_param_env_for (collect_free_vars (List.map fst env') body) penv)).
    { induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_lw seen cur_le Hs Hd Hsy Hcp; cbn in Hs, Hd.
      - inversion Hs; subst cur_lw; cbn in Hcp.
        right; exists cur_le; repeat split; try assumption; reflexivity.
      - cbn in IHbe.
        destruct (is_dollar_let_name bnm && negb (string_in_list bnm seen) &&
                  wt_cert_expr cur_lw be) eqn:Hok; [| discriminate].
        rewrite !andb_true_iff in Hok, Hd.
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
            as [| msg_exp | |] eqn:Eexp_be; cbn in Heq_be; try contradiction.
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
    destruct (Hstep bs lw [] lenv Hbs Hdag_bs Hsync Hpenv)
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


(** ** 6. Source UB Context, Algebraic Normalization & Directional Refinement *)

Definition ub_ctx : Type := list ub_assumption.

Definition ub_assumption_holds {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle) (ua : ub_assumption) : Prop :=
  match ua with
  | UBA_ParamNoUndef param _ =>
      forall dv, penv param = Some dv -> dv <> DVALUE_Base DVALUE_Poison
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
  | UBA_PtrNonNull _
  | UBA_PtrAligned _ _
  | UBA_PtrDereferenceable _ _
  | UBA_LoadNoUndef _ _ => True
  end.

Definition ub_ctx_holds {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle) (ctx : ub_ctx) : Prop :=
  Forall (ub_assumption_holds penv foracle) ctx.

Fixpoint ctx_has_unreachable (ctx : ub_ctx) : bool :=
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

Fixpoint ctx_has_param_noundef (ctx : ub_ctx) (nm : string) (w : positive) : bool :=
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

Fixpoint ctx_has_divisor_nonzero (ctx : ub_ctx) (e : cert_expr) : bool :=
  match ctx with
  | [] => false
  | UBA_DivisorNonZero d :: rest =>
      cert_expr_eqb (expand_lets d) e || ctx_has_divisor_nonzero rest e
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
  apply cert_expr_eqb_eq in Hhere; subst e; exact Hua.
Qed.

Fixpoint ctx_has_branch_cond_defined (ctx : ub_ctx) (e : cert_expr) : bool :=
  match ctx with
  | [] => false
  | UBA_BranchCondDefined c :: rest =>
      cert_expr_eqb (expand_lets c) e || ctx_has_branch_cond_defined rest e
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
  apply cert_expr_eqb_eq in Hhere; subst e; exact (Hua v Hev).
Qed.

(** *** 6.1 Guaranteed Non-Poison & UB-Free Expression Analysis *)

Fixpoint expr_guaranteed_defined (ctx : ub_ctx) (e : cert_expr) : bool :=
  match e with
  | CE_BvConst _ _ => true
  | CE_Poison _ | CE_Let _ _ => false
  | CE_Var nm w =>
      ctx_has_param_noundef ctx nm w || ctx_has_branch_cond_defined ctx (CE_Var nm w)
  | CE_Freeze _ o =>
      ub_free_expr o
  | CE_BinOp op _ fl l r =>
      negb (is_div_or_rem_op op) &&
      negb (is_shift_op op) &&
      cert_binop_flags_eqb fl no_binop_flags &&
      expr_guaranteed_defined ctx l &&
      expr_guaranteed_defined ctx r
  | CE_ICmp _ ss _ l r =>
      negb ss &&
      expr_guaranteed_defined ctx l &&
      expr_guaranteed_defined ctx r
  | CE_Cast CCK_ZExt _ _ fl o =>
      negb (ccf_nneg fl) && expr_guaranteed_defined ctx o
  | CE_Cast CCK_SExt _ _ _ o =>
      expr_guaranteed_defined ctx o
  | CE_Cast CCK_Trunc _ _ fl o =>
      negb (ccf_nuw fl) && negb (ccf_nsw fl) && expr_guaranteed_defined ctx o
  | CE_Select _ c t f =>
      expr_guaranteed_defined ctx c &&
      expr_guaranteed_defined ctx t &&
      expr_guaranteed_defined ctx f
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
    + exact (ctx_has_param_noundef_sound penv foracle ctx nm w _ Hnu Hctx Hpm eq_refl).
    + exact (ctx_has_branch_cond_defined_sound penv foracle ctx _ _ Hbr Hctx Hev eq_refl).
  - cbn [expr_guaranteed_defined wt_cert_expr collect_free_vars cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hdef, Hwt.
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
  - cbn [expr_guaranteed_defined wt_cert_expr collect_free_vars cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hdef, Hwt.
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
  - cbn [wt_cert_expr collect_free_vars cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((Hk & Hwto) & Hwo).
    apply Pos.eqb_eq in Hwo.
    destruct k; cbn [expr_guaranteed_defined] in Hdef.
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
  - cbn [expr_guaranteed_defined wt_cert_expr collect_free_vars cert_expr_bit_width] in *.
    rewrite !andb_true_iff in Hdef, Hwt.
    destruct Hdef as ([Hdc Hdt] & Hdf).
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hwc) & Hwt0) & Hwf0).
    apply Pos.eqb_eq in Hwc; apply Pos.eqb_eq in Hwt0; apply Pos.eqb_eq in Hwf0.
    assert (Hpc : wf_param_env_for (collect_free_vars [] c) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpt : wf_param_env_for (collect_free_vars [] t) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; left; exact Hx).
    assert (Hpf : wf_param_env_for (collect_free_vars [] f) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; right; exact Hx).
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
    unfold cert_to_ibinop, eval_int_op; cbn;
    repeat match goal with
           | H : ?b = false |- context [if ?b then _ else _] => rewrite H
           | |- context [if ?b then _ else _] => destruct b
           end;
    unfold mk_bv_const; cbn;
    repeat split; try reflexivity;
    rewrite repr_of_N_to_N_unsigned; reflexivity.
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
  unfold fold_const_icmp; destruct pr; unfold cert_to_icmp, eval_int_icmp; cbn;
    destruct (ss && _); cbn;
    try (repeat split; reflexivity);
    (match goal with |- context [if ?c then _ else _] => destruct c end;
     cbn; repeat split; try reflexivity;
     [rewrite repr_one_N; reflexivity | rewrite repr_zero_N; reflexivity]).
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
  destruct k; cbn in Hk |- *; rewrite !andb_true_iff in Hk.
  - destruct Hk as ([Hlt _] & _); rewrite Pos.eqb_refl, Hlt; cbn.
    destruct (ccf_nneg fl && (@Integers.signed fw (@Integers.repr fw (Z.of_N val)) <? 0)%Z);
      unfold mk_bv_const; cbn; repeat split; try reflexivity;
      rewrite repr_of_N_to_N_unsigned; reflexivity.
  - destruct Hk as (([Hlt _] & _) & _); rewrite Pos.eqb_refl, Hlt.
    unfold mk_bv_const; cbn; repeat split; try reflexivity;
      rewrite repr_of_N_to_N_unsigned; reflexivity.
  - destruct Hk as [Hlt _]; rewrite Pos.eqb_refl, Hlt; cbn.
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

Definition norm_binop_step
  (ctx : ub_ctx) (op : cert_binop) (w : positive) (fl : cert_binop_flags)
  (nl nr : cert_expr) : cert_expr :=
  match try_fold_const_binop op w fl nl nr with
  | Some c => c
  | None =>
      if cert_binop_flags_eqb fl no_binop_flags then
        match op with
        | CB_Add =>
            if is_zero_const_expr w nr then nl
            else if is_zero_const_expr w nl then nr
            else CE_BinOp op w fl nl nr
        | CB_Sub =>
            if is_zero_const_expr w nr then nl
            else if cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl
                 then CE_BvConst w 0%N
            else CE_BinOp op w fl nl nr
        | CB_Mul =>
            if is_one_const_expr w nr then nl
            else if is_one_const_expr w nl then nr
            else if is_zero_const_expr w nr && expr_guaranteed_defined ctx nl
                 then CE_BvConst w 0%N
            else if is_zero_const_expr w nl && expr_guaranteed_defined ctx nr
                 then CE_BvConst w 0%N
            else CE_BinOp op w fl nl nr
        | CB_And =>
            if is_all_ones_const_expr w nr then nl
            else if is_all_ones_const_expr w nl then nr
            else if cert_expr_eqb nl nr then nl
            else if is_zero_const_expr w nr && expr_guaranteed_defined ctx nl
                 then CE_BvConst w 0%N
            else if is_zero_const_expr w nl && expr_guaranteed_defined ctx nr
                 then CE_BvConst w 0%N
            else CE_BinOp op w fl nl nr
        | CB_Or =>
            if is_zero_const_expr w nr then nl
            else if is_zero_const_expr w nl then nr
            else if cert_expr_eqb nl nr then nl
            else if is_all_ones_const_expr w nr && expr_guaranteed_defined ctx nl
                 then CE_BvConst w (all_ones_N w)
            else if is_all_ones_const_expr w nl && expr_guaranteed_defined ctx nr
                 then CE_BvConst w (all_ones_N w)
            else CE_BinOp op w fl nl nr
        | CB_Xor =>
            if is_zero_const_expr w nr then nl
            else if is_zero_const_expr w nl then nr
            else if cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl
                 then CE_BvConst w 0%N
            else CE_BinOp op w fl nl nr
        | CB_Shl | CB_LShr | CB_AShr =>
            if is_zero_const_expr w nr then nl
            else CE_BinOp op w fl nl nr
        | _ => CE_BinOp op w fl nl nr
        end
      else CE_BinOp op w fl nl nr
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
  assert (Hdef_out :
    cert_expr_bit_width (CE_BinOp op w fl nl nr) = w /\
    wt_cert_expr [] (CE_BinOp op w fl nl nr) = true /\
    is_let_free_expr (CE_BinOp op w fl nl nr) = true /\
    incl (collect_free_vars [] (CE_BinOp op w fl nl nr))
         (collect_free_vars [] nl ++ collect_free_vars [] nr)).
  { cbn; rewrite Hfl, Htl, Htr, Hwl, Hwr, !Pos.eqb_refl, Hfl_l, Hfl_r;
      repeat split; [reflexivity | apply incl_refl]. }
  assert (Hl_out :
    cert_expr_bit_width nl = w /\
    wt_cert_expr [] nl = true /\
    is_let_free_expr nl = true /\
    incl (collect_free_vars [] nl) (collect_free_vars [] nl ++ collect_free_vars [] nr))
    by (repeat split; [exact Hwl | exact Htl | exact Hfl_l | apply incl_appl, incl_refl]).
  assert (Hr_out :
    cert_expr_bit_width nr = w /\
    wt_cert_expr [] nr = true /\
    is_let_free_expr nr = true /\
    incl (collect_free_vars [] nr) (collect_free_vars [] nl ++ collect_free_vars [] nr))
    by (repeat split; [exact Hwr | exact Htr | exact Hfl_r | apply incl_appr, incl_refl]).
  assert (Hc_out : forall cval,
    cert_expr_bit_width (CE_BvConst w cval) = w /\
    wt_cert_expr [] (CE_BvConst w cval) = true /\
    is_let_free_expr (CE_BvConst w cval) = true /\
    incl (collect_free_vars [] (CE_BvConst w cval))
         (collect_free_vars [] nl ++ collect_free_vars [] nr))
    by (intros cval; cbn; repeat split; intros x []).
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
  - destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
    destruct op; try exact Hdef_out;
      repeat match goal with
             | |- context [if ?b then _ else _] => destruct b
             end;
      first [exact Hl_out | exact Hr_out | apply Hc_out | exact Hdef_out].
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
  assert (Hpl : wf_param_env_for (collect_free_vars [] nl) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
  assert (Hpr : wf_param_env_for (collect_free_vars [] nr) penv)
    by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
  assert (Htot_l :
    (exists msg, eval_closed_cert_expr penv foracle nl = raise_ub msg) \/
    (exists vl, eval_closed_cert_expr penv foracle nl = raise_ret vl /\ wf_scalar_dvalue w vl)).
  { rewrite <- Hwl at 1.
    exact (eval_cert_expr_totality nl [] penv [] foracle Htl wf_let_val_env_nil Hpl). }
  assert (Htot_r :
    (exists msg, eval_closed_cert_expr penv foracle nr = raise_ub msg) \/
    (exists vr, eval_closed_cert_expr penv foracle nr = raise_ret vr /\ wf_scalar_dvalue w vr)).
  { rewrite <- Hwr at 1.
    exact (eval_cert_expr_totality nr [] penv [] foracle Htr wf_let_val_env_nil Hpr). }
  assert (Hid_r : forall cval,
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
      (eval_closed_cert_expr penv foracle nl)).
  { intros cval Hfl0 -> Hiop Hndiv.
    apply cert_binop_flags_eqb_eq in Hfl0; subst fl.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]]; cbn [eou_bind].
    - exact I.
    - destruct op; cbn in Hndiv; try discriminate; cbn; reflexivity.
    - rewrite Hiop; cbn; reflexivity. }
  assert (Hid_l : forall cval,
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
      (eval_closed_cert_expr penv foracle nr)).
  { intros cval Hfl0 -> Hiop Hndiv.
    apply cert_binop_flags_eqb_eq in Hfl0; subst fl.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
    destruct Htot_r as [[msgr ->] | [vr [-> [-> | [ir ->]]]]]; cbn [eou_bind].
    - exact I.
    - destruct op; cbn in Hndiv; try discriminate; cbn; reflexivity.
    - rewrite Hiop; cbn; reflexivity. }
  unfold norm_binop_step.
  destruct (try_fold_const_binop op w fl nl nr) as [c |] eqn:Etc.
  - exact (proj2 (proj2 (proj2 (proj2 (try_fold_const_binop_sound op w fl nl nr c penv foracle Etc))))).
  - destruct (cert_binop_flags_eqb fl no_binop_flags) eqn:Efl; [| apply equiv_eou_dvalue_refl].
    destruct op; try apply equiv_eou_dvalue_refl.
    + (* CB_Add *)
      destruct (is_zero_const_expr w nr) eqn:Ezr.
      * apply (Hid_r 0%N Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
        cbn; rewrite Integers.add_zero; reflexivity.
      * destruct (is_zero_const_expr w nl) eqn:Ezl; [| apply equiv_eou_dvalue_refl].
        apply (Hid_l 0%N Efl (is_zero_const_expr_inv w nl Ezl)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
        cbn; rewrite Integers.add_zero_l; reflexivity.
    + (* CB_Sub *)
      destruct (is_zero_const_expr w nr) eqn:Ezr.
      * apply (Hid_r 0%N Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
        cbn; rewrite Integers.sub_zero_l; reflexivity.
      * destruct (cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl) eqn:Eself;
          [| apply equiv_eou_dvalue_refl].
        apply andb_true_iff in Eself as [Eeq Edef].
        apply cert_expr_eqb_eq in Eeq; subst nr.
        apply cert_binop_flags_eqb_eq in Efl; subst fl.
        destruct (expr_guaranteed_defined_sound ctx nl penv foracle Edef Htl Hpl Hctx)
          as [_ [il Hil]].
        revert il Hil; rewrite Hwl; intros il Hil.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil; cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
        cbn; rewrite Integers.sub_idem; reflexivity.
    + (* CB_Mul *)
      destruct (is_one_const_expr w nr) eqn:E1r.
      * apply (Hid_r 1%N Efl (is_one_const_expr_inv w nr E1r)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_one_N.
        cbn; destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_one; reflexivity.
      * destruct (is_one_const_expr w nl) eqn:E1l.
        -- apply (Hid_l 1%N Efl (is_one_const_expr_inv w nl E1l)); [| reflexivity].
           intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_one_N.
           cbn; destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_commut, Integers.mul_one; reflexivity.
        -- destruct (is_zero_const_expr w nr && expr_guaranteed_defined ctx nl) eqn:Ezr.
           ++ apply andb_true_iff in Ezr as [Ez0 Edef].
              rewrite (is_zero_const_expr_inv w nr Ez0).
              apply cert_binop_flags_eqb_eq in Efl; subst fl.
              destruct (expr_guaranteed_defined_sound ctx nl penv foracle Edef Htl Hpl Hctx)
                as [_ [il Hil]].
              revert il Hil; rewrite Hwl; intros il Hil.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil; cbn [eou_bind].
              unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
              cbn; destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_zero; reflexivity.
           ++ destruct (is_zero_const_expr w nl && expr_guaranteed_defined ctx nr) eqn:Ezl;
                [| apply equiv_eou_dvalue_refl].
              apply andb_true_iff in Ezl as [Ez0 Edef].
              rewrite (is_zero_const_expr_inv w nl Ez0).
              apply cert_binop_flags_eqb_eq in Efl; subst fl.
              destruct (expr_guaranteed_defined_sound ctx nr penv foracle Edef Htr Hpr Hctx)
                as [_ [ir Hir]].
              revert ir Hir; rewrite Hwr; intros ir Hir.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hir; cbn [eou_bind].
              unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
              cbn; destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_commut, Integers.mul_zero; reflexivity.
    + (* CB_Shl *)
      destruct (is_zero_const_expr w nr) eqn:Ezr; [| apply equiv_eou_dvalue_refl].
      apply (Hid_r 0%N Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
      intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
      unfold cert_to_ibinop, eval_int_op; cbn.
      rewrite Integers.unsigned_zero; cbn; rewrite alg_shl_zero; reflexivity.
    + (* CB_LShr *)
      destruct (is_zero_const_expr w nr) eqn:Ezr; [| apply equiv_eou_dvalue_refl].
      apply (Hid_r 0%N Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
      intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
      unfold cert_to_ibinop, eval_int_op; cbn.
      rewrite Integers.unsigned_zero; cbn; rewrite alg_shru_zero; reflexivity.
    + (* CB_AShr *)
      destruct (is_zero_const_expr w nr) eqn:Ezr; [| apply equiv_eou_dvalue_refl].
      apply (Hid_r 0%N Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
      intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
      unfold cert_to_ibinop, eval_int_op; cbn.
      rewrite Integers.unsigned_zero; cbn; rewrite alg_shr_zero; reflexivity.
    + (* CB_And *)
      destruct (is_all_ones_const_expr w nr) eqn:Emr.
      * apply (Hid_r (all_ones_N w) Efl (is_all_ones_const_expr_inv w nr Emr)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N.
        cbn; rewrite Integers.and_mone; reflexivity.
      * destruct (is_all_ones_const_expr w nl) eqn:Eml.
        -- apply (Hid_l (all_ones_N w) Efl (is_all_ones_const_expr_inv w nl Eml)); [| reflexivity].
           intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N.
           cbn; rewrite Integers.and_mone_l; reflexivity.
        -- destruct (cert_expr_eqb nl nr) eqn:Eidem.
           ++ apply cert_expr_eqb_eq in Eidem; subst nr.
              apply cert_binop_flags_eqb_eq in Efl; subst fl.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
              destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]]; cbn [eou_bind];
                [exact I | reflexivity |].
              unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn.
              rewrite Integers.and_idem; reflexivity.
           ++ destruct (is_zero_const_expr w nr && expr_guaranteed_defined ctx nl) eqn:Ezr.
              ** apply andb_true_iff in Ezr as [Ez0 Edef].
                 rewrite (is_zero_const_expr_inv w nr Ez0).
                 apply cert_binop_flags_eqb_eq in Efl; subst fl.
                 destruct (expr_guaranteed_defined_sound ctx nl penv foracle Edef Htl Hpl Hctx)
                   as [_ [il Hil]].
                 revert il Hil; rewrite Hwl; intros il Hil.
                 unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil; cbn [eou_bind].
                 unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
                 cbn; rewrite Integers.and_zero; reflexivity.
              ** destruct (is_zero_const_expr w nl && expr_guaranteed_defined ctx nr) eqn:Ezl;
                   [| apply equiv_eou_dvalue_refl].
                 apply andb_true_iff in Ezl as [Ez0 Edef].
                 rewrite (is_zero_const_expr_inv w nl Ez0).
                 apply cert_binop_flags_eqb_eq in Efl; subst fl.
                 destruct (expr_guaranteed_defined_sound ctx nr penv foracle Edef Htr Hpr Hctx)
                   as [_ [ir Hir]].
                 revert ir Hir; rewrite Hwr; intros ir Hir.
                 unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hir; cbn [eou_bind].
                 unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
                 cbn; rewrite Integers.and_zero_l; reflexivity.
    + (* CB_Or *)
      destruct (is_zero_const_expr w nr) eqn:Ezr.
      * apply (Hid_r 0%N Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
        cbn; rewrite Integers.or_zero; reflexivity.
      * destruct (is_zero_const_expr w nl) eqn:Ezl.
        -- apply (Hid_l 0%N Efl (is_zero_const_expr_inv w nl Ezl)); [| reflexivity].
           intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
           cbn; rewrite Integers.or_zero_l; reflexivity.
        -- destruct (cert_expr_eqb nl nr) eqn:Eidem.
           ++ apply cert_expr_eqb_eq in Eidem; subst nr.
              apply cert_binop_flags_eqb_eq in Efl; subst fl.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
              destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]]; cbn [eou_bind];
                [exact I | reflexivity |].
              unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn.
              rewrite Integers.or_idem; reflexivity.
           ++ destruct (is_all_ones_const_expr w nr && expr_guaranteed_defined ctx nl) eqn:Emr.
              ** apply andb_true_iff in Emr as [Em0 Edef].
                 rewrite (is_all_ones_const_expr_inv w nr Em0).
                 apply cert_binop_flags_eqb_eq in Efl; subst fl.
                 destruct (expr_guaranteed_defined_sound ctx nl penv foracle Edef Htl Hpl Hctx)
                   as [_ [il Hil]].
                 revert il Hil; rewrite Hwl; intros il Hil.
                 unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil; cbn [eou_bind].
                 unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N.
                 cbn; rewrite Integers.or_mone; reflexivity.
              ** destruct (is_all_ones_const_expr w nl && expr_guaranteed_defined ctx nr) eqn:Eml;
                   [| apply equiv_eou_dvalue_refl].
                 apply andb_true_iff in Eml as [Em0 Edef].
                 rewrite (is_all_ones_const_expr_inv w nl Em0).
                 apply cert_binop_flags_eqb_eq in Efl; subst fl.
                 destruct (expr_guaranteed_defined_sound ctx nr penv foracle Edef Htr Hpr Hctx)
                   as [_ [ir Hir]].
                 revert ir Hir; rewrite Hwr; intros ir Hir.
                 unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hir; cbn [eou_bind].
                 unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N.
                 cbn; rewrite Integers.or_commut, Integers.or_mone; reflexivity.
    + (* CB_Xor *)
      destruct (is_zero_const_expr w nr) eqn:Ezr.
      * apply (Hid_r 0%N Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
        cbn; rewrite Integers.xor_zero; reflexivity.
      * destruct (is_zero_const_expr w nl) eqn:Ezl.
        -- apply (Hid_l 0%N Efl (is_zero_const_expr_inv w nl Ezl)); [| reflexivity].
           intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
           cbn; rewrite Integers.xor_zero_l; reflexivity.
        -- destruct (cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl) eqn:Eself;
             [| apply equiv_eou_dvalue_refl].
           apply andb_true_iff in Eself as [Eeq Edef].
           apply cert_expr_eqb_eq in Eeq; subst nr.
           apply cert_binop_flags_eqb_eq in Efl; subst fl.
           destruct (expr_guaranteed_defined_sound ctx nl penv foracle Edef Htl Hpl Hctx)
             as [_ [il Hil]].
           revert il Hil; rewrite Hwl; intros il Hil.
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
           cbn; rewrite Integers.xor_idem; reflexivity.
Qed.


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

Definition norm_icmp_step
  (ctx : ub_ctx) (pr : cert_icmp_pred) (ss : bool) (w : positive)
  (nl nr : cert_expr) : cert_expr :=
  match try_fold_const_icmp pr ss w nl nr with
  | Some c => c
  | None =>
      if negb ss && cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl
      then CE_BvConst 1%positive (if is_refl_true_icmp pr then 1%N else 0%N)
      else CE_ICmp pr ss w nl nr
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
    + cbn; rewrite Htl, Htr, Hwl, Hwr, !Pos.eqb_refl, Hfl_l, Hfl_r.
      repeat split; [reflexivity | apply incl_refl].
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
  intros Pa ctx pr ss w nl nr penv foracle Hwl _ Htl _ Hpenv Hctx.
  unfold norm_icmp_step.
  destruct (try_fold_const_icmp pr ss w nl nr) as [c |] eqn:Etc.
  - destruct nl as [w1 v1 | | | | | | | |]; try discriminate Etc.
    destruct nr as [w2 v2 | | | | | | | |]; try discriminate Etc.
    cbn [try_fold_const_icmp] in Etc.
    destruct (Pos.eqb w1 w && Pos.eqb w2 w) eqn:Eww; [| discriminate Etc].
    apply andb_true_iff in Eww as [Ew1 Ew2]; apply Pos.eqb_eq in Ew1; apply Pos.eqb_eq in Ew2.
    inversion Etc; subst w1 w2 c.
    exact (proj2 (proj2 (proj2 (proj2 (fold_const_icmp_sound pr ss w v1 v2 penv foracle))))).
  - destruct (negb ss && cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl) eqn:Erefl;
      [| apply equiv_eou_dvalue_refl].
    rewrite !andb_true_iff in Erefl; destruct Erefl as ([Ess Eeq] & Edef).
    apply negb_true_iff in Ess; apply cert_expr_eqb_eq in Eeq; subst ss nr.
    assert (Hpl : wf_param_env_for (collect_free_vars [] nl) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    destruct (expr_guaranteed_defined_sound ctx nl penv foracle Edef Htl Hpl Hctx)
      as [_ [il Hil]].
    revert il Hil; rewrite Hwl; intros il Hil.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil; cbn [eou_bind].
    rewrite alg_eval_icmp_refl; cbn.
    destruct (is_refl_true_icmp pr);
      [rewrite repr_one_N; reflexivity | rewrite repr_zero_N; reflexivity].
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

Definition norm_cast_step
  (k : cert_cast_kind) (fw tw : positive) (fl : cert_cast_flags) (no : cert_expr)
  : cert_expr :=
  match try_fold_const_cast k fw tw fl no with
  | Some c => c
  | None => CE_Cast k fw tw fl no
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
  destruct (try_fold_const_cast k fw tw fl no) as [c |] eqn:Etc.
  - destruct no as [fw' val | pw | | | | | | |]; try discriminate Etc;
      cbn [try_fold_const_cast] in Etc.
    + destruct (Pos.eqb fw' fw); [| discriminate Etc].
      inversion Etc; subst c; clear Etc.
      unfold fold_const_cast; destruct k;
        repeat match goal with |- context [if ?b then _ else _] => destruct b end;
        unfold mk_bv_const; cbn; repeat split; intros x [].
    + inversion Etc; subst c; cbn; repeat split; intros x [].
  - cbn; rewrite Hk, Hto, Hwo, Pos.eqb_refl, Hfl_o.
    repeat split; [reflexivity | apply incl_refl].
Qed.

Lemma norm_cast_step_eval :
  forall {Pa : Params} k fw tw fl no (penv : param_env Pa) foracle,
    match k with
    | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg fl) && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg fl)
    end = true ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_Cast k fw tw fl no))
      (eval_closed_cert_expr penv foracle (norm_cast_step k fw tw fl no)).
Proof.
  intros Pa k fw tw fl no penv foracle Hk.
  unfold norm_cast_step.
  destruct (try_fold_const_cast k fw tw fl no) as [c |] eqn:Etc;
    [| apply equiv_eou_dvalue_refl].
  destruct no as [fw' val | pw | | | | | | |]; try discriminate Etc;
    cbn [try_fold_const_cast] in Etc.
  - destruct (Pos.eqb fw' fw) eqn:Efw; [| discriminate Etc].
    apply Pos.eqb_eq in Efw; inversion Etc; subst fw' c.
    exact (proj2 (proj2 (proj2 (proj2 (fold_const_cast_sound k fw tw fl val penv foracle Hk))))).
  - inversion Etc; subst c; destruct k; cbn; reflexivity.
Qed.

Definition norm_select_step
  (ctx : ub_ctx) (w : positive) (nc nt nf : cert_expr) : cert_expr :=
  if is_one_const_expr 1%positive nc && ub_free_expr nf then nt
  else if is_zero_const_expr 1%positive nc && ub_free_expr nt then nf
  else if cert_expr_eqb nt nf && expr_guaranteed_defined ctx nc then nt
  else CE_Select w nc nt nf.

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
      * cbn; rewrite Htc, Htt, Htf, Hwc, Hwt0, Hwf0, !Pos.eqb_refl, Hlc, Hlt, Hlf.
        repeat split; [reflexivity | apply incl_refl].
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
    + destruct (cert_expr_eqb nt nf && expr_guaranteed_defined ctx nc) eqn:Esame;
        [| apply equiv_eou_dvalue_refl].
      apply andb_true_iff in Esame as [Eeq Edefc].
      apply cert_expr_eqb_eq in Eeq; subst nf.
      destruct (expr_guaranteed_defined_sound ctx nc penv foracle Edefc Htc Hpc Hctx)
        as [_ [ic Hic]].
      revert ic Hic; rewrite Hwc; intros ic Hic.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hic; cbn [eou_bind].
      destruct (eval_cert_expr_totality nt [] penv [] foracle Htt wf_let_val_env_nil Hpt)
        as [[msgt ->] | [vt [-> _]]]; [cbn; exact I | cbn [eou_bind]].
      cbn; destruct (@Integers.unsigned 1 ic =? 1)%Z; reflexivity.
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
    rewrite !andb_true_iff in Hwt, Hlf.
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
    rewrite !andb_true_iff in Hwt, Hlf.
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
    rewrite !andb_true_iff in Hwt, Hlf.
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
    + destruct o as [| | | | | | | w' inner |];
        try (cbn; rewrite Hwto, Hwo, Pos.eqb_refl, Hlf; repeat split; apply incl_refl).
      destruct (Pos.eqb w' w) eqn:Eww'.
      * apply Pos.eqb_eq in Eww'; subst w'.
        cbn in Hwto, Hlf |- *; rewrite Hwto, Hlf; repeat split; apply incl_refl.
      * cbn in Hwto, Hlf |- *; rewrite Hwto, Hwo, Pos.eqb_refl, Hlf; repeat split; apply incl_refl.
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
    rewrite !andb_true_iff in Hwt, Hlf.
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
    apply (norm_binop_step_eval ctx op w fl _ _ penv foracle Hfl Hbl Hbr Htl Htr _ Hctx).
    intros x wx Hx; apply in_app_iff in Hx as [Hxl | Hxr];
      [exact (Hpl x wx (Hinc_l _ Hxl)) | exact (Hpr x wx (Hinc_r _ Hxr))].
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars normalize_cert_expr] in *.
    rewrite !andb_true_iff in Hwt, Hlf.
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
    apply (norm_icmp_step_eval ctx pr ss w _ _ penv foracle Hbl Hbr Htl Htr _ Hctx).
    intros x wx Hx; apply in_app_iff in Hx as [Hxl | Hxr];
      [exact (Hpl x wx (Hinc_l _ Hxl)) | exact (Hpr x wx (Hinc_r _ Hxr))].
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars normalize_cert_expr] in *.
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((Hk & Hwto) & _).
    assert (Hcong : equiv_eou_dvalue
                      (eval_closed_cert_expr penv foracle (CE_Cast k fw tw fl o))
                      (eval_closed_cert_expr penv foracle
                         (CE_Cast k fw tw fl (normalize_cert_expr ctx o)))).
    { unfold eval_closed_cert_expr; cbn [eval_cert_expr].
      apply eou_bind_equiv_cong;
        [exact (IHo penv foracle Hwto Hlf Hpenv Hctx) | intros vo; apply equiv_eou_dvalue_refl]. }
    exact (equiv_eou_dvalue_trans _ _ _ Hcong (norm_cast_step_eval k fw tw fl _ penv foracle Hk)).
  - cbn [wt_cert_expr is_let_free_expr collect_free_vars normalize_cert_expr] in *.
    rewrite !andb_true_iff in Hwt, Hlf.
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
    apply (norm_select_step_eval ctx w _ _ _ penv foracle Hbc Hbt Hbf Htc Htt Htf _ Hctx).
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
    injection Hi' as Heq_base.
    pose proof (dvalue_I_width_eq w0 (cert_expr_bit_width e) i0 i' Heq_base) as Hw_eq.
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
          unfold cert_to_ibinop, eval_int_op; cbn.
        -- destruct (cbf_nuw fl1), (cbf_nuw fl2), (cbf_nsw fl1), (cbf_nsw fl2);
             cbn in Hnuw, Hnsw; try discriminate;
             repeat match goal with |- context [if ?b then _ else _] => destruct b end;
             cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
        -- destruct (cbf_nuw fl1), (cbf_nuw fl2), (cbf_nsw fl1), (cbf_nsw fl2);
             cbn in Hnuw, Hnsw; try discriminate;
             repeat match goal with |- context [if ?b then _ else _] => destruct b end;
             cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
        -- destruct (Pos.eqb w 1); [cbn; apply dvalue_refines_refl |].
           destruct (cbf_nuw fl1), (cbf_nuw fl2), (cbf_nsw fl1), (cbf_nsw fl2);
             cbn in Hnuw, Hnsw; try discriminate;
             repeat match goal with |- context [if ?b then _ else _] => destruct b end;
             cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
        -- apply dvalue_refines_refl.
        -- destruct (cbf_disjoint fl1), (cbf_disjoint fl2);
             cbn in Hdisj; try discriminate;
             repeat match goal with |- context [if ?b then _ else _] => destruct b end;
             cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
        -- apply dvalue_refines_refl.
        -- destruct (@Integers.unsigned w ir >=? Z.pos w)%Z; [cbn; apply dvalue_refines_refl |].
           destruct (cbf_nuw fl1), (cbf_nuw fl2), (cbf_nsw fl1), (cbf_nsw fl2);
             cbn in Hnuw, Hnsw; try discriminate;
             repeat match goal with |- context [if ?b then _ else _] => destruct b end;
             cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
        -- destruct (@Integers.unsigned w ir >=? Z.pos w)%Z; [cbn; apply dvalue_refines_refl |].
           destruct (cbf_exact fl1), (cbf_exact fl2);
             cbn in Hex; try discriminate;
             repeat match goal with |- context [if ?b then _ else _] => destruct b end;
             cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
        -- destruct (@Integers.unsigned w ir >=? Z.pos w)%Z; [cbn; apply dvalue_refines_refl |].
           destruct (cbf_exact fl1), (cbf_exact fl2);
             cbn in Hex; try discriminate;
             repeat match goal with |- context [if ?b then _ else _] => destruct b end;
             cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
Qed.

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
          destruct (Z.eq_dec (@Integers.signed w ir) (-1)%Z); cbn;
          [exact I | apply dvalue_refines_refl].
      * unfold binop_flags_weaken in Hfl; rewrite !andb_true_iff in Hfl.
        destruct Hfl as (((_ & _) & Hex) & _).
        unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
        destruct op; cbn in Hop; try discriminate;
          unfold cert_to_ibinop, eval_int_op; cbn;
          destruct (cbf_exact fl1), (cbf_exact fl2);
          cbn in Hex; try discriminate;
          repeat match goal with |- context [if ?b then _ else _] => destruct b end;
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
  - assert (Hsrc : @eval_icmp Pa ss1 (cert_to_icmp pr) (DVALUE_Base DVALUE_Poison) vr1 =
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
      destruct pr; unfold cert_to_icmp, eval_int_icmp; cbn;
        repeat match goal with |- context [if ?b then _ else _] => destruct b end;
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
    destruct k; cbn in Hk1 |- *; rewrite !andb_true_iff in Hk1.
    + destruct Hk1 as ([Hlt _] & _); rewrite Pos.eqb_refl, Hlt; cbn.
      destruct (ccf_nneg fl1), (ccf_nneg fl2); cbn in Hnneg; try discriminate;
        repeat match goal with |- context [if ?b then _ else _] => destruct b end;
        cbn; first [apply dvalue_refines_poison_l | apply dvalue_refines_refl].
    + destruct Hk1 as (([Hlt _] & _) & _); rewrite Pos.eqb_refl, Hlt; cbn.
      apply dvalue_refines_refl.
    + destruct Hk1 as [Hlt _]; rewrite Pos.eqb_refl, Hlt; cbn.
      destruct (ccf_nuw fl1), (ccf_nuw fl2), (ccf_nsw fl1), (ccf_nsw fl2);
        cbn in Hnuw, Hnsw; try discriminate;
        repeat match goal with |- context [if ?b then _ else _] => destruct b end;
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

Definition check_src_elim_step
  (rec : cert_expr -> cert_expr -> bool) (ctx : ub_ctx)
  (src tgt : cert_expr) : bool :=
  match src with
  | CE_Poison _ => ub_free_expr tgt
  | CE_BinOp op w _ l r =>
      match op with
      | CB_Add =>
          (is_zero_const_expr w r && rec l tgt) ||
          (is_zero_const_expr w l && rec r tgt)
      | CB_Sub =>
          (is_zero_const_expr w r && rec l tgt) ||
          (cert_expr_eqb l r && is_zero_const_expr w tgt)
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
          (is_zero_const_expr w l && is_zero_const_expr w tgt)
      | CB_Or =>
          (is_zero_const_expr w r && rec l tgt) ||
          (is_zero_const_expr w l && rec r tgt) ||
          (cert_expr_eqb l r && rec l tgt) ||
          (is_all_ones_const_expr w r && is_all_ones_const_expr w tgt) ||
          (is_all_ones_const_expr w l && is_all_ones_const_expr w tgt)
      | CB_Xor =>
          (is_zero_const_expr w r && rec l tgt) ||
          (is_zero_const_expr w l && rec r tgt) ||
          (cert_expr_eqb l r && is_zero_const_expr w tgt)
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
      rec c1 c2 && rec t1 t2 && rec f1 f2
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
  intros w d; unfold Integers.divu, Integers.zero; rewrite Integers.unsigned_zero; reflexivity.
Qed.

Lemma alg_modu_zero_l : forall w (d : @Integers.bit_int w),
  @Integers.modu w (@Integers.zero w) d = @Integers.zero w.
Proof.
  intros w d; unfold Integers.modu, Integers.zero; rewrite Integers.unsigned_zero; reflexivity.
Qed.

Lemma alg_divs_zero_l : forall w (d : @Integers.bit_int w),
  @Integers.divs w (@Integers.zero w) d = @Integers.zero w.
Proof.
  intros w d; unfold Integers.divs, Integers.zero; rewrite Integers.signed_zero; reflexivity.
Qed.

Lemma alg_mods_zero_l : forall w (d : @Integers.bit_int w),
  @Integers.mods w (@Integers.zero w) d = @Integers.zero w.
Proof.
  intros w d; unfold Integers.mods, Integers.zero; rewrite Integers.signed_zero; reflexivity.
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
      (exists vl, eval_closed_cert_expr penv foracle l = raise_ret vl /\ wf_scalar_dvalue w vl))
      by (rewrite <- Hwl at 1;
          exact (eval_cert_expr_totality l [] penv [] foracle Hwtl wf_let_val_env_nil Hpl)).
    assert (Htot_r :
      (exists msg, eval_closed_cert_expr penv foracle r = raise_ub msg) \/
      (exists vr, eval_closed_cert_expr penv foracle r = raise_ret vr /\ wf_scalar_dvalue w vr))
      by (rewrite <- Hwr at 1;
          exact (eval_cert_expr_totality r [] penv [] foracle Hwtr wf_let_val_env_nil Hpr)).
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
      destruct Htot_l as [[msgl ->] | [vl [-> Hwfvl]]]; [cbn; exact I | cbn [eou_bind] in *].
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
          rewrite Hp; exact Hlt.
        + rewrite Hiop; exact Hlt. }
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
      destruct Htot_r as [[msgr ->] | [vr [-> Hwfvr]]]; [cbn; exact I | cbn [eou_bind] in *].
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
          rewrite Hp; exact Hrt.
        + rewrite Hiop; exact Hrt. }
    destruct op.
    + (* CB_Add *)
      apply orb_true_iff in Hstep as [Hc | Hc]; apply andb_true_iff in Hc as [Hz Hrec].
      * apply (Hid_r 0%N eq_refl (is_zero_const_expr_inv w r Hz) Hrec).
        intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.add_zero; reflexivity.
      * apply (Hid_l 0%N eq_refl (is_zero_const_expr_inv w l Hz) Hrec).
        intros ir; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.add_zero_l; reflexivity.
    + (* CB_Sub *)
      apply orb_true_iff in Hstep as [Hc | Hc]; apply andb_true_iff in Hc as [H1 H2].
      * apply (Hid_r 0%N eq_refl (is_zero_const_expr_inv w r H1) H2).
        intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.sub_zero_l; reflexivity.
      * apply cert_expr_eqb_eq in H1; subst r.
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
        destruct Htot_l as [[msgl ->] | [vl [-> Hwfvl]]]; [cbn; exact I | cbn [eou_bind] in *].
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
        rewrite Integers.unsigned_zero; cbn; rewrite andb_false_r, alg_divu_zero_l;
          cbn; apply dvalue_refines_refl.
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
      rewrite Integers.signed_zero; cbn; rewrite andb_false_r, alg_divs_zero_l;
        cbn; apply dvalue_refines_refl.
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
    + (* CB_And *)
      rewrite !orb_true_iff in Hstep; destruct Hstep as [[[[Hc | Hc] | Hc] | Hc] | Hc];
        apply andb_true_iff in Hc as [H1 H2].
      * apply (Hid_r (all_ones_N w) eq_refl (is_all_ones_const_expr_inv w r H1) H2).
        intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
        rewrite Integers.and_mone; reflexivity.
      * apply (Hid_l (all_ones_N w) eq_refl (is_all_ones_const_expr_inv w l H1) H2).
        intros ir; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
        rewrite Integers.and_mone_l; reflexivity.
      * apply cert_expr_eqb_eq in H1; subst r.
        pose proof (IH l tgt H2 (eq_trans Hwl Hbw) Hwtl Hwtt Hpl Hpt) as Hlt.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]];
          [cbn; exact I | cbn [eou_bind]; exact Hlt | cbn [eou_bind]].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn.
        rewrite Integers.and_idem; exact Hlt.
      * rewrite (is_zero_const_expr_inv w r H1), (is_zero_const_expr_inv w tgt H2).
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]];
          [cbn; exact I | cbn; apply dvalue_refines_poison_l | cbn [eou_bind]].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.and_zero; apply dvalue_refines_refl.
      * rewrite (is_zero_const_expr_inv w l H1), (is_zero_const_expr_inv w tgt H2).
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
        destruct Htot_r as [[msgr ->] | [vr [-> [-> | [ir ->]]]]];
          [cbn; exact I | cbn; apply dvalue_refines_poison_l | cbn [eou_bind]].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.and_zero_l; apply dvalue_refines_refl.
    + (* CB_Or *)
      rewrite !orb_true_iff in Hstep; destruct Hstep as [[[[Hc | Hc] | Hc] | Hc] | Hc];
        apply andb_true_iff in Hc as [H1 H2].
      * apply (Hid_r 0%N eq_refl (is_zero_const_expr_inv w r H1) H2).
        intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.or_zero; reflexivity.
      * apply (Hid_l 0%N eq_refl (is_zero_const_expr_inv w l H1) H2).
        intros ir; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.or_zero_l; reflexivity.
      * apply cert_expr_eqb_eq in H1; subst r.
        pose proof (IH l tgt H2 (eq_trans Hwl Hbw) Hwtl Hwtt Hpl Hpt) as Hlt.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [-> Hwfvl]]]; [cbn; exact I | cbn [eou_bind]].
        apply (refine_eou_dvalue_trans _
                 (@eval_iop Pa (cert_to_ibinop CB_Or no_binop_flags) vl vl) _).
        -- exact (eval_iop_non_div_rem_monotone CB_Or fl no_binop_flags w vl vl vl vl
                    eq_refl (binop_flags_weaken_no_flags fl) Hwfvl Hwfvl Hwfvl Hwfvl
                    (dvalue_refines_refl _) (dvalue_refines_refl _)).
        -- destruct Hwfvl as [-> | [il ->]]; [exact Hlt |].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn.
           rewrite Integers.or_idem; exact Hlt.
      * rewrite (is_all_ones_const_expr_inv w r H1), (is_all_ones_const_expr_inv w tgt H2).
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
      * rewrite (is_all_ones_const_expr_inv w l H1), (is_all_ones_const_expr_inv w tgt H2).
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
    + (* CB_Xor *)
      rewrite !orb_true_iff in Hstep; destruct Hstep as [[Hc | Hc] | Hc];
        apply andb_true_iff in Hc as [H1 H2].
      * apply (Hid_r 0%N eq_refl (is_zero_const_expr_inv w r H1) H2).
        intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.xor_zero; reflexivity.
      * apply (Hid_l 0%N eq_refl (is_zero_const_expr_inv w l H1) H2).
        intros ir; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.xor_zero_l; reflexivity.
      * apply cert_expr_eqb_eq in H1; subst r; rewrite (is_zero_const_expr_inv w tgt H2).
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]];
          [cbn; exact I | cbn; apply dvalue_refines_poison_l | cbn [eou_bind]].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.xor_idem; apply dvalue_refines_refl.
    + (* CB_Shl *)
      apply andb_true_iff in Hstep as [H1 H2].
      apply (Hid_r 0%N eq_refl (is_zero_const_expr_inv w r H1) H2).
      intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
      rewrite Integers.unsigned_zero; cbn; rewrite alg_shl_zero; reflexivity.
    + (* CB_LShr *)
      apply andb_true_iff in Hstep as [H1 H2].
      apply (Hid_r 0%N eq_refl (is_zero_const_expr_inv w r H1) H2).
      intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
      rewrite Integers.unsigned_zero; cbn; rewrite alg_shru_zero; reflexivity.
    + (* CB_AShr *)
      apply andb_true_iff in Hstep as [H1 H2].
      apply (Hid_r 0%N eq_refl (is_zero_const_expr_inv w r H1) H2).
      intros il; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
      rewrite Integers.unsigned_zero; cbn; rewrite alg_shr_zero; reflexivity.
  - (* CE_ICmp *)
    cbn [wt_cert_expr collect_free_vars] in Hwts, Hps.
    rewrite !andb_true_iff in Hwts, Hstep.
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
    rewrite !andb_true_iff in Hwts, Hstep.
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
                  IH s t penv foracle Hs Hbs Hts Htt Hps' Hpt')
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
        rewrite !andb_true_iff in Hwts, Hwtt.
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
        rewrite !andb_true_iff in Hwts, Hwtt.
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
        rewrite !andb_true_iff in Hwts, Hwtt.
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
        rewrite !andb_true_iff in Hcong.
        destruct Hcong as (((Hww & Hcc) & Htt0) & Hff0).
        apply Pos.eqb_eq in Hww; subst w2.
        cbn [wt_cert_expr collect_free_vars] in Hwts, Hwtt, Hps, Hpt.
        rewrite !andb_true_iff in Hwts, Hwtt.
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
Qed.

Definition check_expr_refines (ctx : ub_ctx) (src tgt : cert_expr) : bool :=
  Pos.eqb (cert_expr_bit_width src) (cert_expr_bit_width tgt) &&
  wt_cert_expr [] src &&
  wt_cert_expr [] tgt &&
  wf_let_dag [] src &&
  wf_let_dag [] tgt &&
  let ns := normalize_cert_expr ctx (expand_lets src) in
  let nt := normalize_cert_expr ctx (expand_lets tgt) in
  check_norm_refines_fuel (S (expr_size ns + expr_size nt)) ctx ns nt.

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
  unfold check_expr_refines in Hchk; cbn zeta in Hchk.
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as (((((Hbw & Hwts) & Hwtt) & Hdags) & Hdagt) & Hfuel).
  apply Pos.eqb_eq in Hbw.
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
    by congruence.
  apply (refine_eou_compat _ _ _ _ Heq_src Heq_tgt).
  exact (check_norm_refines_fuel_sound _ ctx _ _ penv foracle
           Hfuel Hbw_norm Hwt_ns Hwt_nt Hp_ns Hp_nt Hctx).
Qed.


(** ** 7. Verified 2-Rail [LRAT] Fallback Refinement Checker *)

Definition wf_lit_bound (bound : positive) (l : lit) : Prop :=
  match l with
  | Z.pos p | Z.neg p => (p < bound)%positive
  | Z0 => False
  end.

Definition wf_lits_bound (bound : positive) (ls : list lit) : Prop :=
  Forall (wf_lit_bound bound) ls.

Definition wf_rail_bound (sz bound : positive) (r : rail_bv) : Prop :=
  wf_rail_bv sz r /\
  wf_lits_bound bound (rbv_bits r) /\
  wf_lit_bound bound (rbv_psn r).

Definition wf_clause_bound (bound : positive) (cl : clause) : Prop :=
  Forall (wf_lit_bound bound) cl.

Definition wf_cnf_bound (bound : positive) (f : cnf) : Prop :=
  Forall (fun p => wf_clause_bound bound (snd p)) f.

Definition wf_blast_st (st : blast_state) : Prop :=
  (2 <= bs_next_var st)%positive /\
  wf_cnf_bound (bs_next_var st) (bs_cnf st).

Lemma wf_lit_bound_nonzero : forall bound l,
  wf_lit_bound bound l -> l <> 0%Z.
Proof.
  intros bound [| p | p] H; [contradiction | discriminate | discriminate].
Qed.

Lemma wf_lit_bound_neg : forall bound l,
  wf_lit_bound bound l -> wf_lit_bound bound (neg_lit l).
Proof.
  intros bound [| p | p] H; cbn in *; exact H.
Qed.

Lemma wf_lit_bound_mono : forall b1 b2 l,
  (b1 <= b2)%positive -> wf_lit_bound b1 l -> wf_lit_bound b2 l.
Proof.
  intros b1 b2 [| p | p] Hle H; [contradiction | cbn in *; lia | cbn in *; lia].
Qed.

Lemma wf_lits_bound_mono : forall b1 b2 ls,
  (b1 <= b2)%positive -> wf_lits_bound b1 ls -> wf_lits_bound b2 ls.
Proof.
  intros b1 b2 ls Hle H; unfold wf_lits_bound in *.
  eapply Forall_impl; [| exact H]; intros x Hx; exact (wf_lit_bound_mono b1 b2 x Hle Hx).
Qed.

Lemma wf_rail_bound_mono : forall sz b1 b2 r,
  (b1 <= b2)%positive -> wf_rail_bound sz b1 r -> wf_rail_bound sz b2 r.
Proof.
  intros sz b1 b2 r Hle (Hwf & Hls & Hp); repeat split.
  - exact (proj1 Hwf).
  - exact (proj2 Hwf).
  - exact (wf_lits_bound_mono b1 b2 _ Hle Hls).
  - exact (wf_lit_bound_mono b1 b2 _ Hle Hp).
Qed.

Lemma wf_cnf_bound_mono : forall b1 b2 f,
  (b1 <= b2)%positive -> wf_cnf_bound b1 f -> wf_cnf_bound b2 f.
Proof.
  intros b1 b2 f Hle H; unfold wf_cnf_bound in *.
  eapply Forall_impl; [| exact H]; intros p Hp.
  eapply Forall_impl; [| exact Hp]; intros l Hl.
  exact (wf_lit_bound_mono b1 b2 l Hle Hl).
Qed.

Lemma wf_lits_bound_nonzero : forall bound ls,
  wf_lits_bound bound ls -> wf_lits_nonzero ls.
Proof.
  intros bound ls H; unfold wf_lits_bound, wf_lits_nonzero in *.
  eapply Forall_impl; [| exact H]; exact (wf_lit_bound_nonzero bound).
Qed.

Lemma wf_rail_bound_lits : forall sz bound r,
  wf_rail_bound sz bound r -> wf_rail_lits sz r.
Proof.
  intros sz bound r (Hwf & Hls & Hp); repeat split.
  - exact (proj1 Hwf).
  - exact (proj2 Hwf).
  - exact (wf_lits_bound_nonzero bound _ Hls).
  - exact (wf_lit_bound_nonzero bound _ Hp).
Qed.

Definition agree_below (bound : positive) (a1 a2 : positive -> bool) : Prop :=
  forall p, (p < bound)%positive -> a1 p = a2 p.

Lemma agree_below_refl : forall bound a, agree_below bound a a.
Proof.
  intros bound a p _; reflexivity.
Qed.

Lemma agree_below_trans : forall bound a1 a2 a3,
  agree_below bound a1 a2 -> agree_below bound a2 a3 -> agree_below bound a1 a3.
Proof.
  intros bound a1 a2 a3 H12 H23 p Hp; rewrite (H12 p Hp); exact (H23 p Hp).
Qed.

Lemma agree_below_le : forall b1 b2 a1 a2,
  (b1 <= b2)%positive -> agree_below b2 a1 a2 -> agree_below b1 a1 a2.
Proof.
  intros b1 b2 a1 a2 Hle H p Hp; apply H; lia.
Qed.

Definition set_asg (asg : positive -> bool) (v : positive) (b : bool)
  : positive -> bool :=
  fun p => if Pos.eqb p v then b else asg p.

Lemma set_asg_same : forall asg v b, set_asg asg v b v = b.
Proof.
  intros asg v b; unfold set_asg; rewrite Pos.eqb_refl; reflexivity.
Qed.

Lemma agree_below_set_asg : forall asg v b,
  agree_below v asg (set_asg asg v b).
Proof.
  intros asg v b p Hp; unfold set_asg.
  destruct (Pos.eqb p v) eqn:E; [apply Pos.eqb_eq in E; lia | reflexivity].
Qed.

Lemma eval_lit_agree : forall bound a1 a2 l,
  agree_below bound a1 a2 -> wf_lit_bound bound l ->
  eval_lit a1 l = eval_lit a2 l.
Proof.
  intros bound a1 a2 [| p | p] Hag Hb;
    [contradiction | cbn; apply Hag, Hb | cbn; f_equal; apply Hag, Hb].
Qed.

Lemma eval_lits_agree : forall bound a1 a2 ls,
  agree_below bound a1 a2 -> wf_lits_bound bound ls ->
  List.map (eval_lit a1) ls = List.map (eval_lit a2) ls.
Proof.
  intros bound a1 a2 ls Hag Hwf; induction Hwf as [| l lr Hl Hlr IH]; [reflexivity |].
  cbn; rewrite (eval_lit_agree bound a1 a2 l Hag Hl), IH; reflexivity.
Qed.

Lemma eval_rail_agree : forall sz bound a1 a2 r,
  agree_below bound a1 a2 -> wf_rail_bound sz bound r ->
  eval_rail_psn a1 r = eval_rail_psn a2 r /\
  eval_rail_val sz a1 r = eval_rail_val sz a2 r.
Proof.
  intros sz bound a1 a2 r Hag (_ & Hls & Hp); unfold eval_rail_psn, eval_rail_val; split.
  - exact (eval_lit_agree bound a1 a2 _ Hag Hp).
  - f_equal; exact (eval_lits_agree bound a1 a2 _ Hag Hls).
Qed.

Lemma eval_clause_agree : forall bound a1 a2 cl,
  agree_below bound a1 a2 -> wf_clause_bound bound cl ->
  eval_clause a1 cl = eval_clause a2 cl.
Proof.
  intros bound a1 a2 cl Hag Hwf; unfold eval_clause.
  induction Hwf as [| l lr Hl Hlr IH]; [reflexivity |].
  cbn; rewrite (eval_lit_agree bound a1 a2 l Hag Hl), IH; reflexivity.
Qed.

Lemma eval_cnf_agree : forall bound a1 a2 f,
  agree_below bound a1 a2 -> wf_cnf_bound bound f ->
  eval_cnf a1 f = eval_cnf a2 f.
Proof.
  intros bound a1 a2 f Hag Hwf; unfold eval_cnf.
  induction Hwf as [| [cid cl] fr Hcl Hfr IH]; [reflexivity |].
  cbn in *; rewrite (eval_clause_agree bound a1 a2 cl Hag Hcl), IH; reflexivity.
Qed.

Definition sat_blast_st (asg : positive -> bool) (st : blast_state) : Prop :=
  wf_blast_st st /\
  asg 1%positive = true /\
  eval_cnf asg (bs_cnf st) = true.

Lemma init_blast_state_sat :
  sat_blast_st (fun _ => true) (init_blast_state 2%positive).
Proof.
  repeat split.
  - cbn; lia.
  - constructor; [| constructor].
    cbn; constructor; [cbn; lia | constructor].
Qed.

Lemma append_clauses_sat_intro : forall asg bound cls cid cid' new_cnf,
  Forall (wf_clause_bound bound) cls ->
  (forall cl, In cl cls -> eval_clause asg cl = true) ->
  append_clauses cid cls = (cid', new_cnf) ->
  wf_cnf_bound bound new_cnf /\ eval_cnf asg new_cnf = true.
Proof.
  intros asg bound cls; induction cls as [| c rest IH];
    intros cid cid' new_cnf HF Hsat Happ; cbn in Happ.
  - inversion Happ; subst; split; [constructor | reflexivity].
  - inversion HF as [| ? ? Hc Hrest]; subst.
    destruct (append_clauses (Pos.succ cid) rest) as [cid2 tail_cnf] eqn:Htr.
    inversion Happ; subst; clear Happ.
    destruct (IH (Pos.succ cid) cid' tail_cnf Hrest
                (fun cl H => Hsat cl (or_intror H)) Htr) as [Hwf Hev].
    split.
    + constructor; [exact Hc | exact Hwf].
    + cbn; rewrite (Hsat c (or_introl eq_refl)), Hev; reflexivity.
Qed.

Lemma add_clauses_sat_intro : forall asg st cls,
  (2 <= bs_next_var st)%positive ->
  asg 1%positive = true ->
  wf_cnf_bound (bs_next_var st) (bs_cnf st) ->
  Forall (wf_clause_bound (bs_next_var st)) cls ->
  eval_cnf asg (bs_cnf st) = true ->
  (forall cl, In cl cls -> eval_clause asg cl = true) ->
  sat_blast_st asg (add_clauses cls st).
Proof.
  intros asg st cls Hge2 Ha1 Hwf_st Hwf_cls Hev_st Hcls.
  unfold add_clauses.
  destruct (append_clauses (bs_next_cid st) cls) as [cid' new_cnf] eqn:Happ.
  destruct (append_clauses_sat_intro asg (bs_next_var st) cls
              (bs_next_cid st) cid' new_cnf Hwf_cls Hcls Happ) as [Hwf_new Hev_new].
  repeat split; cbn.
  - exact Hge2.
  - apply Forall_app; split; [exact Hwf_st | exact Hwf_new].
  - exact Ha1.
  - rewrite eval_cnf_app, Hev_st, Hev_new; reflexivity.
Qed.

Lemma alloc_var_sat : forall asg st b out st1,
  sat_blast_st asg st ->
  alloc_var st = (out, st1) ->
  exists asg1,
    (bs_next_var st <= bs_next_var st1)%positive /\
    agree_below (bs_next_var st) asg asg1 /\
    sat_blast_st asg1 st1 /\
    wf_lit_bound (bs_next_var st1) out /\
    eval_lit asg1 out = b.
Proof.
  intros asg st b out st1 ([Hge2 Hwf] & Ha1 & Hev) Hal; cbn in Hal.
  inversion Hal; subst out st1; clear Hal.
  set (v := bs_next_var st).
  set (asg1 := set_asg asg v b).
  pose proof (agree_below_set_asg asg v b) as Hag.
  exists asg1; repeat split; cbn.
  - lia.
  - exact Hag.
  - lia.
  - apply (wf_cnf_bound_mono v (Pos.succ v)); [lia | exact Hwf].
  - rewrite <- (Hag 1%positive) by lia; exact Ha1.
  - rewrite <- (eval_cnf_agree v asg asg1 (bs_cnf st) Hag Hwf); exact Hev.
  - lia.
  - apply set_asg_same.
Qed.

Lemma alloc_fresh_bits_sat : forall bs asg st lits st',
  sat_blast_st asg st ->
  alloc_fresh_bits (List.length bs) st = (lits, st') ->
  exists asg',
    (bs_next_var st <= bs_next_var st')%positive /\
    agree_below (bs_next_var st) asg asg' /\
    sat_blast_st asg' st' /\
    List.length lits = List.length bs /\
    wf_lits_bound (bs_next_var st') lits /\
    List.map (eval_lit asg') lits = bs.
Proof.
  induction bs as [| b br IH]; intros asg st lits st' Hsat Hal; cbn in Hal.
  - inversion Hal; subst; exists asg;
      split; [lia | split; [apply agree_below_refl | split; [exact Hsat |
      split; [reflexivity | split; [constructor | reflexivity]]]]].
  - destruct (alloc_var st) as [v st1] eqn:Hv.
    destruct (alloc_fresh_bits (List.length br) st1) as [vs st2] eqn:Hvs.
    inversion Hal; subst lits st2; clear Hal.
    destruct (alloc_var_sat asg st b v st1 Hsat Hv)
      as (asg1 & Hle1 & Hag1 & Hsat1 & Hwf_v & Hev_v).
    destruct (IH asg1 st1 vs st' Hsat1 Hvs)
      as (asg2 & Hle2 & Hag2 & Hsat2 & Hlen & Hwf_vs & Hev_vs).
    exists asg2; split; [lia | split].
    + exact (agree_below_trans _ asg asg1 asg2 Hag1
               (agree_below_le _ _ asg1 asg2 Hle1 Hag2)).
    + split; [exact Hsat2 | split; [cbn; rewrite Hlen; reflexivity | split]].
      * constructor; [exact (wf_lit_bound_mono _ _ v Hle2 Hwf_v) | exact Hwf_vs].
      * cbn; rewrite <- (eval_lit_agree (bs_next_var st1) asg1 asg2 v Hag2 Hwf_v),
                     Hev_v, Hev_vs; reflexivity.
Qed.

Lemma emit_and2_sat : forall asg a b st out st',
  sat_blast_st asg st ->
  wf_lit_bound (bs_next_var st) a ->
  wf_lit_bound (bs_next_var st) b ->
  emit_and2 a b st = (out, st') ->
  exists asg',
    (bs_next_var st <= bs_next_var st')%positive /\
    agree_below (bs_next_var st) asg asg' /\
    sat_blast_st asg' st' /\
    wf_lit_bound (bs_next_var st') out.
Proof.
  intros asg a b st out st' ([Hge2 Hwf] & Ha1 & Hev) Hwa Hwb Hemit.
  unfold emit_and2 in Hemit.
  destruct (alloc_var st) as [vlit st1] eqn:Hv.
  inversion Hemit; subst out st'; clear Hemit.
  destruct (alloc_var_sat asg st (eval_lit asg a && eval_lit asg b) vlit st1
              (conj (conj Hge2 Hwf) (conj Ha1 Hev)) Hv)
    as (asg1 & Hle1 & Hag1 & ([Hge2_1 Hwf1] & Ha1_1 & Hev1) & Hwf_v & Hev_v).
  assert (Hbs : bs_next_var (add_clauses
                  [[neg_lit vlit; a]; [neg_lit vlit; b]; [vlit; neg_lit a; neg_lit b]] st1) =
                bs_next_var st1)
    by (unfold add_clauses; destruct (append_clauses _ _); reflexivity).
  assert (Hwa1 : wf_lit_bound (bs_next_var st1) a)
    by exact (wf_lit_bound_mono _ _ a Hle1 Hwa).
  assert (Hwb1 : wf_lit_bound (bs_next_var st1) b)
    by exact (wf_lit_bound_mono _ _ b Hle1 Hwb).
  assert (Hcls_wf : Forall (wf_clause_bound (bs_next_var st1))
                      [[neg_lit vlit; a]; [neg_lit vlit; b]; [vlit; neg_lit a; neg_lit b]]).
  { repeat constructor; try assumption; apply wf_lit_bound_neg; assumption. }
  assert (Hcls_sat : forall cl,
            In cl [[neg_lit vlit; a]; [neg_lit vlit; b]; [vlit; neg_lit a; neg_lit b]] ->
            eval_clause asg1 cl = true).
  { intros cl [<- | [<- | [<- | []]]]; cbn [eval_clause existsb];
      rewrite ?(eval_neg_lit_nonzero asg1 vlit (wf_lit_bound_nonzero _ _ Hwf_v)),
              ?(eval_neg_lit_nonzero asg1 a (wf_lit_bound_nonzero _ _ Hwa1)),
              ?(eval_neg_lit_nonzero asg1 b (wf_lit_bound_nonzero _ _ Hwb1)),
              Hev_v,
              <-(eval_lit_agree (bs_next_var st) asg asg1 a Hag1 Hwa),
              <-(eval_lit_agree (bs_next_var st) asg asg1 b Hag1 Hwb);
      destruct (eval_lit asg a), (eval_lit asg b); reflexivity. }
  exists asg1; repeat split.
  - rewrite Hbs; exact Hle1.
  - exact Hag1.
  - exact (proj1 (proj1 (add_clauses_sat_intro asg1 st1 _ Hge2_1 Ha1_1 Hwf1 Hcls_wf Hev1 Hcls_sat))).
  - exact (proj2 (proj1 (add_clauses_sat_intro asg1 st1 _ Hge2_1 Ha1_1 Hwf1 Hcls_wf Hev1 Hcls_sat))).
  - exact (proj1 (proj2 (add_clauses_sat_intro asg1 st1 _ Hge2_1 Ha1_1 Hwf1 Hcls_wf Hev1 Hcls_sat))).
  - exact (proj2 (proj2 (add_clauses_sat_intro asg1 st1 _ Hge2_1 Ha1_1 Hwf1 Hcls_wf Hev1 Hcls_sat))).
  - rewrite Hbs; exact Hwf_v.
Qed.

Lemma emit_or2_sat : forall asg a b st out st',
  sat_blast_st asg st ->
  wf_lit_bound (bs_next_var st) a ->
  wf_lit_bound (bs_next_var st) b ->
  emit_or2 a b st = (out, st') ->
  exists asg',
    (bs_next_var st <= bs_next_var st')%positive /\
    agree_below (bs_next_var st) asg asg' /\
    sat_blast_st asg' st' /\
    wf_lit_bound (bs_next_var st') out.
Proof.
  intros asg a b st out st' ([Hge2 Hwf] & Ha1 & Hev) Hwa Hwb Hemit.
  unfold emit_or2 in Hemit.
  destruct (alloc_var st) as [vlit st1] eqn:Hv.
  inversion Hemit; subst out st'; clear Hemit.
  destruct (alloc_var_sat asg st (eval_lit asg a || eval_lit asg b) vlit st1
              (conj (conj Hge2 Hwf) (conj Ha1 Hev)) Hv)
    as (asg1 & Hle1 & Hag1 & ([Hge2_1 Hwf1] & Ha1_1 & Hev1) & Hwf_v & Hev_v).
  assert (Hbs : bs_next_var (add_clauses
                  [[vlit; neg_lit a]; [vlit; neg_lit b]; [neg_lit vlit; a; b]] st1) =
                bs_next_var st1)
    by (unfold add_clauses; destruct (append_clauses _ _); reflexivity).
  assert (Hwa1 : wf_lit_bound (bs_next_var st1) a)
    by exact (wf_lit_bound_mono _ _ a Hle1 Hwa).
  assert (Hwb1 : wf_lit_bound (bs_next_var st1) b)
    by exact (wf_lit_bound_mono _ _ b Hle1 Hwb).
  assert (Hcls_wf : Forall (wf_clause_bound (bs_next_var st1))
                      [[vlit; neg_lit a]; [vlit; neg_lit b]; [neg_lit vlit; a; b]]).
  { repeat constructor; try assumption; apply wf_lit_bound_neg; assumption. }
  assert (Hcls_sat : forall cl,
            In cl [[vlit; neg_lit a]; [vlit; neg_lit b]; [neg_lit vlit; a; b]] ->
            eval_clause asg1 cl = true).
  { intros cl [<- | [<- | [<- | []]]]; cbn [eval_clause existsb];
      rewrite ?(eval_neg_lit_nonzero asg1 vlit (wf_lit_bound_nonzero _ _ Hwf_v)),
              ?(eval_neg_lit_nonzero asg1 a (wf_lit_bound_nonzero _ _ Hwa1)),
              ?(eval_neg_lit_nonzero asg1 b (wf_lit_bound_nonzero _ _ Hwb1)),
              Hev_v,
              <-(eval_lit_agree (bs_next_var st) asg asg1 a Hag1 Hwa),
              <-(eval_lit_agree (bs_next_var st) asg asg1 b Hag1 Hwb);
      destruct (eval_lit asg a), (eval_lit asg b); reflexivity. }
  pose proof (add_clauses_sat_intro asg1 st1 _ Hge2_1 Ha1_1 Hwf1 Hcls_wf Hev1 Hcls_sat) as Hadd.
  exists asg1; repeat split; try rewrite Hbs;
    [exact Hle1 | exact Hag1
     | exact (proj1 (proj1 Hadd)) | exact (proj2 (proj1 Hadd))
     | exact (proj1 (proj2 Hadd)) | exact (proj2 (proj2 Hadd))
     | exact Hwf_v].
Qed.

Lemma emit_xor2_sat : forall asg a b st out st',
  sat_blast_st asg st ->
  wf_lit_bound (bs_next_var st) a ->
  wf_lit_bound (bs_next_var st) b ->
  emit_xor2 a b st = (out, st') ->
  exists asg',
    (bs_next_var st <= bs_next_var st')%positive /\
    agree_below (bs_next_var st) asg asg' /\
    sat_blast_st asg' st' /\
    wf_lit_bound (bs_next_var st') out.
Proof.
  intros asg a b st out st' ([Hge2 Hwf] & Ha1 & Hev) Hwa Hwb Hemit.
  unfold emit_xor2 in Hemit.
  destruct (alloc_var st) as [vlit st1] eqn:Hv.
  inversion Hemit; subst out st'; clear Hemit.
  destruct (alloc_var_sat asg st (xorb (eval_lit asg a) (eval_lit asg b)) vlit st1
              (conj (conj Hge2 Hwf) (conj Ha1 Hev)) Hv)
    as (asg1 & Hle1 & Hag1 & ([Hge2_1 Hwf1] & Ha1_1 & Hev1) & Hwf_v & Hev_v).
  assert (Hbs : bs_next_var (add_clauses
                  [[neg_lit vlit; a; b]; [neg_lit vlit; neg_lit a; neg_lit b];
                   [vlit; neg_lit a; b]; [vlit; a; neg_lit b]] st1) =
                bs_next_var st1)
    by (unfold add_clauses; destruct (append_clauses _ _); reflexivity).
  assert (Hwa1 : wf_lit_bound (bs_next_var st1) a)
    by exact (wf_lit_bound_mono _ _ a Hle1 Hwa).
  assert (Hwb1 : wf_lit_bound (bs_next_var st1) b)
    by exact (wf_lit_bound_mono _ _ b Hle1 Hwb).
  assert (Hcls_wf : Forall (wf_clause_bound (bs_next_var st1))
                      [[neg_lit vlit; a; b]; [neg_lit vlit; neg_lit a; neg_lit b];
                       [vlit; neg_lit a; b]; [vlit; a; neg_lit b]]).
  { repeat constructor; try assumption; apply wf_lit_bound_neg; assumption. }
  assert (Hcls_sat : forall cl,
            In cl [[neg_lit vlit; a; b]; [neg_lit vlit; neg_lit a; neg_lit b];
                   [vlit; neg_lit a; b]; [vlit; a; neg_lit b]] ->
            eval_clause asg1 cl = true).
  { intros cl [<- | [<- | [<- | [<- | []]]]]; cbn [eval_clause existsb];
      rewrite ?(eval_neg_lit_nonzero asg1 vlit (wf_lit_bound_nonzero _ _ Hwf_v)),
              ?(eval_neg_lit_nonzero asg1 a (wf_lit_bound_nonzero _ _ Hwa1)),
              ?(eval_neg_lit_nonzero asg1 b (wf_lit_bound_nonzero _ _ Hwb1)),
              Hev_v,
              <-(eval_lit_agree (bs_next_var st) asg asg1 a Hag1 Hwa),
              <-(eval_lit_agree (bs_next_var st) asg asg1 b Hag1 Hwb);
      destruct (eval_lit asg a), (eval_lit asg b); reflexivity. }
  pose proof (add_clauses_sat_intro asg1 st1 _ Hge2_1 Ha1_1 Hwf1 Hcls_wf Hev1 Hcls_sat) as Hadd.
  exists asg1; repeat split; try rewrite Hbs;
    [exact Hle1 | exact Hag1
     | exact (proj1 (proj1 Hadd)) | exact (proj2 (proj1 Hadd))
     | exact (proj1 (proj2 Hadd)) | exact (proj2 (proj2 Hadd))
     | exact Hwf_v].
Qed.

Lemma emit_mux2_sat : forall asg sel tl fl st out st',
  sat_blast_st asg st ->
  wf_lit_bound (bs_next_var st) sel ->
  wf_lit_bound (bs_next_var st) tl ->
  wf_lit_bound (bs_next_var st) fl ->
  emit_mux2 sel tl fl st = (out, st') ->
  exists asg',
    (bs_next_var st <= bs_next_var st')%positive /\
    agree_below (bs_next_var st) asg asg' /\
    sat_blast_st asg' st' /\
    wf_lit_bound (bs_next_var st') out.
Proof.
  intros asg sel tl fl st out st' ([Hge2 Hwf] & Ha1 & Hev) Hws Hwt Hwf0 Hemit.
  unfold emit_mux2 in Hemit.
  destruct (alloc_var st) as [vlit st1] eqn:Hv.
  inversion Hemit; subst out st'; clear Hemit.
  destruct (alloc_var_sat asg st
              (if eval_lit asg sel then eval_lit asg tl else eval_lit asg fl)
              vlit st1 (conj (conj Hge2 Hwf) (conj Ha1 Hev)) Hv)
    as (asg1 & Hle1 & Hag1 & ([Hge2_1 Hwf1] & Ha1_1 & Hev1) & Hwf_v & Hev_v).
  assert (Hbs : bs_next_var (add_clauses
                  [[neg_lit sel; neg_lit vlit; tl];
                   [neg_lit sel; vlit; neg_lit tl];
                   [sel; neg_lit vlit; fl];
                   [sel; vlit; neg_lit fl]] st1) =
                bs_next_var st1)
    by (unfold add_clauses; destruct (append_clauses _ _); reflexivity).
  assert (Hws1 : wf_lit_bound (bs_next_var st1) sel)
    by exact (wf_lit_bound_mono _ _ sel Hle1 Hws).
  assert (Hwt1 : wf_lit_bound (bs_next_var st1) tl)
    by exact (wf_lit_bound_mono _ _ tl Hle1 Hwt).
  assert (Hwf1_0 : wf_lit_bound (bs_next_var st1) fl)
    by exact (wf_lit_bound_mono _ _ fl Hle1 Hwf0).
  assert (Hcls_wf : Forall (wf_clause_bound (bs_next_var st1))
                      [[neg_lit sel; neg_lit vlit; tl];
                       [neg_lit sel; vlit; neg_lit tl];
                       [sel; neg_lit vlit; fl];
                       [sel; vlit; neg_lit fl]]).
  { repeat constructor; try assumption; apply wf_lit_bound_neg; assumption. }
  assert (Hcls_sat : forall cl,
            In cl [[neg_lit sel; neg_lit vlit; tl];
                   [neg_lit sel; vlit; neg_lit tl];
                   [sel; neg_lit vlit; fl];
                   [sel; vlit; neg_lit fl]] ->
            eval_clause asg1 cl = true).
  { intros cl [<- | [<- | [<- | [<- | []]]]]; cbn [eval_clause existsb];
      rewrite ?(eval_neg_lit_nonzero asg1 vlit (wf_lit_bound_nonzero _ _ Hwf_v)),
              ?(eval_neg_lit_nonzero asg1 sel (wf_lit_bound_nonzero _ _ Hws1)),
              ?(eval_neg_lit_nonzero asg1 tl (wf_lit_bound_nonzero _ _ Hwt1)),
              ?(eval_neg_lit_nonzero asg1 fl (wf_lit_bound_nonzero _ _ Hwf1_0)),
              Hev_v,
              <-(eval_lit_agree (bs_next_var st) asg asg1 sel Hag1 Hws),
              <-(eval_lit_agree (bs_next_var st) asg asg1 tl Hag1 Hwt),
              <-(eval_lit_agree (bs_next_var st) asg asg1 fl Hag1 Hwf0);
      destruct (eval_lit asg sel), (eval_lit asg tl), (eval_lit asg fl); reflexivity. }
  pose proof (add_clauses_sat_intro asg1 st1 _ Hge2_1 Ha1_1 Hwf1 Hcls_wf Hev1 Hcls_sat) as Hadd.
  exists asg1; repeat split; try rewrite Hbs;
    [exact Hle1 | exact Hag1
     | exact (proj1 (proj1 Hadd)) | exact (proj2 (proj1 Hadd))
     | exact (proj1 (proj2 Hadd)) | exact (proj2 (proj2 Hadd))
     | exact Hwf_v].
Qed.

Lemma map2_emit_sat :
  forall (gate : lit -> lit -> blast_state -> lit * blast_state)
         (Hg_sat : forall asg x y st z st1,
                     sat_blast_st asg st ->
                     wf_lit_bound (bs_next_var st) x ->
                     wf_lit_bound (bs_next_var st) y ->
                     gate x y st = (z, st1) ->
                     exists asg1,
                       (bs_next_var st <= bs_next_var st1)%positive /\
                       agree_below (bs_next_var st) asg asg1 /\
                       sat_blast_st asg1 st1 /\
                       wf_lit_bound (bs_next_var st1) z)
         xs ys asg st zs st',
    List.length xs = List.length ys ->
    wf_lits_bound (bs_next_var st) xs ->
    wf_lits_bound (bs_next_var st) ys ->
    sat_blast_st asg st ->
    map2_emit gate xs ys st = (zs, st') ->
    exists asg',
      (bs_next_var st <= bs_next_var st')%positive /\
      agree_below (bs_next_var st) asg asg' /\
      sat_blast_st asg' st' /\
      List.length zs = List.length xs /\
      wf_lits_bound (bs_next_var st') zs.
Proof.
  intros gate Hg_sat xs; induction xs as [| x rx IH];
    intros [| y ry] asg st zs st' Hlen Hwx Hwy Hsat Hm;
    try discriminate; cbn in Hm.
  - inversion Hm; subst; exists asg;
      split; [lia | split; [apply agree_below_refl | split; [exact Hsat |
      split; [reflexivity | constructor]]]].
  - inversion Hwx as [| ? ? Hx Hwrx]; subst.
    inversion Hwy as [| ? ? Hy Hwry]; subst.
    injection Hlen as Hlen'.
    destruct (gate x y st) as [z st1] eqn:Hg.
    destruct (map2_emit gate rx ry st1) as [zr st2] eqn:Hmr.
    inversion Hm; subst zs st2; clear Hm.
    destruct (Hg_sat asg x y st z st1 Hsat Hx Hy Hg)
      as (asg1 & Hle1 & Hag1 & Hsat1 & Hz).
    destruct (IH ry asg1 st1 zr st' Hlen'
                (wf_lits_bound_mono _ _ rx Hle1 Hwrx)
                (wf_lits_bound_mono _ _ ry Hle1 Hwry)
                Hsat1 Hmr)
      as (asg2 & Hle2 & Hag2 & Hsat2 & Hlen_zr & Hwf_zr).
    exists asg2; split; [lia | split].
    + exact (agree_below_trans _ asg asg1 asg2 Hag1
               (agree_below_le _ _ asg1 asg2 Hle1 Hag2)).
    + split; [exact Hsat2 | split; [cbn; rewrite Hlen_zr; reflexivity |]].
      constructor; [exact (wf_lit_bound_mono _ _ z Hle2 Hz) | exact Hwf_zr].
Qed.

Lemma emit_or_list_sat : forall ls asg st out st',
  wf_lits_bound (bs_next_var st) ls ->
  sat_blast_st asg st ->
  emit_or_list ls st = (out, st') ->
  exists asg',
    (bs_next_var st <= bs_next_var st')%positive /\
    agree_below (bs_next_var st) asg asg' /\
    sat_blast_st asg' st' /\
    wf_lit_bound (bs_next_var st') out.
Proof.
  induction ls as [| x [| y r] IH]; intros asg st out st' Hwf Hsat Hemit; cbn in Hemit.
  - inversion Hemit; subst; exists asg;
      split; [lia | split; [apply agree_below_refl | split; [exact Hsat |
      cbn; pose proof (proj1 (proj1 Hsat)); lia]]].
  - inversion Hemit; subst; inversion Hwf as [| ? ? Hx _]; subst.
    exists asg;
      split; [lia | split; [apply agree_below_refl | split; [exact Hsat | exact Hx]]].
  - inversion Hwf as [| ? ? Hx Hwfr]; subst.
    destruct (emit_or_list (y :: r) st) as [sub st1] eqn:Hsub.
    destruct (IH asg st sub st1 Hwfr Hsat Hsub)
      as (asg1 & Hle1 & Hag1 & Hsat1 & Hwf_sub).
    destruct (emit_or2_sat asg1 x sub st1 out st' Hsat1
                (wf_lit_bound_mono _ _ x Hle1 Hx) Hwf_sub Hemit)
      as (asg2 & Hle2 & Hag2 & Hsat2 & Hwf_out).
    exists asg2; split; [lia | split].
    + exact (agree_below_trans _ asg asg1 asg2 Hag1
               (agree_below_le _ _ asg1 asg2 Hle1 Hag2)).
    + split; [exact Hsat2 | exact Hwf_out].
Qed.

Lemma mux_bits_list_sat : forall ts fs sel asg st ms st',
  List.length ts = List.length fs ->
  wf_lit_bound (bs_next_var st) sel ->
  wf_lits_bound (bs_next_var st) ts ->
  wf_lits_bound (bs_next_var st) fs ->
  sat_blast_st asg st ->
  mux_bits_list sel ts fs st = (ms, st') ->
  exists asg',
    (bs_next_var st <= bs_next_var st')%positive /\
    agree_below (bs_next_var st) asg asg' /\
    sat_blast_st asg' st' /\
    List.length ms = List.length ts /\
    wf_lits_bound (bs_next_var st') ms.
Proof.
  induction ts as [| t rt IH]; intros [| f rf] sel asg st ms st' Hlen Hsel Hwt Hwf Hsat Hm;
    try discriminate; cbn in Hm.
  - inversion Hm; subst; exists asg;
      split; [lia | split; [apply agree_below_refl | split; [exact Hsat |
      split; [reflexivity | constructor]]]].
  - inversion Hwt as [| ? ? Ht Hwrt]; subst.
    inversion Hwf as [| ? ? Hf Hwrf]; subst.
    injection Hlen as Hlen'.
    destruct (emit_mux2 sel t f st) as [m st1] eqn:He.
    destruct (mux_bits_list sel rt rf st1) as [mr st2] eqn:Hmr.
    inversion Hm; subst ms st2; clear Hm.
    destruct (emit_mux2_sat asg sel t f st m st1 Hsat Hsel Ht Hf He)
      as (asg1 & Hle1 & Hag1 & Hsat1 & Hwf_m).
    destruct (IH rf sel asg1 st1 mr st' Hlen'
                (wf_lit_bound_mono _ _ sel Hle1 Hsel)
                (wf_lits_bound_mono _ _ rt Hle1 Hwrt)
                (wf_lits_bound_mono _ _ rf Hle1 Hwrf)
                Hsat1 Hmr)
      as (asg2 & Hle2 & Hag2 & Hsat2 & Hlen_mr & Hwf_mr).
    exists asg2; split; [lia | split].
    + exact (agree_below_trans _ asg asg1 asg2 Hag1
               (agree_below_le _ _ asg1 asg2 Hle1 Hag2)).
    + split; [exact Hsat2 | split; [cbn; rewrite Hlen_mr; reflexivity |]].
      constructor; [exact (wf_lit_bound_mono _ _ m Hle2 Hwf_m) | exact Hwf_mr].
Qed.

Definition rail_matches_dvalue {Pa : Params}
  (sz : positive) (asg : positive -> bool) (r : rail_bv) (dv : @dvalue Pa) : Prop :=
  if eval_rail_psn asg r
  then dv = DVALUE_Base DVALUE_Poison
  else dv = DVALUE_Base (@DVALUE_I Pa sz (eval_rail_val sz asg r)).

Lemma rail_matches_dvalue_agree :
  forall {Pa : Params} sz bound a1 a2 r (dv : @dvalue Pa),
    agree_below bound a1 a2 ->
    wf_rail_bound sz bound r ->
    rail_matches_dvalue sz a1 r dv ->
    rail_matches_dvalue sz a2 r dv.
Proof.
  intros Pa sz bound a1 a2 r dv Hag Hwf Hm.
  destruct (eval_rail_agree sz bound a1 a2 r Hag Hwf) as [Hpsn Hval].
  unfold rail_matches_dvalue in *; rewrite <- Hpsn, <- Hval; exact Hm.
Qed.

Record blast_env : Set :=
  mk_blast_env {
    be_st      : blast_state;
    be_vars    : list (string * positive * rail_bv);
    be_freezes : list (positive * cert_expr * list lit);
  }.

Fixpoint lookup_blast_var
  (vs : list (string * positive * rail_bv)) (nm : string) (w : positive)
  : option rail_bv :=
  match vs with
  | [] => None
  | (k, kw, r) :: rest =>
      if String.eqb k nm && Pos.eqb kw w
      then Some r
      else lookup_blast_var rest nm w
  end.

Fixpoint lookup_blast_freeze
  (fs : list (positive * cert_expr * list lit)) (w : positive) (key : cert_expr)
  : option (list lit) :=
  match fs with
  | [] => None
  | (fw, fk, bits) :: rest =>
      if Pos.eqb fw w && cert_expr_eqb fk key
      then Some bits
      else lookup_blast_freeze rest w key
  end.

Definition blast_binop_fn (op : cert_binop)
  : option (positive -> rail_bv -> rail_bv -> blast_state -> rail_bv * blast_state) :=
  match op with
  | CB_And => Some blast_and_rail
  | CB_Or  => Some blast_or_rail
  | CB_Xor => Some blast_xor_rail
  | _      => None
  end.

Fixpoint blast_let_free_expr
  (ctx : ub_ctx) (e : cert_expr) (env : blast_env) {struct e}
  : option (rail_bv * blast_env) :=
  match e with
  | CE_BvConst w val =>
      Some (blast_const_rail w val, env)
  | CE_Poison w =>
      Some (blast_poison_rail w, env)
  | CE_Var nm w =>
      match lookup_blast_var (be_vars env) nm w with
      | Some r => Some (r, env)
      | None =>
          let '(bits, st1) := alloc_fresh_bits (Pos.to_nat w) (be_st env) in
          let '(psn, st2) :=
              if ctx_has_param_noundef ctx nm w
              then (lit_false, st1)
              else alloc_var st1 in
          let r := mk_rail_bv w bits psn in
          Some (r, mk_blast_env st2 ((nm, w, r) :: be_vars env) (be_freezes env))
      end
  | CE_BinOp op w fl l r =>
      if cert_binop_flags_eqb fl no_binop_flags then
        match blast_binop_fn op with
        | Some bf =>
            match blast_let_free_expr ctx l env with
            | Some (rl, env1) =>
                match blast_let_free_expr ctx r env1 with
                | Some (rr, env2) =>
                    let '(out, st3) := bf w rl rr (be_st env2) in
                    Some (out, mk_blast_env st3 (be_vars env2) (be_freezes env2))
                | None => None
                end
            | None => None
            end
        | None => None
        end
      else None
  | CE_ICmp CIP_Eq false w l r =>
      match blast_let_free_expr ctx l env with
      | Some (rl, env1) =>
          match blast_let_free_expr ctx r env1 with
          | Some (rr, env2) =>
              let '(out, st3) := blast_eq_rail w rl rr (be_st env2) in
              Some (out, mk_blast_env st3 (be_vars env2) (be_freezes env2))
          | None => None
          end
      | None => None
      end
  | CE_ICmp _ _ _ _ _ => None
  | CE_Cast _ _ _ _ _ => None
  | CE_Select w c t f =>
      match blast_let_free_expr ctx c env with
      | Some (rc, env1) =>
          match blast_let_free_expr ctx t env1 with
          | Some (rt, env2) =>
              match blast_let_free_expr ctx f env2 with
              | Some (rf, env3) =>
                  let '(out, st4) := blast_select_rail w rc rt rf (be_st env3) in
                  Some (out, mk_blast_env st4 (be_vars env3) (be_freezes env3))
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | CE_Freeze w o =>
      match blast_let_free_expr ctx o env with
      | Some (ro, env1) =>
          let key := expand_lets_with [] o in
          match lookup_blast_freeze (be_freezes env1) w key with
          | Some fbits =>
              let '(bits, st2) := mux_bits_list (rbv_psn ro) fbits (rbv_bits ro) (be_st env1) in
              Some (mk_rail_bv w bits lit_false,
                    mk_blast_env st2 (be_vars env1) (be_freezes env1))
          | None =>
              let '(fbits, st2) := alloc_fresh_bits (Pos.to_nat w) (be_st env1) in
              let '(bits, st3)  := mux_bits_list (rbv_psn ro) fbits (rbv_bits ro) st2 in
              Some (mk_rail_bv w bits lit_false,
                    mk_blast_env st3 (be_vars env1) ((w, key, fbits) :: be_freezes env1))
          end
      | None => None
      end
  | CE_Let _ _ => None
  end.

Definition sat_blast_env {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (asg : positive -> bool) (env : blast_env) : Prop :=
  sat_blast_st asg (be_st env) /\
  (forall nm w r,
     lookup_blast_var (be_vars env) nm w = Some r ->
     wf_rail_bound w (bs_next_var (be_st env)) r /\
     exists dv, penv nm = Some dv /\
                wf_scalar_dvalue w dv /\
                rail_matches_dvalue w asg r dv) /\
  (forall w key fbits,
     lookup_blast_freeze (be_freezes env) w key = Some fbits ->
     List.length fbits = Pos.to_nat w /\
     wf_lits_bound (bs_next_var (be_st env)) fbits /\
     List.map (eval_lit asg) fbits =
     bit_int_to_bools w (@Integers.repr w (foracle w key))).

Lemma sat_blast_env_step :
  forall {Pa : Params} (penv : param_env Pa) foracle asg asg' env st',
    sat_blast_env penv foracle asg env ->
    (bs_next_var (be_st env) <= bs_next_var st')%positive ->
    agree_below (bs_next_var (be_st env)) asg asg' ->
    sat_blast_st asg' st' ->
    sat_blast_env penv foracle asg' (mk_blast_env st' (be_vars env) (be_freezes env)).
Proof.
  intros Pa penv foracle asg asg' env st' (_ & Hvars & Hfrzs) Hle Hag Hst'; split; [exact Hst' | split].
  - intros nm w r Hlk; cbn in Hlk |- *.
    destruct (Hvars nm w r Hlk) as (Hwf & dv & Hpm & Hwfdv & Hrm).
    split; [exact (wf_rail_bound_mono w _ _ r Hle Hwf) |].
    exists dv; repeat split; [exact Hpm | exact Hwfdv |].
    exact (rail_matches_dvalue_agree w _ asg asg' r dv Hag Hwf Hrm).
  - intros w key fbits Hlk; cbn in Hlk |- *.
    destruct (Hfrzs w key fbits Hlk) as (Hlen & Hwf & Hmap).
    repeat split; [exact Hlen | exact (wf_lits_bound_mono _ _ fbits Hle Hwf) |].
    rewrite <- (eval_lits_agree _ asg asg' fbits Hag Hwf); exact Hmap.
Qed.

Lemma existsb_xor_bits_true_neq : forall sz assign rl rr xor_bits,
  wf_rail_bv sz rl ->
  wf_rail_bv sz rr ->
  List.length xor_bits = Pos.to_nat sz ->
  (forall k, (k < Pos.to_nat sz)%nat ->
     List.nth k (List.map (eval_lit assign) xor_bits) false =
     xorb (List.nth k (List.map (eval_lit assign) (rbv_bits rl)) false)
          (List.nth k (List.map (eval_lit assign) (rbv_bits rr)) false)) ->
  existsb (eval_lit assign) xor_bits = true ->
  eval_rail_val sz assign rl <> eval_rail_val sz assign rr.
Proof.
  intros sz assign rl rr xor_bits [_ Hll] [_ Hlr] Hlx Hxor Hex Heq.
  apply existsb_exists in Hex as [z [Hz_in Hz_ev]].
  assert (Hin_map : In true (List.map (eval_lit assign) xor_bits))
    by (apply in_map_iff; exists z; split; assumption).
  destruct (In_nth _ _ false Hin_map) as [k [Hk Hnth]].
  rewrite map_length, Hlx in Hk.
  rewrite (Hxor k Hk) in Hnth.
  pose proof (eval_rail_val_testbit_nat sz assign rl k Hk) as Htl.
  pose proof (eval_rail_val_testbit_nat sz assign rr k Hk) as Htr.
  rewrite Heq, Htr in Htl; rewrite <- Htl, Bool.xorb_nilpotent in Hnth; discriminate Hnth.
Qed.

Lemma blast_binop_fn_sat :
  forall {Pa : Params} op bf w rl rr asg st out st' (vl vr : @dvalue Pa),
    blast_binop_fn op = Some bf ->
    sat_blast_st asg st ->
    wf_rail_bound w (bs_next_var st) rl ->
    wf_rail_bound w (bs_next_var st) rr ->
    rail_matches_dvalue w asg rl vl ->
    rail_matches_dvalue w asg rr vr ->
    bf w rl rr st = (out, st') ->
    exists asg' vout,
      @eval_iop Pa (cert_to_ibinop op no_binop_flags) vl vr = raise_ret vout /\
      (bs_next_var st <= bs_next_var st')%positive /\
      agree_below (bs_next_var st) asg asg' /\
      sat_blast_st asg' st' /\
      wf_rail_bound w (bs_next_var st') out /\
      rail_matches_dvalue w asg' out vout.
Proof.
  intros Pa op bf w rl rr asg st out st' vl vr Hop Hsat
         ([Hwl Hll] & Hbl & Hpl) ([Hwr Hlr] & Hbr & Hpr) Hml Hmr Hbf.
  assert (Hlen_lr : List.length (rbv_bits rl) = List.length (rbv_bits rr)) by congruence.
  destruct op; cbn in Hop; try discriminate Hop; inversion Hop; subst bf; clear Hop.
  - (* CB_And *)
    unfold blast_and_rail in Hbf.
    destruct (map2_emit emit_and2 (rbv_bits rl) (rbv_bits rr) st) as [bits st1] eqn:Hm.
    destruct (emit_or2 (rbv_psn rl) (rbv_psn rr) st1) as [psn st2] eqn:Hp.
    inversion Hbf; subst out st2; clear Hbf.
    destruct (map2_emit_sat emit_and2 emit_and2_sat _ _ asg st bits st1
                Hlen_lr Hbl Hbr Hsat Hm)
      as (asg1 & Hle1 & Hag1 & Hsat1 & Hblen & Hbwf).
    destruct (emit_or2_sat asg1 (rbv_psn rl) (rbv_psn rr) st1 psn st' Hsat1
                (wf_lit_bound_mono _ _ _ Hle1 Hpl) (wf_lit_bound_mono _ _ _ Hle1 Hpr) Hp)
      as (asg2 & Hle2 & Hag2 & Hsat2 & Hpwf).
    assert (Hag : agree_below (bs_next_var st) asg asg2)
      by exact (agree_below_trans _ asg asg1 asg2 Hag1 (agree_below_le _ _ asg1 asg2 Hle1 Hag2)).
    assert (Hbl_orig : blast_and_rail w rl rr st = (mk_rail_bv w bits psn, st'))
      by (unfold blast_and_rail; rewrite Hm, Hp; reflexivity).
    assert (Hcnf_nil : eval_cnf asg2 (bs_cnf st' ++ []) = true)
      by (rewrite app_nil_r; exact (proj2 (proj2 Hsat2))).
    destruct (blast_and_rail_sound asg2 w rl rr st (mk_rail_bv w bits psn) st' []
                (wf_rail_bound_lits w _ rl (conj (conj Hwl Hll) (conj Hbl Hpl)))
                (wf_rail_bound_lits w _ rr (conj (conj Hwr Hlr) (conj Hbr Hpr)))
                Hbl_orig Hcnf_nil)
      as (_ & Hpsn_eq & Hval_eq).
    pose proof (rail_matches_dvalue_agree w _ asg asg2 rl vl Hag
                  (conj (conj Hwl Hll) (conj Hbl Hpl)) Hml) as Hml2.
    pose proof (rail_matches_dvalue_agree w _ asg asg2 rr vr Hag
                  (conj (conj Hwr Hlr) (conj Hbr Hpr)) Hmr) as Hmr2.
    unfold rail_matches_dvalue in Hml2, Hmr2.
    assert (Hout_wf : wf_rail_bound w (bs_next_var st') (mk_rail_bv w bits psn)).
    { split; [split; [reflexivity | cbn; congruence] |
              split; [exact (wf_lits_bound_mono _ _ bits Hle2 Hbwf) | exact Hpwf]]. }
    destruct (eval_rail_psn asg2 rl) eqn:Epl, (eval_rail_psn asg2 rr) eqn:Epr; subst vl vr.
    + exists asg2, (DVALUE_Base DVALUE_Poison);
        split; [reflexivity | split; [lia | split; [exact Hag |
        split; [exact Hsat2 | split; [exact Hout_wf |
        unfold rail_matches_dvalue; rewrite Hpsn_eq, Epl; reflexivity]]]]].
    + exists asg2, (DVALUE_Base DVALUE_Poison);
        split; [reflexivity | split; [lia | split; [exact Hag |
        split; [exact Hsat2 | split; [exact Hout_wf |
        unfold rail_matches_dvalue; rewrite Hpsn_eq, Epl; reflexivity]]]]].
    + exists asg2, (DVALUE_Base DVALUE_Poison);
        split; [reflexivity | split; [lia | split; [exact Hag |
        split; [exact Hsat2 | split; [exact Hout_wf |
        unfold rail_matches_dvalue; rewrite Hpsn_eq, Epl, Epr; reflexivity]]]]].
    + exists asg2, (DVALUE_Base (@DVALUE_I Pa w (eval_rail_val w asg2 (mk_rail_bv w bits psn)))).
      split; [unfold eval_iop; rewrite eval_iop_integer_base_same_width, Hval_eq; reflexivity |
      split; [lia | split; [exact Hag | split; [exact Hsat2 | split; [exact Hout_wf |
      unfold rail_matches_dvalue; rewrite Hpsn_eq, Epl, Epr; reflexivity]]]]].
  - (* CB_Or *)
    unfold blast_or_rail in Hbf.
    destruct (map2_emit emit_or2 (rbv_bits rl) (rbv_bits rr) st) as [bits st1] eqn:Hm.
    destruct (emit_or2 (rbv_psn rl) (rbv_psn rr) st1) as [psn st2] eqn:Hp.
    inversion Hbf; subst out st2; clear Hbf.
    destruct (map2_emit_sat emit_or2 emit_or2_sat _ _ asg st bits st1
                Hlen_lr Hbl Hbr Hsat Hm)
      as (asg1 & Hle1 & Hag1 & Hsat1 & Hblen & Hbwf).
    destruct (emit_or2_sat asg1 (rbv_psn rl) (rbv_psn rr) st1 psn st' Hsat1
                (wf_lit_bound_mono _ _ _ Hle1 Hpl) (wf_lit_bound_mono _ _ _ Hle1 Hpr) Hp)
      as (asg2 & Hle2 & Hag2 & Hsat2 & Hpwf).
    assert (Hag : agree_below (bs_next_var st) asg asg2)
      by exact (agree_below_trans _ asg asg1 asg2 Hag1 (agree_below_le _ _ asg1 asg2 Hle1 Hag2)).
    assert (Hbl_orig : blast_or_rail w rl rr st = (mk_rail_bv w bits psn, st'))
      by (unfold blast_or_rail; rewrite Hm, Hp; reflexivity).
    assert (Hcnf_nil : eval_cnf asg2 (bs_cnf st' ++ []) = true)
      by (rewrite app_nil_r; exact (proj2 (proj2 Hsat2))).
    destruct (blast_or_rail_sound asg2 w rl rr st (mk_rail_bv w bits psn) st' []
                (wf_rail_bound_lits w _ rl (conj (conj Hwl Hll) (conj Hbl Hpl)))
                (wf_rail_bound_lits w _ rr (conj (conj Hwr Hlr) (conj Hbr Hpr)))
                Hbl_orig Hcnf_nil)
      as (_ & Hpsn_eq & Hval_eq).
    pose proof (rail_matches_dvalue_agree w _ asg asg2 rl vl Hag
                  (conj (conj Hwl Hll) (conj Hbl Hpl)) Hml) as Hml2.
    pose proof (rail_matches_dvalue_agree w _ asg asg2 rr vr Hag
                  (conj (conj Hwr Hlr) (conj Hbr Hpr)) Hmr) as Hmr2.
    unfold rail_matches_dvalue in Hml2, Hmr2.
    assert (Hout_wf : wf_rail_bound w (bs_next_var st') (mk_rail_bv w bits psn)).
    { split; [split; [reflexivity | cbn; congruence] |
              split; [exact (wf_lits_bound_mono _ _ bits Hle2 Hbwf) | exact Hpwf]]. }
    destruct (eval_rail_psn asg2 rl) eqn:Epl, (eval_rail_psn asg2 rr) eqn:Epr; subst vl vr.
    + exists asg2, (DVALUE_Base DVALUE_Poison);
        split; [reflexivity | split; [lia | split; [exact Hag |
        split; [exact Hsat2 | split; [exact Hout_wf |
        unfold rail_matches_dvalue; rewrite Hpsn_eq, Epl; reflexivity]]]]].
    + exists asg2, (DVALUE_Base DVALUE_Poison);
        split; [reflexivity | split; [lia | split; [exact Hag |
        split; [exact Hsat2 | split; [exact Hout_wf |
        unfold rail_matches_dvalue; rewrite Hpsn_eq, Epl; reflexivity]]]]].
    + exists asg2, (DVALUE_Base DVALUE_Poison);
        split; [reflexivity | split; [lia | split; [exact Hag |
        split; [exact Hsat2 | split; [exact Hout_wf |
        unfold rail_matches_dvalue; rewrite Hpsn_eq, Epl, Epr; reflexivity]]]]].
    + exists asg2, (DVALUE_Base (@DVALUE_I Pa w (eval_rail_val w asg2 (mk_rail_bv w bits psn)))).
      split; [unfold eval_iop; rewrite eval_iop_integer_base_same_width, Hval_eq; reflexivity |
      split; [lia | split; [exact Hag | split; [exact Hsat2 | split; [exact Hout_wf |
      unfold rail_matches_dvalue; rewrite Hpsn_eq, Epl, Epr; reflexivity]]]]].
  - (* CB_Xor *)
    unfold blast_xor_rail in Hbf.
    destruct (map2_emit emit_xor2 (rbv_bits rl) (rbv_bits rr) st) as [bits st1] eqn:Hm.
    destruct (emit_or2 (rbv_psn rl) (rbv_psn rr) st1) as [psn st2] eqn:Hp.
    inversion Hbf; subst out st2; clear Hbf.
    destruct (map2_emit_sat emit_xor2 emit_xor2_sat _ _ asg st bits st1
                Hlen_lr Hbl Hbr Hsat Hm)
      as (asg1 & Hle1 & Hag1 & Hsat1 & Hblen & Hbwf).
    destruct (emit_or2_sat asg1 (rbv_psn rl) (rbv_psn rr) st1 psn st' Hsat1
                (wf_lit_bound_mono _ _ _ Hle1 Hpl) (wf_lit_bound_mono _ _ _ Hle1 Hpr) Hp)
      as (asg2 & Hle2 & Hag2 & Hsat2 & Hpwf).
    assert (Hag : agree_below (bs_next_var st) asg asg2)
      by exact (agree_below_trans _ asg asg1 asg2 Hag1 (agree_below_le _ _ asg1 asg2 Hle1 Hag2)).
    assert (Hbl_orig : blast_xor_rail w rl rr st = (mk_rail_bv w bits psn, st'))
      by (unfold blast_xor_rail; rewrite Hm, Hp; reflexivity).
    assert (Hcnf_nil : eval_cnf asg2 (bs_cnf st' ++ []) = true)
      by (rewrite app_nil_r; exact (proj2 (proj2 Hsat2))).
    destruct (blast_xor_rail_sound asg2 w rl rr st (mk_rail_bv w bits psn) st' []
                (wf_rail_bound_lits w _ rl (conj (conj Hwl Hll) (conj Hbl Hpl)))
                (wf_rail_bound_lits w _ rr (conj (conj Hwr Hlr) (conj Hbr Hpr)))
                Hbl_orig Hcnf_nil)
      as (_ & Hpsn_eq & Hval_eq).
    pose proof (rail_matches_dvalue_agree w _ asg asg2 rl vl Hag
                  (conj (conj Hwl Hll) (conj Hbl Hpl)) Hml) as Hml2.
    pose proof (rail_matches_dvalue_agree w _ asg asg2 rr vr Hag
                  (conj (conj Hwr Hlr) (conj Hbr Hpr)) Hmr) as Hmr2.
    unfold rail_matches_dvalue in Hml2, Hmr2.
    assert (Hout_wf : wf_rail_bound w (bs_next_var st') (mk_rail_bv w bits psn)).
    { split; [split; [reflexivity | cbn; congruence] |
              split; [exact (wf_lits_bound_mono _ _ bits Hle2 Hbwf) | exact Hpwf]]. }
    destruct (eval_rail_psn asg2 rl) eqn:Epl, (eval_rail_psn asg2 rr) eqn:Epr; subst vl vr.
    + exists asg2, (DVALUE_Base DVALUE_Poison);
        split; [reflexivity | split; [lia | split; [exact Hag |
        split; [exact Hsat2 | split; [exact Hout_wf |
        unfold rail_matches_dvalue; rewrite Hpsn_eq, Epl; reflexivity]]]]].
    + exists asg2, (DVALUE_Base DVALUE_Poison);
        split; [reflexivity | split; [lia | split; [exact Hag |
        split; [exact Hsat2 | split; [exact Hout_wf |
        unfold rail_matches_dvalue; rewrite Hpsn_eq, Epl; reflexivity]]]]].
    + exists asg2, (DVALUE_Base DVALUE_Poison);
        split; [reflexivity | split; [lia | split; [exact Hag |
        split; [exact Hsat2 | split; [exact Hout_wf |
        unfold rail_matches_dvalue; rewrite Hpsn_eq, Epl, Epr; reflexivity]]]]].
    + exists asg2, (DVALUE_Base (@DVALUE_I Pa w (eval_rail_val w asg2 (mk_rail_bv w bits psn)))).
      split; [unfold eval_iop; rewrite eval_iop_integer_base_same_width, Hval_eq; reflexivity |
      split; [lia | split; [exact Hag | split; [exact Hsat2 | split; [exact Hout_wf |
      unfold rail_matches_dvalue; rewrite Hpsn_eq, Epl, Epr; reflexivity]]]]].
Qed.

Lemma blast_eq_rail_sat :
  forall {Pa : Params} w rl rr asg st out st' (vl vr : @dvalue Pa),
    sat_blast_st asg st ->
    wf_rail_bound w (bs_next_var st) rl ->
    wf_rail_bound w (bs_next_var st) rr ->
    rail_matches_dvalue w asg rl vl ->
    rail_matches_dvalue w asg rr vr ->
    blast_eq_rail w rl rr st = (out, st') ->
    exists asg' vout,
      @eval_icmp Pa false (cert_to_icmp CIP_Eq) vl vr = raise_ret vout /\
      (bs_next_var st <= bs_next_var st')%positive /\
      agree_below (bs_next_var st) asg asg' /\
      sat_blast_st asg' st' /\
      wf_rail_bound 1%positive (bs_next_var st') out /\
      rail_matches_dvalue 1%positive asg' out vout.
Proof.
  intros Pa w rl rr asg st out st' vl vr Hsat
         ([Hwl Hll] & Hbl & Hpl) ([Hwr Hlr] & Hbr & Hpr) Hml Hmr Heq_bl.
  unfold blast_eq_rail in Heq_bl.
  destruct (map2_emit emit_xor2 (rbv_bits rl) (rbv_bits rr) st) as [xor_bits st1] eqn:Hm.
  destruct (emit_or_list xor_bits st1) as [any_diff st2] eqn:Horl.
  destruct (emit_or2 (rbv_psn rl) (rbv_psn rr) st2) as [psn st3] eqn:Hp.
  inversion Heq_bl; subst out st3; clear Heq_bl.
  assert (Hlen_lr : List.length (rbv_bits rl) = List.length (rbv_bits rr)) by congruence.
  destruct (map2_emit_sat emit_xor2 emit_xor2_sat _ _ asg st xor_bits st1
              Hlen_lr Hbl Hbr Hsat Hm)
    as (asg1 & Hle1 & Hag1 & Hsat1 & Hxlen & Hxwf).
  destruct (emit_or_list_sat xor_bits asg1 st1 any_diff st2 Hxwf Hsat1 Horl)
    as (asg2 & Hle2 & Hag2 & Hsat2 & Had_wf).
  assert (Hle12 : (bs_next_var st <= bs_next_var st2)%positive) by lia.
  destruct (emit_or2_sat asg2 (rbv_psn rl) (rbv_psn rr) st2 psn st' Hsat2
              (wf_lit_bound_mono _ _ _ Hle12 Hpl) (wf_lit_bound_mono _ _ _ Hle12 Hpr) Hp)
    as (asg3 & Hle3 & Hag3 & Hsat3 & Hpwf).
  assert (Hag : agree_below (bs_next_var st) asg asg3).
  { apply (agree_below_trans _ asg asg1 asg3 Hag1).
    apply (agree_below_le _ _ asg1 asg3 Hle1).
    exact (agree_below_trans _ asg1 asg2 asg3 Hag2 (agree_below_le _ _ asg2 asg3 Hle2 Hag3)). }
  assert (Had_wf3 : wf_lit_bound (bs_next_var st') any_diff)
    by exact (wf_lit_bound_mono _ _ any_diff Hle3 Had_wf).
  assert (Hout_wf : wf_rail_bound 1%positive (bs_next_var st')
                      (mk_rail_bv 1%positive [neg_lit any_diff] psn)).
  { repeat split; cbn; [constructor; [apply wf_lit_bound_neg; exact Had_wf3 | constructor] | exact Hpwf]. }
  destruct (emit_or_list_pref _ _ _ _ Horl) as [d2 Hd2].
  destruct (emit_or2_pref _ _ _ _ _ Hp) as [d3 Hd3].
  assert (Hs3 : eval_cnf asg3 (bs_cnf st' ++ []) = true)
    by (rewrite app_nil_r; exact (proj2 (proj2 Hsat3))).
  assert (Hs2 : eval_cnf asg3 (bs_cnf st2 ++ d3) = true)
    by (rewrite <- Hd3; exact (proj2 (proj2 Hsat3))).
  assert (Hs1 : eval_cnf asg3 (bs_cnf st1 ++ d2 ++ d3) = true)
    by (rewrite app_assoc, <- Hd2; exact Hs2).
  assert (Hlf3 : eval_lit asg3 lit_false = false)
    by (cbn; rewrite (proj1 (proj2 Hsat3)); reflexivity).
  destruct (map2_emit_sound emit_xor2 xorb emit_xor2_pref
              (fun a0 x y s0 z s1 Hx Hy Hg =>
                 let (Hz, Hev) := emit_xor2_sound a0 x y s0 z s1 Hx Hy Hg in
                 conj Hz (fun r0 Hs0 => proj2 (Hev r0 Hs0)))
              asg3 _ _ _ _ _ Hlen_lr
              (wf_lits_bound_nonzero _ _ Hbl) (wf_lits_bound_nonzero _ _ Hbr) Hm)
    as (_ & Hx_nz & Hx_ev).
  destruct (emit_or_list_sound asg3 xor_bits st1 any_diff st2 d3 Hlf3 Hx_nz Horl Hs2)
    as [Had_nz Had_ev].
  destruct (emit_or2_sound asg3 (rbv_psn rl) (rbv_psn rr) st2 psn st'
              (wf_lit_bound_nonzero _ _ Hpl) (wf_lit_bound_nonzero _ _ Hpr) Hp)
    as [_ Hp_ev].
  pose proof (proj2 (Hp_ev [] Hs3)) as Hpsn_eq.
  pose proof (rail_matches_dvalue_agree w _ asg asg3 rl vl Hag
                (conj (conj Hwl Hll) (conj Hbl Hpl)) Hml) as Hml3.
  pose proof (rail_matches_dvalue_agree w _ asg asg3 rr vr Hag
                (conj (conj Hwr Hlr) (conj Hbr Hpr)) Hmr) as Hmr3.
  unfold rail_matches_dvalue in Hml3, Hmr3.
  destruct (eval_rail_psn asg3 rl) eqn:Epl, (eval_rail_psn asg3 rr) eqn:Epr; subst vl vr.
  - exists asg3, (DVALUE_Base DVALUE_Poison);
      split; [reflexivity | split; [lia | split; [exact Hag |
      split; [exact Hsat3 | split; [exact Hout_wf |
      unfold rail_matches_dvalue; cbn [eval_rail_psn rbv_psn];
      unfold eval_rail_psn in Epl; rewrite Hpsn_eq, Epl; reflexivity]]]]].
  - exists asg3, (DVALUE_Base DVALUE_Poison);
      split; [reflexivity | split; [lia | split; [exact Hag |
      split; [exact Hsat3 | split; [exact Hout_wf |
      unfold rail_matches_dvalue; cbn [eval_rail_psn rbv_psn];
      unfold eval_rail_psn in Epl; rewrite Hpsn_eq, Epl; reflexivity]]]]].
  - exists asg3, (DVALUE_Base DVALUE_Poison);
      split; [reflexivity | split; [lia | split; [exact Hag |
      split; [exact Hsat3 | split; [exact Hout_wf |
      unfold rail_matches_dvalue; cbn [eval_rail_psn rbv_psn];
      unfold eval_rail_psn in Epl, Epr; rewrite Hpsn_eq, Epl, Epr; reflexivity]]]]].
  - exists asg3, (DVALUE_Base (@DVALUE_I Pa 1%positive
                    (eval_rail_val 1%positive asg3 (mk_rail_bv 1%positive [neg_lit any_diff] psn)))).
    split;
      [| split; [lia | split; [exact Hag | split; [exact Hsat3 | split; [exact Hout_wf |
         unfold rail_matches_dvalue; cbn [eval_rail_psn rbv_psn];
         unfold eval_rail_psn in Epl, Epr; rewrite Hpsn_eq, Epl, Epr; reflexivity]]]]].
    unfold eval_icmp; rewrite eval_icmp_base_same_width; unfold cert_to_icmp, eval_int_icmp; cbn.
    unfold eval_rail_val at 3; cbn [rbv_bits List.map].
    rewrite (eval_neg_lit_nonzero asg3 any_diff Had_nz), Had_ev.
    assert (Hx_k : forall k, (k < Pos.to_nat w)%nat ->
              List.nth k (List.map (eval_lit asg3) xor_bits) false =
              xorb (List.nth k (List.map (eval_lit asg3) (rbv_bits rl)) false)
                   (List.nth k (List.map (eval_lit asg3) (rbv_bits rr)) false))
      by (intros k Hk; apply (Hx_ev (d2 ++ d3) k); [congruence | exact Hs1]).
    destruct (existsb (eval_lit asg3) xor_bits) eqn:Eex.
    + pose proof (existsb_xor_bits_true_neq w asg3 rl rr xor_bits
                    (conj Hwl Hll) (conj Hwr Hlr) (eq_trans Hxlen Hll) Hx_k Eex) as Hneq.
      change (@Integers.cmpu w Integers.Ceq (eval_rail_val w asg3 rl) (eval_rail_val w asg3 rr))
        with (@Integers.eq w (eval_rail_val w asg3 rl) (eval_rail_val w asg3 rr)).
      rewrite (@Integers.eq_false w _ _ Hneq); reflexivity.
    + pose proof (existsb_xor_bits_diff w asg3 rl rr xor_bits
                    (conj Hwl Hll) (conj Hwr Hlr) (eq_trans Hxlen Hll) Hx_k Eex) as Heqv.
      change (@Integers.cmpu w Integers.Ceq (eval_rail_val w asg3 rl) (eval_rail_val w asg3 rr))
        with (@Integers.eq w (eval_rail_val w asg3 rl) (eval_rail_val w asg3 rr)).
      rewrite Heqv, (@Integers.eq_true w); reflexivity.
Qed.

Lemma blast_select_rail_sat :
  forall {Pa : Params} w rc rt rf asg st out st' (vc vt vf : @dvalue Pa),
    sat_blast_st asg st ->
    wf_rail_bound 1%positive (bs_next_var st) rc ->
    wf_rail_bound w (bs_next_var st) rt ->
    wf_rail_bound w (bs_next_var st) rf ->
    rail_matches_dvalue 1%positive asg rc vc ->
    rail_matches_dvalue w asg rt vt ->
    rail_matches_dvalue w asg rf vf ->
    blast_select_rail w rc rt rf st = (out, st') ->
    exists asg' vout,
      @eval_select Pa vc (DTYPE_Base (DTYPE_I w)) vt vf = raise_ret vout /\
      (bs_next_var st <= bs_next_var st')%positive /\
      agree_below (bs_next_var st) asg asg' /\
      sat_blast_st asg' st' /\
      wf_rail_bound w (bs_next_var st') out /\
      rail_matches_dvalue w asg' out vout.
Proof.
  intros Pa w rc rt rf asg st out st' vc vt vf Hsat
         ([Hwc Hlc] & Hbc & Hpc) ([Hwt Hlt] & Hbt & Hpt) ([Hwf Hlf] & Hbf & Hpf)
         Hmc Hmt Hmf Hsel_bl.
  destruct (rbv_bits rc) as [| c0 [| ? ?]] eqn:Ecb; cbn in Hlc; try discriminate Hlc.
  inversion Hbc as [| ? ? Hc0 _]; subst.
  unfold blast_select_rail in Hsel_bl; rewrite Ecb in Hsel_bl; cbn [List.hd] in Hsel_bl.
  destruct (mux_bits_list c0 (rbv_bits rt) (rbv_bits rf) st) as [bits st1] eqn:Hmux.
  destruct (emit_mux2 c0 (rbv_psn rt) (rbv_psn rf) st1) as [br_psn st2] eqn:Hbp.
  destruct (emit_or2 (rbv_psn rc) br_psn st2) as [psn st3] eqn:Hp.
  inversion Hsel_bl; subst out st3; clear Hsel_bl.
  assert (Hlen_tf : List.length (rbv_bits rt) = List.length (rbv_bits rf)) by congruence.
  destruct (mux_bits_list_sat (rbv_bits rt) (rbv_bits rf) c0 asg st bits st1
              Hlen_tf Hc0 Hbt Hbf Hsat Hmux)
    as (asg1 & Hle1 & Hag1 & Hsat1 & Hblen & Hbwf).
  destruct (emit_mux2_sat asg1 c0 (rbv_psn rt) (rbv_psn rf) st1 br_psn st2 Hsat1
              (wf_lit_bound_mono _ _ _ Hle1 Hc0)
              (wf_lit_bound_mono _ _ _ Hle1 Hpt)
              (wf_lit_bound_mono _ _ _ Hle1 Hpf) Hbp)
    as (asg2 & Hle2 & Hag2 & Hsat2 & Hbp_wf).
  assert (Hle12 : (bs_next_var st <= bs_next_var st2)%positive) by lia.
  destruct (emit_or2_sat asg2 (rbv_psn rc) br_psn st2 psn st' Hsat2
              (wf_lit_bound_mono _ _ _ Hle12 Hpc) Hbp_wf Hp)
    as (asg3 & Hle3 & Hag3 & Hsat3 & Hpwf).
  assert (Hag : agree_below (bs_next_var st) asg asg3).
  { apply (agree_below_trans _ asg asg1 asg3 Hag1).
    apply (agree_below_le _ _ asg1 asg3 Hle1).
    exact (agree_below_trans _ asg1 asg2 asg3 Hag2 (agree_below_le _ _ asg2 asg3 Hle2 Hag3)). }
  assert (Hout_wf : wf_rail_bound w (bs_next_var st') (mk_rail_bv w bits psn)).
  { split; [split; [reflexivity | cbn; congruence] |
            split; [exact (wf_lits_bound_mono _ _ bits (Pos.le_trans _ _ _ Hle2 Hle3) Hbwf)
                    | exact Hpwf]]. }
  assert (Hd2 : exists d2, bs_cnf st2 = bs_cnf st1 ++ d2).
  { unfold emit_mux2 in Hbp; cbn in Hbp; destruct (append_clauses _ _) as [cid2 nc2];
      inversion Hbp; subst; cbn; exists nc2; reflexivity. }
  destruct Hd2 as [d2 Hd2].
  destruct (emit_or2_pref _ _ _ _ _ Hp) as [d3 Hd3].
  assert (Hs3 : eval_cnf asg3 (bs_cnf st' ++ []) = true)
    by (rewrite app_nil_r; exact (proj2 (proj2 Hsat3))).
  assert (Hs2 : eval_cnf asg3 (bs_cnf st2 ++ d3) = true)
    by (rewrite <- Hd3; exact (proj2 (proj2 Hsat3))).
  assert (Hs1 : eval_cnf asg3 (bs_cnf st1 ++ d2 ++ d3) = true)
    by (rewrite app_assoc, <- Hd2; exact Hs2).
  destruct (mux_bits_list_sound asg3 c0 (rbv_bits rt) (rbv_bits rf) st bits st1 (d2 ++ d3)
              (wf_lit_bound_nonzero _ _ Hc0) Hlen_tf
              (wf_lits_bound_nonzero _ _ Hbt) (wf_lits_bound_nonzero _ _ Hbf) Hmux Hs1)
    as (_ & _ & Hbits_ev).
  destruct (emit_mux2_sound asg3 c0 (rbv_psn rt) (rbv_psn rf) st1 br_psn st2
              (wf_lit_bound_nonzero _ _ Hc0)
              (wf_lit_bound_nonzero _ _ Hpt)
              (wf_lit_bound_nonzero _ _ Hpf) Hbp)
    as [Hbp_nz Hbp_ev].
  destruct (emit_or2_sound asg3 (rbv_psn rc) br_psn st2 psn st'
              (wf_lit_bound_nonzero _ _ Hpc) Hbp_nz Hp)
    as [_ Hp_ev].
  pose proof (proj2 (Hp_ev [] Hs3)) as Hpsn_eq.
  pose proof (proj2 (Hbp_ev d3 Hs2)) as Hbp_eq.
  pose proof (rail_matches_dvalue_agree 1%positive _ asg asg3 rc vc Hag
                (conj (conj Hwc (eq_ind_r (fun l => List.length l = 1%nat) eq_refl Ecb))
                      (conj (eq_ind_r (wf_lits_bound _) Hbc Ecb) Hpc)) Hmc) as Hmc3.
  pose proof (rail_matches_dvalue_agree w _ asg asg3 rt vt Hag
                (conj (conj Hwt Hlt) (conj Hbt Hpt)) Hmt) as Hmt3.
  pose proof (rail_matches_dvalue_agree w _ asg asg3 rf vf Hag
                (conj (conj Hwf Hlf) (conj Hbf Hpf)) Hmf) as Hmf3.
  unfold rail_matches_dvalue in Hmc3, Hmt3, Hmf3.
  destruct (eval_rail_psn asg3 rc) eqn:Epc.
  - subst vc.
    exists asg3, (DVALUE_Base DVALUE_Poison);
      split; [reflexivity | split; [lia | split; [exact Hag |
      split; [exact Hsat3 | split; [exact Hout_wf |
      unfold rail_matches_dvalue; cbn [eval_rail_psn rbv_psn];
      unfold eval_rail_psn in Epc; rewrite Hpsn_eq, Epc; reflexivity]]]]].
  - subst vc; unfold eval_rail_val in Hmc3; rewrite Ecb in Hmc3; cbn [List.map] in Hmc3.
    destruct (eval_lit asg3 c0) eqn:Ec0; cbn [bools_to_Z] in Hmc3.
    + exists asg3, vt;
        split; [cbn; change (@Integers.repr 1 1) with (@Integers.one 1);
                rewrite (@Integers.unsigned_one 1); reflexivity
                | split; [lia | split; [exact Hag | split; [exact Hsat3 | split; [exact Hout_wf |]]]]].
      unfold rail_matches_dvalue, eval_rail_psn, eval_rail_val in *;
        cbn [rbv_psn rbv_bits].
      rewrite Hpsn_eq, Epc, orb_false_l, Hbp_eq, Ec0, Hbits_ev; exact Hmt3.
    + exists asg3, vf;
        split; [cbn; change (@Integers.repr 1 0) with (@Integers.zero 1);
                rewrite (@Integers.unsigned_zero 1); reflexivity
                | split; [lia | split; [exact Hag | split; [exact Hsat3 | split; [exact Hout_wf |]]]]].
      unfold rail_matches_dvalue, eval_rail_psn, eval_rail_val in *;
        cbn [rbv_psn rbv_bits].
      rewrite Hpsn_eq, Epc, orb_false_l, Hbp_eq, Ec0, Hbits_ev; exact Hmf3.
Qed.

Lemma blast_let_free_expr_sat :
  forall {Pa : Params} (e : cert_expr) (ctx : ub_ctx)
         (penv : param_env Pa) (foracle : freeze_oracle)
         (asg : positive -> bool) (env env' : blast_env) (out : rail_bv),
    blast_let_free_expr ctx e env = Some (out, env') ->
    wt_cert_expr [] e = true ->
    wf_param_env_for (collect_free_vars [] e) penv ->
    ub_ctx_holds penv foracle ctx ->
    sat_blast_env penv foracle asg env ->
    exists asg' vout,
      eval_closed_cert_expr penv foracle e = raise_ret vout /\
      (bs_next_var (be_st env) <= bs_next_var (be_st env'))%positive /\
      agree_below (bs_next_var (be_st env)) asg asg' /\
      sat_blast_env penv foracle asg' env' /\
      wf_rail_bound (cert_expr_bit_width e) (bs_next_var (be_st env')) out /\
      rail_matches_dvalue (cert_expr_bit_width e) asg' out vout.
Proof.
  intros Pa e; induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o _
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ ];
    intros ctx penv foracle asg env env' out Hbl Hwt Hpenv Hctx Henv.
  - (* CE_BvConst *)
    cbn [blast_let_free_expr cert_expr_bit_width] in Hbl |- *.
    inversion Hbl; subst out env'; clear Hbl.
    destruct Henv as (([Hge2 Hwfc] & Ha1 & Hevc) & Hvars & Hfrzs).
    assert (Hinit : eval_cnf asg (bs_cnf (init_blast_state 2%positive) ++ []) = true)
      by (cbn; rewrite Ha1; reflexivity).
    destruct (blast_const_rail_sound asg w val 2%positive [] Hinit)
      as (_ & Hpsn & Hval).
    assert (Hwf_out : wf_rail_bound w (bs_next_var (be_st env)) (blast_const_rail w val)).
    { split; [split; [reflexivity | unfold blast_const_rail; cbn; rewrite map_length, seq_length; reflexivity] | split].
      - unfold blast_const_rail, wf_lits_bound; cbn.
        apply Forall_forall; intros l Hin; apply in_map_iff in Hin as [k [<- _]].
        destruct (Z.testbit (Z.of_N val) (Z.of_nat k)); cbn; lia.
      - cbn; lia. }
    exists asg, (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N val)))).
    split; [reflexivity | split; [lia | split; [apply agree_below_refl |
    split; [exact (conj (conj (conj Hge2 Hwfc) (conj Ha1 Hevc)) (conj Hvars Hfrzs)) |
    split; [exact Hwf_out |
    unfold rail_matches_dvalue; rewrite Hpsn, Hval; reflexivity]]]]].
  - (* CE_Poison *)
    cbn [blast_let_free_expr cert_expr_bit_width] in Hbl |- *.
    inversion Hbl; subst out env'; clear Hbl.
    destruct Henv as (([Hge2 Hwfc] & Ha1 & Hevc) & Hvars & Hfrzs).
    assert (Hwf_out : wf_rail_bound w (bs_next_var (be_st env)) (blast_poison_rail w)).
    { split; [split; [reflexivity | unfold blast_poison_rail; cbn; apply repeat_length] | split].
      - unfold blast_poison_rail, wf_lits_bound; cbn.
        apply Forall_forall; intros l Hin; apply repeat_spec in Hin; subst l; cbn; lia.
      - cbn; lia. }
    exists asg, (DVALUE_Base DVALUE_Poison).
    split; [reflexivity | split; [lia | split; [apply agree_below_refl |
    split; [exact (conj (conj (conj Hge2 Hwfc) (conj Ha1 Hevc)) (conj Hvars Hfrzs)) |
    split; [exact Hwf_out |
    unfold rail_matches_dvalue, eval_rail_psn, blast_poison_rail; cbn; rewrite Ha1; reflexivity]]]]].
  - (* CE_Var *)
    cbn [blast_let_free_expr cert_expr_bit_width] in Hbl |- *.
    destruct (lookup_blast_var (be_vars env) nm w) as [r |] eqn:Elk.
    + inversion Hbl; subst out env'; clear Hbl.
      destruct Henv as (Hst & Hvars & Hfrzs).
      destruct (Hvars nm w r Elk) as (Hwf_r & dv & Hpm & Hwfdv & Hrm).
      exists asg, dv.
      split; [unfold eval_closed_cert_expr; cbn; rewrite Hpm; exact (check_scalar_width_ok w dv Hwfdv) |
      split; [lia | split; [apply agree_below_refl |
      split; [exact (conj Hst (conj Hvars Hfrzs)) | split; [exact Hwf_r | exact Hrm]]]]].
    + destruct (Hpenv nm w (or_introl eq_refl)) as [dv [Hpm Hwfdv]].
      assert (Hev_var : eval_closed_cert_expr penv foracle (CE_Var nm w) = raise_ret dv)
        by (unfold eval_closed_cert_expr; cbn; rewrite Hpm; exact (check_scalar_width_ok w dv Hwfdv)).
      destruct (alloc_fresh_bits (Pos.to_nat w) (be_st env)) as [bits st1] eqn:Hfb.
      destruct Henv as (Hst & Hvars & Hfrzs).
      destruct Hwfdv as [-> | [iv ->]].
      * assert (Enu : ctx_has_param_noundef ctx nm w = false).
        { destruct (ctx_has_param_noundef ctx nm w) eqn:E; [| reflexivity].
          exfalso; exact (ctx_has_param_noundef_sound penv foracle ctx nm w _ E Hctx Hpm eq_refl). }
        rewrite Enu in Hbl.
        destruct (alloc_var st1) as [psn st2] eqn:Hpv.
        inversion Hbl; subst out env'; clear Hbl; cbn [be_st].
        rewrite <- (repeat_length false (Pos.to_nat w)) in Hfb.
        destruct (alloc_fresh_bits_sat (List.repeat false (Pos.to_nat w)) asg (be_st env) bits st1 Hst Hfb)
          as (asg1 & Hle1 & Hag1 & Hsat1 & Hblen & Hbwf & _).
        rewrite repeat_length in Hblen.
        destruct (alloc_var_sat asg1 st1 true psn st2 Hsat1 Hpv)
          as (asg2 & Hle2 & Hag2 & Hsat2 & Hpwf & Hpev).
        assert (Hle : (bs_next_var (be_st env) <= bs_next_var st2)%positive) by lia.
        assert (Hag : agree_below (bs_next_var (be_st env)) asg asg2)
          by exact (agree_below_trans _ asg asg1 asg2 Hag1 (agree_below_le _ _ asg1 asg2 Hle1 Hag2)).
        assert (Hwf_r : wf_rail_bound w (bs_next_var st2) (mk_rail_bv w bits psn)).
        { split; [split; [reflexivity | exact Hblen] |
                  split; [exact (wf_lits_bound_mono _ _ bits Hle2 Hbwf) | exact Hpwf]]. }
        assert (Hrm_r : rail_matches_dvalue w asg2 (mk_rail_bv w bits psn) (DVALUE_Base DVALUE_Poison))
          by (unfold rail_matches_dvalue, eval_rail_psn; cbn; rewrite Hpev; reflexivity).
        pose proof (sat_blast_env_step penv foracle asg asg2 env st2
                      (conj Hst (conj Hvars Hfrzs)) Hle Hag Hsat2) as (_ & Hvars2 & Hfrzs2).
        exists asg2, (DVALUE_Base DVALUE_Poison).
        split; [exact Hev_var | split; [exact Hle | split; [exact Hag | split; [| split; [exact Hwf_r | exact Hrm_r]]]]].
        split; [exact Hsat2 | split; [| exact Hfrzs2]].
        intros nm' w' r' Hlk; cbn in Hlk.
        destruct (String.eqb nm nm' && Pos.eqb w w') eqn:Ehit.
        -- apply andb_true_iff in Ehit as [Hs Hp]; apply String.eqb_eq in Hs; apply Pos.eqb_eq in Hp.
           inversion Hlk; subst nm' w' r'; split; [exact Hwf_r |].
           exists (DVALUE_Base DVALUE_Poison); split; [exact Hpm | split; [left; reflexivity | exact Hrm_r]].
        -- exact (Hvars2 nm' w' r' Hlk).
      * rewrite <- (bit_int_to_bools_length w iv) in Hfb.
        destruct (alloc_fresh_bits_sat (bit_int_to_bools w iv) asg (be_st env) bits st1 Hst Hfb)
          as (asg1 & Hle1 & Hag1 & Hsat1 & Hblen & Hbwf & Hbmap).
        rewrite bit_int_to_bools_length in Hblen.
        assert (Hpsn_case :
          exists psn st2 asg2,
            (if ctx_has_param_noundef ctx nm w then (lit_false, st1) else alloc_var st1) = (psn, st2) /\
            (bs_next_var st1 <= bs_next_var st2)%positive /\
            agree_below (bs_next_var st1) asg1 asg2 /\
            sat_blast_st asg2 st2 /\
            wf_lit_bound (bs_next_var st2) psn /\
            eval_lit asg2 psn = false).
        { destruct (ctx_has_param_noundef ctx nm w).
          - exists lit_false, st1, asg1.
            split; [reflexivity | split; [lia | split; [apply agree_below_refl | split; [exact Hsat1 | split]]]].
            + cbn; pose proof (proj1 (proj1 Hsat1)); lia.
            + cbn; rewrite (proj1 (proj2 Hsat1)); reflexivity.
          - destruct (alloc_var st1) as [psn st2] eqn:Hpv.
            destruct (alloc_var_sat asg1 st1 false psn st2 Hsat1 Hpv)
              as (asg2 & Hle2 & Hag2 & Hsat2 & Hpwf & Hpev).
            exists psn, st2, asg2;
              split; [reflexivity | split; [exact Hle2 | split; [exact Hag2 |
              split; [exact Hsat2 | split; [exact Hpwf | exact Hpev]]]]]. }
        destruct Hpsn_case as (psn & st2 & asg2 & Hpsn_eq & Hle2 & Hag2 & Hsat2 & Hpwf & Hpev).
        rewrite Hpsn_eq in Hbl; inversion Hbl; subst out env'; clear Hbl; cbn [be_st].
        assert (Hle : (bs_next_var (be_st env) <= bs_next_var st2)%positive) by lia.
        assert (Hag : agree_below (bs_next_var (be_st env)) asg asg2)
          by exact (agree_below_trans _ asg asg1 asg2 Hag1 (agree_below_le _ _ asg1 asg2 Hle1 Hag2)).
        assert (Hwf_r : wf_rail_bound w (bs_next_var st2) (mk_rail_bv w bits psn)).
        { split; [split; [reflexivity | exact Hblen] |
                  split; [exact (wf_lits_bound_mono _ _ bits Hle2 Hbwf) | exact Hpwf]]. }
        assert (Hrm_r : rail_matches_dvalue w asg2 (mk_rail_bv w bits psn)
                          (DVALUE_Base (@DVALUE_I Pa w iv))).
        { unfold rail_matches_dvalue, eval_rail_psn, eval_rail_val; cbn [rbv_psn rbv_bits].
          rewrite Hpev, <- (eval_lits_agree (bs_next_var st1) asg1 asg2 bits Hag2 Hbwf),
                  Hbmap, bit_int_to_bools_repr; reflexivity. }
        pose proof (sat_blast_env_step penv foracle asg asg2 env st2
                      (conj Hst (conj Hvars Hfrzs)) Hle Hag Hsat2) as (_ & Hvars2 & Hfrzs2).
        exists asg2, (DVALUE_Base (@DVALUE_I Pa w iv)).
        split; [exact Hev_var | split; [exact Hle | split; [exact Hag | split; [| split; [exact Hwf_r | exact Hrm_r]]]]].
        split; [exact Hsat2 | split; [| exact Hfrzs2]].
        intros nm' w' r' Hlk; cbn in Hlk.
        destruct (String.eqb nm nm' && Pos.eqb w w') eqn:Ehit.
        -- apply andb_true_iff in Ehit as [Hs Hp]; apply String.eqb_eq in Hs; apply Pos.eqb_eq in Hp.
           inversion Hlk; subst nm' w' r'; split; [exact Hwf_r |].
           exists (DVALUE_Base (@DVALUE_I Pa w iv));
             split; [exact Hpm | split; [right; exists iv; reflexivity | exact Hrm_r]].
        -- exact (Hvars2 nm' w' r' Hlk).
  - (* CE_BinOp *)
    cbn [blast_let_free_expr wt_cert_expr collect_free_vars cert_expr_bit_width] in *.
    destruct (cert_binop_flags_eqb fl no_binop_flags) eqn:Efl; [| discriminate Hbl].
    apply cert_binop_flags_eqb_eq in Efl; subst fl.
    destruct (blast_binop_fn op) as [bf |] eqn:Ebf; [| discriminate Hbl].
    destruct (blast_let_free_expr ctx l env) as [[rl env1] |] eqn:Ebl_l; [| discriminate Hbl].
    destruct (blast_let_free_expr ctx r env1) as [[rr env2] |] eqn:Ebl_r; [| discriminate Hbl].
    destruct (bf w rl rr (be_st env2)) as [out0 st3] eqn:Ebf_run.
    inversion Hbl; subst out0 env'; clear Hbl; cbn [be_st].
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((((_ & Htl) & Htr) & Hwl) & Hwr).
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    assert (Hpl : wf_param_env_for (collect_free_vars [] l) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars [] r) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
    destruct (IHl ctx penv foracle asg env env1 rl Ebl_l Htl Hpl Hctx Henv)
      as (asg1 & vl & Evl & Hle1 & Hag1 & Henv1 & Hwfrl & Hmrl).
    destruct (IHr ctx penv foracle asg1 env1 env2 rr Ebl_r Htr Hpr Hctx Henv1)
      as (asg2 & vr & Evr & Hle2 & Hag2 & Henv2 & Hwfrr & Hmrr).
    rewrite Hwl in Hwfrl, Hmrl; rewrite Hwr in Hwfrr, Hmrr.
    pose proof (wf_rail_bound_mono w _ _ rl Hle2 Hwfrl) as Hwfrl2.
    pose proof (rail_matches_dvalue_agree w _ asg1 asg2 rl vl Hag2 Hwfrl Hmrl) as Hmrl2.
    destruct (blast_binop_fn_sat op bf w rl rr asg2 (be_st env2) out st3 vl vr
                Ebf (proj1 Henv2) Hwfrl2 Hwfrr Hmrl2 Hmrr Ebf_run)
      as (asg3 & vout & Evout & Hle3 & Hag3 & Hsat3 & Hwf_out & Hm_out).
    assert (Hle : (bs_next_var (be_st env) <= bs_next_var st3)%positive) by lia.
    assert (Hag : agree_below (bs_next_var (be_st env)) asg asg3).
    { apply (agree_below_trans _ asg asg1 asg3 Hag1).
      apply (agree_below_le _ _ asg1 asg3 Hle1).
      exact (agree_below_trans _ asg1 asg2 asg3 Hag2 (agree_below_le _ _ asg2 asg3 Hle2 Hag3)). }
    exists asg3, vout.
    split; [unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
            rewrite Evl, Evr; cbn [eou_bind]; exact Evout |
    split; [exact Hle | split; [exact Hag |
    split; [exact (sat_blast_env_step penv foracle asg2 asg3 env2 st3 Henv2 Hle3 Hag3 Hsat3) |
    split; [exact Hwf_out | exact Hm_out]]]]].
  - (* CE_ICmp *)
    destruct pr; try discriminate Hbl; destruct ss; try discriminate Hbl.
    cbn [blast_let_free_expr wt_cert_expr collect_free_vars cert_expr_bit_width] in *.
    destruct (blast_let_free_expr ctx l env) as [[rl env1] |] eqn:Ebl_l; [| discriminate Hbl].
    destruct (blast_let_free_expr ctx r env1) as [[rr env2] |] eqn:Ebl_r; [| discriminate Hbl].
    destruct (blast_eq_rail w rl rr (be_st env2)) as [out0 st3] eqn:Eeq_run.
    inversion Hbl; subst out0 env'; clear Hbl; cbn [be_st].
    rewrite !andb_true_iff in Hwt; destruct Hwt as (((Htl & Htr) & Hwl) & Hwr).
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    assert (Hpl : wf_param_env_for (collect_free_vars [] l) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars [] r) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
    destruct (IHl ctx penv foracle asg env env1 rl Ebl_l Htl Hpl Hctx Henv)
      as (asg1 & vl & Evl & Hle1 & Hag1 & Henv1 & Hwfrl & Hmrl).
    destruct (IHr ctx penv foracle asg1 env1 env2 rr Ebl_r Htr Hpr Hctx Henv1)
      as (asg2 & vr & Evr & Hle2 & Hag2 & Henv2 & Hwfrr & Hmrr).
    rewrite Hwl in Hwfrl, Hmrl; rewrite Hwr in Hwfrr, Hmrr.
    pose proof (wf_rail_bound_mono w _ _ rl Hle2 Hwfrl) as Hwfrl2.
    pose proof (rail_matches_dvalue_agree w _ asg1 asg2 rl vl Hag2 Hwfrl Hmrl) as Hmrl2.
    destruct (blast_eq_rail_sat w rl rr asg2 (be_st env2) out st3 vl vr
                (proj1 Henv2) Hwfrl2 Hwfrr Hmrl2 Hmrr Eeq_run)
      as (asg3 & vout & Evout & Hle3 & Hag3 & Hsat3 & Hwf_out & Hm_out).
    assert (Hle : (bs_next_var (be_st env) <= bs_next_var st3)%positive) by lia.
    assert (Hag : agree_below (bs_next_var (be_st env)) asg asg3).
    { apply (agree_below_trans _ asg asg1 asg3 Hag1).
      apply (agree_below_le _ _ asg1 asg3 Hle1).
      exact (agree_below_trans _ asg1 asg2 asg3 Hag2 (agree_below_le _ _ asg2 asg3 Hle2 Hag3)). }
    exists asg3, vout.
    split; [unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
            rewrite Evl, Evr; cbn [eou_bind]; exact Evout |
    split; [exact Hle | split; [exact Hag |
    split; [exact (sat_blast_env_step penv foracle asg2 asg3 env2 st3 Henv2 Hle3 Hag3 Hsat3) |
    split; [exact Hwf_out | exact Hm_out]]]]].
  - (* CE_Cast *)
    discriminate Hbl.
  - (* CE_Select *)
    cbn [blast_let_free_expr wt_cert_expr collect_free_vars cert_expr_bit_width] in *.
    destruct (blast_let_free_expr ctx c env) as [[rc env1] |] eqn:Ebl_c; [| discriminate Hbl].
    destruct (blast_let_free_expr ctx t env1) as [[rt env2] |] eqn:Ebl_t; [| discriminate Hbl].
    destruct (blast_let_free_expr ctx f env2) as [[rf env3] |] eqn:Ebl_f; [| discriminate Hbl].
    destruct (blast_select_rail w rc rt rf (be_st env3)) as [out0 st4] eqn:Esel_run.
    inversion Hbl; subst out0 env'; clear Hbl; cbn [be_st].
    rewrite !andb_true_iff in Hwt; destruct Hwt as (((((Htc & Htt) & Htf) & Hwc) & Hwt0) & Hwf0).
    apply Pos.eqb_eq in Hwc; apply Pos.eqb_eq in Hwt0; apply Pos.eqb_eq in Hwf0.
    assert (Hpc : wf_param_env_for (collect_free_vars [] c) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpt : wf_param_env_for (collect_free_vars [] t) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; left; exact Hx).
    assert (Hpf : wf_param_env_for (collect_free_vars [] f) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; right; exact Hx).
    destruct (IHc ctx penv foracle asg env env1 rc Ebl_c Htc Hpc Hctx Henv)
      as (asg1 & vc & Evc & Hle1 & Hag1 & Henv1 & Hwfrc & Hmrc).
    destruct (IHt ctx penv foracle asg1 env1 env2 rt Ebl_t Htt Hpt Hctx Henv1)
      as (asg2 & vt & Evt & Hle2 & Hag2 & Henv2 & Hwfrt & Hmrt).
    destruct (IHf ctx penv foracle asg2 env2 env3 rf Ebl_f Htf Hpf Hctx Henv2)
      as (asg3 & vf & Evf & Hle3 & Hag3 & Henv3 & Hwfrf & Hmrf).
    rewrite Hwc in Hwfrc, Hmrc; rewrite Hwt0 in Hwfrt, Hmrt; rewrite Hwf0 in Hwfrf, Hmrf.
    assert (Hle23 : (bs_next_var (be_st env1) <= bs_next_var (be_st env3))%positive) by lia.
    assert (Hag13 : agree_below (bs_next_var (be_st env1)) asg1 asg3)
      by exact (agree_below_trans _ asg1 asg2 asg3 Hag2 (agree_below_le _ _ asg2 asg3 Hle2 Hag3)).
    pose proof (wf_rail_bound_mono 1%positive _ _ rc Hle23 Hwfrc) as Hwfrc3.
    pose proof (rail_matches_dvalue_agree 1%positive _ asg1 asg3 rc vc Hag13 Hwfrc Hmrc) as Hmrc3.
    pose proof (wf_rail_bound_mono w _ _ rt Hle3 Hwfrt) as Hwfrt3.
    pose proof (rail_matches_dvalue_agree w _ asg2 asg3 rt vt Hag3 Hwfrt Hmrt) as Hmrt3.
    destruct (blast_select_rail_sat w rc rt rf asg3 (be_st env3) out st4 vc vt vf
                (proj1 Henv3) Hwfrc3 Hwfrt3 Hwfrf Hmrc3 Hmrt3 Hmrf Esel_run)
      as (asg4 & vout & Evout & Hle4 & Hag4 & Hsat4 & Hwf_out & Hm_out).
    assert (Hle : (bs_next_var (be_st env) <= bs_next_var st4)%positive) by lia.
    assert (Hag : agree_below (bs_next_var (be_st env)) asg asg4).
    { apply (agree_below_trans _ asg asg1 asg4 Hag1).
      apply (agree_below_le _ _ asg1 asg4 Hle1).
      exact (agree_below_trans _ asg1 asg3 asg4 Hag13 (agree_below_le _ _ asg3 asg4 Hle23 Hag4)). }
    exists asg4, vout.
    split; [unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
            rewrite Evc, Evt, Evf; cbn [eou_bind]; exact Evout |
    split; [exact Hle | split; [exact Hag |
    split; [exact (sat_blast_env_step penv foracle asg3 asg4 env3 st4 Henv3 Hle4 Hag4 Hsat4) |
    split; [exact Hwf_out | exact Hm_out]]]]].
  - (* CE_Freeze *)
    cbn [blast_let_free_expr wt_cert_expr collect_free_vars cert_expr_bit_width] in *.
    destruct (blast_let_free_expr ctx o env) as [[ro env1] |] eqn:Ebl_o; [| discriminate Hbl].
    apply andb_true_iff in Hwt as [Hto Hwo]; apply Pos.eqb_eq in Hwo.
    destruct (IHo ctx penv foracle asg env env1 ro Ebl_o Hto Hpenv Hctx Henv)
      as (asg1 & vo & Evo & Hle1 & Hag1 & Henv1 & Hwfro & Hmro).
    rewrite Hwo in Hwfro, Hmro.
    destruct Hwfro as ([Hwro Hlro] & Hbro & Hpro).
    set (key := expand_lets_with [] o) in *.
    set (fval := @Integers.repr w (foracle w key)).
    destruct (lookup_blast_freeze (be_freezes env1) w key) as [fbits |] eqn:Efrz.
    + destruct (mux_bits_list (rbv_psn ro) fbits (rbv_bits ro) (be_st env1))
        as [bits st2] eqn:Hmux.
      inversion Hbl; subst out env'; clear Hbl; cbn [be_st].
      destruct Henv1 as (Hst1 & Hvars1 & Hfrzs1).
      destruct (Hfrzs1 w key fbits Efrz) as (Hflen & Hfwf & Hfmap).
      assert (Hlen_fo : List.length fbits = List.length (rbv_bits ro)) by congruence.
      destruct (mux_bits_list_sat fbits (rbv_bits ro) (rbv_psn ro) asg1 (be_st env1) bits st2
                  Hlen_fo Hpro Hfwf Hbro Hst1 Hmux)
        as (asg2 & Hle2 & Hag2 & Hsat2 & Hblen & Hbwf).
      assert (Hs2 : eval_cnf asg2 (bs_cnf st2 ++ []) = true)
        by (rewrite app_nil_r; exact (proj2 (proj2 Hsat2))).
      destruct (mux_bits_list_sound asg2 (rbv_psn ro) fbits (rbv_bits ro) (be_st env1) bits st2 []
                  (wf_lit_bound_nonzero _ _ Hpro) Hlen_fo
                  (wf_lits_bound_nonzero _ _ Hfwf) (wf_lits_bound_nonzero _ _ Hbro) Hmux Hs2)
        as (_ & _ & Hbits_ev).
      assert (Hle : (bs_next_var (be_st env) <= bs_next_var st2)%positive) by lia.
      assert (Hag : agree_below (bs_next_var (be_st env)) asg asg2)
        by exact (agree_below_trans _ asg asg1 asg2 Hag1 (agree_below_le _ _ asg1 asg2 Hle1 Hag2)).
      assert (Hwf_out : wf_rail_bound w (bs_next_var st2) (mk_rail_bv w bits lit_false)).
      { split; [split; [reflexivity | cbn; congruence] |
                split; [exact Hbwf | cbn; pose proof (proj1 (proj1 Hsat2)); lia]]. }
      pose proof (rail_matches_dvalue_agree w _ asg1 asg2 ro vo Hag2
                    (conj (conj Hwro Hlro) (conj Hbro Hpro)) Hmro) as Hmro2.
      unfold rail_matches_dvalue in Hmro2.
      assert (Hlf2 : eval_lit asg2 lit_false = false)
        by (cbn; rewrite (proj1 (proj2 Hsat2)); reflexivity).
      destruct (eval_rail_psn asg2 ro) eqn:Epo; subst vo.
      * exists asg2, (DVALUE_Base (@DVALUE_I Pa w fval)).
        split; [unfold eval_closed_cert_expr in *; cbn [eval_cert_expr let_val_exprs];
                rewrite Evo; reflexivity |
        split; [exact Hle | split; [exact Hag |
        split; [exact (sat_blast_env_step penv foracle asg1 asg2 env1 st2
                         (conj Hst1 (conj Hvars1 Hfrzs1)) Hle2 Hag2 Hsat2) |
        split; [exact Hwf_out |]]]]].
        unfold rail_matches_dvalue, eval_rail_psn, eval_rail_val; cbn [rbv_psn rbv_bits].
        unfold eval_rail_psn in Epo.
        rewrite Hlf2, Hbits_ev, Epo, <- (eval_lits_agree _ asg1 asg2 fbits Hag2 Hfwf),
                Hfmap, bit_int_to_bools_repr; reflexivity.
      * exists asg2, (DVALUE_Base (@DVALUE_I Pa w (eval_rail_val w asg2 ro))).
        split; [unfold eval_closed_cert_expr in *; cbn [eval_cert_expr let_val_exprs];
                rewrite Evo; reflexivity |
        split; [exact Hle | split; [exact Hag |
        split; [exact (sat_blast_env_step penv foracle asg1 asg2 env1 st2
                         (conj Hst1 (conj Hvars1 Hfrzs1)) Hle2 Hag2 Hsat2) |
        split; [exact Hwf_out |]]]]].
        unfold rail_matches_dvalue, eval_rail_psn, eval_rail_val; cbn [rbv_psn rbv_bits].
        unfold eval_rail_psn in Epo.
        rewrite Hlf2, Hbits_ev, Epo; reflexivity.
    + destruct (alloc_fresh_bits (Pos.to_nat w) (be_st env1)) as [fbits st2] eqn:Hfb.
      destruct (mux_bits_list (rbv_psn ro) fbits (rbv_bits ro) st2) as [bits st3] eqn:Hmux.
      inversion Hbl; subst out env'; clear Hbl; cbn [be_st].
      destruct Henv1 as (Hst1 & Hvars1 & Hfrzs1).
      rewrite <- (bit_int_to_bools_length w fval) in Hfb.
      destruct (alloc_fresh_bits_sat (bit_int_to_bools w fval) asg1 (be_st env1) fbits st2 Hst1 Hfb)
        as (asg2 & Hle2 & Hag2 & Hsat2 & Hflen & Hfwf & Hfmap).
      rewrite bit_int_to_bools_length in Hflen.
      assert (Hlen_fo : List.length fbits = List.length (rbv_bits ro)) by congruence.
      destruct (mux_bits_list_sat fbits (rbv_bits ro) (rbv_psn ro) asg2 st2 bits st3
                  Hlen_fo (wf_lit_bound_mono _ _ _ Hle2 Hpro) Hfwf
                  (wf_lits_bound_mono _ _ _ Hle2 Hbro) Hsat2 Hmux)
        as (asg3 & Hle3 & Hag3 & Hsat3 & Hblen & Hbwf).
      assert (Hs3 : eval_cnf asg3 (bs_cnf st3 ++ []) = true)
        by (rewrite app_nil_r; exact (proj2 (proj2 Hsat3))).
      destruct (mux_bits_list_sound asg3 (rbv_psn ro) fbits (rbv_bits ro) st2 bits st3 []
                  (wf_lit_bound_nonzero _ _ Hpro) Hlen_fo
                  (wf_lits_bound_nonzero _ _ Hfwf) (wf_lits_bound_nonzero _ _ Hbro) Hmux Hs3)
        as (_ & _ & Hbits_ev).
      assert (Hle13 : (bs_next_var (be_st env1) <= bs_next_var st3)%positive) by lia.
      assert (Hag13 : agree_below (bs_next_var (be_st env1)) asg1 asg3)
        by exact (agree_below_trans _ asg1 asg2 asg3 Hag2 (agree_below_le _ _ asg2 asg3 Hle2 Hag3)).
      assert (Hle : (bs_next_var (be_st env) <= bs_next_var st3)%positive) by lia.
      assert (Hag : agree_below (bs_next_var (be_st env)) asg asg3)
        by exact (agree_below_trans _ asg asg1 asg3 Hag1 (agree_below_le _ _ asg1 asg3 Hle1 Hag13)).
      assert (Hwf_out : wf_rail_bound w (bs_next_var st3) (mk_rail_bv w bits lit_false)).
      { split; [split; [reflexivity | cbn; congruence] |
                split; [exact Hbwf | cbn; pose proof (proj1 (proj1 Hsat3)); lia]]. }
      assert (Hfmap3 : List.map (eval_lit asg3) fbits = bit_int_to_bools w fval)
        by (rewrite <- (eval_lits_agree (bs_next_var st2) asg2 asg3 fbits Hag3 Hfwf); exact Hfmap).
      pose proof (sat_blast_env_step penv foracle asg1 asg3 env1 st3
                    (conj Hst1 (conj Hvars1 Hfrzs1)) Hle13 Hag13 Hsat3) as (_ & Hvars3 & Hfrzs3).
      assert (Henv_new : sat_blast_env penv foracle asg3
                           (mk_blast_env st3 (be_vars env1) ((w, key, fbits) :: be_freezes env1))).
      { split; [exact Hsat3 | split; [exact Hvars3 |]].
        intros w' key' fbits' Hlk; cbn in Hlk.
        destruct (Pos.eqb w w' && cert_expr_eqb key key') eqn:Ehit.
        - apply andb_true_iff in Ehit as [Hw' Hk']; apply Pos.eqb_eq in Hw'; apply cert_expr_eqb_eq in Hk'.
          inversion Hlk; subst w' key' fbits'.
          split; [exact Hflen | split; [exact (wf_lits_bound_mono _ _ fbits Hle3 Hfwf) | exact Hfmap3]].
        - exact (Hfrzs3 w' key' fbits' Hlk). }
      pose proof (rail_matches_dvalue_agree w _ asg1 asg3 ro vo Hag13
                    (conj (conj Hwro Hlro) (conj Hbro Hpro)) Hmro) as Hmro3.
      unfold rail_matches_dvalue in Hmro3.
      assert (Hlf3 : eval_lit asg3 lit_false = false)
        by (cbn; rewrite (proj1 (proj2 Hsat3)); reflexivity).
      destruct (eval_rail_psn asg3 ro) eqn:Epo; subst vo.
      * exists asg3, (DVALUE_Base (@DVALUE_I Pa w fval)).
        split; [unfold eval_closed_cert_expr in *; cbn [eval_cert_expr let_val_exprs];
                rewrite Evo; reflexivity |
        split; [exact Hle | split; [exact Hag |
        split; [exact Henv_new | split; [exact Hwf_out |]]]]].
        unfold rail_matches_dvalue, eval_rail_psn, eval_rail_val; cbn [rbv_psn rbv_bits].
        unfold eval_rail_psn in Epo.
        rewrite Hlf3, Hbits_ev, Epo, Hfmap3, bit_int_to_bools_repr; reflexivity.
      * exists asg3, (DVALUE_Base (@DVALUE_I Pa w (eval_rail_val w asg3 ro))).
        split; [unfold eval_closed_cert_expr in *; cbn [eval_cert_expr let_val_exprs];
                rewrite Evo; reflexivity |
        split; [exact Hle | split; [exact Hag |
        split; [exact Henv_new | split; [exact Hwf_out |]]]]].
        unfold rail_matches_dvalue, eval_rail_psn, eval_rail_val; cbn [rbv_psn rbv_bits].
        unfold eval_rail_psn in Epo.
        rewrite Hlf3, Hbits_ev, Epo; reflexivity.
  - (* CE_Let *)
    discriminate Hbl.
Qed.

Lemma blast_refinement_cex_gates_sat :
  forall sz src_r tgt_r asg st,
    sat_blast_st asg st ->
    wf_rail_bound sz (bs_next_var st) src_r ->
    wf_rail_bound sz (bs_next_var st) tgt_r ->
    exists asg5,
      agree_below (bs_next_var st) asg asg5 /\
      sat_blast_st asg5 (snd (blast_refinement_cex_gates sz lit_true src_r tgt_r st)).
Proof.
  intros sz src_r tgt_r asg st Hsat
         ([Hws Hls] & Hbs & Hps) ([Hwt Hlt] & Hbt & Hpt).
  unfold blast_refinement_cex_gates.
  destruct (map2_emit emit_xor2 (rbv_bits src_r) (rbv_bits tgt_r) st) as [xor_bits st1] eqn:Hm.
  destruct (emit_or_list xor_bits st1) as [val_diff st2] eqn:Horl.
  destruct (emit_or2 (rbv_psn tgt_r) val_diff st2) as [bad_tgt st3] eqn:Hbad.
  destruct (emit_and2 (neg_lit (rbv_psn src_r)) bad_tgt st3) as [def_bad st4] eqn:Hdef.
  destruct (emit_and2 lit_true def_bad st4) as [cex_lit st5] eqn:Hcex.
  cbn [snd].
  assert (Hlen_st : List.length (rbv_bits src_r) = List.length (rbv_bits tgt_r)) by congruence.
  destruct (map2_emit_sat emit_xor2 emit_xor2_sat _ _ asg st xor_bits st1
              Hlen_st Hbs Hbt Hsat Hm)
    as (asg1 & Hle1 & Hag1 & Hsat1 & _ & Hxwf).
  destruct (emit_or_list_sat xor_bits asg1 st1 val_diff st2 Hxwf Hsat1 Horl)
    as (asg2 & Hle2 & Hag2 & Hsat2 & Hvd_wf).
  assert (Hle12 : (bs_next_var st <= bs_next_var st2)%positive) by lia.
  destruct (emit_or2_sat asg2 (rbv_psn tgt_r) val_diff st2 bad_tgt st3 Hsat2
              (wf_lit_bound_mono _ _ _ Hle12 Hpt) Hvd_wf Hbad)
    as (asg3 & Hle3 & Hag3 & Hsat3 & Hbt_wf).
  assert (Hle13 : (bs_next_var st <= bs_next_var st3)%positive) by lia.
  destruct (emit_and2_sat asg3 (neg_lit (rbv_psn src_r)) bad_tgt st3 def_bad st4 Hsat3
              (wf_lit_bound_neg _ _ (wf_lit_bound_mono _ _ _ Hle13 Hps)) Hbt_wf Hdef)
    as (asg4 & Hle4 & Hag4 & Hsat4 & Hdb_wf).
  assert (Hlt4 : wf_lit_bound (bs_next_var st4) lit_true)
    by (cbn; pose proof (proj1 (proj1 Hsat4)); lia).
  destruct (emit_and2_sat asg4 lit_true def_bad st4 cex_lit st5 Hsat4 Hlt4 Hdb_wf Hcex)
    as (asg5 & _ & Hag5 & Hsat5 & _).
  exists asg5; split; [| exact Hsat5].
  apply (agree_below_trans _ asg asg1 asg5 Hag1); apply (agree_below_le _ _ asg1 asg5 Hle1).
  apply (agree_below_trans _ asg1 asg2 asg5 Hag2); apply (agree_below_le _ _ asg2 asg5 Hle2).
  apply (agree_below_trans _ asg2 asg3 asg5 Hag3); apply (agree_below_le _ _ asg3 asg5 Hle3).
  exact (agree_below_trans _ asg3 asg4 asg5 Hag4 (agree_below_le _ _ asg4 asg5 Hle4 Hag5)).
Qed.

Definition check_expr_refines_with_lrat
  (ctx : ub_ctx) (src tgt : cert_expr) (opt_pf : option (list lrat_step)) : bool :=
  if check_expr_refines ctx src tgt then true
  else
    match opt_pf with
    | None => false
    | Some pf =>
        Pos.eqb (cert_expr_bit_width src) (cert_expr_bit_width tgt) &&
        wt_cert_expr [] src &&
        wt_cert_expr [] tgt &&
        wf_let_dag [] src &&
        wf_let_dag [] tgt &&
        let sz := cert_expr_bit_width src in
        let ns := normalize_cert_expr ctx (expand_lets src) in
        let nt := normalize_cert_expr ctx (expand_lets tgt) in
        let env0 := mk_blast_env (init_blast_state 2%positive) [] [] in
        match blast_let_free_expr ctx ns env0 with
        | Some (src_r, env1) =>
            match blast_let_free_expr ctx nt env1 with
            | Some (tgt_r, env2) =>
                check_lrat_unsat
                  (blast_refinement_cex sz lit_true src_r tgt_r (be_st env2))
                  pf
            | None => false
            end
        | None => false
        end
    end.

Theorem check_expr_refines_with_lrat_sound :
  forall {Pa : Params} (ctx : ub_ctx) (src tgt : cert_expr)
         (opt_pf : option (list lrat_step))
         (penv : param_env Pa) (foracle : freeze_oracle),
    check_expr_refines_with_lrat ctx src tgt opt_pf = true ->
    wf_param_env_for (collect_free_vars [] src) penv ->
    wf_param_env_for (collect_free_vars [] tgt) penv ->
    ub_ctx_holds penv foracle ctx ->
    refine_eou_dvalue
      (eval_closed_cert_expr penv foracle src)
      (eval_closed_cert_expr penv foracle tgt).
Proof.
  intros Pa ctx src tgt opt_pf penv foracle Hchk Hps Hpt Hctx.
  unfold check_expr_refines_with_lrat in Hchk.
  destruct (check_expr_refines ctx src tgt) eqn:Ealg;
    [exact (check_expr_refines_sound ctx src tgt penv foracle Ealg Hps Hpt Hctx) |].
  destruct opt_pf as [pf |]; [| discriminate Hchk].
  cbn zeta in Hchk; rewrite !andb_true_iff in Hchk.
  destruct Hchk as (((((Hbw & Hwts) & Hwtt) & Hdags) & Hdagt) & Hunsat_bl).
  apply Pos.eqb_eq in Hbw.
  set (sz := cert_expr_bit_width src) in *.
  set (ns := normalize_cert_expr ctx (expand_lets src)) in *.
  set (nt := normalize_cert_expr ctx (expand_lets tgt)) in *.
  set (env0 := mk_blast_env (init_blast_state 2%positive) [] []) in *.
  destruct (blast_let_free_expr ctx ns env0) as [[src_r env1] |] eqn:Ebs; [| discriminate Hunsat_bl].
  destruct (blast_let_free_expr ctx nt env1) as [[tgt_r env2] |] eqn:Ebt; [| discriminate Hunsat_bl].
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
  assert (Hp_ns : wf_param_env_for (collect_free_vars [] ns) penv)
    by (intros x wx Hx; exact (Hp_es x wx (Hinc_ns _ Hx))).
  assert (Hp_nt : wf_param_env_for (collect_free_vars [] nt) penv)
    by (intros x wx Hx; exact (Hp_et x wx (Hinc_nt _ Hx))).
  assert (Heq_src : equiv_eou_dvalue
                      (eval_closed_cert_expr penv foracle src)
                      (eval_closed_cert_expr penv foracle ns)).
  { apply (equiv_eou_dvalue_trans _ (eval_closed_cert_expr penv foracle (expand_lets src))).
    - exact (eval_expand_lets_equiv src penv foracle Hwts Hdags Hps).
    - exact (normalize_cert_expr_eval ctx (expand_lets src) penv foracle Hwt_es Hlf_es Hp_es Hctx). }
  assert (Heq_tgt : equiv_eou_dvalue
                      (eval_closed_cert_expr penv foracle tgt)
                      (eval_closed_cert_expr penv foracle nt)).
  { apply (equiv_eou_dvalue_trans _ (eval_closed_cert_expr penv foracle (expand_lets tgt))).
    - exact (eval_expand_lets_equiv tgt penv foracle Hwtt Hdagt Hpt).
    - exact (normalize_cert_expr_eval ctx (expand_lets tgt) penv foracle Hwt_et Hlf_et Hp_et Hctx). }
  apply (refine_eou_compat _ _ _ _ Heq_src Heq_tgt).
  assert (Henv0 : sat_blast_env penv foracle (fun _ => true) env0).
  { split; [exact init_blast_state_sat | split; intros; discriminate]. }
  destruct (blast_let_free_expr_sat ns ctx penv foracle (fun _ => true) env0 env1 src_r
              Ebs Hwt_ns Hp_ns Hctx Henv0)
    as (asg1 & vs & Evs & _ & _ & Henv1 & Hwfs & Hms).
  destruct (blast_let_free_expr_sat nt ctx penv foracle asg1 env1 env2 tgt_r
              Ebt Hwt_nt Hp_nt Hctx Henv1)
    as (asg2 & vt & Evt & Hle12 & Hag12 & Henv2 & Hwft & Hmt).
  assert (Hbw_ns : cert_expr_bit_width ns = sz) by (unfold ns, sz; congruence).
  assert (Hbw_nt : cert_expr_bit_width nt = sz) by (unfold nt, sz; congruence).
  rewrite Hbw_ns in Hwfs, Hms; rewrite Hbw_nt in Hwft, Hmt.
  pose proof (wf_rail_bound_mono sz _ _ src_r Hle12 Hwfs) as Hwfs2.
  pose proof (rail_matches_dvalue_agree sz _ asg1 asg2 src_r vs Hag12 Hwfs Hms) as Hms2.
  destruct (blast_refinement_cex_gates_sat sz src_r tgt_r asg2 (be_st env2)
              (proj1 Henv2) Hwfs2 Hwft)
    as (asg5 & Hag25 & Hsat5).
  pose proof (rail_matches_dvalue_agree sz _ asg2 asg5 src_r vs Hag25 Hwfs2 Hms2) as Hms5.
  pose proof (rail_matches_dvalue_agree sz _ asg2 asg5 tgt_r vt Hag25 Hwft Hmt) as Hmt5.
  rewrite Evs, Evt; cbn [refine_eou_dvalue].
  unfold rail_matches_dvalue in Hms5, Hmt5.
  destruct (eval_rail_psn asg5 src_r) eqn:Eps.
  - subst vs; apply dvalue_refines_poison_l.
  - assert (Hlt_nz : lit_true <> 0%Z) by discriminate.
    assert (Hlf5 : eval_lit asg5 lit_false = false)
      by (cbn; rewrite (proj1 (proj2 Hsat5)); reflexivity).
    assert (Hlt5 : eval_lit asg5 lit_true = true)
      by exact (proj1 (proj2 Hsat5)).
    destruct (blast_refinement_cex_unsat_sound sz lit_true src_r tgt_r (be_st env2) pf asg5
                Hlt_nz (wf_rail_bound_lits sz _ src_r Hwfs2) (wf_rail_bound_lits sz _ tgt_r Hwft)
                Hunsat_bl Hlf5 (proj2 (proj2 Hsat5)) Hlt5 Eps)
      as [Ept Heqv].
    rewrite Ept, Heqv in Hmt5; subst vs vt; apply dvalue_refines_refl.
Qed.
