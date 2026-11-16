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
  Numeric.Zbits
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

#[local] Arguments Pos.ltb _ _ : simpl nomatch.
#[local] Arguments Pos.leb _ _ : simpl nomatch.
#[local] Arguments N.ltb _ _ : simpl nomatch.
#[local] Arguments N.leb _ _ : simpl nomatch.
#[local] Arguments Z.ltb _ _ : simpl nomatch.
#[local] Arguments Z.leb _ _ : simpl nomatch.
#[local] Arguments Z.gtb _ _ : simpl nomatch.
#[local] Arguments Z.geb _ _ : simpl nomatch.

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

Definition default_let_expand_budget : nat := 8192%nat.
Definition norm_let_expand_budget : nat := 4096%nat.

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
    { revert ms fuel ms' f1 Ebs; induction IHbs as [| [bnm be] rest Hbe _ IHrest];
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
  - cbn [ub_free_expr]; rewrite !andb_true_iff in Hub |- *.
    destruct Hub as ([Hop Hl] & Hr).
    split; [split; [exact Hop | exact (IHl m Hm Hl)] | exact (IHr m Hm Hr)].
  - cbn [ub_free_expr]; rewrite !andb_true_iff in Hub |- *.
    destruct Hub as [Hl Hr]; split; [exact (IHl m Hm Hl) | exact (IHr m Hm Hr)].
  - cbn [ub_free_expr]; exact (IHo m Hm Hub).
  - cbn [ub_free_expr]; rewrite !andb_true_iff in Hub |- *.
    destruct Hub as ([Hc Ht] & Hf).
    split; [split; [exact (IHc m Hm Hc) | exact (IHt m Hm Ht)] | exact (IHf m Hm Hf)].
  - cbn [ub_free_expr]; exact (IHo m Hm Hub).
  - apply andb_true_iff in Hub as [Hbs Hbody].
    assert (Hstep :
      forall xs cur_m,
        (forall k ce, In (k, ce) cur_m -> ub_free_expr ce = true) ->
        ub_free_let_binds ub_free_expr xs = true ->
        forall k ce, In (k, ce) (expand_let_binds expand_lets_with cur_m xs) ->
                     ub_free_expr ce = true).
    { induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_m Hcm Hxs; cbn in Hxs |- *.
      - exact Hcm.
      - apply andb_true_iff in Hxs as [Hbe Hrx].
        pose proof (IHbe cur_m Hcm Hbe) as Hub_exp.
        apply IHrx; [| exact Hrx].
        intros k ce [Heq | Hin]; [inversion Heq; subst; exact Hub_exp | exact (Hcm k ce Hin)]. }
    exact (IHb (expand_let_binds expand_lets_with m bs) (Hstep bs m Hm Hbs) Hbody).
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
  - rewrite !andb_true_iff in Hub |- *.
    destruct Hub as ([_ Hl] & Hr); split; [exact (IHl m Hm Hl) | exact (IHr m Hm Hr)].
  - rewrite !andb_true_iff in Hub |- *.
    destruct Hub as [Hl Hr]; split; [exact (IHl m Hm Hl) | exact (IHr m Hm Hr)].
  - exact (IHo m Hm Hub).
  - rewrite !andb_true_iff in Hub |- *.
    destruct Hub as ([Hc Ht] & Hf).
    split; [split; [exact (IHc m Hm Hc) | exact (IHt m Hm Ht)] | exact (IHf m Hm Hf)].
  - exact (IHo m Hm Hub).
  - apply andb_true_iff in Hub as [Hbs Hbody].
    assert (Hstep :
      forall exp_body xs cur_m,
        (forall k ce, In (k, ce) cur_m -> ub_free_expr ce = true) ->
        ub_free_let_binds ub_free_expr xs = true ->
        wf_let_dag_binds wf_let_dag exp_body cur_m xs = true /\
        (forall k ce, In (k, ce) (expand_let_binds expand_lets_with cur_m xs) ->
                      ub_free_expr ce = true)).
    { intros exp_body; induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_m Hcm Hxs; cbn in Hxs |- *.
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
                    bs m Hm Hbs) as [Hwf_bs Hm'].
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
      forall xs cur_ms f_in f_out,
        wf_let_dag_binds_fueled wf_let_dag_fueled_with exp_b cur_ms xs f_in = Some f_out ->
        wf_let_dag_binds wf_let_dag exp_b (strip_let_sizes cur_ms) xs = true).
    { induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_ms f_in f_out H; cbn in H |- *.
      - reflexivity.
      - destruct (wf_let_dag_fueled_with cur_ms be f_in) as [fa |] eqn:Ebe1; [| discriminate H].
        destruct (expand_lets_fueled_with cur_ms be fa) as [[[exp_be bsz] fb] |] eqn:Ebe2;
          [| discriminate H].
        destruct (ub_free_expr exp_be || is_syntactic_subexpr exp_be exp_b) eqn:Esub;
          [| discriminate H].
        pose proof (expand_lets_fueled_with_eq be cur_ms fa exp_be bsz fb Ebe2) as Hebe.
        subst exp_be.
        rewrite (IHbe _ _ _ Ebe1), Esub,
                (IHrx ((bnm, (expand_lets_with (strip_let_sizes cur_ms) be, bsz)) :: cur_ms) _ _ H).
        reflexivity. }
    rewrite (Hstep bs ms f2 f3 Ewbs), <- Hms', (IHb ms' f3 fuel' Hwf); reflexivity.
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
  exact (expand_lets_fueled_eq default_let_expand_budget d e Ef).
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
  destruct ua as [| | p align | | | | | |]; cbn in H; try exact (IH H).
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
  { apply Zmod_unique with (q := ((Z.of_N align / p2) * (@Integers.unsigned w iv / Z.of_N align))%Z);
      [lia |].
    rewrite Hdu, Hda; ring. }
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
  - cbn [expr_guaranteed_defined] in Hdef.
    apply orb_true_iff in Hdef as [Htop | Hdef];
      [exact (ub_free_branch_cond_defined_sound ctx _ penv foracle Htop Hwt Hpenv Hctx) |].
    cbn [wt_cert_expr collect_free_vars cert_expr_bit_width] in *.
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
  apply Pos.eqb_eq in Ew; inversion H; subst; exists v; split; reflexivity.
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
  intros op0 w [| | | op' w' fl' a0 c | | | | |] a ic H; cbn in H; try discriminate H.
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

Definition norm_binop_step
  (ctx : ub_ctx) (op : cert_binop) (w : positive) (fl : cert_binop_flags)
  (nl nr : cert_expr) : cert_expr :=
  match try_fold_const_binop op w fl nl nr with
  | Some c => c
  | None =>
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
      end
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
  assert (Hsub_l : forall op0 a v,
    nl = CE_BinOp op0 w no_binop_flags a (CE_BvConst w v) ->
    cert_expr_bit_width a = w /\
    wt_cert_expr [] a = true /\
    is_let_free_expr a = true /\
    incl (collect_free_vars [] a) (collect_free_vars [] nl ++ collect_free_vars [] nr)).
  { intros op0 a v Heq; subst nl.
    cbn in Htl, Hfl_l; rewrite !andb_true_iff in Htl, Hfl_l.
    destruct Htl as ((((_ & Hta) & _) & Hwa) & _); destruct Hfl_l as [Hlfa _].
    apply Pos.eqb_eq in Hwa.
    repeat split; [exact Hwa | exact Hta | exact Hlfa |
                   cbn; rewrite app_nil_r; apply incl_appl, incl_refl]. }
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
  - destruct op.
    + (* CB_Add *)
      destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
      destruct (is_zero_const_expr w nr); [exact Hl_out |].
      destruct (is_zero_const_expr w nl); [exact Hr_out |].
      destruct ((1 <? w)%positive && cert_expr_eqb nl nr);
        [exact (norm_binop_rhs_const_out CB_Shl w no_binop_flags nl 1%N nl nr
                  eq_refl Hwl Htl Hfl_l (incl_appl _ (incl_refl _))) |].
      destruct (extract_neg_expr w nr) as [y |] eqn:Eneg.
      * pose proof (extract_neg_expr_inv w nr y Eneg) as Heqy; subst nr.
        cbn in Htr, Hfl_r; rewrite !andb_true_iff in Htr, Hfl_r.
        destruct Htr as ((((_ & _) & Hty) & _) & Hwy); apply Pos.eqb_eq in Hwy.
        cbn; rewrite Htl, Hty, Hwl, Hwy, !Pos.eqb_refl, Hfl_l, Hfl_r;
          repeat split; apply incl_refl.
      * destruct (extract_const_expr w nr) as [ic2 |].
        -- destruct (extract_binop_rhs_const CB_Add w nl) as [[a ic1] |] eqn:Erc; [| exact Hdef_out].
           destruct (extract_binop_rhs_const_inv CB_Add w nl a ic1 Erc) as [v1 [Heql _]].
           destruct (Hsub_l CB_Add a v1 Heql) as (Hwa & Hta & Hlfa & Hinca).
           cbn zeta; destruct (@Integers.unsigned w _ =? 0)%Z;
             [repeat split; assumption |
              unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Add w no_binop_flags a _ nl nr
                                           eq_refl Hwa Hta Hlfa Hinca)].
        -- destruct (extract_const_expr w nl) as [ic1 |]; [| exact Hdef_out].
           unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Add w no_binop_flags nr _ nl nr
                                        eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))).
    + (* CB_Sub *)
      destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
      destruct (is_zero_const_expr w nr); [exact Hl_out |].
      destruct (cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl); [apply Hc_out |].
      destruct (is_zero_const_expr w nl).
      * destruct (extract_neg_expr w nr) as [a |] eqn:Eneg; [| exact Hdef_out].
        pose proof (extract_neg_expr_inv w nr a Eneg) as Heqa; subst nr.
        cbn in Htr, Hfl_r; rewrite !andb_true_iff in Htr, Hfl_r.
        destruct Htr as ((((_ & _) & Hta) & _) & Hwa); apply Pos.eqb_eq in Hwa.
        repeat split; [exact Hwa | exact Hta | exact Hfl_r |
                       cbn; apply incl_appr, incl_refl].
      * destruct (extract_const_expr w nr) as [ic |]; [| exact Hdef_out].
        unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Add w no_binop_flags nl _ nl nr
                                     eq_refl Hwl Htl Hfl_l (incl_appl _ (incl_refl _))).
    + (* CB_Mul *)
      destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
      destruct (is_one_const_expr w nr); [exact Hl_out |].
      destruct (is_one_const_expr w nl); [exact Hr_out |].
      destruct (is_zero_const_expr w nr && expr_guaranteed_defined ctx nl); [apply Hc_out |].
      destruct (is_zero_const_expr w nl && expr_guaranteed_defined ctx nr); [apply Hc_out |].
      destruct (is_all_ones_const_expr w nr);
        [exact (norm_binop_lhs_const_out CB_Sub w no_binop_flags 0%N nl nl nr
                  eq_refl Hwl Htl Hfl_l (incl_appl _ (incl_refl _))) |].
      destruct (is_all_ones_const_expr w nl);
        [exact (norm_binop_lhs_const_out CB_Sub w no_binop_flags 0%N nr nl nr
                  eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))) |].
      destruct (extract_const_expr w nr) as [ic |].
      * destruct (@Integers.is_power2 w ic) as [logn |]; [| exact Hdef_out].
        unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Shl w no_binop_flags nl _ nl nr
                                     eq_refl Hwl Htl Hfl_l (incl_appl _ (incl_refl _))).
      * destruct (extract_const_expr w nl) as [ic |]; [| exact Hdef_out].
        destruct (@Integers.is_power2 w ic) as [logn |]; unfold mk_bv_const;
          [exact (norm_binop_rhs_const_out CB_Shl w no_binop_flags nr _ nl nr
                    eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))) |
           exact (norm_binop_rhs_const_out CB_Mul w no_binop_flags nr _ nl nr
                    eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _)))].
    + (* CB_UDiv *)
      destruct (negb (cbf_nuw fl) && negb (cbf_nsw fl) && negb (cbf_disjoint fl)) eqn:Efl_ok;
        [| exact Hdef_out].
      destruct (extract_const_expr w nr) as [ic |]; [| exact Hdef_out].
      destruct (@Integers.is_power2 w ic) as [logn |]; [| exact Hdef_out].
      destruct (@Integers.unsigned w logn =? 0)%Z; [exact Hl_out |].
      unfold mk_bv_const.
      exact (norm_binop_rhs_const_out CB_LShr w fl nl _ nl nr
               Efl_ok Hwl Htl Hfl_l (incl_appl _ (incl_refl _))).
    + (* CB_SDiv *)
      destruct (cert_binop_flags_eqb fl no_binop_flags); exact Hdef_out.
    + (* CB_URem *)
      destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
      destruct (extract_const_expr w nr) as [ic |]; [| exact Hdef_out].
      destruct (@Integers.is_power2 w ic); [| exact Hdef_out].
      unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_And w no_binop_flags nl _ nl nr
                                   eq_refl Hwl Htl Hfl_l (incl_appl _ (incl_refl _))).
    + (* CB_SRem *)
      destruct (cert_binop_flags_eqb fl no_binop_flags); exact Hdef_out.
    + (* CB_Shl *)
      destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
      destruct (is_zero_const_expr w nr); [exact Hl_out |].
      destruct (extract_const_expr w nr) as [ic2 |]; [| exact Hdef_out].
      destruct (extract_binop_rhs_const CB_Shl w nl) as [[a ic1] |] eqn:Erc; [| exact Hdef_out].
      destruct (extract_binop_rhs_const_inv CB_Shl w nl a ic1 Erc) as [v1 [Heql _]].
      destruct (Hsub_l CB_Shl a v1 Heql) as (Hwa & Hta & Hlfa & Hinca).
      destruct (_ <? Z.pos w)%Z; [| exact Hdef_out].
      unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Shl w no_binop_flags a _ nl nr
                                   eq_refl Hwa Hta Hlfa Hinca).
    + (* CB_LShr *)
      destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
      destruct (is_zero_const_expr w nr); [exact Hl_out |].
      destruct (extract_const_expr w nr) as [ic2 |]; [| exact Hdef_out].
      destruct (extract_binop_rhs_const CB_LShr w nl) as [[a ic1] |] eqn:Erc; [| exact Hdef_out].
      destruct (extract_binop_rhs_const_inv CB_LShr w nl a ic1 Erc) as [v1 [Heql _]].
      destruct (Hsub_l CB_LShr a v1 Heql) as (Hwa & Hta & Hlfa & Hinca).
      destruct (_ <? Z.pos w)%Z; [| exact Hdef_out].
      unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_LShr w no_binop_flags a _ nl nr
                                   eq_refl Hwa Hta Hlfa Hinca).
    + (* CB_AShr *)
      destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
      destruct (is_zero_const_expr w nr); [exact Hl_out |].
      destruct (extract_const_expr w nr) as [ic2 |]; [| exact Hdef_out].
      destruct (extract_binop_rhs_const CB_AShr w nl) as [[a ic1] |] eqn:Erc; [| exact Hdef_out].
      destruct (extract_binop_rhs_const_inv CB_AShr w nl a ic1 Erc) as [v1 [Heql _]].
      destruct (Hsub_l CB_AShr a v1 Heql) as (Hwa & Hta & Hlfa & Hinca).
      destruct (_ <? Z.pos w)%Z; [| exact Hdef_out].
      unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_AShr w no_binop_flags a _ nl nr
                                   eq_refl Hwa Hta Hlfa Hinca).
    + (* CB_And *)
      destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
      destruct (is_all_ones_const_expr w nr); [exact Hl_out |].
      destruct (is_all_ones_const_expr w nl); [exact Hr_out |].
      destruct (cert_expr_eqb nl nr); [exact Hl_out |].
      destruct (is_zero_const_expr w nr && expr_guaranteed_defined ctx nl); [apply Hc_out |].
      destruct (is_zero_const_expr w nl && expr_guaranteed_defined ctx nr); [apply Hc_out |].
      destruct (extract_not_expr w nl) as [a |] eqn:Enl,
               (extract_not_expr w nr) as [b |] eqn:Enr.
      * destruct (Hsub_l CB_Xor a (all_ones_N w) (extract_not_expr_inv w nl a Enl))
          as (Hwa & Hta & Hlfa & _).
        pose proof (extract_not_expr_inv w nr b Enr) as Heqr; subst nl nr.
        cbn in Htr, Hfl_r; rewrite !andb_true_iff in Htr, Hfl_r.
        destruct Htr as ((((_ & Htb) & _) & Hwb) & _); destruct Hfl_r as [Hlfb _].
        apply Pos.eqb_eq in Hwb.
        cbn; rewrite Hta, Htb, Hwa, Hwb, !Pos.eqb_refl, Hlfa, Hlfb, !app_nil_r.
        repeat split; apply incl_refl.
      * destruct (extract_const_expr w nr) as [ic2 |].
        -- destruct (extract_binop_rhs_const CB_And w nl) as [[a0 ic1] |] eqn:Erc; [| exact Hdef_out].
           destruct (extract_binop_rhs_const_inv CB_And w nl a0 ic1 Erc) as [v1 [Heql _]].
           destruct (Hsub_l CB_And a0 v1 Heql) as (Hwa & Hta & Hlfa & Hinca).
           unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_And w no_binop_flags a0 _ nl nr
                                        eq_refl Hwa Hta Hlfa Hinca).
        -- destruct (extract_const_expr w nl) as [ic1 |]; [| exact Hdef_out].
           unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_And w no_binop_flags nr _ nl nr
                                        eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))).
      * destruct (extract_const_expr w nr) as [ic2 |].
        -- destruct (extract_binop_rhs_const CB_And w nl) as [[a0 ic1] |] eqn:Erc; [| exact Hdef_out].
           destruct (extract_binop_rhs_const_inv CB_And w nl a0 ic1 Erc) as [v1 [Heql _]].
           destruct (Hsub_l CB_And a0 v1 Heql) as (Hwa & Hta & Hlfa & Hinca).
           unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_And w no_binop_flags a0 _ nl nr
                                        eq_refl Hwa Hta Hlfa Hinca).
        -- destruct (extract_const_expr w nl) as [ic1 |]; [| exact Hdef_out].
           unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_And w no_binop_flags nr _ nl nr
                                        eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))).
      * destruct (extract_const_expr w nr) as [ic2 |].
        -- destruct (extract_binop_rhs_const CB_And w nl) as [[a0 ic1] |] eqn:Erc; [| exact Hdef_out].
           destruct (extract_binop_rhs_const_inv CB_And w nl a0 ic1 Erc) as [v1 [Heql _]].
           destruct (Hsub_l CB_And a0 v1 Heql) as (Hwa & Hta & Hlfa & Hinca).
           unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_And w no_binop_flags a0 _ nl nr
                                        eq_refl Hwa Hta Hlfa Hinca).
        -- destruct (extract_const_expr w nl) as [ic1 |]; [| exact Hdef_out].
           unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_And w no_binop_flags nr _ nl nr
                                        eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))).
    + (* CB_Or *)
      destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
      destruct (is_zero_const_expr w nr); [exact Hl_out |].
      destruct (is_zero_const_expr w nl); [exact Hr_out |].
      destruct (cert_expr_eqb nl nr); [exact Hl_out |].
      destruct (is_all_ones_const_expr w nr && expr_guaranteed_defined ctx nl); [apply Hc_out |].
      destruct (is_all_ones_const_expr w nl && expr_guaranteed_defined ctx nr); [apply Hc_out |].
      destruct (extract_not_expr w nl) as [a |] eqn:Enl,
               (extract_not_expr w nr) as [b |] eqn:Enr.
      * destruct (Hsub_l CB_Xor a (all_ones_N w) (extract_not_expr_inv w nl a Enl))
          as (Hwa & Hta & Hlfa & _).
        pose proof (extract_not_expr_inv w nr b Enr) as Heqr; subst nl nr.
        cbn in Htr, Hfl_r; rewrite !andb_true_iff in Htr, Hfl_r.
        destruct Htr as ((((_ & Htb) & _) & Hwb) & _); destruct Hfl_r as [Hlfb _].
        apply Pos.eqb_eq in Hwb.
        cbn; rewrite Hta, Htb, Hwa, Hwb, !Pos.eqb_refl, Hlfa, Hlfb, !app_nil_r.
        repeat split; apply incl_refl.
      * destruct (extract_const_expr w nr) as [ic2 |].
        -- destruct (extract_binop_rhs_const CB_Or w nl) as [[a0 ic1] |] eqn:Erc; [| exact Hdef_out].
           destruct (extract_binop_rhs_const_inv CB_Or w nl a0 ic1 Erc) as [v1 [Heql _]].
           destruct (Hsub_l CB_Or a0 v1 Heql) as (Hwa & Hta & Hlfa & Hinca).
           unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Or w no_binop_flags a0 _ nl nr
                                        eq_refl Hwa Hta Hlfa Hinca).
        -- destruct (extract_const_expr w nl) as [ic1 |]; [| exact Hdef_out].
           unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Or w no_binop_flags nr _ nl nr
                                        eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))).
      * destruct (extract_const_expr w nr) as [ic2 |].
        -- destruct (extract_binop_rhs_const CB_Or w nl) as [[a0 ic1] |] eqn:Erc; [| exact Hdef_out].
           destruct (extract_binop_rhs_const_inv CB_Or w nl a0 ic1 Erc) as [v1 [Heql _]].
           destruct (Hsub_l CB_Or a0 v1 Heql) as (Hwa & Hta & Hlfa & Hinca).
           unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Or w no_binop_flags a0 _ nl nr
                                        eq_refl Hwa Hta Hlfa Hinca).
        -- destruct (extract_const_expr w nl) as [ic1 |]; [| exact Hdef_out].
           unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Or w no_binop_flags nr _ nl nr
                                        eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))).
      * destruct (extract_const_expr w nr) as [ic2 |].
        -- destruct (extract_binop_rhs_const CB_Or w nl) as [[a0 ic1] |] eqn:Erc; [| exact Hdef_out].
           destruct (extract_binop_rhs_const_inv CB_Or w nl a0 ic1 Erc) as [v1 [Heql _]].
           destruct (Hsub_l CB_Or a0 v1 Heql) as (Hwa & Hta & Hlfa & Hinca).
           unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Or w no_binop_flags a0 _ nl nr
                                        eq_refl Hwa Hta Hlfa Hinca).
        -- destruct (extract_const_expr w nl) as [ic1 |]; [| exact Hdef_out].
           unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Or w no_binop_flags nr _ nl nr
                                        eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))).
    + (* CB_Xor *)
      destruct (cert_binop_flags_eqb fl no_binop_flags); [| exact Hdef_out].
      destruct (is_zero_const_expr w nr); [exact Hl_out |].
      destruct (is_zero_const_expr w nl); [exact Hr_out |].
      destruct (cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl); [apply Hc_out |].
      destruct (extract_const_expr w nr) as [ic2 |].
      * destruct (extract_binop_rhs_const CB_Xor w nl) as [[a ic1] |] eqn:Erc; [| exact Hdef_out].
        destruct (extract_binop_rhs_const_inv CB_Xor w nl a ic1 Erc) as [v1 [Heql _]].
        destruct (Hsub_l CB_Xor a v1 Heql) as (Hwa & Hta & Hlfa & Hinca).
        cbn zeta; destruct (@Integers.unsigned w _ =? 0)%Z;
          [repeat split; assumption |
           unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Xor w no_binop_flags a _ nl nr
                                        eq_refl Hwa Hta Hlfa Hinca)].
      * destruct (extract_const_expr w nl) as [ic1 |]; [| exact Hdef_out].
        unfold mk_bv_const; exact (norm_binop_rhs_const_out CB_Xor w no_binop_flags nr _ nl nr
                                     eq_refl Hwr Htr Hfl_r (incl_appr _ (incl_refl _))).
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
  assert (Hcomm_l : forall v1,
    cert_binop_flags_eqb fl no_binop_flags = true ->
    nl = CE_BvConst w v1 ->
    is_commutative_binop op = true ->
    is_div_or_rem_op op = false ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle (CE_BinOp op w fl nl nr))
      (eval_closed_cert_expr penv foracle
         (CE_BinOp op w no_binop_flags nr (mk_bv_const w (@Integers.repr w (Z.of_N v1)))))).
  { intros v1 Hfl0 -> Hcomm Hndiv.
    apply cert_binop_flags_eqb_eq in Hfl0; subst fl.
    unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
    rewrite repr_of_N_to_N_unsigned.
    destruct Htot_r as [[msgr ->] | [vr [-> Hwfvr]]]; cbn [eou_bind]; [exact I |].
    rewrite (eval_iop_commut op no_binop_flags w _ vr Hcomm
               (or_intror (ex_intro _ _ eq_refl)) Hwfvr).
    apply equiv_eou_dvalue_refl. }
  assert (Hreassoc : forall a v1 v2 (iop : @Integers.bit_int w -> @Integers.bit_int w -> @Integers.bit_int w),
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
            (mk_bv_const w (iop (@Integers.repr w (Z.of_N v1)) (@Integers.repr w (Z.of_N v2))))))).
  { intros a v1 v2 iop Hfl0 -> -> Hndiv Hiop Hassoc.
    apply cert_binop_flags_eqb_eq in Hfl0; subst fl.
    cbn in Htl, Hpl; rewrite !andb_true_iff in Htl; destruct Htl as ((((_ & Hta) & _) & Hwa) & _).
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
      rewrite !Hp1; cbn; reflexivity.
    - unfold eval_iop; rewrite !eval_iop_integer_base_same_width, !Hiop; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width, Hiop, Hassoc; cbn; reflexivity. }
  unfold norm_binop_step.
  destruct (try_fold_const_binop op w fl nl nr) as [c |] eqn:Etc.
  - exact (proj2 (proj2 (proj2 (proj2 (try_fold_const_binop_sound op w fl nl nr c penv foracle Etc))))).
  - destruct op.
    + (* CB_Add *)
      destruct (cert_binop_flags_eqb fl no_binop_flags) eqn:Efl; [| apply equiv_eou_dvalue_refl].
      destruct (is_zero_const_expr w nr) eqn:Ezr.
      * apply (Hid_r 0%N Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.add_zero; reflexivity.
      * destruct (is_zero_const_expr w nl) eqn:Ezl.
        -- apply (Hid_l 0%N Efl (is_zero_const_expr_inv w nl Ezl)); [| reflexivity].
           intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
           rewrite Integers.add_zero_l; reflexivity.
        -- destruct ((1 <? w)%positive && cert_expr_eqb nl nr) eqn:Edbl.
           ++ apply andb_true_iff in Edbl as [Hw1 Eeq].
              apply cert_expr_eqb_eq in Eeq; apply cert_binop_flags_eqb_eq in Efl; subst nr fl.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
              destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]]; cbn [eou_bind];
                [exact I | reflexivity |].
              unfold eval_iop; rewrite !eval_iop_integer_base_same_width, repr_one_N.
              unfold cert_to_ibinop, eval_int_op; cbn.
              rewrite (@Integers.unsigned_one w).
              assert (Hge : (1 >=? Z.pos w)%Z = false)
                by (apply Pos.ltb_lt in Hw1; apply Z.geb_leb; apply Z.leb_gt; lia).
              rewrite Hge, (alg_add_self_shl1 w il Hw1); cbn; reflexivity.
           ++ destruct (extract_neg_expr w nr) as [y |] eqn:Eneg.
              ** pose proof (extract_neg_expr_inv w nr y Eneg) as Heqr; subst nr.
                 apply cert_binop_flags_eqb_eq in Efl; subst fl.
                 cbn in Htr, Hpr; rewrite !andb_true_iff in Htr.
                 destruct Htr as ((((_ & _) & Hty) & _) & Hwy); apply Pos.eqb_eq in Hwy.
                 unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
                 destruct Htot_l as [[msgl ->] | [vl [-> Hwfvl]]]; cbn [eou_bind]; [exact I |].
                 destruct (eval_cert_expr_totality y [] penv [] foracle Hty wf_let_val_env_nil Hpr)
                   as [[msgy ->] | [vy [-> Hwfvy]]]; cbn [eou_bind]; [exact I |].
                 rewrite Hwy in Hwfvy.
                 destruct Hwfvl as [-> | [il ->]], Hwfvy as [-> | [iy ->]]; cbn;
                   try reflexivity.
                 unfold eval_iop; rewrite !eval_iop_integer_base_same_width, repr_zero_N; cbn.
                 rewrite Integers.sub_zero_r, <- Integers.sub_add_opp; reflexivity.
              ** destruct (extract_const_expr w nr) as [ic2 |] eqn:Ec2.
                 --- destruct (extract_binop_rhs_const CB_Add w nl) as [[a ic1] |] eqn:Erc;
                       [| apply equiv_eou_dvalue_refl].
                     destruct (extract_const_expr_inv w nr ic2 Ec2) as [v2 [Heqr ->]].
                     destruct (extract_binop_rhs_const_inv CB_Add w nl a ic1 Erc) as [v1 [Heql ->]].
                     pose proof (Hreassoc a v1 v2 (@Integers.add w) Efl Heql Heqr eq_refl
                                   (fun x y => eq_refl)
                                   (@Integers.add_assoc w)) as Hra.
                     cbn zeta; destruct (@Integers.unsigned w _ =? 0)%Z eqn:Esum0; [| exact Hra].
                     apply (equiv_eou_dvalue_trans _ _ _ Hra).
                     apply Z.eqb_eq in Esum0.
                     assert (Hs_zero : @Integers.add w (@Integers.repr w (Z.of_N v1))
                                                       (@Integers.repr w (Z.of_N v2)) =
                                       @Integers.zero w)
                       by (rewrite <- (@Integers.repr_unsigned w (_)), Esum0; reflexivity).
                     subst nl; cbn in Htl, Hpl; rewrite !andb_true_iff in Htl.
                     destruct Htl as ((((_ & Hta) & _) & Hwa) & _); apply Pos.eqb_eq in Hwa.
                     rewrite app_nil_r in Hpl.
                     unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
                     rewrite Hs_zero, Integers.unsigned_zero, repr_zero_N.
                     destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpl)
                       as [[msga ->] | [va [-> Hwfva]]]; cbn [eou_bind]; [exact I |].
                     rewrite Hwa in Hwfva; destruct Hwfva as [-> | [ia ->]]; cbn; [reflexivity |].
                     unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn.
                     rewrite Integers.add_zero; reflexivity.
                 --- destruct (extract_const_expr w nl) as [ic1 |] eqn:Ec1;
                       [| apply equiv_eou_dvalue_refl].
                     destruct (extract_const_expr_inv w nl ic1 Ec1) as [v1 [Heql ->]].
                     exact (Hcomm_l v1 Efl Heql eq_refl eq_refl).
    + (* CB_Sub *)
      destruct (cert_binop_flags_eqb fl no_binop_flags) eqn:Efl; [| apply equiv_eou_dvalue_refl].
      destruct (is_zero_const_expr w nr) eqn:Ezr.
      * apply (Hid_r 0%N Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.sub_zero_l; reflexivity.
      * destruct (cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl) eqn:Eself.
        -- apply andb_true_iff in Eself as [Eeq Edef].
           apply cert_expr_eqb_eq in Eeq; apply cert_binop_flags_eqb_eq in Efl; subst nr fl.
           destruct (expr_guaranteed_defined_sound ctx nl penv foracle Edef Htl Hpl Hctx)
             as [_ [il Hil]].
           revert il Hil; rewrite Hwl; intros il Hil.
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
           rewrite Integers.sub_idem; reflexivity.
        -- destruct (is_zero_const_expr w nl) eqn:Ezl.
           ++ destruct (extract_neg_expr w nr) as [a |] eqn:Eneg; [| apply equiv_eou_dvalue_refl].
              rewrite (is_zero_const_expr_inv w nl Ezl).
              pose proof (extract_neg_expr_inv w nr a Eneg) as Heqr; subst nr.
              apply cert_binop_flags_eqb_eq in Efl; subst fl.
              cbn in Htr, Hpr; rewrite !andb_true_iff in Htr.
              destruct Htr as ((((_ & _) & Hta) & _) & Hwa); apply Pos.eqb_eq in Hwa.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
              destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpr)
                as [[msga ->] | [va [-> Hwfva]]]; cbn [eou_bind]; [exact I |].
              rewrite Hwa in Hwfva; destruct Hwfva as [-> | [ia ->]]; cbn; [reflexivity |].
              unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn [eou_bind].
              unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn.
              rewrite !Integers.sub_zero_r, Integers.neg_involutive; reflexivity.
           ++ destruct (extract_const_expr w nr) as [ic |] eqn:Ec; [| apply equiv_eou_dvalue_refl].
              destruct (extract_const_expr_inv w nr ic Ec) as [v [-> ->]].
              apply cert_binop_flags_eqb_eq in Efl; subst fl.
              unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
              rewrite repr_of_N_to_N_unsigned.
              destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]]; cbn [eou_bind];
                [exact I | reflexivity |].
              unfold eval_iop; rewrite !eval_iop_integer_base_same_width; cbn.
              rewrite Integers.sub_add_opp; reflexivity.
    + (* CB_Mul *)
      destruct (cert_binop_flags_eqb fl no_binop_flags) eqn:Efl; [| apply equiv_eou_dvalue_refl].
      destruct (is_one_const_expr w nr) eqn:E1r.
      * apply (Hid_r 1%N Efl (is_one_const_expr_inv w nr E1r)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_one_N; cbn.
        destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_one; reflexivity.
      * destruct (is_one_const_expr w nl) eqn:E1l.
        -- apply (Hid_l 1%N Efl (is_one_const_expr_inv w nl E1l)); [| reflexivity].
           intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_one_N; cbn.
           destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_commut, Integers.mul_one; reflexivity.
        -- destruct (is_zero_const_expr w nr && expr_guaranteed_defined ctx nl) eqn:Ezr.
           ++ apply andb_true_iff in Ezr as [Ez0 Edef].
              rewrite (is_zero_const_expr_inv w nr Ez0).
              apply cert_binop_flags_eqb_eq in Efl; subst fl.
              destruct (expr_guaranteed_defined_sound ctx nl penv foracle Edef Htl Hpl Hctx)
                as [_ [il Hil]].
              revert il Hil; rewrite Hwl; intros il Hil.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil; cbn [eou_bind].
              unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
              destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_zero; reflexivity.
           ++ destruct (is_zero_const_expr w nl && expr_guaranteed_defined ctx nr) eqn:Ezl.
              ** apply andb_true_iff in Ezl as [Ez0 Edef].
                 rewrite (is_zero_const_expr_inv w nl Ez0).
                 apply cert_binop_flags_eqb_eq in Efl; subst fl.
                 destruct (expr_guaranteed_defined_sound ctx nr penv foracle Edef Htr Hpr Hctx)
                   as [_ [ir Hir]].
                 revert ir Hir; rewrite Hwr; intros ir Hir.
                 unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hir; cbn [eou_bind].
                 unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
                 destruct (Pos.eqb w 1); cbn; rewrite Integers.mul_commut, Integers.mul_zero; reflexivity.
              ** destruct (is_all_ones_const_expr w nr) eqn:Emr.
                 --- rewrite (is_all_ones_const_expr_inv w nr Emr).
                     apply cert_binop_flags_eqb_eq in Efl; subst fl.
                     unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
                     destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]]; cbn [eou_bind];
                       [exact I | reflexivity |].
                     unfold eval_iop; rewrite !eval_iop_integer_base_same_width,
                                              repr_all_ones_N, repr_zero_N; cbn.
                     destruct (Pos.eqb w 1); cbn;
                       rewrite Integers.mul_mone, Integers.sub_zero_r; reflexivity.
                 --- destruct (is_all_ones_const_expr w nl) eqn:Eml.
                     +++ rewrite (is_all_ones_const_expr_inv w nl Eml).
                         apply cert_binop_flags_eqb_eq in Efl; subst fl.
                         unfold eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
                         destruct Htot_r as [[msgr ->] | [vr [-> [-> | [ir ->]]]]]; cbn [eou_bind];
                           [exact I | reflexivity |].
                         unfold eval_iop; rewrite !eval_iop_integer_base_same_width,
                                                  repr_all_ones_N, repr_zero_N; cbn.
                         destruct (Pos.eqb w 1); cbn;
                           rewrite Integers.mul_commut, Integers.mul_mone, Integers.sub_zero_r; reflexivity.
                     +++ destruct (extract_const_expr w nr) as [ic |] eqn:Ecr.
                         *** destruct (@Integers.is_power2 w ic) as [logn |] eqn:Ep2;
                               [| apply equiv_eou_dvalue_refl].
                             destruct (extract_const_expr_inv w nr ic Ecr) as [v [-> ->]].
                             apply cert_binop_flags_eqb_eq in Efl; subst fl.
                             pose proof (@Integers.is_power2_rng w _ logn Ep2) as Hrng.
                             unfold Integers.zwordsize in Hrng.
                             assert (Hge : (@Integers.unsigned w logn >=? Z.pos w)%Z = false)
                               by (apply Z.geb_leb; apply Z.leb_gt; lia).
                             unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
                             rewrite repr_of_N_to_N_unsigned.
                             destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]]; cbn [eou_bind];
                               [exact I | reflexivity |].
                             unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
                             unfold cert_to_ibinop, eval_int_op; cbn.
                             rewrite Hge, (@Integers.mul_pow2 w il _ logn Ep2).
                             destruct (Pos.eqb w 1); reflexivity.
                         *** destruct (extract_const_expr w nl) as [ic |] eqn:Ecl;
                               [| apply equiv_eou_dvalue_refl].
                             destruct (extract_const_expr_inv w nl ic Ecl) as [v [Heql ->]].
                             destruct (@Integers.is_power2 w (@Integers.repr w (Z.of_N v)))
                               as [logn |] eqn:Ep2;
                               [| exact (Hcomm_l v Efl Heql eq_refl eq_refl)].
                             subst nl; apply cert_binop_flags_eqb_eq in Efl; subst fl.
                             pose proof (@Integers.is_power2_rng w _ logn Ep2) as Hrng.
                             unfold Integers.zwordsize in Hrng.
                             assert (Hge : (@Integers.unsigned w logn >=? Z.pos w)%Z = false)
                               by (apply Z.geb_leb; apply Z.leb_gt; lia).
                             unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr eou_bind].
                             rewrite repr_of_N_to_N_unsigned.
                             destruct Htot_r as [[msgr ->] | [vr [-> [-> | [ir ->]]]]]; cbn [eou_bind];
                               [exact I | reflexivity |].
                             unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
                             unfold cert_to_ibinop, eval_int_op; cbn.
                             rewrite Hge, Integers.mul_commut, (@Integers.mul_pow2 w ir _ logn Ep2).
                             destruct (Pos.eqb w 1); reflexivity.
    + (* CB_UDiv *)
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
        by (apply Z.geb_leb; apply Z.leb_gt; lia).
      destruct (@Integers.unsigned w logn =? 0)%Z eqn:Eln0.
      * apply Z.eqb_eq in Eln0.
        assert (Hic1 : @Integers.unsigned w ic = 1%Z) by (rewrite Hpow, Eln0; reflexivity).
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]]; cbn [eou_bind];
          [exact I | reflexivity |].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width.
        unfold cert_to_ibinop, eval_int_op; cbn; fold ic.
        rewrite Hnz_ic, Hic1, Z.mod_1_r, Z.eqb_refl; cbn; rewrite andb_false_r.
        assert (Hic_one : ic = @Integers.one w)
          by (rewrite <- (@Integers.repr_unsigned w ic), Hic1; reflexivity).
        rewrite Hic_one, (@Integers.divu_one w il); reflexivity.
      * unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
        rewrite repr_of_N_to_N_unsigned.
        destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]]; cbn [eou_bind];
          [exact I | reflexivity |].
        unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
        unfold cert_to_ibinop, eval_int_op; cbn; fold ic.
        rewrite Hnz_ic, Hge_ln, Hpow, (@Integers.divu_pow2 w il ic logn Ep2).
        destruct (cbf_exact fl && _); reflexivity.
    + (* CB_SDiv *)
      destruct (cert_binop_flags_eqb fl no_binop_flags); apply equiv_eou_dvalue_refl.
    + (* CB_URem *)
      destruct (cert_binop_flags_eqb fl no_binop_flags) eqn:Efl; [| apply equiv_eou_dvalue_refl].
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
      destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]]; cbn [eou_bind];
        [exact I | reflexivity |].
      unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
      unfold cert_to_ibinop, eval_int_op; cbn; fold ic.
      rewrite Hnz_ic, (@Integers.modu_and w il ic logn Ep2); reflexivity.
    + (* CB_SRem *)
      destruct (cert_binop_flags_eqb fl no_binop_flags); apply equiv_eou_dvalue_refl.
    + (* CB_Shl *)
      destruct (cert_binop_flags_eqb fl no_binop_flags) eqn:Efl; [| apply equiv_eou_dvalue_refl].
      destruct (is_zero_const_expr w nr) eqn:Ezr.
      * apply (Hid_r 0%N Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
        unfold cert_to_ibinop, eval_int_op; cbn.
        rewrite Integers.unsigned_zero; cbn; rewrite alg_shl_zero; reflexivity.
      * destruct (extract_const_expr w nr) as [ic2 |] eqn:Ec2; [| apply equiv_eou_dvalue_refl].
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
          by (apply Z.geb_leb; apply Z.leb_gt; lia).
        assert (Hg2 : (@Integers.unsigned w c2 >=? Z.pos w)%Z = false)
          by (apply Z.geb_leb; apply Z.leb_gt; lia).
        assert (Hg12 : (@Integers.unsigned w (@Integers.add w c1 c2) >=? Z.pos w)%Z = false)
          by (rewrite Hu_add; apply Z.geb_leb; apply Z.leb_gt; lia).
        cbn in Htl, Hpl; rewrite !andb_true_iff in Htl;
          destruct Htl as ((((_ & Hta) & _) & Hwa) & _); apply Pos.eqb_eq in Hwa; rewrite app_nil_r in Hpl.
        unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
        rewrite repr_of_N_to_N_unsigned.
        destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpl)
          as [[msga ->] | [va [-> Hwfva]]]; cbn [eou_bind]; [exact I |].
        rewrite Hwa in Hwfva; destruct Hwfva as [-> | [ia ->]]; cbn; [reflexivity |].
        unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
        unfold cert_to_ibinop, eval_int_op; cbn; fold c1 c2.
        rewrite Hg1; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
        unfold eval_int_op; cbn; rewrite Hg2, Hg12.
        rewrite (@Integers.shl_shl w ia c1 c2);
          [reflexivity | apply alg_ltu_iwordsize_iff; lia |
           apply alg_ltu_iwordsize_iff; lia | apply alg_ltu_iwordsize_iff; lia].
    + (* CB_LShr *)
      destruct (cert_binop_flags_eqb fl no_binop_flags) eqn:Efl; [| apply equiv_eou_dvalue_refl].
      destruct (is_zero_const_expr w nr) eqn:Ezr.
      * apply (Hid_r 0%N Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
        unfold cert_to_ibinop, eval_int_op; cbn.
        rewrite Integers.unsigned_zero; cbn; rewrite alg_shru_zero; reflexivity.
      * destruct (extract_const_expr w nr) as [ic2 |] eqn:Ec2; [| apply equiv_eou_dvalue_refl].
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
          by (apply Z.geb_leb; apply Z.leb_gt; lia).
        assert (Hg2 : (@Integers.unsigned w c2 >=? Z.pos w)%Z = false)
          by (apply Z.geb_leb; apply Z.leb_gt; lia).
        assert (Hg12 : (@Integers.unsigned w (@Integers.add w c1 c2) >=? Z.pos w)%Z = false)
          by (rewrite Hu_add; apply Z.geb_leb; apply Z.leb_gt; lia).
        cbn in Htl, Hpl; rewrite !andb_true_iff in Htl;
          destruct Htl as ((((_ & Hta) & _) & Hwa) & _); apply Pos.eqb_eq in Hwa; rewrite app_nil_r in Hpl.
        unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
        rewrite repr_of_N_to_N_unsigned.
        destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpl)
          as [[msga ->] | [va [-> Hwfva]]]; cbn [eou_bind]; [exact I |].
        rewrite Hwa in Hwfva; destruct Hwfva as [-> | [ia ->]]; cbn; [reflexivity |].
        unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
        unfold cert_to_ibinop, eval_int_op; cbn; fold c1 c2.
        rewrite Hg1; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
        unfold eval_int_op; cbn; rewrite Hg2, Hg12.
        rewrite (@Integers.shru_shru w ia c1 c2);
          [reflexivity | apply alg_ltu_iwordsize_iff; lia |
           apply alg_ltu_iwordsize_iff; lia | apply alg_ltu_iwordsize_iff; lia].
    + (* CB_AShr *)
      destruct (cert_binop_flags_eqb fl no_binop_flags) eqn:Efl; [| apply equiv_eou_dvalue_refl].
      destruct (is_zero_const_expr w nr) eqn:Ezr.
      * apply (Hid_r 0%N Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N.
        unfold cert_to_ibinop, eval_int_op; cbn.
        rewrite Integers.unsigned_zero; cbn; rewrite alg_shr_zero; reflexivity.
      * destruct (extract_const_expr w nr) as [ic2 |] eqn:Ec2; [| apply equiv_eou_dvalue_refl].
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
          by (apply Z.geb_leb; apply Z.leb_gt; lia).
        assert (Hg2 : (@Integers.unsigned w c2 >=? Z.pos w)%Z = false)
          by (apply Z.geb_leb; apply Z.leb_gt; lia).
        assert (Hg12 : (@Integers.unsigned w (@Integers.add w c1 c2) >=? Z.pos w)%Z = false)
          by (rewrite Hu_add; apply Z.geb_leb; apply Z.leb_gt; lia).
        cbn in Htl, Hpl; rewrite !andb_true_iff in Htl;
          destruct Htl as ((((_ & Hta) & _) & Hwa) & _); apply Pos.eqb_eq in Hwa; rewrite app_nil_r in Hpl.
        unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
        rewrite repr_of_N_to_N_unsigned.
        destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpl)
          as [[msga ->] | [va [-> Hwfva]]]; cbn [eou_bind]; [exact I |].
        rewrite Hwa in Hwfva; destruct Hwfva as [-> | [ia ->]]; cbn; [reflexivity |].
        unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
        unfold cert_to_ibinop, eval_int_op; cbn; fold c1 c2.
        rewrite Hg1; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
        unfold eval_int_op; cbn; rewrite Hg2, Hg12.
        rewrite (@Integers.shr_shr w ia c1 c2);
          [reflexivity | apply alg_ltu_iwordsize_iff; lia |
           apply alg_ltu_iwordsize_iff; lia | apply alg_ltu_iwordsize_iff; lia].
    + (* CB_And *)
      destruct (cert_binop_flags_eqb fl no_binop_flags) eqn:Efl; [| apply equiv_eou_dvalue_refl].
      destruct (is_all_ones_const_expr w nr) eqn:Emr.
      * apply (Hid_r (all_ones_N w) Efl (is_all_ones_const_expr_inv w nr Emr)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
        rewrite Integers.and_mone; reflexivity.
      * destruct (is_all_ones_const_expr w nl) eqn:Eml.
        -- apply (Hid_l (all_ones_N w) Efl (is_all_ones_const_expr_inv w nl Eml)); [| reflexivity].
           intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
           rewrite Integers.and_mone_l; reflexivity.
        -- destruct (cert_expr_eqb nl nr) eqn:Eidem.
           ++ apply cert_expr_eqb_eq in Eidem; apply cert_binop_flags_eqb_eq in Efl; subst nr fl.
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
                 unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
                 rewrite Integers.and_zero; reflexivity.
              ** destruct (is_zero_const_expr w nl && expr_guaranteed_defined ctx nr) eqn:Ezl.
                 --- apply andb_true_iff in Ezl as [Ez0 Edef].
                     rewrite (is_zero_const_expr_inv w nl Ez0).
                     apply cert_binop_flags_eqb_eq in Efl; subst fl.
                     destruct (expr_guaranteed_defined_sound ctx nr penv foracle Edef Htr Hpr Hctx)
                       as [_ [ir Hir]].
                     revert ir Hir; rewrite Hwr; intros ir Hir.
                     unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hir; cbn [eou_bind].
                     unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
                     rewrite Integers.and_zero_l; reflexivity.
                 --- assert (Hrest_and :
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
                         exact (Hreassoc a v1 v2 (@Integers.and w) Efl Heql Heqr eq_refl
                                  (fun x y => eq_refl)
                                  (@Integers.and_assoc w)).
                       - destruct (extract_const_expr w nl) as [ic1 |] eqn:Ec1;
                           [| apply equiv_eou_dvalue_refl].
                         destruct (extract_const_expr_inv w nl ic1 Ec1) as [v1 [Heql ->]].
                         exact (Hcomm_l v1 Efl Heql eq_refl eq_refl). }
                     destruct (extract_not_expr w nl) as [a |] eqn:Enl,
                              (extract_not_expr w nr) as [b |] eqn:Enr;
                       try exact Hrest_and.
                     pose proof (extract_not_expr_inv w nl a Enl) as Heql;
                       pose proof (extract_not_expr_inv w nr b Enr) as Heqr.
                     apply cert_binop_flags_eqb_eq in Efl; subst nl nr fl.
                     cbn in Htl, Htr, Hpl, Hpr; rewrite !andb_true_iff in Htl, Htr;
                       rewrite !app_nil_r in Hpl, Hpr.
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
                       cbn in Hvxa |- *; try (inversion Hvxa; subst vxa; cbn; reflexivity).
                     unfold eval_iop in Hvxa |- *;
                       rewrite !eval_iop_integer_base_same_width, repr_all_ones_N in Hvxa |- *;
                       inversion Hvxa; subst vxa; clear Hvxa; cbn [eou_bind].
                     unfold eval_iop; rewrite !eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
                     change (@Integers.xor w ia (@Integers.mone w)) with (@Integers.not w ia).
                     change (@Integers.xor w ib (@Integers.mone w)) with (@Integers.not w ib).
                     change (@Integers.xor w (@Integers.or w ia ib) (@Integers.mone w))
                       with (@Integers.not w (@Integers.or w ia ib)).
                     rewrite Integers.not_or_and_not; reflexivity.
    + (* CB_Or *)
      destruct (cert_binop_flags_eqb fl no_binop_flags) eqn:Efl; [| apply equiv_eou_dvalue_refl].
      destruct (is_zero_const_expr w nr) eqn:Ezr.
      * apply (Hid_r 0%N Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.or_zero; reflexivity.
      * destruct (is_zero_const_expr w nl) eqn:Ezl.
        -- apply (Hid_l 0%N Efl (is_zero_const_expr_inv w nl Ezl)); [| reflexivity].
           intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
           rewrite Integers.or_zero_l; reflexivity.
        -- destruct (cert_expr_eqb nl nr) eqn:Eidem.
           ++ apply cert_expr_eqb_eq in Eidem; apply cert_binop_flags_eqb_eq in Efl; subst nr fl.
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
                 unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
                 rewrite Integers.or_mone; reflexivity.
              ** destruct (is_all_ones_const_expr w nl && expr_guaranteed_defined ctx nr) eqn:Eml.
                 --- apply andb_true_iff in Eml as [Em0 Edef].
                     rewrite (is_all_ones_const_expr_inv w nl Em0).
                     apply cert_binop_flags_eqb_eq in Efl; subst fl.
                     destruct (expr_guaranteed_defined_sound ctx nr penv foracle Edef Htr Hpr Hctx)
                       as [_ [ir Hir]].
                     revert ir Hir; rewrite Hwr; intros ir Hir.
                     unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hir; cbn [eou_bind].
                     unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
                     rewrite Integers.or_commut, Integers.or_mone; reflexivity.
                 --- assert (Hrest_or :
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
                         exact (Hreassoc a v1 v2 (@Integers.or w) Efl Heql Heqr eq_refl
                                  (fun x y => eq_refl)
                                  (@Integers.or_assoc w)).
                       - destruct (extract_const_expr w nl) as [ic1 |] eqn:Ec1;
                           [| apply equiv_eou_dvalue_refl].
                         destruct (extract_const_expr_inv w nl ic1 Ec1) as [v1 [Heql ->]].
                         exact (Hcomm_l v1 Efl Heql eq_refl eq_refl). }
                     destruct (extract_not_expr w nl) as [a |] eqn:Enl,
                              (extract_not_expr w nr) as [b |] eqn:Enr;
                       try exact Hrest_or.
                     pose proof (extract_not_expr_inv w nl a Enl) as Heql;
                       pose proof (extract_not_expr_inv w nr b Enr) as Heqr.
                     apply cert_binop_flags_eqb_eq in Efl; subst nl nr fl.
                     cbn in Htl, Htr, Hpl, Hpr; rewrite !andb_true_iff in Htl, Htr;
                       rewrite !app_nil_r in Hpl, Hpr.
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
                       cbn in Hvxa |- *; try (inversion Hvxa; subst vxa; cbn; reflexivity).
                     unfold eval_iop in Hvxa |- *;
                       rewrite !eval_iop_integer_base_same_width, repr_all_ones_N in Hvxa |- *;
                       inversion Hvxa; subst vxa; clear Hvxa; cbn [eou_bind].
                     unfold eval_iop; rewrite !eval_iop_integer_base_same_width, repr_all_ones_N; cbn.
                     change (@Integers.xor w ia (@Integers.mone w)) with (@Integers.not w ia).
                     change (@Integers.xor w ib (@Integers.mone w)) with (@Integers.not w ib).
                     change (@Integers.xor w (@Integers.and w ia ib) (@Integers.mone w))
                       with (@Integers.not w (@Integers.and w ia ib)).
                     rewrite Integers.not_and_or_not; reflexivity.
    + (* CB_Xor *)
      destruct (cert_binop_flags_eqb fl no_binop_flags) eqn:Efl; [| apply equiv_eou_dvalue_refl].
      destruct (is_zero_const_expr w nr) eqn:Ezr.
      * apply (Hid_r 0%N Efl (is_zero_const_expr_inv w nr Ezr)); [| reflexivity].
        intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
        rewrite Integers.xor_zero; reflexivity.
      * destruct (is_zero_const_expr w nl) eqn:Ezl.
        -- apply (Hid_l 0%N Efl (is_zero_const_expr_inv w nl Ezl)); [| reflexivity].
           intros i; unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
           rewrite Integers.xor_zero_l; reflexivity.
        -- destruct (cert_expr_eqb nl nr && expr_guaranteed_defined ctx nl) eqn:Eself.
           ++ apply andb_true_iff in Eself as [Eeq Edef].
              apply cert_expr_eqb_eq in Eeq; apply cert_binop_flags_eqb_eq in Efl; subst nr fl.
              destruct (expr_guaranteed_defined_sound ctx nl penv foracle Edef Htl Hpl Hctx)
                as [_ [il Hil]].
              revert il Hil; rewrite Hwl; intros il Hil.
              unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hil; cbn [eou_bind].
              unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_zero_N; cbn.
              rewrite Integers.xor_idem; reflexivity.
           ++ destruct (extract_const_expr w nr) as [ic2 |] eqn:Ec2.
              ** destruct (extract_binop_rhs_const CB_Xor w nl) as [[a ic1] |] eqn:Erc;
                   [| apply equiv_eou_dvalue_refl].
                 destruct (extract_const_expr_inv w nr ic2 Ec2) as [v2 [Heqr ->]].
                 destruct (extract_binop_rhs_const_inv CB_Xor w nl a ic1 Erc) as [v1 [Heql ->]].
                 pose proof (Hreassoc a v1 v2 (@Integers.xor w) Efl Heql Heqr eq_refl
                               (fun x y => eq_refl)
                               (@Integers.xor_assoc w)) as Hra.
                 cbn zeta; destruct (@Integers.unsigned w _ =? 0)%Z eqn:Exr0; [| exact Hra].
                 apply (equiv_eou_dvalue_trans _ _ _ Hra).
                 apply Z.eqb_eq in Exr0.
                 assert (Hx_zero : @Integers.xor w (@Integers.repr w (Z.of_N v1))
                                                   (@Integers.repr w (Z.of_N v2)) =
                                   @Integers.zero w)
                   by (rewrite <- (@Integers.repr_unsigned w (_)), Exr0; reflexivity).
                 subst nl; cbn in Htl, Hpl; rewrite !andb_true_iff in Htl.
                 destruct Htl as ((((_ & Hta) & _) & Hwa) & _); apply Pos.eqb_eq in Hwa.
                 rewrite app_nil_r in Hpl.
                 unfold mk_bv_const, eval_closed_cert_expr in *; cbn [eval_cert_expr].
                 rewrite Hx_zero, Integers.unsigned_zero, repr_zero_N.
                 destruct (eval_cert_expr_totality a [] penv [] foracle Hta wf_let_val_env_nil Hpl)
                   as [[msga ->] | [va [-> Hwfva]]]; cbn [eou_bind]; [exact I |].
                 rewrite Hwa in Hwfva; destruct Hwfva as [-> | [ia ->]]; cbn; [reflexivity |].
                 unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn.
                 rewrite Integers.xor_zero; reflexivity.
              ** destruct (extract_const_expr w nl) as [ic1 |] eqn:Ec1;
                   [| apply equiv_eou_dvalue_refl].
                 destruct (extract_const_expr_inv w nl ic1 Ec1) as [v1 [Heql ->]].
                 exact (Hcomm_l v1 Efl Heql eq_refl eq_refl).
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
                | None => CE_ICmp (swap_cert_icmp pr) ss w nr (mk_bv_const w ic)
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
    repeat split; [reflexivity | apply incl_refl]. }
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
      * apply andb_true_iff in Ei1 as [_ Ew1]; apply Pos.eqb_eq in Ew1; subst w.
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
    destruct (alg_i1_cases ic) as [Hic | Hic]; rewrite Hic in Hn |- *.
    + rewrite (@Integers.unsigned_zero 1%positive) in Hn; cbn in Hn; inversion Hn; subst out.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; fold ic; rewrite Hic.
      destruct (eval_cert_expr_totality e [] penv [] foracle Hte wf_let_val_env_nil Hpe)
        as [[msge ->] | [ve [-> Hwfve]]]; cbn [eou_bind]; [exact I |].
      rewrite Hwe in Hwfve; destruct Hwfve as [-> | [ie ->]]; cbn; [reflexivity |].
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
      rewrite Hwe in Hwfve; destruct Hwfve as [-> | [ie ->]]; cbn; [reflexivity |].
      unfold eval_icmp; rewrite eval_icmp_base_same_width; cbn.
      destruct (alg_i1_cases ie) as [-> | ->]; cbn [Integers.cmpu].
      * rewrite (@Integers.eq_false 1%positive _ _ alg_zero_neq_one_1); reflexivity.
      * rewrite (@Integers.eq_true 1%positive); reflexivity.
  - (* CIP_Ne *)
    destruct (alg_i1_cases ic) as [Hic | Hic]; rewrite Hic in Hn |- *.
    + rewrite (@Integers.unsigned_zero 1%positive) in Hn; cbn in Hn; inversion Hn; subst out.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; fold ic; rewrite Hic.
      destruct (eval_cert_expr_totality e [] penv [] foracle Hte wf_let_val_env_nil Hpe)
        as [[msge ->] | [ve [-> Hwfve]]]; cbn [eou_bind]; [exact I |].
      rewrite Hwe in Hwfve; destruct Hwfve as [-> | [ie ->]]; cbn; [reflexivity |].
      unfold eval_icmp; rewrite eval_icmp_base_same_width; cbn.
      destruct (alg_i1_cases ie) as [-> | ->]; cbn [Integers.cmpu].
      * rewrite (@Integers.eq_true 1%positive); reflexivity.
      * rewrite (@Integers.eq_false 1%positive _ _ (not_eq_sym alg_zero_neq_one_1)); reflexivity.
    + rewrite (@Integers.unsigned_one 1%positive) in Hn; cbn in Hn; inversion Hn; subst out.
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; fold ic; rewrite Hic.
      destruct (eval_cert_expr_totality e [] penv [] foracle Hte wf_let_val_env_nil Hpe)
        as [[msge ->] | [ve [-> Hwfve]]]; cbn [eou_bind]; [exact I |].
      rewrite Hwe in Hwfve; destruct Hwfve as [-> | [ie ->]]; cbn; [reflexivity |].
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
    apply equiv_eou_dvalue_refl.
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
          apply negb_true_iff in Ess; apply Pos.eqb_eq in Ew1; subst ss w.
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

Definition norm_cast_step
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
  assert (Hdef_out :
    cert_expr_bit_width (CE_Cast k fw tw fl no) = tw /\
    wt_cert_expr [] (CE_Cast k fw tw fl no) = true /\
    is_let_free_expr (CE_Cast k fw tw fl no) = true /\
    incl (collect_free_vars [] (CE_Cast k fw tw fl no)) (collect_free_vars [] no)).
  { cbn; rewrite Hk, Hto, Hwo, Pos.eqb_refl, Hfl_o; repeat split; [reflexivity | apply incl_refl]. }
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
  - destruct (is_no_cast_flags fl) eqn:Eno; [| exact Hdef_out].
    destruct (norm_cast_chain k fw tw no) as [out0 |] eqn:Ech; [| exact Hdef_out].
    destruct no as [| | | | | k_in iw fw' fl_in inner | | |]; cbn in Ech; try discriminate Ech.
    destruct (Pos.eqb fw' fw && is_no_cast_flags fl_in) eqn:Ein; [| discriminate Ech].
    apply andb_true_iff in Ein as [Efw Efl_in]; apply Pos.eqb_eq in Efw; subst fw'.
    cbn in Hto, Hfl_o; rewrite !andb_true_iff in Hto;
      destruct Hto as ((Hk_in & Hti) & Hwi); apply Pos.eqb_eq in Hwi.
    destruct k, k_in; try discriminate Ech.
    + destruct (iw <? fw)%positive eqn:Eif; [| discriminate Ech]; inversion Ech; subst out0.
      rewrite !andb_true_iff in Hk; destruct Hk as ([Hft _] & _).
      assert (Hit : (iw <? tw)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.ltb_lt in Eif; apply Pos.ltb_lt in Hft; lia).
      cbn; rewrite Hit, Hti, Hwi, Pos.eqb_refl, Hfl_o; repeat split; apply incl_refl.
    + destruct (iw <? fw)%positive eqn:Eif; [| discriminate Ech]; inversion Ech; subst out0.
      rewrite !andb_true_iff in Hk; destruct Hk as (([Hft _] & _) & _).
      assert (Hit : (iw <? tw)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.ltb_lt in Eif; apply Pos.ltb_lt in Hft; lia).
      cbn; rewrite Hit, Hti, Hwi, Pos.eqb_refl, Hfl_o; repeat split; apply incl_refl.
    + destruct (Pos.eqb iw tw) eqn:Eit; [| discriminate Ech];
        apply Pos.eqb_eq in Eit; inversion Ech; subst iw out0.
      repeat split; [exact Hwi | exact Hti | exact Hfl_o | apply incl_refl].
    + destruct (Pos.eqb iw tw) eqn:Eit; [| discriminate Ech];
        apply Pos.eqb_eq in Eit; inversion Ech; subst iw out0.
      repeat split; [exact Hwi | exact Hti | exact Hfl_o | apply incl_refl].
    + destruct (fw <? iw)%positive eqn:Efi; [| discriminate Ech]; inversion Ech; subst out0.
      rewrite !andb_true_iff in Hk; destruct Hk as [Htf _].
      assert (Hti_lt : (tw <? iw)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.ltb_lt in Efi; apply Pos.ltb_lt in Htf; lia).
      cbn; rewrite Hti_lt, Hti, Hwi, Pos.eqb_refl, Hfl_o; repeat split; apply incl_refl.
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
    destruct no as [| | | | | k_in iw fw' fl_in inner | | |]; cbn in Ech; try discriminate Ech.
    destruct (Pos.eqb fw' fw && is_no_cast_flags fl_in) eqn:Ein; [| discriminate Ech].
    apply andb_true_iff in Ein as [Efw Efl_in];
      apply Pos.eqb_eq in Efw; pose proof (is_no_cast_flags_inv fl_in Efl_in) as Hfl_in;
      subst fw' fl_in.
    cbn [wt_cert_expr collect_free_vars] in Hto, Hpo; rewrite !andb_true_iff in Hto.
    destruct Hto as ((Hk_in & Hti) & Hwi); apply Pos.eqb_eq in Hwi.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    destruct (eval_cert_expr_totality inner [] penv [] foracle Hti wf_let_val_env_nil Hpo)
      as [[msgi ->] | [vi [Evi Hwfvi]]]; [cbn; destruct out0; exact I |].
    rewrite Hwi in Hwfvi.
    destruct k, k_in; try discriminate Ech.
    + (* ZExt(ZExt) *)
      destruct (iw <? fw)%positive eqn:Eif; [| discriminate Ech]; inversion Ech; subst out0.
      cbn [eval_cert_expr]; rewrite Evi; cbn [eou_bind].
      destruct Hwfvi as [-> | [ii ->]]; [cbn; reflexivity |].
      cbn in Hk; apply andb_true_iff in Hk as [[Hft _] _].
      assert (Hit : (iw <? tw)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.ltb_lt in Eif; apply Pos.ltb_lt in Hft; lia).
      cbn; rewrite !Pos.eqb_refl, Eif, Hft, Hit; cbn.
      rewrite (@Integers.unsigned_repr fw (@Integers.unsigned iw ii)); [reflexivity |].
      pose proof (@Integers.unsigned_range_2 iw ii) as Hur.
      pose proof (alg_modulus_le iw fw (Pos.lt_le_incl _ _ (Pos.ltb_lt _ _ Eif))) as Hm.
      unfold Integers.max_unsigned in *; lia.
    + (* SExt(SExt) *)
      destruct (iw <? fw)%positive eqn:Eif; [| discriminate Ech]; inversion Ech; subst out0.
      cbn [eval_cert_expr]; rewrite Evi; cbn [eou_bind].
      destruct Hwfvi as [-> | [ii ->]]; [cbn; reflexivity |].
      cbn in Hk; apply andb_true_iff in Hk as [[[Hft _] _] _].
      assert (Hit : (iw <? tw)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.ltb_lt in Eif; apply Pos.ltb_lt in Hft; lia).
      cbn; rewrite !Pos.eqb_refl, Eif, Hft, Hit; cbn.
      rewrite (@Integers.signed_repr fw (@Integers.signed iw ii)); [reflexivity |].
      exact (alg_signed_bounds_le iw fw ii (Pos.lt_le_incl _ _ (Pos.ltb_lt _ _ Eif))).
    + (* Trunc(ZExt) *)
      destruct (Pos.eqb iw tw) eqn:Eit; [| discriminate Ech];
        apply Pos.eqb_eq in Eit; inversion Ech; subst iw out0.
      rewrite Evi; cbn [eou_bind].
      destruct Hwfvi as [-> | [ii ->]]; [cbn; reflexivity |].
      cbn in Hk; apply andb_true_iff in Hk as [Htf _].
      cbn; rewrite !Pos.eqb_refl, Htf; cbn.
      rewrite (alg_repr_unsigned_repr_le tw fw _ (Pos.lt_le_incl _ _ (Pos.ltb_lt _ _ Htf))),
              (@Integers.repr_unsigned tw ii); reflexivity.
    + (* Trunc(SExt) *)
      destruct (Pos.eqb iw tw) eqn:Eit; [| discriminate Ech];
        apply Pos.eqb_eq in Eit; inversion Ech; subst iw out0.
      rewrite Evi; cbn [eou_bind].
      destruct Hwfvi as [-> | [ii ->]]; [cbn; reflexivity |].
      cbn in Hk; apply andb_true_iff in Hk as [Htf _].
      cbn; rewrite !Pos.eqb_refl, Htf; cbn.
      rewrite (alg_repr_unsigned_repr_le tw fw _ (Pos.lt_le_incl _ _ (Pos.ltb_lt _ _ Htf))),
              (@Integers.repr_signed tw ii); reflexivity.
    + (* Trunc(Trunc) *)
      destruct (fw <? iw)%positive eqn:Efi; [| discriminate Ech]; inversion Ech; subst out0.
      cbn [eval_cert_expr]; rewrite Evi; cbn [eou_bind].
      destruct Hwfvi as [-> | [ii ->]]; [cbn; reflexivity |].
      cbn in Hk; apply andb_true_iff in Hk as [Htf _].
      assert (Hti_lt : (tw <? iw)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.ltb_lt in Efi; apply Pos.ltb_lt in Htf; lia).
      cbn; rewrite !Pos.eqb_refl, Efi, Htf, Hti_lt; cbn.
      rewrite (alg_repr_unsigned_repr_le tw fw _ (Pos.lt_le_incl _ _ (Pos.ltb_lt _ _ Htf)));
        reflexivity.
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
    repeat split; [reflexivity | apply incl_refl]. }
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
             apply Pos.eqb_eq in Ew1; subst w.
           repeat split; [exact Hwc | exact Htc | exact Hlc | apply incl_appl, incl_refl].
        -- destruct (Pos.eqb w 1 && is_zero_const_expr 1 nt && is_one_const_expr 1 nf) eqn:Es01.
           ++ rewrite !andb_true_iff in Es01; destruct Es01 as ([Ew1 _] & _);
                apply Pos.eqb_eq in Ew1; subst w.
              cbn; rewrite Htc, Hwc, Hlc, app_nil_r; repeat split; apply incl_appl, incl_refl.
           ++ destruct (extract_not_expr 1 nc) as [c0 |] eqn:Enc; [| exact Hdef_out].
              destruct (ub_free_expr nt && ub_free_expr nf); [| exact Hdef_out].
              pose proof (extract_not_expr_inv 1 nc c0 Enc) as Heqc; subst nc.
              cbn in Htc, Hlc; rewrite !andb_true_iff in Htc, Hlc.
              destruct Htc as ((((_ & Htc0) & _) & Hwc0) & _); destruct Hlc as [Hlc0 _].
              apply Pos.eqb_eq in Hwc0.
              cbn; rewrite Htc0, Htf, Htt, Hwc0, Hwf0, Hwt0, !Pos.eqb_refl, Hlc0, Hlf, Hlt, app_nil_r.
              repeat split.
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
              rewrite Hwc in Hwfvc; destruct Hwfvc as [-> | [ic ->]]; cbn; [reflexivity |].
              unfold eval_iop; rewrite eval_iop_integer_base_same_width, repr_one_N, repr_zero_N; cbn.
              destruct (alg_i1_cases ic) as [-> | ->];
                rewrite ?(@Integers.unsigned_zero 1), ?(@Integers.unsigned_one 1),
                        ?(@Integers.xor_zero_l 1), ?(@Integers.xor_idem 1); cbn; reflexivity.
           ++ destruct (extract_not_expr 1 nc) as [c0 |] eqn:Enc; [| apply equiv_eou_dvalue_refl].
              destruct (ub_free_expr nt && ub_free_expr nf) eqn:Eubtf; [| apply equiv_eou_dvalue_refl].
              apply andb_true_iff in Eubtf as [Eubt Eubf].
              pose proof (extract_not_expr_inv 1 nc c0 Enc) as Heqc; subst nc.
              cbn in Htc, Hpc; rewrite !andb_true_iff in Htc; rewrite app_nil_r in Hpc.
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
                 change (@Integers.mone 1) with (@Integers.one 1).
                 destruct (alg_i1_cases ic0) as [-> | ->];
                   rewrite ?(@Integers.xor_zero_l 1), ?(@Integers.xor_idem 1); cbn;
                   rewrite !(@Integers.unsigned_zero 1), !(@Integers.unsigned_one 1); cbn; reflexivity.
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
                    ltac:(rewrite Hib in Hic; inversion Hic; subst ic;
                          rewrite Hcan, <- Hia; exact Hat))).
      - rewrite !andb_true_iff in Har; destruct Har as (((Hc_in & Heqar) & Hubr) & Hrec).
        apply cert_expr_eqb_eq in Heqar; subst a.
        pose proof (IH b tgt Hrec (eq_trans Hwb Hbw) Htb Hwtt Hpb Hpt) as Hbt.
        destruct (ub_free_expr_eval_ret r [] penv [] foracle Hubr Hwtr wf_let_val_env_nil Hpr)
          as [vr [Evr Hwfvr]]; rewrite Hwr in Hwfvr.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Evr; cbn [eou_bind].
        destruct (eval_cert_expr_totality b [] penv [] foracle Htb wf_let_val_env_nil Hpb)
          as [[msgb ->] | [vb [Evb Hwfvb]]]; [cbn; exact I | rewrite Evb in Hbt |- *; cbn [eou_bind]].
        rewrite Hwb in Hwfvb; rewrite Evr; cbn [eou_bind].
        destruct (eval_cert_expr penv [] foracle tgt) as [| | | vtgt];
          cbn in Hbt; try contradiction.
        exact (eval_iop_nested_weaken_l op_in op fl_in fl w vr vb vr vtgt iop_in iop_out
                 Hndiv_in Hndiv_out Hwfvr Hwfvb Hwfvr Hiop_in Hiop_out
                 (fun ia ib ic Hia Hib Hic =>
                    ltac:(rewrite Hia in Hic; inversion Hic; subst ic;
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
        rewrite Hwa in Hwfva; rewrite Evl; cbn [eou_bind].
        destruct (eval_cert_expr penv [] foracle tgt) as [| | | vtgt];
          cbn in Hat; try contradiction.
        exact (eval_iop_nested_weaken_r op_in op fl_in fl w vl va vl vtgt iop_in iop_out
                 Hndiv_in Hndiv_out Hwfvl Hwfva Hwfvl Hiop_in Hiop_out
                 (fun ia ib ic Hia Hib Hic =>
                    ltac:(rewrite Hia in Hic; inversion Hic; subst ic;
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
                    ltac:(rewrite Hia in Hib; inversion Hib; subst ib;
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
        destruct Htot_l as [[msgl ->] | [vl [Evl Hwfvl]]]; [cbn; exact I | rewrite !Evl in Hlt |- *; cbn [eou_bind]].
        rewrite Evb; cbn [eou_bind].
        destruct (eval_cert_expr penv [] foracle tgt) as [| | | vtgt];
          cbn in Hlt; try contradiction.
        exact (eval_iop_nested_weaken_r op_in op fl_in fl w vl vl vb vtgt iop_in iop_out
                 Hndiv_in Hndiv_out Hwfvl Hwfvl Hwfvb Hiop_in Hiop_out
                 (fun ia ib ic Hia Hib _ =>
                    ltac:(rewrite Hia in Hib; inversion Hib; subst ib;
                          rewrite Habs, <- Hia; exact Hlt))).
      - destruct Hbl as ([Heqbl Huba] & Hrec); apply cert_expr_eqb_eq in Heqbl; subst b.
        pose proof (IH l tgt Hrec (eq_trans Hwl Hbw) Hwtl Hwtt Hpl Hpt) as Hlt.
        destruct (ub_free_expr_eval_ret a [] penv [] foracle Huba Hta wf_let_val_env_nil Hpa)
          as [va [Eva Hwfva]]; rewrite Hwa in Hwfva.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct Htot_l as [[msgl ->] | [vl [Evl Hwfvl]]]; [cbn; exact I | rewrite Evl in Hlt |- *; cbn [eou_bind]].
        rewrite Eva, Evl; cbn [eou_bind].
        destruct (eval_cert_expr penv [] foracle tgt) as [| | | vtgt];
          cbn in Hlt; try contradiction.
        exact (eval_iop_nested_weaken_r op_in op fl_in fl w vl va vl vtgt iop_in iop_out
                 Hndiv_in Hndiv_out Hwfvl Hwfva Hwfvl Hiop_in Hiop_out
                 (fun ia ib ic Hia _ Hic =>
                    ltac:(rewrite Hia in Hic; inversion Hic; subst ic;
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
        rewrite Evb, Evr; cbn [eou_bind].
        destruct (eval_cert_expr penv [] foracle tgt) as [| | | vtgt];
          cbn in Hrt; try contradiction.
        exact (eval_iop_nested_weaken_l op_in op fl_in fl w vr vb vr vtgt iop_in iop_out
                 Hndiv_in Hndiv_out Hwfvr Hwfvb Hwfvr Hiop_in Hiop_out
                 (fun ia ib ic Hia _ Hic =>
                    ltac:(rewrite Hia in Hic; inversion Hic; subst ic;
                          rewrite Habs, <- Hia; exact Hrt))).
      - destruct Hbr as ([Heqbr Huba] & Hrec); apply cert_expr_eqb_eq in Heqbr; subst b.
        pose proof (IH r tgt Hrec (eq_trans Hwr Hbw) Hwtr Hwtt Hpr Hpt) as Hrt.
        destruct (ub_free_expr_eval_ret a [] penv [] foracle Huba Hta wf_let_val_env_nil Hpa)
          as [va [Eva Hwfva]]; rewrite Hwa in Hwfva.
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Eva; cbn [eou_bind].
        destruct Htot_r as [[msgr ->] | [vr [Evr Hwfvr]]]; [cbn; exact I | rewrite !Evr in Hrt |- *; cbn [eou_bind]].
        destruct (eval_cert_expr penv [] foracle tgt) as [| | | vtgt];
          cbn in Hrt; try contradiction.
        exact (eval_iop_nested_weaken_l op_in op fl_in fl w va vr vr vtgt iop_in iop_out
                 Hndiv_in Hndiv_out Hwfva Hwfvr Hwfvr Hiop_in Hiop_out
                 (fun ia ib ic _ Hib Hic =>
                    ltac:(rewrite Hib in Hic; inversion Hic; subst ic;
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
        destruct Htot_l as [[msgl ->] | [vl [-> [-> | [il ->]]]]];
          [cbn; exact I | cbn [eou_bind]; exact Hlt | cbn [eou_bind]].
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
        destruct Htot_l as [[msgl ->] | [vl [-> Hwfvl]]]; [cbn; exact I | cbn [eou_bind]].
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
    by congruence.
  apply (refine_eou_compat _ _ _ _ Heq_src Heq_tgt).
  exact (check_norm_refines_fuel_sound _ ctx _ _ penv foracle
           Hbody Hbw_norm Hwt_ns Hwt_nt Hp_ns Hp_nt Hctx).
Qed.


(** ** 7. Verified 2-Rail [LRAT] & Auto-DPLL Fallback Refinement Checker *)

(** *** 7.1 Tail-Recursive Cone-of-Influence ([COI]) Clause Filter *)

Definition lit_var (l : lit) : option positive :=
  match l with
  | Z.pos v | Z.neg v => Some v
  | Z0 => None
  end.

Fixpoint clause_touches_coi (coi : pos_trie unit) (cl : clause) {struct cl} : bool :=
  match cl with
  | [] => false
  | l :: rest =>
      match lit_var l with
      | Some v =>
          match pt_get v coi with
          | Some _ => true
          | None => clause_touches_coi coi rest
          end
      | None => clause_touches_coi coi rest
      end
  end.

Fixpoint add_clause_vars_coi (cl : clause) (coi : pos_trie unit) {struct cl}
  : pos_trie unit :=
  match cl with
  | [] => coi
  | l :: rest =>
      let coi' :=
          match lit_var l with
          | Some v => pt_set v tt coi
          | None => coi
          end in
      add_clause_vars_coi rest coi'
  end.

Fixpoint coi_scan_rev (rev_f : cnf) (coi : pos_trie unit) (acc : cnf)
  {struct rev_f} : cnf :=
  match rev_f with
  | [] => acc
  | (cid, cl) :: rest =>
      let keep :=
          match cl with
          | [] | [_] => true
          | _ => clause_touches_coi coi cl
          end in
      if keep
      then coi_scan_rev rest (add_clause_vars_coi cl coi) ((cid, cl) :: acc)
      else coi_scan_rev rest coi acc
  end.

Definition coi_filter_cnf (f : cnf) : cnf :=
  coi_scan_rev (List.rev_append f []) (pt_set 1%positive tt PT_Empty) [].

Lemma rev_append_in_iff :
  forall {A : Type} (xs acc : list A) (x : A),
    In x (List.rev_append xs acc) <-> In x xs \/ In x acc.
Proof.
  intros A xs; induction xs as [| y rest IH]; intros acc x; cbn [List.rev_append In].
  - tauto.
  - rewrite IH; cbn [In]; tauto.
Qed.

Lemma coi_scan_rev_incl :
  forall rev_f coi acc V,
    incl rev_f V ->
    incl acc V ->
    incl (coi_scan_rev rev_f coi acc) V.
Proof.
  induction rev_f as [| [cid cl] rest IH]; intros coi acc V Hrev Hacc;
    cbn [coi_scan_rev]; [exact Hacc |].
  assert (Hrest : incl rest V) by (intros z Hz; apply Hrev; right; exact Hz).
  assert (Hhead : In (cid, cl) V) by (apply Hrev; left; reflexivity).
  destruct (match cl with [] | [_] => true | _ => clause_touches_coi coi cl end).
  - apply IH; [exact Hrest |].
    intros z [<- | Hz]; [exact Hhead | exact (Hacc z Hz)].
  - exact (IH coi acc V Hrest Hacc).
Qed.

Lemma coi_filter_cnf_incl : forall f, incl (coi_filter_cnf f) f.
Proof.
  intros f; unfold coi_filter_cnf.
  apply coi_scan_rev_incl.
  - intros z Hz; apply rev_append_in_iff in Hz as [Hz | []]; exact Hz.
  - intros z [].
Qed.

Lemma eval_cnf_incl_false :
  forall f1 f2 a,
    incl f1 f2 ->
    eval_cnf a f1 = false ->
    eval_cnf a f2 = false.
Proof.
  intros f1 f2 a Hincl Hf1.
  destruct (eval_cnf a f2) eqn:Ef2; [| reflexivity].
  unfold eval_cnf in *.
  rewrite forallb_forall in Ef2.
  assert (Ht1 : forallb (fun '(_, c) => eval_clause a c) f1 = true).
  { apply forallb_forall; intros x Hx; exact (Ef2 x (Hincl x Hx)). }
  congruence.
Qed.

(** *** 7.2 Alignment-Aware Variable Allocation & Relational Value Matching *)

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

Fixpoint alloc_aligned_bits
  (zero_pred : nat -> bool) (idx rem : nat) (st : blast_state) {struct rem}
  : list lit * blast_state :=
  match rem with
  | O => ([], st)
  | S rem' =>
      let '(b, st1) := if zero_pred idx then (lit_false, st) else alloc_var st in
      let '(bs, st2) := alloc_aligned_bits zero_pred (S idx) rem' st1 in
      (b :: bs, st2)
  end.

Lemma alloc_aligned_bits_any_step :
  forall rem zero_pred idx asg st bits st',
    sat_blast_st asg st ->
    alloc_aligned_bits zero_pred idx rem st = (bits, st') ->
    exists asg',
      step_spec st st' asg asg' /\
      List.length bits = rem /\
      wf_lits_bound (bs_next_var st') bits.
Proof.
  induction rem as [| rem' IH]; intros zp idx asg st bits st' Hsat Hal; cbn in Hal.
  - inversion Hal; subst; exists asg; split;
      [exact (step_spec_refl st asg Hsat) | split; [reflexivity | constructor]].
  - assert (Hb_step :
              exists b st1 asg1,
                (if zp idx then (lit_false, st) else alloc_var st) = (b, st1) /\
                step_spec st st1 asg asg1 /\
                wf_lit_bound (bs_next_var st1) b).
    { destruct (zp idx).
      - exists lit_false, st, asg; split; [reflexivity | split;
          [exact (step_spec_refl st asg Hsat)
           | exact (wf_lit_bound_false _ (proj1 (proj1 Hsat)))]].
      - destruct (alloc_var st) as [b st1] eqn:Eb.
        destruct (alloc_var_sat asg st false b st1 Hsat Eb)
          as (a1 & Hle1 & Hag1 & Hsat1 & Hwb & _).
        exists b, st1, a1; split; [reflexivity | split;
          [exact (conj Hle1 (conj Hag1 Hsat1)) | exact Hwb]]. }
    destruct Hb_step as (b & st1 & asg1 & Hb_eq & Hs1 & Hwb).
    rewrite Hb_eq in Hal; clear Hb_eq.
    destruct (alloc_aligned_bits zp (S idx) rem' st1) as [bs st2] eqn:Ebs.
    inversion Hal; subst bits st2; clear Hal.
    destruct (IH zp (S idx) asg1 st1 bs st' (proj2 (proj2 Hs1)) Ebs)
      as (asg2 & Hs2 & Hlen & Hwbs).
    exists asg2; split; [exact (step_spec_trans st st1 st' asg asg1 asg2 Hs1 Hs2) | split].
    + cbn; rewrite Hlen; reflexivity.
    + constructor; [exact (wf_lit_bound_mono _ _ b (proj1 Hs2) Hwb) | exact Hwbs].
Qed.

Lemma alloc_aligned_bits_val_step :
  forall target zero_pred idx asg st bits st',
    sat_blast_st asg st ->
    (forall k, zero_pred (idx + k)%nat = true -> List.nth k target false = false) ->
    alloc_aligned_bits zero_pred idx (List.length target) st = (bits, st') ->
    exists asg',
      step_spec st st' asg asg' /\
      List.length bits = List.length target /\
      wf_lits_bound (bs_next_var st') bits /\
      List.map (eval_lit asg') bits = target.
Proof.
  induction target as [| tb tr IH]; intros zp idx asg st bits st' Hsat Hzp Hal; cbn in Hal.
  - inversion Hal; subst; exists asg; split;
      [exact (step_spec_refl st asg Hsat) | split; [reflexivity | split; [constructor | reflexivity]]].
  - assert (Hb_step :
              exists b st1 asg1,
                (if zp idx then (lit_false, st) else alloc_var st) = (b, st1) /\
                step_spec st st1 asg asg1 /\
                wf_lit_bound (bs_next_var st1) b /\
                eval_lit asg1 b = tb).
    { destruct (zp idx) eqn:Ez.
      - assert (Htb : tb = false)
          by (pose proof (Hzp 0%nat) as H0; rewrite Nat.add_0_r in H0; exact (H0 Ez)).
        subst tb; exists lit_false, st, asg; split; [reflexivity | split;
          [exact (step_spec_refl st asg Hsat) | split;
           [exact (wf_lit_bound_false _ (proj1 (proj1 Hsat)))
            | exact (sat_eval_lit_false asg st Hsat)]]].
      - destruct (alloc_var st) as [b st1] eqn:Eb.
        destruct (alloc_var_sat asg st tb b st1 Hsat Eb)
          as (a1 & Hle1 & Hag1 & Hsat1 & Hwb & Hevb).
        exists b, st1, a1; split; [reflexivity | split;
          [exact (conj Hle1 (conj Hag1 Hsat1)) | split; [exact Hwb | exact Hevb]]]. }
    destruct Hb_step as (b & st1 & asg1 & Hb_eq & Hs1 & Hwb & Hevb).
    rewrite Hb_eq in Hal; clear Hb_eq.
    destruct (alloc_aligned_bits zp (S idx) (List.length tr) st1) as [bs st2] eqn:Ebs.
    inversion Hal; subst bits st2; clear Hal.
    assert (Hzp_tr : forall k, zp (S idx + k)%nat = true -> List.nth k tr false = false).
    { intros k Hk; replace (S idx + k)%nat with (idx + S k)%nat in Hk by lia.
      exact (Hzp (S k) Hk). }
    destruct (IH zp (S idx) asg1 st1 bs st' (proj2 (proj2 Hs1)) Hzp_tr Ebs)
      as (asg2 & Hs2 & Hlen & Hwbs & Hevbs).
    exists asg2; split; [exact (step_spec_trans st st1 st' asg asg1 asg2 Hs1 Hs2) | split].
    + cbn; rewrite Hlen; reflexivity.
    + split.
      * constructor; [exact (wf_lit_bound_mono _ _ b (proj1 Hs2) Hwb) | exact Hwbs].
      * cbn; rewrite (step_spec_eval_lit st1 st' asg1 asg2 b Hs2 Hwb), Hevb, Hevbs; reflexivity.
Qed.

(** *** 7.3 Verified 2-Rail Multiplier ([CB_Mul] with [nuw]/[nsw] & [i1] Semantics) *)

Definition is_const_rail (r : rail_bv) : bool :=
  forallb (fun l => Z.eqb l lit_true || Z.eqb l lit_false) (rbv_bits r).

Fixpoint emit_scale_bits (x : lit) (ys : list lit) (st : blast_state)
  {struct ys} : list lit * blast_state :=
  match ys with
  | [] => ([], st)
  | y :: ry =>
      let '(p, st1) := emit_and2_opt x y st in
      let '(ps, st2) := emit_scale_bits x ry st1 in
      (p :: ps, st2)
  end.

Lemma emit_scale_bits_step :
  forall ys x asg st out st',
    sat_blast_st asg st ->
    wf_lit_bound (bs_next_var st) x ->
    wf_lits_bound (bs_next_var st) ys ->
    emit_scale_bits x ys st = (out, st') ->
    exists asg',
      step_spec st st' asg asg' /\
      List.length out = List.length ys /\
      wf_lits_bound (bs_next_var st') out /\
      bools_to_Z (List.map (eval_lit asg') out) =
      (b2z (eval_lit asg x) * bools_to_Z (List.map (eval_lit asg) ys))%Z.
Proof.
  induction ys as [| y ry IH]; intros x asg st out st' Hsat Hwx Hwy He; cbn in He.
  - inversion He; subst; exists asg; split;
      [exact (step_spec_refl st asg Hsat) | split; [reflexivity | split;
       [constructor | cbn; lia]]].
  - inversion Hwy as [| ? ? Hy Hwry]; subst.
    destruct (emit_and2_opt x y st) as [p st1] eqn:Ep.
    destruct (emit_scale_bits x ry st1) as [ps st2] eqn:Eps.
    inversion He; subst out st2; clear He.
    destruct (emit_and2_opt_step asg x y st p st1 Hsat Hwx Hy Ep)
      as (asg1 & Hs1 & Hwp & Hevp).
    destruct (IH x asg1 st1 ps st' (proj2 (proj2 Hs1))
                (wf_lit_bound_mono _ _ x (proj1 Hs1) Hwx)
                (wf_lits_bound_mono _ _ ry (proj1 Hs1) Hwry) Eps)
      as (asg2 & Hs2 & Hlen & Hwps & Hevps).
    exists asg2; split; [exact (step_spec_trans st st1 st' asg asg1 asg2 Hs1 Hs2) | split].
    + cbn; rewrite Hlen; reflexivity.
    + split.
      * constructor; [exact (wf_lit_bound_mono _ _ p (proj1 Hs2) Hwp) | exact Hwps].
      * cbn [List.map]; rewrite !bools_to_Z_cons,
          (step_spec_eval_lit st1 st' asg1 asg2 p Hs2 Hwp), Hevp, Hevps,
          (step_spec_eval_lit st st1 asg asg1 x Hs1 Hwx),
          (step_spec_eval_lits st st1 asg asg1 ry Hs1 Hwry).
        assert (Hb_mul : b2z (eval_lit asg x && eval_lit asg y) =
                         (b2z (eval_lit asg x) * b2z (eval_lit asg y))%Z)
          by (destruct (eval_lit asg x), (eval_lit asg y); reflexivity).
        rewrite Hb_mul; ring.
Qed.

Fixpoint emit_mul_bits (xs ys : list lit) (st : blast_state)
  {struct xs} : list lit * blast_state :=
  match xs with
  | [] => (List.repeat lit_false (List.length ys), st)
  | x :: rx =>
      match ys with
      | [] => ([], st)
      | _ :: _ =>
          let m' := (List.length ys - 1)%nat in
          let '(sub, st1) := emit_mul_bits rx (List.firstn m' ys) st in
          let shifted := lit_false :: sub in
          let '(pp, st2) := emit_scale_bits x ys st1 in
          let '((sums, _), st3) := emit_ripple_add lit_false pp shifted st2 in
          (sums, st3)
      end
  end.

Lemma emit_mul_bits_step :
  forall xs ys asg st out st',
    sat_blast_st asg st ->
    wf_lits_bound (bs_next_var st) xs ->
    wf_lits_bound (bs_next_var st) ys ->
    emit_mul_bits xs ys st = (out, st') ->
    exists asg',
      step_spec st st' asg asg' /\
      List.length out = List.length ys /\
      wf_lits_bound (bs_next_var st') out /\
      exists k : Z,
        (bools_to_Z (List.map (eval_lit asg') out) =
         bools_to_Z (List.map (eval_lit asg) xs) *
         bools_to_Z (List.map (eval_lit asg) ys) +
         2 ^ Z.of_nat (List.length ys) * k)%Z.
Proof.
  induction xs as [| x rx IH]; intros ys asg st out st' Hsat Hwx Hwy He; cbn in He.
  - inversion He; subst; exists asg; split;
      [exact (step_spec_refl st asg Hsat) | split; [apply repeat_length | split]].
    + exact (wf_lits_bound_repeat _ _ _ (wf_lit_bound_false _ (proj1 (proj1 Hsat)))).
    + rewrite map_repeat_eq, (sat_eval_lit_false asg st Hsat), bools_to_Z_repeat_false.
      exists 0%Z; cbn [List.map bools_to_Z]; lia.
  - inversion Hwx as [| ? ? Hx Hwrx]; subst.
    destruct ys as [| y0 ry].
    + inversion He; subst; exists asg; split;
        [exact (step_spec_refl st asg Hsat) | split; [reflexivity | split;
         [constructor | exists 0%Z; cbn; lia]]].
    + set (ys_full := y0 :: ry) in *.
      set (m' := (List.length ys_full - 1)%nat) in *.
      assert (Hm'_eq : m' = List.length ry) by (unfold m', ys_full; cbn; lia).
      assert (Hlen_ys : List.length ys_full = S m') by (unfold ys_full; cbn; lia).
      destruct (emit_mul_bits rx (List.firstn m' ys_full) st) as [sub st1] eqn:Esub.
      destruct (emit_scale_bits x ys_full st1) as [pp st2] eqn:Epp.
      destruct (emit_ripple_add lit_false pp (lit_false :: sub) st2)
        as [[sums cout] st3] eqn:Eadd.
      inversion He; subst out st3; clear He.
      destruct (IH (List.firstn m' ys_full) asg st sub st1 Hsat Hwrx
                  (wf_lits_bound_firstn _ _ _ Hwy) Esub)
        as (asg1 & Hs1 & Hlen_sub & Hwf_sub & k1 & Hk1).
      assert (Hlen_fn : List.length (List.firstn m' ys_full) = m')
        by (apply len_firstn_le; lia).
      rewrite Hlen_fn in Hlen_sub, Hk1.
      destruct (emit_scale_bits_step ys_full x asg1 st1 pp st2 (proj2 (proj2 Hs1))
                  (wf_lit_bound_mono _ _ x (proj1 Hs1) Hx)
                  (wf_lits_bound_mono _ _ ys_full (proj1 Hs1) Hwy) Epp)
        as (asg2 & Hs2 & Hlen_pp & Hwf_pp & Hev_pp).
      pose proof (step_spec_trans st st1 st2 asg asg1 asg2 Hs1 Hs2) as Hs12.
      assert (Hlen_ps : List.length pp = List.length (lit_false :: sub))
        by (cbn; rewrite Hlen_pp, Hlen_ys, Hlen_sub; reflexivity).
      assert (Hwf_sh : wf_lits_bound (bs_next_var st2) (lit_false :: sub)).
      { constructor;
          [exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs2)))))
           | exact (wf_lits_bound_mono _ _ sub (proj1 Hs2) Hwf_sub)]. }
      destruct (emit_ripple_add_step pp (lit_false :: sub) lit_false asg2 st2 sums cout st'
                  Hlen_ps
                  (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs2)))))
                  Hwf_pp Hwf_sh (proj2 (proj2 Hs2)) Eadd)
        as (asg3 & Hs3 & Hlen_sums & Hwf_sums & _ & Heq_sum).
      pose proof (step_spec_trans st st2 st' asg asg2 asg3 Hs12 Hs3) as Hs13.
      exists asg3; split; [exact Hs13 | split; [congruence | split; [exact Hwf_sums |]]].
      rewrite Hlen_pp, Hlen_ys, Nat2Z.inj_succ, Z.pow_succ_r in Heq_sum by lia.
      rewrite (sat_eval_lit_false asg2 st2 (proj2 (proj2 Hs2))) in Heq_sum.
      cbn [List.map b2z] in Heq_sum.
      rewrite (sat_eval_lit_false asg2 st2 (proj2 (proj2 Hs2))),
              bools_to_Z_cons,
              (step_spec_eval_lits st1 st2 asg1 asg2 sub Hs2 Hwf_sub),
              Hk1, Hev_pp,
              (step_spec_eval_lit st st1 asg asg1 x Hs1 Hx),
              (step_spec_eval_lits st st1 asg asg1 ys_full Hs1 Hwy) in Heq_sum;
        cbn [b2z] in Heq_sum.
      set (bys := List.map (eval_lit asg) ys_full) in *.
      set (brx := List.map (eval_lit asg) rx) in *.
      assert (Hbys_split :
                (bools_to_Z bys =
                 bools_to_Z (List.firstn m' bys) +
                 2 ^ Z.of_nat m' * bools_to_Z (List.skipn m' bys))%Z).
      { rewrite <- (firstn_skipn_eq m' bys) at 1, bools_to_Z_app.
        assert (Hfl : List.length (List.firstn m' bys) = m')
          by (unfold bys; apply len_firstn_le; rewrite map_length; lia).
        rewrite Hfl; reflexivity. }
      rewrite map_firstn_eq in Heq_sum; fold bys in Heq_sum.
      assert (Hlo_eq : (bools_to_Z (List.firstn m' bys) =
                        bools_to_Z bys - 2 ^ Z.of_nat m' * bools_to_Z (List.skipn m' bys))%Z)
        by lia.
      rewrite Hlo_eq in Heq_sum.
      rewrite Hlen_ys, Nat2Z.inj_succ, Z.pow_succ_r by lia.
      cbn [List.map]; rewrite bools_to_Z_cons; fold brx.
      exists (k1 - bools_to_Z brx * bools_to_Z (List.skipn m' bys) -
              b2z (eval_lit asg3 cout))%Z.
      lia.
Qed.

Lemma mul_eq_repr_signed : forall sz (x y : @Integers.bit_int sz),
  @Integers.mul sz x y =
  @Integers.repr sz (@Integers.signed sz x * @Integers.signed sz y).
Proof.
  intros sz x y; unfold Integers.mul; apply @Integers.eqm_samerepr.
  rewrite (signed_eq_unsigned_msb sz x), (signed_eq_unsigned_msb sz y).
  exists (b2z (msb_of sz x) * @Integers.unsigned sz y +
          b2z (msb_of sz y) * @Integers.unsigned sz x -
          b2z (msb_of sz x) * b2z (msb_of sz y) * @Integers.modulus sz)%Z.
  ring.
Qed.

Lemma signed_repr_neq_iff_oob : forall sz (v : Z),
  negb (Z.eqb (@Integers.signed sz (@Integers.repr sz v)) v) =
  ((@Integers.min_signed sz >? v)%Z || (v >? @Integers.max_signed sz)%Z).
Proof.
  intros sz v; rewrite !Z.gtb_ltb.
  pose proof (@Integers.signed_range sz (@Integers.repr sz v)) as Hsr.
  destruct (Z.ltb_spec v (@Integers.min_signed sz)) as [Hlt | Hge].
  - cbn [orb]; destruct (Z.eqb_spec (@Integers.signed sz (@Integers.repr sz v)) v);
      [lia | reflexivity].
  - destruct (Z.ltb_spec (@Integers.max_signed sz) v) as [Hgt | Hle].
    + cbn [orb]; destruct (Z.eqb_spec (@Integers.signed sz (@Integers.repr sz v)) v);
        [lia | reflexivity].
    + cbn [orb]; rewrite (@Integers.signed_repr sz v (conj Hge Hle)), Z.eqb_refl; reflexivity.
Qed.

Definition blast_mul_rail (nuw nsw : bool) (sz : positive) (a b : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let '(prod_bits, st1) := emit_mul_bits (rbv_bits a) (rbv_bits b) st in
  let '(base_psn, st2) := emit_or2_opt (rbv_psn a) (rbv_psn b) st1 in
  if Pos.eqb sz 1%positive || (negb nuw && negb nsw) then
    (mk_rail_bv sz prod_bits base_psn, st2)
  else
    let dw := (sz + sz)%positive in
    let '(nuw_psn, st6) :=
        if nuw then
          let '(za, st3) := blast_zext_rail false sz dw a st2 in
          let '(zb, st4) := blast_zext_rail false sz dw b st3 in
          let '(ubits, st5) := emit_mul_bits (rbv_bits za) (rbv_bits zb) st4 in
          let '(tr_u, st6) := blast_trunc_rail true false dw sz (mk_rail_bv dw ubits lit_false) st5 in
          (rbv_psn tr_u, st6)
        else (lit_false, st2) in
    let '(nsw_psn, st10) :=
        if nsw then
          let '(sa, st7) := blast_sext_rail sz dw a st6 in
          let '(sb, st8) := blast_sext_rail sz dw b st7 in
          let '(sbits, st9) := emit_mul_bits (rbv_bits sa) (rbv_bits sb) st8 in
          let '(tr_s, st10) := blast_trunc_rail false true dw sz (mk_rail_bv dw sbits lit_false) st9 in
          (rbv_psn tr_s, st10)
        else (lit_false, st6) in
    let '(ov_psn, st11) := emit_or2_opt nuw_psn nsw_psn st10 in
    let '(psn, st12) := emit_or2_opt base_psn ov_psn st11 in
    (mk_rail_bv sz prod_bits psn, st12).

Theorem blast_mul_rail_step :
  forall nuw nsw sz a b asg st out st',
    sat_blast_st asg st ->
    wf_rail_bound sz (bs_next_var st) a ->
    wf_rail_bound sz (bs_next_var st) b ->
    blast_mul_rail nuw nsw sz a b st = (out, st') ->
    exists asg',
      step_spec st st' asg asg' /\
      wf_rail_bound sz (bs_next_var st') out /\
      eval_rail_psn asg' out =
        ((eval_rail_psn asg a || eval_rail_psn asg b) ||
         (if Pos.eqb sz 1%positive then false
          else
            let va := eval_rail_val sz asg a in
            let vb := eval_rail_val sz asg b in
            let res := @Integers.mul sz va vb in
            let res_u' := (@Integers.unsigned sz va * @Integers.unsigned sz vb)%Z in
            let res_s' := (@Integers.signed sz va * @Integers.signed sz vb)%Z in
            (nuw && (res_u' >? @Integers.unsigned sz res)%Z) ||
            (nsw && ((@Integers.min_signed sz >? res_s')%Z ||
                     (res_s' >? @Integers.max_signed sz)%Z)))) /\
      eval_rail_val sz asg' out =
        @Integers.mul sz (eval_rail_val sz asg a) (eval_rail_val sz asg b).
Proof.
  intros nuw nsw sz a b asg st out st' Hsat Hwa Hwb Hbl.
  destruct Hwa as ([Hwa_w Hla] & Hba & Hpa), Hwb as ([Hwb_w Hlb] & Hbb & Hpb).
  assert (Hwa_f : wf_rail_bound sz (bs_next_var st) a)
    by exact (conj (conj Hwa_w Hla) (conj Hba Hpa)).
  assert (Hwb_f : wf_rail_bound sz (bs_next_var st) b)
    by exact (conj (conj Hwb_w Hlb) (conj Hbb Hpb)).
  unfold blast_mul_rail in Hbl.
  destruct (emit_mul_bits (rbv_bits a) (rbv_bits b) st) as [prod_bits st1] eqn:Emul.
  destruct (emit_or2_opt (rbv_psn a) (rbv_psn b) st1) as [base_psn st2] eqn:Ebp.
  destruct (emit_mul_bits_step (rbv_bits a) (rbv_bits b) asg st prod_bits st1
              Hsat Hba Hbb Emul)
    as (asg1 & Hs1 & Hlen_pb & Hwf_pb & k0 & Hk0).
  destruct (emit_or2_opt_step asg1 (rbv_psn a) (rbv_psn b) st1 base_psn st2 (proj2 (proj2 Hs1))
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpa)
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpb) Ebp)
    as (asg2 & Hs2 & Hwf_bp & Hev_bp).
  pose proof (step_spec_trans st st1 st2 asg asg1 asg2 Hs1 Hs2) as Hs02.
  set (va := eval_rail_val sz asg a).
  set (vb := eval_rail_val sz asg b).
  assert (Hval_pb :
            @Integers.repr sz (bools_to_Z (List.map (eval_lit asg1) prod_bits)) =
            @Integers.mul sz va vb).
  { unfold Integers.mul; apply @Integers.eqm_samerepr.
    rewrite Hk0, Hlb, positive_nat_Z, <- modulus_pow_sz,
            <- (unsigned_eval_rail_val sz asg a Hla),
            <- (unsigned_eval_rail_val sz asg b Hlb); fold va vb.
    exists (- k0)%Z; ring. }
  destruct (Pos.eqb sz 1%positive || (negb nuw && negb nsw)) eqn:Efast.
  - inversion Hbl; subst out st2; clear Hbl.
    exists asg2; split; [exact Hs02 | split].
    + split; [split; [reflexivity | cbn; congruence] |
              split; [exact (wf_lits_bound_mono _ _ prod_bits (proj1 Hs2) Hwf_pb) | exact Hwf_bp]].
    + split.
      * unfold eval_rail_psn; rewrite Hev_bp,
          (step_spec_eval_lit st st1 asg asg1 (rbv_psn a) Hs1 Hpa),
          (step_spec_eval_lit st st1 asg asg1 (rbv_psn b) Hs1 Hpb).
        apply orb_true_iff in Efast as [Esz1 | Eflags].
        -- rewrite Esz1, orb_false_r; reflexivity.
        -- apply andb_true_iff in Eflags as [Enuw Ensw];
             apply negb_true_iff in Enuw; apply negb_true_iff in Ensw; subst nuw nsw.
           destruct (Pos.eqb sz 1%positive); rewrite !orb_false_r; reflexivity.
      * unfold eval_rail_val; cbn [rbv_bits];
          rewrite (step_spec_eval_lits st1 st' asg1 asg2 prod_bits Hs2 Hwf_pb); exact Hval_pb.
  - apply orb_false_iff in Efast as [Esz_gt1 _].
    assert (Hsz2 : (2 <= Z.pos sz)%Z)
      by (destruct sz; [lia | lia | discriminate Esz_gt1]).
    set (dw := (sz + sz)%positive) in *.
    assert (Hlt_dw : (sz < dw)%positive) by (unfold dw; lia).
    assert (Hmod_dw : @Integers.modulus dw = (@Integers.modulus sz * @Integers.modulus sz)%Z)
      by (rewrite !modulus_pow_sz; unfold dw; rewrite Pos2Z.inj_add, Z.pow_add_r by lia; reflexivity).
    assert (Hnuw_step :
              exists nuw_psn st6 asg6,
                (if nuw then
                   let '(za, st3) := blast_zext_rail false sz dw a st2 in
                   let '(zb, st4) := blast_zext_rail false sz dw b st3 in
                   let '(ubits, st5) := emit_mul_bits (rbv_bits za) (rbv_bits zb) st4 in
                   let '(tr_u, st6) := blast_trunc_rail true false dw sz (mk_rail_bv dw ubits lit_false) st5 in
                   (rbv_psn tr_u, st6)
                 else (lit_false, st2)) = (nuw_psn, st6) /\
                step_spec st2 st6 asg2 asg6 /\
                wf_lit_bound (bs_next_var st6) nuw_psn /\
                eval_lit asg6 nuw_psn =
                  (nuw && ((@Integers.unsigned sz va * @Integers.unsigned sz vb) >?
                           @Integers.unsigned sz (@Integers.mul sz va vb))%Z)).
    { destruct nuw; [| exists lit_false, st2, asg2; repeat split;
                        try exact (step_spec_refl st2 asg2 (proj2 (proj2 Hs02)));
                        [exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs02)))))
                         | exact (sat_eval_lit_false asg2 st2 (proj2 (proj2 Hs02)))]].
      destruct (blast_zext_rail false sz dw a st2) as [za st3] eqn:Eza.
      destruct (blast_zext_rail false sz dw b st3) as [zb st4] eqn:Ezb.
      destruct (emit_mul_bits (rbv_bits za) (rbv_bits zb) st4) as [ubits st5] eqn:Eum.
      destruct (blast_trunc_rail true false dw sz (mk_rail_bv dw ubits lit_false) st5)
        as [tr_u st6] eqn:Etru.
      destruct (blast_zext_rail_step false sz dw a asg2 st2 za st3 Hlt_dw (proj2 (proj2 Hs02))
                  (wf_rail_bound_mono _ _ _ a (proj1 Hs02) Hwa_f) Eza)
        as (a3 & Hs23 & Hwf_za & _ & Hval_za).
      pose proof (step_spec_trans st st2 st3 asg asg2 a3 Hs02 Hs23) as Hs03.
      destruct (blast_zext_rail_step false sz dw b a3 st3 zb st4 Hlt_dw (proj2 (proj2 Hs23))
                  (wf_rail_bound_mono _ _ _ b (proj1 Hs03) Hwb_f) Ezb)
        as (a4 & Hs34 & Hwf_zb & _ & Hval_zb).
      destruct (eval_rail_agree sz _ asg asg2 a (proj1 (proj2 Hs02)) Hwa_f) as [_ Hva2].
      destruct (eval_rail_agree sz _ asg a3 b (proj1 (proj2 Hs03)) Hwb_f) as [_ Hvb3].
      rewrite <- Hva2 in Hval_za; rewrite <- Hvb3 in Hval_zb; fold va in Hval_za; fold vb in Hval_zb.
      destruct Hwf_za as ([Hw_za Hl_za] & Hb_za & Hp_za).
      destruct Hwf_zb as ([Hw_zb Hl_zb] & Hb_zb & Hp_zb).
      destruct (emit_mul_bits_step (rbv_bits za) (rbv_bits zb) a4 st4 ubits st5
                  (proj2 (proj2 Hs34))
                  (wf_lits_bound_mono _ _ _ (proj1 Hs34) Hb_za) Hb_zb Eum)
        as (a5 & Hs45 & Hlen_ub & Hwf_ub & ku & Hku).
      assert (Hwf_ru : wf_rail_bound dw (bs_next_var st5) (mk_rail_bv dw ubits lit_false)).
      { split; [split; [reflexivity | cbn; congruence] |
                split; [exact Hwf_ub
                        | exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs45)))))]]. }
      destruct (blast_trunc_rail_step true false dw sz (mk_rail_bv dw ubits lit_false)
                  a5 st5 tr_u st6 Hlt_dw (proj2 (proj2 Hs45)) Hwf_ru Etru)
        as (a6 & Hs56 & (_ & _ & Hwf_trp) & Hev_trp & _).
      pose proof (step_spec_trans st2 st3 st4 asg2 a3 a4 Hs23 Hs34) as Hs24.
      pose proof (step_spec_trans st2 st4 st5 asg2 a4 a5 Hs24 Hs45) as Hs25.
      pose proof (step_spec_trans st2 st5 st6 asg2 a5 a6 Hs25 Hs56) as Hs26.
      exists (rbv_psn tr_u), st6, a6; split; [reflexivity | split; [exact Hs26 | split; [exact Hwf_trp |]]].
      cbn [andb]; unfold eval_rail_psn in Hev_trp; rewrite Hev_trp.
      cbn [eval_rail_psn rbv_psn orb andb] in *.
      rewrite (sat_eval_lit_false a5 st5 (proj2 (proj2 Hs45))), orb_false_l, orb_false_r.
      destruct (eval_rail_agree dw _ a3 a4 za (proj1 (proj2 Hs34))
                  (conj (conj Hw_za Hl_za) (conj Hb_za Hp_za))) as [_ Hza34].
      pose proof (@Integers.unsigned_range sz va) as Hur_a.
      pose proof (@Integers.unsigned_range sz vb) as Hur_b.
      assert (Hmod_le : (@Integers.modulus sz <= @Integers.modulus dw)%Z)
        by (rewrite !modulus_pow_sz; apply Z.pow_le_mono_r; unfold dw; lia).
      assert (Hu_za : @Integers.unsigned dw (eval_rail_val dw a4 za) = @Integers.unsigned sz va).
      { rewrite <- Hza34, Hval_za; apply @Integers.unsigned_repr; unfold Integers.max_unsigned; lia. }
      assert (Hu_zb : @Integers.unsigned dw (eval_rail_val dw a4 zb) = @Integers.unsigned sz vb).
      { rewrite Hval_zb; apply @Integers.unsigned_repr; unfold Integers.max_unsigned; lia. }
      set (prod_u := eval_rail_val dw a5 (mk_rail_bv dw ubits lit_false)).
      assert (Hprod_u_eq : prod_u = @Integers.repr dw (@Integers.unsigned sz va * @Integers.unsigned sz vb)).
      { unfold prod_u, eval_rail_val; cbn [rbv_bits]; apply @Integers.eqm_samerepr.
        rewrite Hku, Hl_zb, positive_nat_Z, <- modulus_pow_sz,
                <- (unsigned_eval_rail_val dw a4 za Hl_za),
                <- (unsigned_eval_rail_val dw a4 zb Hl_zb), Hu_za, Hu_zb.
        exists (- ku)%Z; ring. }
      assert (Hprod_rng : (0 <= @Integers.unsigned sz va * @Integers.unsigned sz vb < @Integers.modulus dw)%Z).
      { rewrite Hmod_dw; split; [nia |].
        apply Z.mul_lt_mono_nonneg; lia. }
      assert (Hu_prod : @Integers.unsigned dw prod_u =
                        (@Integers.unsigned sz va * @Integers.unsigned sz vb)%Z).
      { rewrite Hprod_u_eq; apply @Integers.unsigned_repr; unfold Integers.max_unsigned; lia. }
      change (eval_rail_val dw a5 (mk_rail_bv dw ubits lit_false)) with prod_u.
      rewrite Hu_prod; change (@Integers.repr sz (@Integers.unsigned sz va * @Integers.unsigned sz vb))
        with (@Integers.mul sz va vb).
      set (res := @Integers.mul sz va vb); set (ru := (@Integers.unsigned sz va * @Integers.unsigned sz vb)%Z).
      assert (Hle_res : (@Integers.unsigned sz res <= ru)%Z).
      { unfold res, Integers.mul; rewrite @Integers.unsigned_repr_eq; fold ru.
        pose proof (@Integers.modulus_pos sz) as Hmp.
        pose proof (Z_div_mod_eq_full ru (@Integers.modulus sz)) as Hdm.
        assert (Hq0 : (0 <= ru / @Integers.modulus sz)%Z) by (apply Z.div_pos; lia).
        nia. }
      rewrite Z.gtb_ltb.
      destruct (Z.eqb_spec (@Integers.unsigned sz res) ru),
               (Z.ltb_spec (@Integers.unsigned sz res) ru);
        cbn [negb]; try reflexivity; lia. }
    destruct Hnuw_step as (nuw_psn & st6 & asg6 & Hnuw_eq & Hs26 & Hwf_nuwp & Hev_nuwp).
    rewrite Hnuw_eq in Hbl; clear Hnuw_eq.
    pose proof (step_spec_trans st st2 st6 asg asg2 asg6 Hs02 Hs26) as Hs06.
    assert (Hnsw_step :
              exists nsw_psn st10 asg10,
                (if nsw then
                   let '(sa, st7) := blast_sext_rail sz dw a st6 in
                   let '(sb, st8) := blast_sext_rail sz dw b st7 in
                   let '(sbits, st9) := emit_mul_bits (rbv_bits sa) (rbv_bits sb) st8 in
                   let '(tr_s, st10) := blast_trunc_rail false true dw sz (mk_rail_bv dw sbits lit_false) st9 in
                   (rbv_psn tr_s, st10)
                 else (lit_false, st6)) = (nsw_psn, st10) /\
                step_spec st6 st10 asg6 asg10 /\
                wf_lit_bound (bs_next_var st10) nsw_psn /\
                eval_lit asg10 nsw_psn =
                  (nsw && ((@Integers.min_signed sz >? (@Integers.signed sz va * @Integers.signed sz vb))%Z ||
                           ((@Integers.signed sz va * @Integers.signed sz vb) >? @Integers.max_signed sz)%Z))).
    { destruct nsw; [| exists lit_false, st6, asg6; repeat split;
                        try exact (step_spec_refl st6 asg6 (proj2 (proj2 Hs06)));
                        [exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs06)))))
                         | exact (sat_eval_lit_false asg6 st6 (proj2 (proj2 Hs06)))]].
      destruct (blast_sext_rail sz dw a st6) as [sa st7] eqn:Esa.
      destruct (blast_sext_rail sz dw b st7) as [sb st8] eqn:Esb.
      destruct (emit_mul_bits (rbv_bits sa) (rbv_bits sb) st8) as [sbits st9] eqn:Esm.
      destruct (blast_trunc_rail false true dw sz (mk_rail_bv dw sbits lit_false) st9)
        as [tr_s st10] eqn:Etrs.
      destruct (blast_sext_rail_step sz dw a asg6 st6 sa st7 Hlt_dw (proj2 (proj2 Hs06))
                  (wf_rail_bound_mono _ _ _ a (proj1 Hs06) Hwa_f) Esa)
        as (a7 & Hs67 & Hwf_sa & _ & Hval_sa).
      pose proof (step_spec_trans st st6 st7 asg asg6 a7 Hs06 Hs67) as Hs07.
      destruct (blast_sext_rail_step sz dw b a7 st7 sb st8 Hlt_dw (proj2 (proj2 Hs67))
                  (wf_rail_bound_mono _ _ _ b (proj1 Hs07) Hwb_f) Esb)
        as (a8 & Hs78 & Hwf_sb & _ & Hval_sb).
      destruct (eval_rail_agree sz _ asg asg6 a (proj1 (proj2 Hs06)) Hwa_f) as [_ Hva6].
      destruct (eval_rail_agree sz _ asg a7 b (proj1 (proj2 Hs07)) Hwb_f) as [_ Hvb7].
      rewrite <- Hva6 in Hval_sa; rewrite <- Hvb7 in Hval_sb; fold va in Hval_sa; fold vb in Hval_sb.
      destruct Hwf_sa as ([Hw_sa Hl_sa] & Hb_sa & Hp_sa).
      destruct Hwf_sb as ([Hw_sb Hl_sb] & Hb_sb & Hp_sb).
      destruct (emit_mul_bits_step (rbv_bits sa) (rbv_bits sb) a8 st8 sbits st9
                  (proj2 (proj2 Hs78))
                  (wf_lits_bound_mono _ _ _ (proj1 Hs78) Hb_sa) Hb_sb Esm)
        as (a9 & Hs89 & Hlen_sb & Hwf_sb_b & ks & Hks).
      assert (Hwf_rs : wf_rail_bound dw (bs_next_var st9) (mk_rail_bv dw sbits lit_false)).
      { split; [split; [reflexivity | cbn; congruence] |
                split; [exact Hwf_sb_b
                        | exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs89)))))]]. }
      destruct (blast_trunc_rail_step false true dw sz (mk_rail_bv dw sbits lit_false)
                  a9 st9 tr_s st10 Hlt_dw (proj2 (proj2 Hs89)) Hwf_rs Etrs)
        as (a10 & Hs910 & (_ & _ & Hwf_trp) & Hev_trp & _).
      pose proof (step_spec_trans st6 st7 st8 asg6 a7 a8 Hs67 Hs78) as Hs68.
      pose proof (step_spec_trans st6 st8 st9 asg6 a8 a9 Hs68 Hs89) as Hs69.
      pose proof (step_spec_trans st6 st9 st10 asg6 a9 a10 Hs69 Hs910) as Hs610.
      exists (rbv_psn tr_s), st10, a10; split; [reflexivity | split; [exact Hs610 | split; [exact Hwf_trp |]]].
      cbn [andb]; unfold eval_rail_psn in Hev_trp; rewrite Hev_trp.
      cbn [eval_rail_psn rbv_psn orb andb] in *.
      rewrite (sat_eval_lit_false a9 st9 (proj2 (proj2 Hs89))), orb_false_l.
      destruct (eval_rail_agree dw _ a7 a8 sa (proj1 (proj2 Hs78))
                  (conj (conj Hw_sa Hl_sa) (conj Hb_sa Hp_sa))) as [_ Hsa78].
      set (H := @Integers.half_modulus sz).
      assert (HH2 : (2 <= H)%Z).
      { pose proof (@Integers.half_modulus_modulus sz) as Hhm; fold H in Hhm.
        rewrite modulus_pow_sz in Hhm.
        replace (Z.pos sz) with (2 + (Z.pos sz - 2))%Z in Hhm by lia.
        rewrite Z.pow_add_r in Hhm by lia.
        pose proof (Z.pow_pos_nonneg 2 (Z.pos sz - 2)); lia. }
      assert (Hhm_dw : @Integers.half_modulus dw = (2 * H * H)%Z).
      { pose proof (@Integers.half_modulus_modulus dw) as Hhd.
        pose proof (@Integers.half_modulus_modulus sz) as Hhs; fold H in Hhs.
        rewrite Hmod_dw in Hhd; nia. }
      pose proof (@Integers.signed_range sz va) as Hsr_a.
      pose proof (@Integers.signed_range sz vb) as Hsr_b.
      unfold Integers.min_signed, Integers.max_signed in Hsr_a, Hsr_b; fold H in Hsr_a, Hsr_b.
      assert (Hs_sa : @Integers.signed dw (eval_rail_val dw a8 sa) = @Integers.signed sz va).
      { rewrite <- Hsa78, Hval_sa; apply @Integers.signed_repr.
        unfold Integers.min_signed, Integers.max_signed; rewrite Hhm_dw; nia. }
      assert (Hs_sb : @Integers.signed dw (eval_rail_val dw a8 sb) = @Integers.signed sz vb).
      { rewrite Hval_sb; apply @Integers.signed_repr.
        unfold Integers.min_signed, Integers.max_signed; rewrite Hhm_dw; nia. }
      set (rs := (@Integers.signed sz va * @Integers.signed sz vb)%Z).
      set (prod_s := eval_rail_val dw a9 (mk_rail_bv dw sbits lit_false)).
      assert (Hprod_s_eq : prod_s = @Integers.repr dw rs).
      { unfold prod_s, eval_rail_val; cbn [rbv_bits].
        assert (Hm_eq : @Integers.repr dw (bools_to_Z (List.map (eval_lit a9) sbits)) =
                        @Integers.mul dw (eval_rail_val dw a8 sa) (eval_rail_val dw a8 sb)).
        { unfold Integers.mul; apply @Integers.eqm_samerepr.
          rewrite Hks, Hl_sb, positive_nat_Z, <- modulus_pow_sz,
                  <- (unsigned_eval_rail_val dw a8 sa Hl_sa),
                  <- (unsigned_eval_rail_val dw a8 sb Hl_sb).
          exists (- ks)%Z; ring. }
        rewrite Hm_eq, mul_eq_repr_signed, Hs_sa, Hs_sb; reflexivity. }
      assert (Hrs_rng : (@Integers.min_signed dw <= rs <= @Integers.max_signed dw)%Z).
      { unfold Integers.min_signed, Integers.max_signed, rs; rewrite Hhm_dw.
        destruct (Z_le_gt_dec 0 (@Integers.signed sz va)),
                 (Z_le_gt_dec 0 (@Integers.signed sz vb)); nia. }
      assert (Hs_prod : @Integers.signed dw prod_s = rs)
        by (rewrite Hprod_s_eq; exact (@Integers.signed_repr dw rs Hrs_rng)).
      assert (Hres_s_eq : @Integers.repr sz (@Integers.unsigned dw prod_s) = @Integers.repr sz rs).
      { rewrite Hprod_s_eq, @Integers.unsigned_repr_eq.
        apply @Integers.eqm_samerepr.
        pose proof (Z_div_mod_eq_full rs (@Integers.modulus dw)) as Hdm.
        rewrite Hmod_dw in Hdm.
        exists (- (@Integers.modulus sz * (rs / (@Integers.modulus sz * @Integers.modulus sz))))%Z.
        lia. }
      change (eval_rail_val dw a9 (mk_rail_bv dw sbits lit_false)) with prod_s.
      rewrite Hres_s_eq, Hs_prod; exact (signed_repr_neq_iff_oob sz rs). }
    destruct Hnsw_step as (nsw_psn & st10 & asg10 & Hnsw_eq & Hs610 & Hwf_nswp & Hev_nswp).
    rewrite Hnsw_eq in Hbl; clear Hnsw_eq.
    destruct (emit_or2_opt nuw_psn nsw_psn st10) as [ov_psn st11] eqn:Eov.
    destruct (emit_or2_opt base_psn ov_psn st11) as [psn st12] eqn:Ep.
    inversion Hbl; subst out st12; clear Hbl.
    destruct (emit_or2_opt_step asg10 nuw_psn nsw_psn st10 ov_psn st11 (proj2 (proj2 Hs610))
                (wf_lit_bound_mono _ _ _ (proj1 Hs610) Hwf_nuwp) Hwf_nswp Eov)
      as (asg11 & Hs1011 & Hwf_ov & Hev_ov).
    pose proof (step_spec_trans st2 st6 st10 asg2 asg6 asg10 Hs26 Hs610) as Hs210.
    pose proof (step_spec_trans st2 st10 st11 asg2 asg10 asg11 Hs210 Hs1011) as Hs211.
    destruct (emit_or2_opt_step asg11 base_psn ov_psn st11 psn st' (proj2 (proj2 Hs1011))
                (wf_lit_bound_mono _ _ _ (proj1 Hs211) Hwf_bp) Hwf_ov Ep)
      as (asg12 & Hs1112 & Hwf_p & Hev_p).
    pose proof (step_spec_trans st2 st11 st' asg2 asg11 asg12 Hs211 Hs1112) as Hs212.
    pose proof (step_spec_trans st1 st2 st' asg1 asg2 asg12 Hs2 Hs212) as Hs112.
    pose proof (step_spec_trans st st1 st' asg asg1 asg12 Hs1 Hs112) as Hs012.
    exists asg12; split; [exact Hs012 | split].
    + split; [split; [reflexivity | cbn; congruence] |
              split; [exact (wf_lits_bound_mono _ _ prod_bits (proj1 Hs112) Hwf_pb) | exact Hwf_p]].
    + split.
      * unfold eval_rail_psn; rewrite Esz_gt1, Hev_p,
          (step_spec_eval_lit st2 st11 asg2 asg11 base_psn Hs211 Hwf_bp),
          Hev_bp,
          (step_spec_eval_lit st st1 asg asg1 (rbv_psn a) Hs1 Hpa),
          (step_spec_eval_lit st st1 asg asg1 (rbv_psn b) Hs1 Hpb),
          Hev_ov,
          (step_spec_eval_lit st6 st10 asg6 asg10 nuw_psn Hs610 Hwf_nuwp),
          Hev_nuwp, Hev_nswp; reflexivity.
      * unfold eval_rail_val; cbn [rbv_bits];
          rewrite (step_spec_eval_lits st1 st' asg1 asg12 prod_bits Hs112 Hwf_pb); exact Hval_pb.
Qed.

(** *** 7.4 Unified Operator-Level Relational Step Lemmas *)

Definition blast_binop_rail
  (op : cert_binop) (fl : cert_binop_flags) (sz : positive)
  (rl rr : rail_bv) (st : blast_state) : option (rail_bv * blast_state) :=
  match op with
  | CB_And  => Some (blast_and_rail_opt sz rl rr st)
  | CB_Or   => Some (blast_or_disjoint_rail (cbf_disjoint fl) sz rl rr st)
  | CB_Xor  => Some (blast_xor_rail_opt sz rl rr st)
  | CB_Add  => Some (blast_add_rail (cbf_nuw fl) (cbf_nsw fl) sz rl rr st)
  | CB_Sub  => Some (blast_sub_rail (cbf_nuw fl) (cbf_nsw fl) sz rl rr st)
  | CB_Mul  =>
      if (sz <=? 12)%positive || is_const_rail rl || is_const_rail rr
      then Some (blast_mul_rail (cbf_nuw fl) (cbf_nsw fl) sz rl rr st)
      else None
  | CB_Shl  =>
      if (sz <=? 64)%positive
      then Some (blast_shl_rail (cbf_nuw fl) (cbf_nsw fl) sz rl rr st)
      else None
  | CB_LShr =>
      if (sz <=? 64)%positive
      then Some (blast_lshr_rail (cbf_exact fl) sz rl rr st)
      else None
  | CB_AShr =>
      if (sz <=? 64)%positive
      then Some (blast_ashr_rail (cbf_exact fl) sz rl rr st)
      else None
  | CB_UDiv | CB_SDiv | CB_URem | CB_SRem => None
  end.

Lemma dvalue_poison_or_int_rail :
  forall {Pa : Params} sz asg out (pcond : bool) (val : @Integers.bit_int sz),
    eval_rail_psn asg out = pcond ->
    (pcond = false -> eval_rail_val sz asg out = val) ->
    rail_matches_dvalue sz asg out
      (if pcond then DVALUE_Base DVALUE_Poison else DVALUE_Base (@DVALUE_I Pa sz val)).
Proof.
  intros Pa sz asg out pcond val Hp Hval; unfold rail_matches_dvalue; rewrite Hp.
  destruct pcond; [reflexivity | rewrite (Hval eq_refl); reflexivity].
Qed.

Lemma blast_binop_rail_sat :
  forall {Pa : Params} op fl sz rl rr asg st out st' (vl vr : @dvalue Pa),
    blast_binop_rail op fl sz rl rr st = Some (out, st') ->
    sat_blast_st asg st ->
    wf_rail_bound sz (bs_next_var st) rl ->
    wf_rail_bound sz (bs_next_var st) rr ->
    rail_matches_dvalue sz asg rl vl ->
    rail_matches_dvalue sz asg rr vr ->
    exists asg' vout,
      @eval_iop Pa (cert_to_ibinop op fl) vl vr = raise_ret vout /\
      step_spec st st' asg asg' /\
      wf_rail_bound sz (bs_next_var st') out /\
      rail_matches_dvalue sz asg' out vout.
Proof.
  intros Pa op fl sz rl rr asg st out st' vl vr Hbl Hsat Hwfl Hwfr Hml Hmr.
  unfold rail_matches_dvalue in Hml, Hmr.
  destruct op; cbn [blast_binop_rail] in Hbl; try discriminate Hbl.
  - (* CB_Add *)
    inversion Hbl as [Hrun]; clear Hbl.
    destruct (blast_add_rail_step (cbf_nuw fl) (cbf_nsw fl) sz rl rr asg st out st'
                Hsat Hwfl Hwfr Hrun)
      as (asg' & Hs & Hwf_out & Hpsn & Hval).
    destruct (eval_rail_psn asg rl) eqn:Epl, (eval_rail_psn asg rr) eqn:Epr; subst vl vr;
      try (exists asg', (DVALUE_Base DVALUE_Poison);
           split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
             unfold rail_matches_dvalue; rewrite Hpsn; cbn; reflexivity]]]).
    cbn [orb] in Hpsn.
    set (ov := ((cbf_nuw fl && @Integers.eq sz
                  (@Integers.add_carry sz (eval_rail_val sz asg rl) (eval_rail_val sz asg rr) (@Integers.zero sz))
                  (@Integers.one sz)) ||
                (cbf_nsw fl && @Integers.eq sz
                  (@Integers.add_overflow sz (eval_rail_val sz asg rl) (eval_rail_val sz asg rr) (@Integers.zero sz))
                  (@Integers.one sz)))) in *.
    exists asg', (if ov then DVALUE_Base DVALUE_Poison
                  else DVALUE_Base (@DVALUE_I Pa sz (@Integers.add sz (eval_rail_val sz asg rl) (eval_rail_val sz asg rr)))).
    split.
    + unfold eval_iop; rewrite eval_iop_integer_base_same_width; unfold cert_to_ibinop, eval_int_op; cbn.
      fold ov; destruct ov; reflexivity.
    + split; [exact Hs | split; [exact Hwf_out |
      exact (dvalue_poison_or_int_rail sz asg' out ov _ Hpsn (fun _ => Hval))]].
  - (* CB_Sub *)
    inversion Hbl as [Hrun]; clear Hbl.
    destruct (blast_sub_rail_step (cbf_nuw fl) (cbf_nsw fl) sz rl rr asg st out st'
                Hsat Hwfl Hwfr Hrun)
      as (asg' & Hs & Hwf_out & Hpsn & Hval).
    destruct (eval_rail_psn asg rl) eqn:Epl, (eval_rail_psn asg rr) eqn:Epr; subst vl vr;
      try (exists asg', (DVALUE_Base DVALUE_Poison);
           split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
             unfold rail_matches_dvalue; rewrite Hpsn; cbn; reflexivity]]]).
    cbn [orb] in Hpsn.
    set (ov := ((cbf_nuw fl && @Integers.eq sz
                  (@Integers.sub_borrow sz (eval_rail_val sz asg rl) (eval_rail_val sz asg rr) (@Integers.zero sz))
                  (@Integers.one sz)) ||
                (cbf_nsw fl && @Integers.eq sz
                  (@Integers.sub_overflow sz (eval_rail_val sz asg rl) (eval_rail_val sz asg rr) (@Integers.zero sz))
                  (@Integers.one sz)))) in *.
    exists asg', (if ov then DVALUE_Base DVALUE_Poison
                  else DVALUE_Base (@DVALUE_I Pa sz (@Integers.sub sz (eval_rail_val sz asg rl) (eval_rail_val sz asg rr)))).
    split.
    + unfold eval_iop; rewrite eval_iop_integer_base_same_width; unfold cert_to_ibinop, eval_int_op; cbn.
      fold ov; destruct ov; reflexivity.
    + split; [exact Hs | split; [exact Hwf_out |
      exact (dvalue_poison_or_int_rail sz asg' out ov _ Hpsn (fun _ => Hval))]].
  - (* CB_Mul *)
    destruct ((sz <=? 12)%positive || is_const_rail rl || is_const_rail rr); [| discriminate Hbl].
    inversion Hbl as [Hrun]; clear Hbl.
    destruct (blast_mul_rail_step (cbf_nuw fl) (cbf_nsw fl) sz rl rr asg st out st'
                Hsat Hwfl Hwfr Hrun)
      as (asg' & Hs & Hwf_out & Hpsn & Hval).
    destruct (eval_rail_psn asg rl) eqn:Epl, (eval_rail_psn asg rr) eqn:Epr; subst vl vr;
      try (exists asg', (DVALUE_Base DVALUE_Poison);
           split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
             unfold rail_matches_dvalue; rewrite Hpsn; cbn; reflexivity]]]).
    cbn [orb] in Hpsn.
    set (va := eval_rail_val sz asg rl) in *; set (vb := eval_rail_val sz asg rr) in *.
    set (ov := if Pos.eqb sz 1%positive then false
               else
                 ((cbf_nuw fl && ((@Integers.unsigned sz va * @Integers.unsigned sz vb) >?
                                  @Integers.unsigned sz (@Integers.mul sz va vb))%Z) ||
                  (cbf_nsw fl && ((@Integers.min_signed sz >? (@Integers.signed sz va * @Integers.signed sz vb))%Z ||
                                  ((@Integers.signed sz va * @Integers.signed sz vb) >? @Integers.max_signed sz)%Z)))) in *.
    exists asg', (if ov then DVALUE_Base DVALUE_Poison
                  else DVALUE_Base (@DVALUE_I Pa sz (@Integers.mul sz va vb))).
    split.
    + unfold eval_iop; rewrite eval_iop_integer_base_same_width; unfold cert_to_ibinop, eval_int_op;
        cbn [mbitwidth mdtyp_of_int option_pred mmin_signed mmax_signed mmul munsigned msigned
             VIntVMemInt VInt_Bounded bitwidth dtyp_base_eq_dec fmap dvp].
      unfold ov; destruct (Pos.eqb sz 1%positive); [reflexivity |].
      cbn; match goal with |- context [if ?b then _ else _] => destruct b; reflexivity end.
    + split; [exact Hs | split; [exact Hwf_out |
      exact (dvalue_poison_or_int_rail sz asg' out ov _ Hpsn (fun _ => Hval))]].
  - (* CB_Shl *)
    destruct (sz <=? 64)%positive; [| discriminate Hbl].
    inversion Hbl as [Hrun]; clear Hbl.
    destruct (blast_shl_rail_step (cbf_nuw fl) (cbf_nsw fl) sz rl rr asg st out st'
                Hsat Hwfl Hwfr Hrun)
      as (asg' & Hs & Hwf_out & Hpsn & Hval).
    destruct (eval_rail_psn asg rl) eqn:Epl, (eval_rail_psn asg rr) eqn:Epr; subst vl vr;
      try (exists asg', (DVALUE_Base DVALUE_Poison);
           split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
             unfold rail_matches_dvalue; rewrite Hpsn; cbn; reflexivity]]]).
    cbn [orb] in Hpsn; cbn zeta in Hpsn.
    set (va := eval_rail_val sz asg rl) in *; set (vb := eval_rail_val sz asg rr) in *.
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; unfold cert_to_ibinop, eval_int_op;
      cbn [mbitwidth mdtyp_of_int option_pred mshl munsigned mnegative
           VIntVMemInt VInt_Bounded bitwidth dtyp_base_eq_dec dvp].
    destruct (@Integers.unsigned sz vb >=? Z.pos sz)%Z eqn:Ege.
    + exists asg', (DVALUE_Base DVALUE_Poison).
      split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
        unfold rail_matches_dvalue; rewrite Hpsn; reflexivity]]].
    + set (res := @Integers.shl sz va vb) in *.
      set (nuw_p := cbf_nuw fl && (Z.shiftl (@Integers.unsigned sz va) (@Integers.unsigned sz vb) >?
                                   @Integers.unsigned sz res)%Z) in *.
      set (nsw_p := cbf_nsw fl && negb (Z.shiftr (@Integers.unsigned sz va)
                                                 (Z.pos sz - @Integers.unsigned sz vb) =?
                                        @Integers.unsigned sz (@Integers.negative sz res) *
                                        (2 ^ @Integers.unsigned sz vb - 1))%Z) in *.
      exists asg', (if nuw_p || nsw_p then DVALUE_Base DVALUE_Poison
                    else DVALUE_Base (@DVALUE_I Pa sz res)).
      split.
      * cbn [Monad.bind Monad_EOU Monad.ret]; fold res nuw_p.
        destruct nuw_p; [reflexivity |].
        cbn [orb]; unfold nsw_p; destruct (cbf_nsw fl); [| reflexivity].
        cbn [andb Monad.bind Monad_EOU];
          destruct (negb _); reflexivity.
      * split; [exact Hs | split; [exact Hwf_out |
        exact (dvalue_poison_or_int_rail sz asg' out (nuw_p || nsw_p) res Hpsn
                 (fun _ => Hval eq_refl))]].
  - (* CB_LShr *)
    destruct (sz <=? 64)%positive; [| discriminate Hbl].
    inversion Hbl as [Hrun]; clear Hbl.
    destruct (blast_lshr_rail_step (cbf_exact fl) sz rl rr asg st out st'
                Hsat Hwfl Hwfr Hrun)
      as (asg' & Hs & Hwf_out & Hpsn & Hval).
    destruct (eval_rail_psn asg rl) eqn:Epl, (eval_rail_psn asg rr) eqn:Epr; subst vl vr;
      try (exists asg', (DVALUE_Base DVALUE_Poison);
           split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
             unfold rail_matches_dvalue; rewrite Hpsn; cbn; reflexivity]]]).
    cbn [orb] in Hpsn; cbn zeta in Hpsn.
    set (va := eval_rail_val sz asg rl) in *; set (vb := eval_rail_val sz asg rr) in *.
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; unfold cert_to_ibinop, eval_int_op;
      cbn [mbitwidth mdtyp_of_int option_pred mshru munsigned dtyp_base_eqb negb
           VIntVMemInt VInt_Bounded bitwidth dvp].
    destruct (@Integers.unsigned sz vb >=? Z.pos sz)%Z eqn:Ege.
    + exists asg', (DVALUE_Base DVALUE_Poison).
      split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
        unfold rail_matches_dvalue; rewrite Hpsn; reflexivity]]].
    + set (ov := cbf_exact fl && negb ((@Integers.unsigned sz va mod (2 ^ @Integers.unsigned sz vb)) =? 0)%Z) in *.
      exists asg', (if ov then DVALUE_Base DVALUE_Poison
                    else DVALUE_Base (@DVALUE_I Pa sz (@Integers.shru sz va vb))).
      split; [cbn; fold ov; destruct ov; reflexivity |
      split; [exact Hs | split; [exact Hwf_out |
        exact (dvalue_poison_or_int_rail sz asg' out ov _ Hpsn (fun _ => Hval eq_refl))]]].
  - (* CB_AShr *)
    destruct (sz <=? 64)%positive; [| discriminate Hbl].
    inversion Hbl as [Hrun]; clear Hbl.
    destruct (blast_ashr_rail_step (cbf_exact fl) sz rl rr asg st out st'
                Hsat Hwfl Hwfr Hrun)
      as (asg' & Hs & Hwf_out & Hpsn & Hval).
    destruct (eval_rail_psn asg rl) eqn:Epl, (eval_rail_psn asg rr) eqn:Epr; subst vl vr;
      try (exists asg', (DVALUE_Base DVALUE_Poison);
           split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
             unfold rail_matches_dvalue; rewrite Hpsn; cbn; reflexivity]]]).
    cbn [orb] in Hpsn; cbn zeta in Hpsn.
    set (va := eval_rail_val sz asg rl) in *; set (vb := eval_rail_val sz asg rr) in *.
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; unfold cert_to_ibinop, eval_int_op;
      cbn [mbitwidth mdtyp_of_int option_pred mshr munsigned dtyp_base_eq_dec
           VIntVMemInt VInt_Bounded bitwidth dvp].
    destruct (@Integers.unsigned sz vb >=? Z.pos sz)%Z eqn:Ege.
    + exists asg', (DVALUE_Base DVALUE_Poison).
      split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
        unfold rail_matches_dvalue; rewrite Hpsn; reflexivity]]].
    + set (ov := cbf_exact fl && negb ((@Integers.unsigned sz va mod (2 ^ @Integers.unsigned sz vb)) =? 0)%Z) in *.
      exists asg', (if ov then DVALUE_Base DVALUE_Poison
                    else DVALUE_Base (@DVALUE_I Pa sz (@Integers.shr sz va vb))).
      split; [cbn; fold ov; destruct ov; reflexivity |
      split; [exact Hs | split; [exact Hwf_out |
        exact (dvalue_poison_or_int_rail sz asg' out ov _ Hpsn (fun _ => Hval eq_refl))]]].
  - (* CB_And *)
    inversion Hbl as [Hrun]; clear Hbl.
    destruct (blast_and_rail_opt_step sz rl rr asg st out st' Hsat Hwfl Hwfr Hrun)
      as (asg' & Hs & Hwf_out & Hpsn & Hval).
    destruct (eval_rail_psn asg rl) eqn:Epl, (eval_rail_psn asg rr) eqn:Epr; subst vl vr;
      try (exists asg', (DVALUE_Base DVALUE_Poison);
           split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
             unfold rail_matches_dvalue; rewrite Hpsn; cbn; reflexivity]]]).
    exists asg', (DVALUE_Base (@DVALUE_I Pa sz (@Integers.and sz (eval_rail_val sz asg rl) (eval_rail_val sz asg rr)))).
    split; [unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity |
    split; [exact Hs | split; [exact Hwf_out |
      unfold rail_matches_dvalue; rewrite Hpsn, Hval; reflexivity]]].
  - (* CB_Or *)
    inversion Hbl as [Hrun]; clear Hbl.
    destruct (blast_or_disjoint_rail_step (cbf_disjoint fl) sz rl rr asg st out st'
                Hsat Hwfl Hwfr Hrun)
      as (asg' & Hs & Hwf_out & Hpsn & Hval).
    destruct (eval_rail_psn asg rl) eqn:Epl, (eval_rail_psn asg rr) eqn:Epr; subst vl vr;
      try (exists asg', (DVALUE_Base DVALUE_Poison);
           split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
             unfold rail_matches_dvalue; rewrite Hpsn; cbn; reflexivity]]]).
    cbn [orb] in Hpsn.
    set (va := eval_rail_val sz asg rl) in *; set (vb := eval_rail_val sz asg rr) in *.
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; unfold cert_to_ibinop, eval_int_op; cbn.
    destruct (cbf_disjoint fl); cbn [andb] in *.
    + destruct (@Integers.eq sz (@Integers.or sz va vb) (@Integers.xor sz va vb)) eqn:Eox; cbn [negb] in Hpsn.
      * exists asg', (DVALUE_Base (@DVALUE_I Pa sz (@Integers.or sz va vb))).
        split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
          unfold rail_matches_dvalue; rewrite Hpsn, Hval; reflexivity]]].
      * exists asg', (DVALUE_Base DVALUE_Poison).
        split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
          unfold rail_matches_dvalue; rewrite Hpsn; reflexivity]]].
    + exists asg', (DVALUE_Base (@DVALUE_I Pa sz (@Integers.or sz va vb))).
      split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
        unfold rail_matches_dvalue; rewrite Hpsn, Hval; reflexivity]]].
  - (* CB_Xor *)
    inversion Hbl as [Hrun]; clear Hbl.
    destruct (blast_xor_rail_opt_step sz rl rr asg st out st' Hsat Hwfl Hwfr Hrun)
      as (asg' & Hs & Hwf_out & Hpsn & Hval).
    destruct (eval_rail_psn asg rl) eqn:Epl, (eval_rail_psn asg rr) eqn:Epr; subst vl vr;
      try (exists asg', (DVALUE_Base DVALUE_Poison);
           split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
             unfold rail_matches_dvalue; rewrite Hpsn; cbn; reflexivity]]]).
    exists asg', (DVALUE_Base (@DVALUE_I Pa sz (@Integers.xor sz (eval_rail_val sz asg rl) (eval_rail_val sz asg rr)))).
    split; [unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity |
    split; [exact Hs | split; [exact Hwf_out |
      unfold rail_matches_dvalue; rewrite Hpsn, Hval; reflexivity]]].
Qed.

Definition cert_icmp_to_signed_comp (pr : cert_icmp_pred) : bool * Integers.comparison :=
  match pr with
  | CIP_Eq  => (false, Integers.Ceq)
  | CIP_Ne  => (false, Integers.Cne)
  | CIP_Ult => (false, Integers.Clt)
  | CIP_Ule => (false, Integers.Cle)
  | CIP_Ugt => (false, Integers.Cgt)
  | CIP_Uge => (false, Integers.Cge)
  | CIP_Slt => (true,  Integers.Clt)
  | CIP_Sle => (true,  Integers.Cle)
  | CIP_Sgt => (true,  Integers.Cgt)
  | CIP_Sge => (true,  Integers.Cge)
  end.

Lemma msamesign_negb_eq_xorb_msb : forall sz (x y : @Integers.bit_int sz),
  negb (@msamesign (@Integers.bit_int sz) _ x y) =
  xorb (msb_of sz x) (msb_of sz y).
Proof.
  intros sz x y; cbn [msamesign VIntVMemInt VInt_Bounded samesign Integers.cmp].
  rewrite (lt_zero_eq_msb sz x), (lt_zero_eq_msb sz y).
  destruct (msb_of sz x), (msb_of sz y); reflexivity.
Qed.

Lemma blast_icmp_pred_sat :
  forall {Pa : Params} pr ss sz rl rr asg st out st' (vl vr : @dvalue Pa),
    let '(is_s, c) := cert_icmp_to_signed_comp pr in
    blast_icmp_rail ss is_s c sz rl rr st = (out, st') ->
    sat_blast_st asg st ->
    wf_rail_bound sz (bs_next_var st) rl ->
    wf_rail_bound sz (bs_next_var st) rr ->
    rail_matches_dvalue sz asg rl vl ->
    rail_matches_dvalue sz asg rr vr ->
    exists asg' vout,
      @eval_icmp Pa ss (cert_to_icmp pr) vl vr = raise_ret vout /\
      step_spec st st' asg asg' /\
      wf_rail_bound 1%positive (bs_next_var st') out /\
      rail_matches_dvalue 1%positive asg' out vout.
Proof.
  intros Pa pr ss sz rl rr asg st out st' vl vr.
  destruct (cert_icmp_to_signed_comp pr) as [is_s c] eqn:Esc.
  intros Hbl Hsat Hwfl Hwfr Hml Hmr.
  destruct (blast_icmp_rail_step ss is_s c sz rl rr asg st out st' Hsat Hwfl Hwfr Hbl)
    as (asg' & Hs & Hwf_out & Hpsn & Hval).
  unfold rail_matches_dvalue in Hml, Hmr.
  destruct (eval_rail_psn asg rl) eqn:Epl, (eval_rail_psn asg rr) eqn:Epr; subst vl vr;
    try (exists asg', (DVALUE_Base DVALUE_Poison);
         split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
           unfold rail_matches_dvalue; rewrite Hpsn; cbn; reflexivity]]]).
  cbn [orb] in Hpsn.
  set (va := eval_rail_val sz asg rl) in *; set (vb := eval_rail_val sz asg rr) in *.
  rewrite <- (msamesign_negb_eq_xorb_msb sz va vb) in Hpsn.
  set (ssp := ss && negb (@msamesign (@Integers.bit_int sz) _ va vb)) in *.
  set (cb := if is_s then @Integers.cmp sz c va vb else @Integers.cmpu sz c va vb) in *.
  exists asg', (if ssp then DVALUE_Base DVALUE_Poison
                else DVALUE_Base (@DVALUE_I Pa 1%positive
                                  (if cb then @Integers.one 1%positive else @Integers.zero 1%positive))).
  split.
  - unfold eval_icmp; rewrite eval_icmp_base_same_width.
    assert (Hcmp_eq :
              @eval_int_icmp (@Integers.bit_int sz) _ ss (cert_to_icmp pr) va vb =
              raise_ret (if ssp then DVALUE_Poison
                         else if cb then @DVALUE_I Pa 1%positive (@Integers.one 1%positive)
                         else @DVALUE_I Pa 1%positive (@Integers.zero 1%positive))).
    { destruct pr; cbn in Esc; inversion Esc; subst is_s c;
        unfold cert_to_icmp, eval_int_icmp; cbn; fold ssp cb; destruct ssp, cb; reflexivity. }
    rewrite Hcmp_eq; destruct ssp, cb; reflexivity.
  - split; [exact Hs | split; [exact Hwf_out |
    exact (dvalue_poison_or_int_rail 1%positive asg' out ssp _ Hpsn (fun _ => Hval))]].
Qed.

Definition blast_cast_op
  (k : cert_cast_kind) (fw tw : positive) (fl : cert_cast_flags)
  (ro : rail_bv) (st : blast_state) : rail_bv * blast_state :=
  match k with
  | CCK_ZExt  => blast_zext_rail (ccf_nneg fl) fw tw ro st
  | CCK_SExt  => blast_sext_rail fw tw ro st
  | CCK_Trunc => blast_trunc_rail (ccf_nuw fl) (ccf_nsw fl) fw tw ro st
  end.

Lemma blast_cast_op_sat :
  forall {Pa : Params} k fw tw fl ro asg st out st' (vo : @dvalue Pa),
    match k with
    | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg fl) && negb (ccf_nuw fl) && negb (ccf_nsw fl)
    | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg fl)
    end = true ->
    blast_cast_op k fw tw fl ro st = (out, st') ->
    sat_blast_st asg st ->
    wf_rail_bound fw (bs_next_var st) ro ->
    rail_matches_dvalue fw asg ro vo ->
    exists asg' vout,
      @convert_pure Pa (cert_to_pure_conv k fl)
        (DTYPE_Base (DTYPE_I fw)) vo (DTYPE_Base (DTYPE_I tw)) = raise_ret vout /\
      step_spec st st' asg asg' /\
      wf_rail_bound tw (bs_next_var st') out /\
      rail_matches_dvalue tw asg' out vout.
Proof.
  intros Pa k fw tw fl ro asg st out st' vo Hk Hbl Hsat Hwfo Hmo.
  unfold rail_matches_dvalue in Hmo.
  destruct k; cbn [blast_cast_op] in Hbl; rewrite !andb_true_iff in Hk.
  - (* CCK_ZExt *)
    destruct Hk as ([Hlt _] & _).
    pose proof (proj1 (Pos.ltb_lt fw tw) Hlt) as Hlt_p.
    destruct (blast_zext_rail_step (ccf_nneg fl) fw tw ro asg st out st' Hlt_p Hsat Hwfo Hbl)
      as (asg' & Hs & Hwf_out & Hpsn & Hval).
    destruct (eval_rail_psn asg ro) eqn:Epo; subst vo.
    + exists asg', (DVALUE_Base DVALUE_Poison);
        split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
          unfold rail_matches_dvalue; rewrite Hpsn; reflexivity]]].
    + cbn [orb] in Hpsn.
      set (va := eval_rail_val fw asg ro) in *.
      set (ov := ccf_nneg fl && (@Integers.signed fw va <? 0)%Z) in *.
      exists asg', (if ov then DVALUE_Base DVALUE_Poison
                    else DVALUE_Base (@DVALUE_I Pa tw (@Integers.repr tw (@Integers.unsigned fw va)))).
      split.
      * cbn; rewrite Pos.eqb_refl, Hlt; cbn; fold ov; destruct ov; reflexivity.
      * split; [exact Hs | split; [exact Hwf_out |
        exact (dvalue_poison_or_int_rail tw asg' out ov _ Hpsn (fun _ => Hval))]].
  - (* CCK_SExt *)
    destruct Hk as (([Hlt _] & _) & _).
    pose proof (proj1 (Pos.ltb_lt fw tw) Hlt) as Hlt_p.
    destruct (blast_sext_rail_step fw tw ro asg st out st' Hlt_p Hsat Hwfo Hbl)
      as (asg' & Hs & Hwf_out & Hpsn & Hval).
    destruct (eval_rail_psn asg ro) eqn:Epo; subst vo.
    + exists asg', (DVALUE_Base DVALUE_Poison);
        split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
          unfold rail_matches_dvalue; rewrite Hpsn, Epo; reflexivity]]].
    + exists asg', (DVALUE_Base (@DVALUE_I Pa tw (@Integers.repr tw (@Integers.signed fw (eval_rail_val fw asg ro))))).
      split; [cbn; rewrite Pos.eqb_refl, Hlt; reflexivity |
      split; [exact Hs | split; [exact Hwf_out |
        unfold rail_matches_dvalue; rewrite Hpsn, Epo, Hval; reflexivity]]].
  - (* CCK_Trunc *)
    destruct Hk as [Hlt _].
    pose proof (proj1 (Pos.ltb_lt tw fw) Hlt) as Hlt_p.
    destruct (blast_trunc_rail_step (ccf_nuw fl) (ccf_nsw fl) fw tw ro asg st out st' Hlt_p Hsat Hwfo Hbl)
      as (asg' & Hs & Hwf_out & Hpsn & Hval).
    destruct (eval_rail_psn asg ro) eqn:Epo; subst vo.
    + exists asg', (DVALUE_Base DVALUE_Poison);
        split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
          unfold rail_matches_dvalue; rewrite Hpsn; reflexivity]]].
    + cbn [orb] in Hpsn.
      set (va := eval_rail_val fw asg ro) in *.
      set (res := @Integers.repr tw (@Integers.unsigned fw va)) in *.
      set (ov := (ccf_nuw fl && negb (Z.eqb (@Integers.unsigned tw res) (@Integers.unsigned fw va))) ||
                 (ccf_nsw fl && negb (Z.eqb (@Integers.signed tw res) (@Integers.signed fw va)))) in *.
      exists asg', (if ov then DVALUE_Base DVALUE_Poison
                    else DVALUE_Base (@DVALUE_I Pa tw res)).
      split.
      * cbn; rewrite Pos.eqb_refl, Hlt; cbn; fold res ov; destruct ov; reflexivity.
      * split; [exact Hs | split; [exact Hwf_out |
        exact (dvalue_poison_or_int_rail tw asg' out ov res Hpsn (fun _ => Hval))]].
Qed.

(** *** 7.5 Verified 2-Rail [select], $O(|V|)$ [CE_Let] DAG Blasting & [ub_ctx] Clause Encoding *)

Lemma eq_one_eqb_unsigned : forall ic : @Integers.bit_int 1%positive,
  (@Integers.unsigned 1%positive ic =? 1)%Z =
  @Integers.eq 1%positive ic (@Integers.one 1%positive).
Proof.
  intros ic; unfold Integers.eq, Numeric.Rocqlib.zeq.
  rewrite (@Integers.unsigned_one 1%positive).
  destruct (Z.eqb_spec (@Integers.unsigned 1%positive ic) 1%Z),
           (Z.eq_dec (@Integers.unsigned 1%positive ic) 1%Z);
    try reflexivity; lia.
Qed.

Lemma blast_select_op_sat :
  forall {Pa : Params} w rc rt rf asg st out st' (vc vt vf : @dvalue Pa),
    blast_select_rail_opt w rc rt rf st = (out, st') ->
    sat_blast_st asg st ->
    wf_rail_bound 1%positive (bs_next_var st) rc ->
    wf_rail_bound w (bs_next_var st) rt ->
    wf_rail_bound w (bs_next_var st) rf ->
    rail_matches_dvalue 1%positive asg rc vc ->
    rail_matches_dvalue w asg rt vt ->
    rail_matches_dvalue w asg rf vf ->
    exists asg' vout,
      @eval_select Pa vc (DTYPE_Base (DTYPE_I w)) vt vf = raise_ret vout /\
      step_spec st st' asg asg' /\
      wf_rail_bound w (bs_next_var st') out /\
      rail_matches_dvalue w asg' out vout.
Proof.
  intros Pa w rc rt rf asg st out st' vc vt vf Hbl Hsat Hwfc Hwft Hwff Hmc Hmt Hmf.
  destruct (blast_select_rail_opt_step w rc rt rf asg st out st' Hsat Hwfc Hwft Hwff Hbl)
    as (asg' & Hs & Hwf_out & Hpsn & Hval).
  unfold rail_matches_dvalue in Hmc.
  destruct (eval_rail_psn asg rc) eqn:Epc; subst vc.
  - exists asg', (DVALUE_Base DVALUE_Poison);
      split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
        unfold rail_matches_dvalue; rewrite Hpsn; reflexivity]]].
  - cbn [orb] in Hpsn.
    set (cond_b := @Integers.eq 1%positive (eval_rail_val 1%positive asg rc) (@Integers.one 1%positive))
      in Hpsn, Hval |- *.
    exists asg', (if cond_b then vt else vf).
    split.
    + cbn; rewrite eq_one_eqb_unsigned; fold cond_b; destruct cond_b; reflexivity.
    + split; [exact Hs | split; [exact Hwf_out |]].
      unfold rail_matches_dvalue in *; rewrite Hpsn, Hval.
      destruct cond_b; [exact Hmt | exact Hmf].
Qed.

Lemma rail_matches_wf_scalar :
  forall {Pa : Params} w asg r (dv : @dvalue Pa),
    rail_matches_dvalue w asg r dv ->
    wf_scalar_dvalue w dv.
Proof.
  intros Pa w asg r dv Hm; unfold rail_matches_dvalue in Hm.
  destruct (eval_rail_psn asg r); [left; exact Hm | right; eexists; exact Hm].
Qed.

Record blast_env := mk_blast_env {
  be_st      : blast_state;
  be_vars    : list (string * positive * rail_bv);
  be_freezes : list (positive * cert_expr * list lit)
}.

Fixpoint lookup_blast_var
  (vs : list (string * positive * rail_bv)) (nm : string) (w : positive)
  {struct vs} : option rail_bv :=
  match vs with
  | [] => None
  | (nm', w', r) :: rest =>
      if String.eqb nm nm' && Pos.eqb w w'
      then Some r
      else lookup_blast_var rest nm w
  end.

Fixpoint lookup_blast_freeze
  (fs : list (positive * cert_expr * list lit)) (w : positive) (key : cert_expr)
  {struct fs} : option (list lit) :=
  match fs with
  | [] => None
  | (w', key', fbits) :: rest =>
      if Pos.eqb w w' && cert_expr_eqb key key'
      then Some fbits
      else lookup_blast_freeze rest w key
  end.

Definition sat_blast_env {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (asg : positive -> bool) (env : blast_env) : Prop :=
  sat_blast_st asg (be_st env) /\
  (forall nm w r,
     lookup_blast_var (be_vars env) nm w = Some r ->
     wf_rail_bound w (bs_next_var (be_st env)) r /\
     exists dv,
       penv nm = Some dv /\
       wf_scalar_dvalue w dv /\
       rail_matches_dvalue w asg r dv) /\
  (forall w key fbits,
     lookup_blast_freeze (be_freezes env) w key = Some fbits ->
     List.length fbits = Pos.to_nat w /\
     wf_lits_bound (bs_next_var (be_st env)) fbits /\
     List.map (eval_lit asg) fbits =
       bit_int_to_bools w (@Integers.repr w (foracle w key))).

Lemma sat_blast_env_step :
  forall {Pa : Params} (penv : param_env Pa) (foracle : freeze_oracle)
         asg asg' env st',
    sat_blast_env penv foracle asg env ->
    step_spec (be_st env) st' asg asg' ->
    sat_blast_env penv foracle asg'
      (mk_blast_env st' (be_vars env) (be_freezes env)).
Proof.
  intros Pa penv foracle asg asg' env st' (_ & Hvars & Hfrzs) (Hle & Hag & Hsat');
    cbn [be_st be_vars be_freezes].
  split; [exact Hsat' | split].
  - intros nm w r Hlk.
    destruct (Hvars nm w r Hlk) as (Hwf_r & dv & Hpm & Hwfdv & Hrm).
    split; [exact (wf_rail_bound_mono w _ _ r Hle Hwf_r) |].
    exists dv; split; [exact Hpm | split; [exact Hwfdv |
      exact (rail_matches_dvalue_agree w _ asg asg' r dv Hag Hwf_r Hrm)]].
  - intros w key fbits Hlk.
    destruct (Hfrzs w key fbits Hlk) as (Hflen & Hfwf & Hfmap).
    split; [exact Hflen | split; [exact (wf_lits_bound_mono _ _ fbits Hle Hfwf) |]].
    rewrite <- (eval_lits_agree _ asg asg' fbits Hag Hfwf); exact Hfmap.
Qed.

Definition let_rail_env : Type := list (string * (positive * rail_bv)).

Fixpoint lookup_let_rail (lr : let_rail_env) (nm : string) {struct lr}
  : option (positive * rail_bv) :=
  match lr with
  | [] => None
  | (k, v) :: rest =>
      if String.eqb k nm then Some v else lookup_let_rail rest nm
  end.

Section HasFreezeBinds.
  Variable ehf : cert_expr -> bool.

  Fixpoint has_freeze_binds (xs : list (string * cert_expr)) {struct xs} : bool :=
    match xs with
    | [] => false
    | (_, be) :: rest => ehf be || has_freeze_binds rest
    end.
End HasFreezeBinds.

Fixpoint expr_has_freeze (e : cert_expr) {struct e} : bool :=
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ => false
  | CE_BinOp _ _ _ l r | CE_ICmp _ _ _ l r =>
      expr_has_freeze l || expr_has_freeze r
  | CE_Cast _ _ _ _ o => expr_has_freeze o
  | CE_Select _ c t f =>
      expr_has_freeze c || expr_has_freeze t || expr_has_freeze f
  | CE_Freeze _ _ => true
  | CE_Let bs body =>
      has_freeze_binds expr_has_freeze bs || expr_has_freeze body
  end.

Section BlastLetBinds.
  Variable bl_e :
    let_rail_env -> option (sized_let_map * nat) -> cert_expr -> blast_env ->
    option (rail_bv * blast_env).

  Fixpoint blast_let_binds
    (cur_lr : let_rail_env)
    (cur_ms : option (sized_let_map * nat))
    (xs : list (string * cert_expr))
    (env : blast_env)
    {struct xs}
    : option (let_rail_env * option (sized_let_map * nat) * blast_env) :=
    match xs with
    | [] => Some (cur_lr, cur_ms, env)
    | (bnm, be) :: rest =>
        match bl_e cur_lr cur_ms be env with
        | Some (r_be, env1) =>
            let next_ms_opt :=
                match cur_ms with
                | None => Some None
                | Some (ms, fuel) =>
                    match expand_lets_fueled_with ms be fuel with
                    | Some (ebe, bsz, fuel1) =>
                        Some (Some ((bnm, (ebe, bsz)) :: ms, fuel1))
                    | None => None
                    end
                end in
            match next_ms_opt with
            | Some next_ms =>
                blast_let_binds
                  ((bnm, (cert_expr_bit_width be, r_be)) :: cur_lr)
                  next_ms rest env1
            | None => None
            end
        | None => None
        end
    end.
End BlastLetBinds.

Fixpoint blast_cert_expr
  (ctx : ub_ctx)
  (lr : let_rail_env)
  (ms_opt : option (sized_let_map * nat))
  (e : cert_expr)
  (env : blast_env)
  {struct e} : option (rail_bv * blast_env) :=
  match e with
  | CE_BvConst w val =>
      Some (blast_const_rail w val, env)
  | CE_Poison w =>
      Some (blast_poison_rail w, env)
  | CE_Var nm w =>
      match lookup_let_rail lr nm with
      | Some (rw, r) =>
          if Pos.eqb rw w then Some (r, env) else None
      | None =>
          match lookup_blast_var (be_vars env) nm w with
          | Some r => Some (r, env)
          | None =>
              let '(bits, st1) :=
                  alloc_aligned_bits (ctx_ptr_low_bit_zero ctx nm w) 0%nat (Pos.to_nat w) (be_st env) in
              let '(psn, st2) :=
                  if ctx_has_var_nonpoison ctx nm w
                  then (lit_false, st1)
                  else alloc_var st1 in
              let r := mk_rail_bv w bits psn in
              Some (r, mk_blast_env st2 ((nm, w, r) :: be_vars env) (be_freezes env))
          end
      end
  | CE_BinOp op w fl l r =>
      match blast_cert_expr ctx lr ms_opt l env with
      | Some (rl, env1) =>
          match blast_cert_expr ctx lr ms_opt r env1 with
          | Some (rr, env2) =>
              match blast_binop_rail op fl w rl rr (be_st env2) with
              | Some (out, st3) =>
                  Some (out, mk_blast_env st3 (be_vars env2) (be_freezes env2))
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | CE_ICmp pr ss w l r =>
      match blast_cert_expr ctx lr ms_opt l env with
      | Some (rl, env1) =>
          match blast_cert_expr ctx lr ms_opt r env1 with
          | Some (rr, env2) =>
              let '(is_s, cmp_c) := cert_icmp_to_signed_comp pr in
              let '(out, st3) := blast_icmp_rail ss is_s cmp_c w rl rr (be_st env2) in
              Some (out, mk_blast_env st3 (be_vars env2) (be_freezes env2))
          | None => None
          end
      | None => None
      end
  | CE_Cast k fw tw fl o =>
      match blast_cert_expr ctx lr ms_opt o env with
      | Some (ro, env1) =>
          let '(out, st2) := blast_cast_op k fw tw fl ro (be_st env1) in
          Some (out, mk_blast_env st2 (be_vars env1) (be_freezes env1))
      | None => None
      end
  | CE_Select w c t f =>
      match blast_cert_expr ctx lr ms_opt c env with
      | Some (rc, env1) =>
          match blast_cert_expr ctx lr ms_opt t env1 with
          | Some (rt, env2) =>
              match blast_cert_expr ctx lr ms_opt f env2 with
              | Some (rf, env3) =>
                  let '(out, st4) := blast_select_rail_opt w rc rt rf (be_st env3) in
                  Some (out, mk_blast_env st4 (be_vars env3) (be_freezes env3))
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | CE_Freeze w o =>
      match ms_opt with
      | None => None
      | Some (ms, _) =>
          match expand_lets_fueled_with ms o default_let_expand_budget with
          | Some (key, _, _) =>
              match blast_cert_expr ctx lr ms_opt o env with
              | Some (ro, env1) =>
                  match lookup_blast_freeze (be_freezes env1) w key with
                  | Some fbits =>
                      let '(bits, st2) :=
                          mux_bits_list_opt (rbv_psn ro) fbits (rbv_bits ro) (be_st env1) in
                      Some (mk_rail_bv w bits lit_false,
                            mk_blast_env st2 (be_vars env1) (be_freezes env1))
                  | None =>
                      let '(fbits, st2) := alloc_fresh_bits (Pos.to_nat w) (be_st env1) in
                      let '(bits, st3) :=
                          mux_bits_list_opt (rbv_psn ro) fbits (rbv_bits ro) st2 in
                      Some (mk_rail_bv w bits lit_false,
                            mk_blast_env st3 (be_vars env1) ((w, key, fbits) :: be_freezes env1))
                  end
              | None => None
              end
          | None => None
          end
      end
  | CE_Let bs body =>
      match blast_let_binds (fun lr0 ms0 x env0 => blast_cert_expr ctx lr0 ms0 x env0)
                            lr ms_opt bs env with
      | Some (lr', ms_opt', env1) => blast_cert_expr ctx lr' ms_opt' body env1
      | None => None
      end
  end.

Definition wf_let_rails_sync {Pa : Params}
  (asg : positive -> bool) (bound : positive)
  (lw : list (string * positive))
  (lenv : let_val_env Pa)
  (lr : let_rail_env) : Prop :=
  forall nm,
    match lookup_let_width lw nm, lookup_let_val lenv nm, lookup_let_rail lr nm with
    | Some bw, Some dv, Some (rw, r) =>
        rw = bw /\
        wf_scalar_dvalue bw dv /\
        wf_rail_bound bw bound r /\
        rail_matches_dvalue bw asg r dv
    | None, None, None => True
    | _, _, _ => False
    end.

Lemma wf_let_rails_sync_nil :
  forall {Pa : Params} asg bound,
    @wf_let_rails_sync Pa asg bound [] [] [].
Proof.
  intros Pa asg bound nm; cbn; exact I.
Qed.

Lemma wf_let_rails_sync_step :
  forall {Pa : Params} asg asg' st st' lw (lenv : let_val_env Pa) lr,
    wf_let_rails_sync asg (bs_next_var st) lw lenv lr ->
    step_spec st st' asg asg' ->
    wf_let_rails_sync asg' (bs_next_var st') lw lenv lr.
Proof.
  intros Pa asg asg' st st' lw lenv lr Hsync (Hle & Hag & _) nm.
  specialize (Hsync nm).
  destruct (lookup_let_width lw nm) as [bw |],
           (lookup_let_val lenv nm) as [dv |],
           (lookup_let_rail lr nm) as [[rw r] |];
    try exact Hsync.
  destruct Hsync as (Hrw & Hwfdv & Hwfr & Hrm).
  split; [exact Hrw | split; [exact Hwfdv | split;
    [exact (wf_rail_bound_mono bw _ _ r Hle Hwfr)
    | exact (rail_matches_dvalue_agree bw _ asg asg' r dv Hag Hwfr Hrm)]]].
Qed.

Definition wf_ms_sync {Pa : Params}
  (lenv : let_val_env Pa) (ms_opt : option (sized_let_map * nat)) : Prop :=
  match ms_opt with
  | None => True
  | Some (ms, _) => strip_let_sizes ms = let_val_exprs lenv
  end.

Lemma blast_cert_expr_sat :
  forall {Pa : Params} (e : cert_expr) (ctx : ub_ctx)
         (lw : list (string * positive))
         (lr : let_rail_env) (ms_opt : option (sized_let_map * nat))
         (penv : param_env Pa) (lenv : let_val_env Pa) (foracle : freeze_oracle)
         (asg : positive -> bool) (env env' : blast_env) (out : rail_bv),
    blast_cert_expr ctx lr ms_opt e env = Some (out, env') ->
    wt_cert_expr lw e = true ->
    wf_let_rails_sync asg (bs_next_var (be_st env)) lw lenv lr ->
    wf_ms_sync lenv ms_opt ->
    wf_param_env_for (collect_free_vars (List.map fst lw) e) penv ->
    ub_ctx_holds penv foracle ctx ->
    sat_blast_env penv foracle asg env ->
    exists asg' vout,
      eval_cert_expr penv lenv foracle e = raise_ret vout /\
      step_spec (be_st env) (be_st env') asg asg' /\
      sat_blast_env penv foracle asg' env' /\
      wf_rail_bound (cert_expr_bit_width e) (bs_next_var (be_st env')) out /\
      rail_matches_dvalue (cert_expr_bit_width e) asg' out vout.
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
    intros ctx lw lr ms_opt penv lenv foracle asg env env' out
           Hbl Hwt Hsync Hms Hpenv Hctx Henv.
  - (* CE_BvConst *)
    cbn [blast_cert_expr cert_expr_bit_width eval_cert_expr] in Hbl |- *.
    inversion Hbl; subst out env'; clear Hbl.
    destruct Henv as (Hst & Hvars & Hfrzs).
    assert (Hinit : eval_cnf asg (bs_cnf (init_blast_state 2%positive) ++ []) = true)
      by (cbn; rewrite (proj1 (proj2 Hst)); reflexivity).
    destruct (blast_const_rail_sound asg w val 2%positive [] Hinit)
      as (_ & Hpsn & Hval).
    assert (Hwf_out : wf_rail_bound w (bs_next_var (be_st env)) (blast_const_rail w val)).
    { split; [split; [reflexivity | unfold blast_const_rail; cbn; rewrite map_length, seq_length; reflexivity] | split].
      - unfold blast_const_rail, wf_lits_bound; cbn.
        apply Forall_forall; intros l0 Hin; apply in_map_iff in Hin as [k0 [<- _]].
        pose proof (proj1 (proj1 Hst)); destruct (Z.testbit (Z.of_N val) (Z.of_nat k0)); cbn; lia.
      - cbn; pose proof (proj1 (proj1 Hst)); lia. }
    exists asg, (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N val)))).
    split; [reflexivity | split; [exact (step_spec_refl _ asg Hst) |
    split; [exact (conj Hst (conj Hvars Hfrzs)) | split; [exact Hwf_out |
      unfold rail_matches_dvalue; rewrite Hpsn, Hval; reflexivity]]]].
  - (* CE_Poison *)
    cbn [blast_cert_expr cert_expr_bit_width eval_cert_expr] in Hbl |- *.
    inversion Hbl; subst out env'; clear Hbl.
    destruct Henv as (Hst & Hvars & Hfrzs).
    assert (Hwf_out : wf_rail_bound w (bs_next_var (be_st env)) (blast_poison_rail w)).
    { split; [split; [reflexivity | unfold blast_poison_rail; cbn; apply repeat_length] | split].
      - unfold blast_poison_rail, wf_lits_bound; cbn.
        apply Forall_forall; intros l0 Hin; apply repeat_spec in Hin; subst l0;
          cbn; pose proof (proj1 (proj1 Hst)); lia.
      - cbn; pose proof (proj1 (proj1 Hst)); lia. }
    exists asg, (DVALUE_Base DVALUE_Poison).
    split; [reflexivity | split; [exact (step_spec_refl _ asg Hst) |
    split; [exact (conj Hst (conj Hvars Hfrzs)) | split; [exact Hwf_out |
      unfold rail_matches_dvalue, eval_rail_psn, blast_poison_rail; cbn;
      rewrite (proj1 (proj2 Hst)); reflexivity]]]].
  - (* CE_Var *)
    cbn [blast_cert_expr wt_cert_expr eval_cert_expr cert_expr_bit_width] in Hbl, Hwt |- *.
    pose proof (Hsync nm) as Hsnm.
    destruct (lookup_let_rail lr nm) as [[rw r_let] |] eqn:Elr.
    + destruct (lookup_let_width lw nm) as [bw |]; [| contradiction].
      destruct (lookup_let_val lenv nm) as [dv |]; [| contradiction].
      destruct (Pos.eqb rw w) eqn:Erw; [| discriminate Hbl].
      apply Pos.eqb_eq in Erw; apply Pos.eqb_eq in Hwt; subst rw bw.
      inversion Hbl; subst out env'; clear Hbl.
      destruct Hsnm as (_ & Hwfdv & Hwfr & Hrm).
      exists asg, dv.
      split; [exact (check_scalar_width_ok w dv Hwfdv) |
      split; [exact (step_spec_refl _ asg (proj1 Henv)) |
      split; [exact Henv | split; [exact Hwfr | exact Hrm]]]].
    + destruct (lookup_let_width lw nm) as [bw |] eqn:Elw;
        [destruct (lookup_let_val lenv nm); contradiction |].
      destruct (lookup_let_val lenv nm) as [dv0 |]; [contradiction |].
      destruct (lookup_blast_var (be_vars env) nm w) as [r_var |] eqn:Elk.
      * inversion Hbl; subst out env'; clear Hbl.
        destruct Henv as (Hst & Hvars & Hfrzs).
        destruct (Hvars nm w r_var Elk) as (Hwf_r & dv & Hpm & Hwfdv & Hrm).
        exists asg, dv.
        split; [rewrite Hpm; exact (check_scalar_width_ok w dv Hwfdv) |
        split; [exact (step_spec_refl _ asg Hst) |
        split; [exact (conj Hst (conj Hvars Hfrzs)) | split; [exact Hwf_r | exact Hrm]]]].
      * cbn [collect_free_vars] in Hpenv.
        assert (Hnin : string_in_list nm (List.map fst lw) = false).
        { destruct (string_in_list nm (List.map fst lw)) eqn:Ein; [| reflexivity].
          apply string_in_list_spec in Ein; apply lookup_let_width_in_dom in Elw; contradiction. }
        rewrite Hnin in Hpenv.
        destruct (Hpenv nm w (or_introl eq_refl)) as [dv [Hpm Hwfdv]].
        assert (Hev_var : match penv nm with
                          | Some dv0 => check_scalar_width w dv0
                          | None => raise_error ("unbound variable: " ++ nm)
                          end = raise_ret dv)
          by (rewrite Hpm; exact (check_scalar_width_ok w dv Hwfdv)).
        destruct (alloc_aligned_bits (ctx_ptr_low_bit_zero ctx nm w) 0%nat
                    (Pos.to_nat w) (be_st env)) as [bits st1] eqn:Hal.
        destruct Henv as (Hst & Hvars & Hfrzs).
        destruct Hwfdv as [-> | [iv ->]].
        -- assert (Enp : ctx_has_var_nonpoison ctx nm w = false).
           { destruct (ctx_has_var_nonpoison ctx nm w) eqn:E; [| reflexivity].
             exfalso; exact (ctx_has_var_nonpoison_sound penv foracle ctx nm w _ E Hctx Hpm eq_refl). }
           rewrite Enp in Hbl.
           destruct (alloc_var st1) as [psn st2] eqn:Hpv.
           inversion Hbl; subst out env'; clear Hbl; cbn [be_st].
           destruct (alloc_aligned_bits_any_step (Pos.to_nat w)
                       (ctx_ptr_low_bit_zero ctx nm w) 0%nat asg (be_st env) bits st1 Hst Hal)
             as (asg1 & Hs1 & Hblen & Hbwf).
           destruct (alloc_var_sat asg1 st1 true psn st2 (proj2 (proj2 Hs1)) Hpv)
             as (asg2 & Hle2 & Hag2 & Hsat2 & Hpwf & Hpev).
           pose proof (step_spec_trans (be_st env) st1 st2 asg asg1 asg2 Hs1
                         (conj Hle2 (conj Hag2 Hsat2))) as Hs02.
           assert (Hwf_r : wf_rail_bound w (bs_next_var st2) (mk_rail_bv w bits psn)).
           { split; [split; [reflexivity | exact Hblen] |
                     split; [exact (wf_lits_bound_mono _ _ bits Hle2 Hbwf) | exact Hpwf]]. }
           assert (Hrm_r : rail_matches_dvalue w asg2 (mk_rail_bv w bits psn) (DVALUE_Base DVALUE_Poison))
             by (unfold rail_matches_dvalue, eval_rail_psn; cbn; rewrite Hpev; reflexivity).
           pose proof (sat_blast_env_step penv foracle asg asg2 env st2
                         (conj Hst (conj Hvars Hfrzs)) Hs02) as (_ & Hvars2 & Hfrzs2).
           exists asg2, (DVALUE_Base DVALUE_Poison).
           split; [exact Hev_var | split; [exact Hs02 | split; [| split; [exact Hwf_r | exact Hrm_r]]]].
           split; [exact Hsat2 | split; [| exact Hfrzs2]].
           intros nm' w' r' Hlk; cbn in Hlk.
           destruct (String.eqb nm nm' && Pos.eqb w w') eqn:Ehit.
           ++ apply andb_true_iff in Ehit as [Hs Hp]; apply String.eqb_eq in Hs; apply Pos.eqb_eq in Hp.
              inversion Hlk; subst nm' w' r'; split; [exact Hwf_r |].
              exists (DVALUE_Base DVALUE_Poison);
                split; [exact Hpm | split; [left; reflexivity | exact Hrm_r]].
           ++ exact (Hvars2 nm' w' r' Hlk).
        -- assert (Hzp : forall k,
                     ctx_ptr_low_bit_zero ctx nm w (0 + k)%nat = true ->
                     List.nth k (bit_int_to_bools w iv) false = false).
           { cbn [Nat.add]; intros k Hkz.
             destruct (Nat.lt_ge_cases k (Pos.to_nat w)) as [Hlt | Hge].
             - rewrite bit_int_to_bools_nth by exact Hlt.
               unfold Integers.testbit.
               exact (ctx_ptr_low_bit_zero_sound penv foracle ctx nm w k iv Hkz Hctx Hpm).
             - apply nth_overflow; rewrite bit_int_to_bools_length; exact Hge. }
           rewrite <- (bit_int_to_bools_length w iv) in Hal.
           destruct (alloc_aligned_bits_val_step (bit_int_to_bools w iv)
                       (ctx_ptr_low_bit_zero ctx nm w) 0%nat asg (be_st env) bits st1 Hst Hzp Hal)
             as (asg1 & Hs1 & Hblen & Hbwf & Hbmap).
           rewrite bit_int_to_bools_length in Hblen.
           assert (Hpsn_case :
             exists psn st2 asg2,
               (if ctx_has_var_nonpoison ctx nm w then (lit_false, st1) else alloc_var st1) = (psn, st2) /\
               step_spec st1 st2 asg1 asg2 /\
               wf_lit_bound (bs_next_var st2) psn /\
               eval_lit asg2 psn = false).
           { destruct (ctx_has_var_nonpoison ctx nm w).
             - exists lit_false, st1, asg1; split; [reflexivity | split;
                 [exact (step_spec_refl st1 asg1 (proj2 (proj2 Hs1))) | split;
                  [exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs1)))))
                   | exact (sat_eval_lit_false asg1 st1 (proj2 (proj2 Hs1)))]]].
             - destruct (alloc_var st1) as [psn st2] eqn:Hpv.
               destruct (alloc_var_sat asg1 st1 false psn st2 (proj2 (proj2 Hs1)) Hpv)
                 as (asg2 & Hle2 & Hag2 & Hsat2 & Hpwf & Hpev).
               exists psn, st2, asg2; split; [reflexivity | split;
                 [exact (conj Hle2 (conj Hag2 Hsat2)) | split; [exact Hpwf | exact Hpev]]]. }
           destruct Hpsn_case as (psn & st2 & asg2 & Hpsn_eq & Hs2 & Hpwf & Hpev).
           rewrite Hpsn_eq in Hbl; inversion Hbl; subst out env'; clear Hbl; cbn [be_st].
           pose proof (step_spec_trans (be_st env) st1 st2 asg asg1 asg2 Hs1 Hs2) as Hs02.
           assert (Hwf_r : wf_rail_bound w (bs_next_var st2) (mk_rail_bv w bits psn)).
           { split; [split; [reflexivity | exact Hblen] |
                     split; [exact (wf_lits_bound_mono _ _ bits (proj1 Hs2) Hbwf) | exact Hpwf]]. }
           assert (Hrm_r : rail_matches_dvalue w asg2 (mk_rail_bv w bits psn)
                             (DVALUE_Base (@DVALUE_I Pa w iv))).
           { unfold rail_matches_dvalue, eval_rail_psn, eval_rail_val; cbn [rbv_psn rbv_bits].
             rewrite Hpev, (step_spec_eval_lits st1 st2 asg1 asg2 bits Hs2 Hbwf),
                     Hbmap, bit_int_to_bools_repr; reflexivity. }
           pose proof (sat_blast_env_step penv foracle asg asg2 env st2
                         (conj Hst (conj Hvars Hfrzs)) Hs02) as (_ & Hvars2 & Hfrzs2).
           exists asg2, (DVALUE_Base (@DVALUE_I Pa w iv)).
           split; [exact Hev_var | split; [exact Hs02 | split; [| split; [exact Hwf_r | exact Hrm_r]]]].
           split; [exact (proj2 (proj2 Hs2)) | split; [| exact Hfrzs2]].
           intros nm' w' r' Hlk; cbn in Hlk.
           destruct (String.eqb nm nm' && Pos.eqb w w') eqn:Ehit.
           ++ apply andb_true_iff in Ehit as [Hs Hp]; apply String.eqb_eq in Hs; apply Pos.eqb_eq in Hp.
              inversion Hlk; subst nm' w' r'; split; [exact Hwf_r |].
              exists (DVALUE_Base (@DVALUE_I Pa w iv));
                split; [exact Hpm | split; [right; exists iv; reflexivity | exact Hrm_r]].
           ++ exact (Hvars2 nm' w' r' Hlk).
  - (* CE_BinOp *)
    cbn [blast_cert_expr wt_cert_expr collect_free_vars eval_cert_expr cert_expr_bit_width] in *.
    destruct (blast_cert_expr ctx lr ms_opt l env) as [[rl env1] |] eqn:Ebl_l; [| discriminate Hbl].
    destruct (blast_cert_expr ctx lr ms_opt r env1) as [[rr env2] |] eqn:Ebl_r; [| discriminate Hbl].
    destruct (blast_binop_rail op fl w rl rr (be_st env2)) as [[out0 st3] |] eqn:Eop; [| discriminate Hbl].
    inversion Hbl; subst out0 env'; clear Hbl; cbn [be_st].
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((((_ & Htl) & Htr) & Hwl) & Hwr).
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    assert (Hpl : wf_param_env_for (collect_free_vars (List.map fst lw) l) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars (List.map fst lw) r) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
    destruct (IHl ctx lw lr ms_opt penv lenv foracle asg env env1 rl Ebl_l Htl Hsync Hms Hpl Hctx Henv)
      as (asg1 & vl & Evl & Hs1 & Henv1 & Hwfrl & Hmrl).
    pose proof (wf_let_rails_sync_step asg asg1 (be_st env) (be_st env1) lw lenv lr Hsync Hs1) as Hsync1.
    destruct (IHr ctx lw lr ms_opt penv lenv foracle asg1 env1 env2 rr Ebl_r Htr Hsync1 Hms Hpr Hctx Henv1)
      as (asg2 & vr & Evr & Hs2 & Henv2 & Hwfrr & Hmrr).
    rewrite Hwl in Hwfrl, Hmrl; rewrite Hwr in Hwfrr, Hmrr.
    pose proof (wf_rail_bound_mono w _ _ rl (proj1 Hs2) Hwfrl) as Hwfrl2.
    pose proof (rail_matches_dvalue_agree w _ asg1 asg2 rl vl (proj1 (proj2 Hs2)) Hwfrl Hmrl) as Hmrl2.
    destruct (blast_binop_rail_sat op fl w rl rr asg2 (be_st env2) out st3 vl vr
                Eop (proj1 Henv2) Hwfrl2 Hwfrr Hmrl2 Hmrr)
      as (asg3 & vout & Evout & Hs3 & Hwf_out & Hm_out).
    pose proof (step_spec_trans _ _ _ _ _ _ Hs1 (step_spec_trans _ _ _ _ _ _ Hs2 Hs3)) as Hs03.
    exists asg3, vout.
    split; [rewrite Evl, Evr; cbn [eou_bind]; exact Evout |
    split; [exact Hs03 |
    split; [exact (sat_blast_env_step penv foracle asg2 asg3 env2 st3 Henv2 Hs3) |
    split; [exact Hwf_out | exact Hm_out]]]].
  - (* CE_ICmp *)
    cbn [blast_cert_expr wt_cert_expr collect_free_vars eval_cert_expr cert_expr_bit_width] in *.
    destruct (blast_cert_expr ctx lr ms_opt l env) as [[rl env1] |] eqn:Ebl_l; [| discriminate Hbl].
    destruct (blast_cert_expr ctx lr ms_opt r env1) as [[rr env2] |] eqn:Ebl_r; [| discriminate Hbl].
    pose proof (blast_icmp_pred_sat (Pa := Pa) pr ss w rl rr) as Hicmp_lem.
    destruct (cert_icmp_to_signed_comp pr) as [is_s cmp_c] eqn:Esc.
    destruct (blast_icmp_rail ss is_s cmp_c w rl rr (be_st env2)) as [out0 st3] eqn:Eic.
    inversion Hbl; subst out0 env'; clear Hbl; cbn [be_st].
    rewrite !andb_true_iff in Hwt; destruct Hwt as (((Htl & Htr) & Hwl) & Hwr).
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    assert (Hpl : wf_param_env_for (collect_free_vars (List.map fst lw) l) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpr : wf_param_env_for (collect_free_vars (List.map fst lw) r) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; exact Hx).
    destruct (IHl ctx lw lr ms_opt penv lenv foracle asg env env1 rl Ebl_l Htl Hsync Hms Hpl Hctx Henv)
      as (asg1 & vl & Evl & Hs1 & Henv1 & Hwfrl & Hmrl).
    pose proof (wf_let_rails_sync_step asg asg1 (be_st env) (be_st env1) lw lenv lr Hsync Hs1) as Hsync1.
    destruct (IHr ctx lw lr ms_opt penv lenv foracle asg1 env1 env2 rr Ebl_r Htr Hsync1 Hms Hpr Hctx Henv1)
      as (asg2 & vr & Evr & Hs2 & Henv2 & Hwfrr & Hmrr).
    rewrite Hwl in Hwfrl, Hmrl; rewrite Hwr in Hwfrr, Hmrr.
    pose proof (wf_rail_bound_mono w _ _ rl (proj1 Hs2) Hwfrl) as Hwfrl2.
    pose proof (rail_matches_dvalue_agree w _ asg1 asg2 rl vl (proj1 (proj2 Hs2)) Hwfrl Hmrl) as Hmrl2.
    destruct (Hicmp_lem asg2 (be_st env2) out st3 vl vr Eic (proj1 Henv2) Hwfrl2 Hwfrr Hmrl2 Hmrr)
      as (asg3 & vout & Evout & Hs3 & Hwf_out & Hm_out).
    pose proof (step_spec_trans _ _ _ _ _ _ Hs1 (step_spec_trans _ _ _ _ _ _ Hs2 Hs3)) as Hs03.
    exists asg3, vout.
    split; [rewrite Evl, Evr; cbn [eou_bind]; exact Evout |
    split; [exact Hs03 |
    split; [exact (sat_blast_env_step penv foracle asg2 asg3 env2 st3 Henv2 Hs3) |
    split; [exact Hwf_out | exact Hm_out]]]].
  - (* CE_Cast *)
    cbn [blast_cert_expr wt_cert_expr collect_free_vars eval_cert_expr cert_expr_bit_width] in *.
    destruct (blast_cert_expr ctx lr ms_opt o env) as [[ro env1] |] eqn:Ebl_o; [| discriminate Hbl].
    destruct (blast_cast_op k fw tw fl ro (be_st env1)) as [out0 st2] eqn:Ecst.
    inversion Hbl; subst out0 env'; clear Hbl; cbn [be_st].
    rewrite !andb_true_iff in Hwt; destruct Hwt as ((Hk & Hto) & Hwo).
    apply Pos.eqb_eq in Hwo.
    destruct (IHo ctx lw lr ms_opt penv lenv foracle asg env env1 ro Ebl_o Hto Hsync Hms Hpenv Hctx Henv)
      as (asg1 & vo & Evo & Hs1 & Henv1 & Hwfro & Hmro).
    rewrite Hwo in Hwfro, Hmro.
    destruct (blast_cast_op_sat k fw tw fl ro asg1 (be_st env1) out st2 vo
                Hk Ecst (proj1 Henv1) Hwfro Hmro)
      as (asg2 & vout & Evout & Hs2 & Hwf_out & Hm_out).
    pose proof (step_spec_trans _ _ _ _ _ _ Hs1 Hs2) as Hs02.
    exists asg2, vout.
    split; [rewrite Evo; cbn [eou_bind]; exact Evout |
    split; [exact Hs02 |
    split; [exact (sat_blast_env_step penv foracle asg1 asg2 env1 st2 Henv1 Hs2) |
    split; [exact Hwf_out | exact Hm_out]]]].
  - (* CE_Select *)
    cbn [blast_cert_expr wt_cert_expr collect_free_vars eval_cert_expr cert_expr_bit_width] in *.
    destruct (blast_cert_expr ctx lr ms_opt c env) as [[rc env1] |] eqn:Ebl_c; [| discriminate Hbl].
    destruct (blast_cert_expr ctx lr ms_opt t env1) as [[rt env2] |] eqn:Ebl_t; [| discriminate Hbl].
    destruct (blast_cert_expr ctx lr ms_opt f env2) as [[rf env3] |] eqn:Ebl_f; [| discriminate Hbl].
    destruct (blast_select_rail_opt w rc rt rf (be_st env3)) as [out0 st4] eqn:Esel.
    inversion Hbl; subst out0 env'; clear Hbl; cbn [be_st].
    rewrite !andb_true_iff in Hwt; destruct Hwt as (((((Htc & Htt) & Htf) & Hwc) & Hwt0) & Hwf0).
    apply Pos.eqb_eq in Hwc; apply Pos.eqb_eq in Hwt0; apply Pos.eqb_eq in Hwf0.
    assert (Hpc : wf_param_env_for (collect_free_vars (List.map fst lw) c) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; left; exact Hx).
    assert (Hpt : wf_param_env_for (collect_free_vars (List.map fst lw) t) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; left; exact Hx).
    assert (Hpf : wf_param_env_for (collect_free_vars (List.map fst lw) f) penv)
      by (intros x wx Hx; apply Hpenv, in_app_iff; right; apply in_app_iff; right; exact Hx).
    destruct (IHc ctx lw lr ms_opt penv lenv foracle asg env env1 rc Ebl_c Htc Hsync Hms Hpc Hctx Henv)
      as (asg1 & vc & Evc & Hs1 & Henv1 & Hwfrc & Hmrc).
    pose proof (wf_let_rails_sync_step asg asg1 _ _ lw lenv lr Hsync Hs1) as Hsync1.
    destruct (IHt ctx lw lr ms_opt penv lenv foracle asg1 env1 env2 rt Ebl_t Htt Hsync1 Hms Hpt Hctx Henv1)
      as (asg2 & vt & Evt & Hs2 & Henv2 & Hwfrt & Hmrt).
    pose proof (wf_let_rails_sync_step asg1 asg2 _ _ lw lenv lr Hsync1 Hs2) as Hsync2.
    destruct (IHf ctx lw lr ms_opt penv lenv foracle asg2 env2 env3 rf Ebl_f Htf Hsync2 Hms Hpf Hctx Henv2)
      as (asg3 & vf & Evf & Hs3 & Henv3 & Hwfrf & Hmrf).
    rewrite Hwc in Hwfrc, Hmrc; rewrite Hwt0 in Hwfrt, Hmrt; rewrite Hwf0 in Hwfrf, Hmrf.
    pose proof (step_spec_trans _ _ _ _ _ _ Hs2 Hs3) as Hs13.
    pose proof (wf_rail_bound_mono 1%positive _ _ rc (proj1 Hs13) Hwfrc) as Hwfrc3.
    pose proof (rail_matches_dvalue_agree 1%positive _ asg1 asg3 rc vc (proj1 (proj2 Hs13)) Hwfrc Hmrc) as Hmrc3.
    pose proof (wf_rail_bound_mono w _ _ rt (proj1 Hs3) Hwfrt) as Hwfrt3.
    pose proof (rail_matches_dvalue_agree w _ asg2 asg3 rt vt (proj1 (proj2 Hs3)) Hwfrt Hmrt) as Hmrt3.
    destruct (blast_select_op_sat w rc rt rf asg3 (be_st env3) out st4 vc vt vf
                Esel (proj1 Henv3) Hwfrc3 Hwfrt3 Hwfrf Hmrc3 Hmrt3 Hmrf)
      as (asg4 & vout & Evout & Hs4 & Hwf_out & Hm_out).
    pose proof (step_spec_trans _ _ _ _ _ _ Hs1 (step_spec_trans _ _ _ _ _ _ Hs13 Hs4)) as Hs04.
    exists asg4, vout.
    split; [rewrite Evc, Evt, Evf; cbn [eou_bind]; exact Evout |
    split; [exact Hs04 |
    split; [exact (sat_blast_env_step penv foracle asg3 asg4 env3 st4 Henv3 Hs4) |
    split; [exact Hwf_out | exact Hm_out]]]].
  - (* CE_Freeze *)
    cbn [blast_cert_expr wt_cert_expr collect_free_vars eval_cert_expr cert_expr_bit_width] in *.
    destruct ms_opt as [[ms fuel_unused] |]; [| discriminate Hbl].
    destruct (expand_lets_fueled_with ms o default_let_expand_budget)
      as [[[key ksz] kf] |] eqn:Ekey; [| discriminate Hbl].
    destruct (blast_cert_expr ctx lr (Some (ms, fuel_unused)) o env)
      as [[ro env1] |] eqn:Ebl_o; [| discriminate Hbl].
    apply andb_true_iff in Hwt as [Hto Hwo]; apply Pos.eqb_eq in Hwo.
    destruct (IHo ctx lw lr (Some (ms, fuel_unused)) penv lenv foracle asg env env1 ro
                Ebl_o Hto Hsync Hms Hpenv Hctx Henv)
      as (asg1 & vo & Evo & Hs1 & Henv1 & Hwfro & Hmro).
    rewrite Hwo in Hwfro, Hmro.
    destruct Hwfro as ([Hwro Hlro] & Hbro & Hpro).
    cbn [wf_ms_sync] in Hms.
    pose proof (expand_lets_fueled_with_eq o ms default_let_expand_budget key ksz kf Ekey) as Hkey_eq.
    rewrite Hms in Hkey_eq; subst key.
    set (key := expand_lets_with (let_val_exprs lenv) o) in *.
    set (fval := @Integers.repr w (foracle w key)) in *.
    destruct (lookup_blast_freeze (be_freezes env1) w key) as [fbits |] eqn:Efrz.
    + destruct (mux_bits_list_opt (rbv_psn ro) fbits (rbv_bits ro) (be_st env1))
        as [bits st2] eqn:Hmux.
      inversion Hbl; subst out env'; clear Hbl; cbn [be_st].
      destruct Henv1 as (Hst1 & Hvars1 & Hfrzs1).
      destruct (Hfrzs1 w key fbits Efrz) as (Hflen & Hfwf & Hfmap).
      assert (Hlen_fo : List.length fbits = List.length (rbv_bits ro)) by congruence.
      destruct (mux_bits_list_opt_step fbits (rbv_bits ro) (rbv_psn ro) asg1 (be_st env1) bits st2
                  Hlen_fo Hpro Hfwf Hbro Hst1 Hmux)
        as (asg2 & Hs2 & Hblen & Hbwf & Hbits_ev).
      pose proof (step_spec_trans _ _ _ _ _ _ Hs1 Hs2) as Hs02.
      assert (Hwf_out : wf_rail_bound w (bs_next_var st2) (mk_rail_bv w bits lit_false)).
      { split; [split; [reflexivity | cbn; congruence] |
                split; [exact Hbwf | exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs2)))))]]. }
      pose proof (rail_matches_dvalue_agree w _ asg1 asg2 ro vo (proj1 (proj2 Hs2))
                    (conj (conj Hwro Hlro) (conj Hbro Hpro)) Hmro) as Hmro2.
      pose proof (sat_eval_lit_false asg2 st2 (proj2 (proj2 Hs2))) as Hlf2.
      pose proof (step_spec_eval_lit _ _ asg1 asg2 (rbv_psn ro) Hs2 Hpro) as Hpo_ag.
      unfold rail_matches_dvalue in Hmro2.
      destruct (eval_rail_psn asg1 ro) eqn:Epo.
      * unfold eval_rail_psn in Epo, Hmro2; rewrite Hpo_ag, Epo in Hmro2; subst vo.
        exists asg2, (DVALUE_Base (@DVALUE_I Pa w fval)).
        split; [rewrite Evo; reflexivity |
        split; [exact Hs02 |
        split; [exact (sat_blast_env_step penv foracle asg1 asg2 env1 st2
                         (conj Hst1 (conj Hvars1 Hfrzs1)) Hs2) |
        split; [exact Hwf_out |]]]].
        unfold rail_matches_dvalue, eval_rail_psn, eval_rail_val; cbn [rbv_psn rbv_bits].
        rewrite Hlf2, Hbits_ev, Epo, Hfmap, bit_int_to_bools_repr; reflexivity.
      * unfold eval_rail_psn in Epo, Hmro2; rewrite Hpo_ag, Epo in Hmro2; subst vo.
        exists asg2, (DVALUE_Base (@DVALUE_I Pa w (eval_rail_val w asg2 ro))).
        split; [rewrite Evo; reflexivity |
        split; [exact Hs02 |
        split; [exact (sat_blast_env_step penv foracle asg1 asg2 env1 st2
                         (conj Hst1 (conj Hvars1 Hfrzs1)) Hs2) |
        split; [exact Hwf_out |]]]].
        unfold rail_matches_dvalue, eval_rail_psn, eval_rail_val; cbn [rbv_psn rbv_bits].
        rewrite Hlf2, Hbits_ev, Epo,
                <- (step_spec_eval_lits _ _ asg1 asg2 (rbv_bits ro) Hs2 Hbro);
          reflexivity.
    + destruct (alloc_fresh_bits (Pos.to_nat w) (be_st env1)) as [fbits st2] eqn:Hfb.
      destruct (mux_bits_list_opt (rbv_psn ro) fbits (rbv_bits ro) st2) as [bits st3] eqn:Hmux.
      inversion Hbl; subst out env'; clear Hbl; cbn [be_st].
      destruct Henv1 as (Hst1 & Hvars1 & Hfrzs1).
      rewrite <- (bit_int_to_bools_length w fval) in Hfb.
      destruct (alloc_fresh_bits_sat (bit_int_to_bools w fval) asg1 (be_st env1) fbits st2 Hst1 Hfb)
        as (asg2 & Hle2 & Hag2 & Hsat2 & Hflen & Hfwf & Hfmap).
      rewrite bit_int_to_bools_length in Hflen.
      assert (Hlen_fo : List.length fbits = List.length (rbv_bits ro)) by congruence.
      destruct (mux_bits_list_opt_step fbits (rbv_bits ro) (rbv_psn ro) asg2 st2 bits st3
                  Hlen_fo (wf_lit_bound_mono _ _ _ Hle2 Hpro) Hfwf
                  (wf_lits_bound_mono _ _ _ Hle2 Hbro) Hsat2 Hmux)
        as (asg3 & Hs3 & Hblen & Hbwf & Hbits_ev).
      pose proof (step_spec_trans (be_st env1) st2 st3 asg1 asg2 asg3
                    (conj Hle2 (conj Hag2 Hsat2)) Hs3) as Hs13.
      pose proof (step_spec_trans _ _ _ _ _ _ Hs1 Hs13) as Hs03.
      assert (Hwf_out : wf_rail_bound w (bs_next_var st3) (mk_rail_bv w bits lit_false)).
      { split; [split; [reflexivity | cbn; congruence] |
                split; [exact Hbwf | exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs3)))))]]. }
      pose proof (sat_blast_env_step penv foracle asg1 asg3 env1 st3
                    (conj Hst1 (conj Hvars1 Hfrzs1)) Hs13) as (_ & Hvars3 & Hfrzs3).
      assert (Hfmap3 : List.map (eval_lit asg3) fbits = bit_int_to_bools w fval)
        by (rewrite (step_spec_eval_lits st2 st3 asg2 asg3 fbits Hs3 Hfwf); exact Hfmap).
      assert (Henv_new : sat_blast_env penv foracle asg3
                           (mk_blast_env st3 (be_vars env1) ((w, key, fbits) :: be_freezes env1))).
      { split; [exact (proj2 (proj2 Hs3)) | split; [exact Hvars3 |]].
        intros w' key' fbits' Hlk; cbn in Hlk.
        destruct (Pos.eqb w w' && cert_expr_eqb key key') eqn:Ehit.
        - apply andb_true_iff in Ehit as [Hw' Hk']; apply Pos.eqb_eq in Hw'; apply cert_expr_eqb_eq in Hk'.
          inversion Hlk; subst w' key' fbits'.
          split; [exact Hflen | split; [exact (wf_lits_bound_mono _ _ fbits (proj1 Hs3) Hfwf) | exact Hfmap3]].
        - exact (Hfrzs3 w' key' fbits' Hlk). }
      pose proof (rail_matches_dvalue_agree w _ asg1 asg3 ro vo (proj1 (proj2 Hs13))
                    (conj (conj Hwro Hlro) (conj Hbro Hpro)) Hmro) as Hmro3.
      pose proof (sat_eval_lit_false asg3 st3 (proj2 (proj2 Hs3))) as Hlf3.
      pose proof (step_spec_eval_lit _ _ asg1 asg2 (rbv_psn ro)
                    (conj Hle2 (conj Hag2 Hsat2)) Hpro) as Hpo12.
      pose proof (step_spec_eval_lit _ _ asg1 asg3 (rbv_psn ro) Hs13 Hpro) as Hpo13.
      unfold rail_matches_dvalue in Hmro3.
      destruct (eval_rail_psn asg1 ro) eqn:Epo.
      * unfold eval_rail_psn in Epo, Hmro3; rewrite Hpo13, Epo in Hmro3; subst vo.
        exists asg3, (DVALUE_Base (@DVALUE_I Pa w fval)).
        split; [rewrite Evo; reflexivity |
        split; [exact Hs03 | split; [exact Henv_new | split; [exact Hwf_out |]]]].
        unfold rail_matches_dvalue, eval_rail_psn, eval_rail_val; cbn [rbv_psn rbv_bits].
        rewrite Hlf3, Hbits_ev, Hpo12, Epo, Hfmap, bit_int_to_bools_repr; reflexivity.
      * unfold eval_rail_psn in Epo, Hmro3; rewrite Hpo13, Epo in Hmro3; subst vo.
        exists asg3, (DVALUE_Base (@DVALUE_I Pa w (eval_rail_val w asg3 ro))).
        split; [rewrite Evo; reflexivity |
        split; [exact Hs03 | split; [exact Henv_new | split; [exact Hwf_out |]]]].
        unfold rail_matches_dvalue, eval_rail_psn, eval_rail_val; cbn [rbv_psn rbv_bits].
        rewrite Hlf3, Hbits_ev, Hpo12, Epo,
                (step_spec_eval_lits _ _ asg1 asg2 (rbv_bits ro) (conj Hle2 (conj Hag2 Hsat2)) Hbro),
                <- (step_spec_eval_lits _ _ asg1 asg3 (rbv_bits ro) Hs13 Hbro);
          reflexivity.
  - (* CE_Let *)
    cbn [blast_cert_expr wt_cert_expr collect_free_vars eval_cert_expr cert_expr_bit_width] in *.
    destruct (wf_let_binds_step wt_cert_expr lw [] bs) as [lw' |] eqn:Elw; [| discriminate Hwt].
    destruct (blast_let_binds (fun lr0 ms0 x env0 => blast_cert_expr ctx lr0 ms0 x env0)
                              lr ms_opt bs env)
      as [[[lr' ms_opt'] env_b] |] eqn:Ebs; [| discriminate Hbl].
    assert (Hstep_bs :
      forall xs cur_lw seen cur_lr cur_ms cur_le cur_asg cur_env,
        wf_let_binds_step wt_cert_expr cur_lw seen xs = Some lw' ->
        blast_let_binds (fun lr0 ms0 x env0 => blast_cert_expr ctx lr0 ms0 x env0)
                        cur_lr cur_ms xs cur_env = Some (lr', ms_opt', env_b) ->
        wf_let_rails_sync cur_asg (bs_next_var (be_st cur_env)) cur_lw cur_le cur_lr ->
        wf_ms_sync cur_le cur_ms ->
        wf_param_env_for
          (let '(b', vs_xs) := collect_bind_vars collect_free_vars (List.map fst cur_lw) xs in
           vs_xs ++ collect_free_vars b' body) penv ->
        sat_blast_env penv foracle cur_asg cur_env ->
        exists asg_b lenv',
          eval_let_binds (fun ce x => eval_cert_expr penv ce foracle x) cur_le xs =
            raise_ret lenv' /\
          step_spec (be_st cur_env) (be_st env_b) cur_asg asg_b /\
          sat_blast_env penv foracle asg_b env_b /\
          wf_let_rails_sync asg_b (bs_next_var (be_st env_b)) lw' lenv' lr' /\
          wf_ms_sync lenv' ms_opt' /\
          wf_param_env_for (collect_free_vars (List.map fst lw') body) penv).
    { induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_lw seen cur_lr cur_ms cur_le cur_asg cur_env
               Hlw_xs Hbl_xs Hsync_c Hms_c Hpenv_c Henv_c;
        cbn in Hlw_xs, Hbl_xs.
      - inversion Hlw_xs; inversion Hbl_xs; subst cur_lw cur_lr cur_ms cur_env.
        exists cur_asg, cur_le.
        split; [reflexivity |
        split; [exact (step_spec_refl _ cur_asg (proj1 Henv_c)) |
        split; [exact Henv_c | split; [exact Hsync_c | split; [exact Hms_c | exact Hpenv_c]]]]].
      - cbn in IHbe.
        destruct (is_dollar_let_name bnm && negb (string_in_list bnm seen) &&
                  wt_cert_expr cur_lw be) eqn:Hok; [| discriminate Hlw_xs].
        rewrite !andb_true_iff in Hok; destruct Hok as ([_ _] & Hwt_be).
        destruct (blast_cert_expr ctx cur_lr cur_ms be cur_env)
          as [[r_be env1] |] eqn:Ebe; [| discriminate Hbl_xs].
        cbn [collect_bind_vars] in Hpenv_c.
        destruct (collect_bind_vars collect_free_vars (bnm :: List.map fst cur_lw) rx)
          as [b_end vs_rx] eqn:Hbv.
        assert (Hp_be : wf_param_env_for (collect_free_vars (List.map fst cur_lw) be) penv)
          by (intros x wx Hx; apply Hpenv_c; rewrite <- app_assoc; apply in_app_iff; left; exact Hx).
        destruct (IHbe ctx cur_lw cur_lr cur_ms penv cur_le foracle cur_asg cur_env env1 r_be
                    Ebe Hwt_be Hsync_c Hms_c Hp_be Hctx Henv_c)
          as (asg1 & dv_be & Ev_be & Hs1 & Henv1 & Hwfr_be & Hrm_be).
        set (exp_be := expand_lets_with (let_val_exprs cur_le) be).
        assert (Hnext_ms :
                  exists next_ms,
                    (match cur_ms with
                     | None => Some None
                     | Some (ms, fuel) =>
                         match expand_lets_fueled_with ms be fuel with
                         | Some (ebe, bsz, fuel1) =>
                             Some (Some ((bnm, (ebe, bsz)) :: ms, fuel1))
                         | None => None
                         end
                     end) = Some next_ms /\
                    wf_ms_sync ((bnm, (dv_be, exp_be)) :: cur_le) next_ms).
        { destruct cur_ms as [[ms fuel] |].
          - destruct (expand_lets_fueled_with ms be fuel)
              as [[[ebe bsz] fuel1] |] eqn:Efbe; [| discriminate Hbl_xs].
            exists (Some ((bnm, (ebe, bsz)) :: ms, fuel1)); split; [reflexivity |].
            cbn [wf_ms_sync strip_let_sizes let_val_exprs List.map] in Hms_c |- *.
            pose proof (expand_lets_fueled_with_eq be ms fuel ebe bsz fuel1 Efbe) as Hebe.
            rewrite Hms_c in Hebe; subst ebe; rewrite Hms_c; reflexivity.
          - exists None; split; [reflexivity | exact I]. }
        destruct Hnext_ms as (next_ms & Hnms_eq & Hms_next).
        rewrite Hnms_eq in Hbl_xs; clear Hnms_eq.
        pose proof (wf_let_rails_sync_step cur_asg asg1 _ _ cur_lw cur_le cur_lr Hsync_c Hs1)
          as Hsync1.
        assert (Hsync_next :
                  wf_let_rails_sync asg1 (bs_next_var (be_st env1))
                    ((bnm, cert_expr_bit_width be) :: cur_lw)
                    ((bnm, (dv_be, exp_be)) :: cur_le)
                    ((bnm, (cert_expr_bit_width be, r_be)) :: cur_lr)).
        { intros q; cbn [lookup_let_width lookup_let_val lookup_let_rail].
          destruct (String.eqb bnm q); [| exact (Hsync1 q)].
          split; [reflexivity | split; [exact (rail_matches_wf_scalar _ asg1 r_be dv_be Hrm_be) |
            split; [exact Hwfr_be | exact Hrm_be]]]. }
        assert (Hp_rx :
                  wf_param_env_for
                    (let '(b', vs_xs) :=
                       collect_bind_vars collect_free_vars
                         (List.map fst ((bnm, cert_expr_bit_width be) :: cur_lw)) rx in
                     vs_xs ++ collect_free_vars b' body) penv).
        { cbn [List.map fst]; rewrite Hbv.
          intros x wx Hx; apply Hpenv_c; rewrite <- app_assoc; apply in_app_iff; right; exact Hx. }
        destruct (IHrx ((bnm, cert_expr_bit_width be) :: cur_lw) (bnm :: seen)
                    ((bnm, (cert_expr_bit_width be, r_be)) :: cur_lr)
                    next_ms ((bnm, (dv_be, exp_be)) :: cur_le) asg1 env1
                    Hlw_xs Hbl_xs Hsync_next Hms_next Hp_rx Henv1)
          as (asg_b & lenv' & Ev_rx & Hs_rx & Henv_b & Hsync_b & Hms_b & Hp_body).
        exists asg_b, lenv'.
        split; [cbn [eval_let_binds]; rewrite Ev_be; cbn [eou_bind]; exact Ev_rx |
        split; [exact (step_spec_trans _ _ _ _ _ _ Hs1 Hs_rx) |
        split; [exact Henv_b | split; [exact Hsync_b | split; [exact Hms_b | exact Hp_body]]]]]. }
    destruct (Hstep_bs bs lw [] lr ms_opt lenv asg env Elw Ebs Hsync Hms Hpenv Henv)
      as (asg_b & lenv' & Ev_bs & Hs_bs & Henv_b & Hsync_b & Hms_b & Hp_body).
    destruct (IHb ctx lw' lr' ms_opt' penv lenv' foracle asg_b env_b env' out
                Hbl Hwt Hsync_b Hms_b Hp_body Hctx Henv_b)
      as (asg' & vout & Ev_body & Hs_body & Henv' & Hwf_out & Hm_out).
    exists asg', vout.
    split; [rewrite Ev_bs; cbn [eou_bind]; exact Ev_body |
    split; [exact (step_spec_trans _ _ _ _ _ _ Hs_bs Hs_body) |
    split; [exact Henv' | split; [exact Hwf_out | exact Hm_out]]]].
Qed.

(** *** 7.6 [ub_ctx] Assumption Clause Encoding & Top-Level Refinement Entrypoint *)

Fixpoint vars_subset_b (sub sup : list (string * positive)) {struct sub} : bool :=
  match sub with
  | [] => true
  | (nm, w) :: rest =>
      existsb (fun '(nm', w') => String.eqb nm nm' && Pos.eqb w w') sup &&
      vars_subset_b rest sup
  end.

Lemma vars_subset_b_wf_param_env :
  forall {Pa : Params} sub sup (penv : param_env Pa),
    vars_subset_b sub sup = true ->
    wf_param_env_for sup penv ->
    wf_param_env_for sub penv.
Proof.
  induction sub as [| [nm w] rest IH]; intros sup penv Hsub Hsup nm0 w0 Hin; [contradiction |].
  cbn [vars_subset_b] in Hsub; apply andb_true_iff in Hsub as [Hhd Htl].
  destruct Hin as [Heq | Hrest]; [| exact (IH sup penv Htl Hsup nm0 w0 Hrest)].
  inversion Heq; subst nm0 w0; clear Heq.
  apply existsb_exists in Hhd as [[nm' w'] [Hin_sup Heqb]].
  apply andb_true_iff in Heqb as [Hs Hw].
  apply String.eqb_eq in Hs; apply Pos.eqb_eq in Hw; subst nm' w'.
  exact (Hsup nm w Hin_sup).
Qed.

Lemma eval_let_free_ret_wf_param_env :
  forall {Pa : Params} (e : cert_expr) (penv : param_env Pa) (foracle : freeze_oracle) v,
    is_let_free_expr e = true ->
    eval_cert_expr penv [] foracle e = raise_ret v ->
    wf_param_env_for (collect_free_vars [] e) penv.
Proof.
  intros Pa e; induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ];
    intros penv foracle v Hlf Hev;
    cbn [is_let_free_expr eval_cert_expr collect_free_vars] in *.
  - intros _ _ [].
  - intros _ _ [].
  - intros nm0 w0 [Heq | []]; inversion Heq; subst nm0 w0.
    destruct (penv nm) as [dv |] eqn:Epm; [| discriminate Hev].
    destruct (check_scalar_width_inv w dv v Hev) as [_ Hwf].
    exists dv; split; [reflexivity | exact Hwf].
  - apply andb_true_iff in Hlf as [Hl Hr].
    destruct (eval_cert_expr penv [] foracle l) as [| | | vl] eqn:El;
      [discriminate Hev.. | cbn [eou_bind] in Hev].
    destruct (eval_cert_expr penv [] foracle r) as [| | | vr] eqn:Er;
      [discriminate Hev.. |].
    intros x wx Hx; apply in_app_iff in Hx as [Hx | Hx];
      [exact (IHl penv foracle vl Hl El x wx Hx)
      | exact (IHr penv foracle vr Hr Er x wx Hx)].
  - apply andb_true_iff in Hlf as [Hl Hr].
    destruct (eval_cert_expr penv [] foracle l) as [| | | vl] eqn:El;
      [discriminate Hev.. | cbn [eou_bind] in Hev].
    destruct (eval_cert_expr penv [] foracle r) as [| | | vr] eqn:Er;
      [discriminate Hev.. |].
    intros x wx Hx; apply in_app_iff in Hx as [Hx | Hx];
      [exact (IHl penv foracle vl Hl El x wx Hx)
      | exact (IHr penv foracle vr Hr Er x wx Hx)].
  - destruct (eval_cert_expr penv [] foracle o) as [| | | vo] eqn:Eo;
      [discriminate Hev.. | exact (IHo penv foracle vo Hlf Eo)].
  - rewrite !andb_true_iff in Hlf; destruct Hlf as ([Hc Ht] & Hf).
    destruct (eval_cert_expr penv [] foracle c) as [| | | vc] eqn:Ec;
      [discriminate Hev.. | cbn [eou_bind] in Hev].
    destruct (eval_cert_expr penv [] foracle t) as [| | | vt] eqn:Et;
      [discriminate Hev.. | cbn [eou_bind] in Hev].
    destruct (eval_cert_expr penv [] foracle f) as [| | | vf] eqn:Ef;
      [discriminate Hev.. |].
    intros x wx Hx; apply in_app_iff in Hx as [Hx | Hx];
      [exact (IHc penv foracle vc Hc Ec x wx Hx) |].
    apply in_app_iff in Hx as [Hx | Hx];
      [exact (IHt penv foracle vt Ht Et x wx Hx)
      | exact (IHf penv foracle vf Hf Ef x wx Hx)].
  - destruct (eval_cert_expr penv [] foracle o) as [| | | vo] eqn:Eo;
      [discriminate Hev.. | exact (IHo penv foracle vo Hlf Eo)].
  - discriminate Hlf.
Qed.

Definition dvalue_int_unsigned {Pa : Params} (dv : @dvalue Pa) : Z :=
  match dv with
  | DVALUE_Base (@DVALUE_I _ w x) => @Integers.unsigned w x
  | _ => 0%Z
  end.

Definition blast_one_ub_assumption
  (full_ctx : ub_ctx) (known_vars : list (string * positive))
  (ua : ub_assumption) (env : blast_env) : blast_env :=
  match ua with
  | UBA_DivisorNonZero div_e =>
      match expand_lets_fueled norm_let_expand_budget div_e with
      | Some ec =>
          if is_let_free_expr ec && wt_cert_expr [] ec then
            let ms_ec := if expr_has_freeze ec then Some ([], default_let_expand_budget) else None in
            match blast_cert_expr full_ctx [] ms_ec ec env with
            | Some (r_d, env1) =>
                let '(nz_lit, st2) := emit_or_list_opt (rbv_bits r_d) (be_st env1) in
                let st3 := add_clauses [[neg_lit (rbv_psn r_d)]; [nz_lit]] st2 in
                mk_blast_env st3 (be_vars env1) (be_freezes env1)
            | None => env
            end
          else env
      | None => env
      end
  | UBA_BranchCondDefined cond_e =>
      match expand_lets_fueled norm_let_expand_budget cond_e with
      | Some ec =>
          if is_let_free_expr ec && wt_cert_expr [] ec &&
             vars_subset_b (collect_free_vars [] ec) known_vars then
            let ms_ec := if expr_has_freeze ec then Some ([], default_let_expand_budget) else None in
            match blast_cert_expr full_ctx [] ms_ec ec env with
            | Some (r_c, env1) =>
                let st2 := add_clauses [[neg_lit (rbv_psn r_c)]] (be_st env1) in
                mk_blast_env st2 (be_vars env1) (be_freezes env1)
            | None => env
            end
          else env
      | None => env
      end
  | _ => env
  end.

Fixpoint blast_ub_ctx
  (full_ctx : ub_ctx) (known_vars : list (string * positive))
  (rem : ub_ctx) (env : blast_env) {struct rem} : blast_env :=
  match rem with
  | [] => env
  | ua :: rest =>
      blast_ub_ctx full_ctx known_vars rest
        (blast_one_ub_assumption full_ctx known_vars ua env)
  end.

Lemma blast_one_ub_assumption_sat :
  forall {Pa : Params} full_ctx known_vars ua (penv : param_env Pa) foracle asg env,
    ub_ctx_holds penv foracle full_ctx ->
    ub_assumption_holds penv foracle ua ->
    wf_param_env_for known_vars penv ->
    sat_blast_env penv foracle asg env ->
    exists asg',
      sat_blast_env penv foracle asg'
        (blast_one_ub_assumption full_ctx known_vars ua env).
Proof.
  intros Pa full_ctx known_vars ua penv foracle asg env Hctx Hua Hknown Henv.
  destruct ua; cbn [blast_one_ub_assumption]; try (exists asg; exact Henv).
  - (* UBA_DivisorNonZero *)
    rename divisor into div_e.
    destruct (expand_lets_fueled norm_let_expand_budget div_e) as [ec |] eqn:Eexp;
      [| exists asg; exact Henv].
    destruct (is_let_free_expr ec && wt_cert_expr [] ec) eqn:Echk;
      [| exists asg; exact Henv].
    apply andb_true_iff in Echk as [Hlf Hwt].
    set (ms_ec := if expr_has_freeze ec then Some (@nil (string * (cert_expr * nat)), default_let_expand_budget) else None).
    destruct (blast_cert_expr full_ctx [] ms_ec ec env) as [[r_d env1] |] eqn:Ebl;
      [| exists asg; exact Henv].
    destruct Hua as (w0 & i0 & Hev_div & Hnz0).
    pose proof (expand_lets_fueled_eq norm_let_expand_budget div_e ec Eexp) as Hec_eq.
    rewrite <- Hec_eq in Hev_div.
    pose proof (eval_let_free_ret_wf_param_env ec penv foracle _ Hlf Hev_div) as Hpenv_ec.
    assert (Hms_ec : wf_ms_sync (@nil (string * (@dvalue Pa * cert_expr))) ms_ec)
      by (unfold ms_ec; destruct (expr_has_freeze ec); cbn; trivial).
    destruct (blast_cert_expr_sat ec full_ctx [] [] ms_ec penv [] foracle asg env env1 r_d
                Ebl Hwt (wf_let_rails_sync_nil asg _) Hms_ec Hpenv_ec Hctx Henv)
      as (asg1 & vd & Evd & _ & Henv1 & Hwfr & Hmrd).
    set (sz := cert_expr_bit_width ec) in *.
    unfold eval_closed_cert_expr in Hev_div; rewrite Hev_div in Evd.
    injection Evd as Evd_eq; subst vd.
    destruct Hwfr as ([Hwr Hlr] & Hbr & Hpr).
    destruct (emit_or_list_opt (rbv_bits r_d) (be_st env1)) as [nz_lit st2] eqn:Eor.
    destruct (emit_or_list_opt_step (rbv_bits r_d) asg1 (be_st env1) nz_lit st2
                Hbr (proj1 Henv1) Eor)
      as (asg2 & Hs2 & Hwf_nz & Hev_nz).
    pose proof (sat_blast_env_step penv foracle asg1 asg2 env1 st2 Henv1 Hs2) as Henv2.
    unfold rail_matches_dvalue in Hmrd.
    destruct (eval_rail_psn asg1 r_d) eqn:Epd; [discriminate Hmrd |].
    pose proof (f_equal dvalue_int_unsigned Hmrd) as Hu_eq; cbn in Hu_eq.
    rewrite Hu_eq, (unsigned_eval_rail_val sz asg1 r_d Hlr) in Hnz0.
    assert (Hex_true : existsb (fun b : bool => b) (List.map (eval_lit asg1) (rbv_bits r_d)) = true).
    { pose proof (bools_to_Z_zero_iff (List.map (eval_lit asg1) (rbv_bits r_d))) as Hzf.
      destruct (Z.eqb_spec (bools_to_Z (List.map (eval_lit asg1) (rbv_bits r_d))) 0%Z)
        as [Hez | _]; [congruence |].
      destruct (existsb (fun b : bool => b) (List.map (eval_lit asg1) (rbv_bits r_d)));
        [reflexivity | discriminate Hzf]. }
    pose proof (wf_lit_bound_mono _ _ (rbv_psn r_d) (proj1 Hs2) Hpr) as Hpr2.
    pose proof (step_spec_eval_lit _ _ asg1 asg2 (rbv_psn r_d) Hs2 Hpr) as Hpr_ev2.
    destruct (proj1 Henv2) as ([Hge2 Hwf_st2] & Ha1_2 & Hev_st2); cbn [be_st] in *.
    assert (Hcls_wf : Forall (wf_clause_bound (bs_next_var st2))
                        [[neg_lit (rbv_psn r_d)]; [nz_lit]]).
    { repeat constructor; [apply wf_lit_bound_neg; exact Hpr2 | exact Hwf_nz]. }
    assert (Hcls_sat : forall cl,
              In cl [[neg_lit (rbv_psn r_d)]; [nz_lit]] ->
              eval_clause asg2 cl = true).
    { intros cl [<- | [<- | []]]; cbn [eval_clause existsb].
      - rewrite (eval_neg_lit_nonzero asg2 _ (wf_lit_bound_nonzero _ _ Hpr2)), Hpr_ev2.
        unfold eval_rail_psn in Epd; rewrite Epd; reflexivity.
      - rewrite Hev_nz, Hex_true; reflexivity. }
    pose proof (add_clauses_sat_intro asg2 st2 _ Hge2 Ha1_2 Hwf_st2 Hcls_wf Hev_st2 Hcls_sat)
      as Hsat3.
    assert (Hbs3 : bs_next_var (add_clauses [[neg_lit (rbv_psn r_d)]; [nz_lit]] st2) =
                   bs_next_var st2)
      by (unfold add_clauses; destruct (append_clauses _ _); reflexivity).
    exists asg2.
    exact (sat_blast_env_step penv foracle asg2 asg2
             (mk_blast_env st2 (be_vars env1) (be_freezes env1))
             (add_clauses [[neg_lit (rbv_psn r_d)]; [nz_lit]] st2)
             Henv2
             (conj (eq_ind_r (fun x => (bs_next_var st2 <= x)%positive) (Pos.le_refl _) Hbs3)
                   (conj (agree_below_refl _ asg2) Hsat3))).
  - (* UBA_BranchCondDefined *)
    rename cond into cond_e.
    destruct (expand_lets_fueled norm_let_expand_budget cond_e) as [ec |] eqn:Eexp;
      [| exists asg; exact Henv].
    destruct (is_let_free_expr ec && wt_cert_expr [] ec &&
              vars_subset_b (collect_free_vars [] ec) known_vars) eqn:Echk;
      [| exists asg; exact Henv].
    rewrite !andb_true_iff in Echk; destruct Echk as ([Hlf Hwt] & Hsub).
    set (ms_ec := if expr_has_freeze ec then Some (@nil (string * (cert_expr * nat)), default_let_expand_budget) else None).
    destruct (blast_cert_expr full_ctx [] ms_ec ec env) as [[r_c env1] |] eqn:Ebl;
      [| exists asg; exact Henv].
    pose proof (vars_subset_b_wf_param_env _ _ penv Hsub Hknown) as Hpenv_ec.
    assert (Hms_ec : wf_ms_sync (@nil (string * (@dvalue Pa * cert_expr))) ms_ec)
      by (unfold ms_ec; destruct (expr_has_freeze ec); cbn; trivial).
    destruct (blast_cert_expr_sat ec full_ctx [] [] ms_ec penv [] foracle asg env env1 r_c
                Ebl Hwt (wf_let_rails_sync_nil asg _) Hms_ec Hpenv_ec Hctx Henv)
      as (asg1 & vc & Evc & _ & Henv1 & (_ & _ & Hpc) & Hmrc).
    pose proof (expand_lets_fueled_eq norm_let_expand_budget cond_e ec Eexp) as Hec_eq.
    assert (Hvc_np : vc <> DVALUE_Base DVALUE_Poison)
      by (apply Hua; rewrite <- Hec_eq; exact Evc).
    unfold rail_matches_dvalue in Hmrc.
    destruct (eval_rail_psn asg1 r_c) eqn:Epc; [congruence |].
    destruct (proj1 Henv1) as ([Hge2 Hwf_st1] & Ha1_1 & Hev_st1).
    assert (Hcls_wf : Forall (wf_clause_bound (bs_next_var (be_st env1)))
                        [[neg_lit (rbv_psn r_c)]])
      by (repeat constructor; apply wf_lit_bound_neg; exact Hpc).
    assert (Hcls_sat : forall cl,
              In cl [[neg_lit (rbv_psn r_c)]] ->
              eval_clause asg1 cl = true).
    { intros cl [<- | []]; cbn [eval_clause existsb].
      rewrite (eval_neg_lit_nonzero asg1 _ (wf_lit_bound_nonzero _ _ Hpc)).
      unfold eval_rail_psn in Epc; rewrite Epc; reflexivity. }
    pose proof (add_clauses_sat_intro asg1 (be_st env1) _ Hge2 Ha1_1 Hwf_st1 Hcls_wf Hev_st1 Hcls_sat)
      as Hsat2.
    assert (Hbs2 : bs_next_var (add_clauses [[neg_lit (rbv_psn r_c)]] (be_st env1)) =
                   bs_next_var (be_st env1))
      by (unfold add_clauses; destruct (append_clauses _ _); reflexivity).
    exists asg1.
    exact (sat_blast_env_step penv foracle asg1 asg1 env1
             (add_clauses [[neg_lit (rbv_psn r_c)]] (be_st env1))
             Henv1
             (conj (eq_ind_r (fun x => (bs_next_var (be_st env1) <= x)%positive) (Pos.le_refl _) Hbs2)
                   (conj (agree_below_refl _ asg1) Hsat2))).
Qed.

Lemma blast_ub_ctx_sat :
  forall {Pa : Params} full_ctx known_vars rem (penv : param_env Pa) foracle asg env,
    ub_ctx_holds penv foracle full_ctx ->
    Forall (ub_assumption_holds penv foracle) rem ->
    wf_param_env_for known_vars penv ->
    sat_blast_env penv foracle asg env ->
    exists asg',
      sat_blast_env penv foracle asg' (blast_ub_ctx full_ctx known_vars rem env).
Proof.
  intros Pa full_ctx known_vars rem penv foracle asg env Hctx Hrem Hknown; revert asg env.
  induction Hrem as [| ua rest Hua _ IH]; intros asg env Henv; cbn [blast_ub_ctx].
  - exists asg; exact Henv.
  - destruct (blast_one_ub_assumption_sat full_ctx known_vars ua penv foracle asg env
                Hctx Hua Hknown Henv) as [asg1 Henv1].
    exact (IH asg1 _ Henv1).
Qed.

Definition default_dpll_fuel : nat := 4096%nat.

Definition check_cex_unsat
  (cex_cnf : cnf) (opt_pf : option (list lrat_step)) : bool :=
  match opt_pf with
  | Some pf => check_lrat_unsat cex_cnf pf
  | None => solve_cnf_unsat default_dpll_fuel (coi_filter_cnf cex_cnf)
  end.

Lemma check_cex_unsat_sound :
  forall cex_cnf opt_pf,
    check_cex_unsat cex_cnf opt_pf = true ->
    forall a, eval_cnf a cex_cnf = false.
Proof.
  intros cex_cnf [pf |] Hchk a; cbn [check_cex_unsat] in Hchk.
  - exact (check_lrat_unsat_sound cex_cnf pf Hchk a).
  - exact (eval_cnf_incl_false _ cex_cnf a (coi_filter_cnf_incl cex_cnf)
             (solve_cnf_unsat_sound default_dpll_fuel _ a Hchk)).
Qed.

Definition check_blast_pair
  (ctx : ub_ctx) (s t : cert_expr) (opt_pf : option (list lrat_step)) : bool :=
  let sz := cert_expr_bit_width s in
  let known_vars := collect_free_vars [] s ++ collect_free_vars [] t in
  let env0 := blast_ub_ctx ctx known_vars ctx (mk_blast_env (init_blast_state 2%positive) [] []) in
  let ms_s := if expr_has_freeze s then Some ([], default_let_expand_budget) else None in
  let ms_t := if expr_has_freeze t then Some ([], default_let_expand_budget) else None in
  match blast_cert_expr ctx [] ms_s s env0 with
  | Some (src_r, env1) =>
      match blast_cert_expr ctx [] ms_t t env1 with
      | Some (tgt_r, env2) =>
          check_cex_unsat
            (blast_refinement_cex_opt sz lit_true src_r tgt_r (be_st env2))
            opt_pf
      | None => false
      end
  | None => false
  end.

Lemma check_blast_pair_sound :
  forall {Pa : Params} (ctx : ub_ctx) (s t : cert_expr)
         (opt_pf : option (list lrat_step))
         (penv : param_env Pa) (foracle : freeze_oracle),
    Pos.eqb (cert_expr_bit_width s) (cert_expr_bit_width t) = true ->
    wt_cert_expr [] s = true ->
    wt_cert_expr [] t = true ->
    check_blast_pair ctx s t opt_pf = true ->
    wf_param_env_for (collect_free_vars [] s) penv ->
    wf_param_env_for (collect_free_vars [] t) penv ->
    ub_ctx_holds penv foracle ctx ->
    refine_eou_dvalue
      (eval_closed_cert_expr penv foracle s)
      (eval_closed_cert_expr penv foracle t).
Proof.
  intros Pa ctx s t opt_pf penv foracle Hbw Hwts Hwtt Hchk Hps Hpt Hctx.
  apply Pos.eqb_eq in Hbw.
  unfold check_blast_pair in Hchk; cbn zeta in Hchk.
  set (sz := cert_expr_bit_width s) in *.
  set (known_vars := collect_free_vars [] s ++ collect_free_vars [] t) in *.
  set (init_env := mk_blast_env (init_blast_state 2%positive) [] []).
  set (env0 := blast_ub_ctx ctx known_vars ctx init_env) in *.
  set (ms_s := if expr_has_freeze s then Some (@nil (string * (cert_expr * nat)), default_let_expand_budget) else None) in *.
  set (ms_t := if expr_has_freeze t then Some (@nil (string * (cert_expr * nat)), default_let_expand_budget) else None) in *.
  destruct (blast_cert_expr ctx [] ms_s s env0) as [[src_r env1] |] eqn:Ebs; [| discriminate Hchk].
  destruct (blast_cert_expr ctx [] ms_t t env1) as [[tgt_r env2] |] eqn:Ebt; [| discriminate Hchk].
  assert (Hknown : wf_param_env_for known_vars penv).
  { intros x wx Hx; apply in_app_iff in Hx as [Hx | Hx]; [exact (Hps x wx Hx) | exact (Hpt x wx Hx)]. }
  assert (Hinit_env : sat_blast_env penv foracle (fun _ => true) init_env).
  { split; [exact init_blast_state_sat | split; intros; discriminate]. }
  destruct (blast_ub_ctx_sat ctx known_vars ctx penv foracle (fun _ => true) init_env
              Hctx Hctx Hknown Hinit_env)
    as [asg0 Henv0].
  assert (Hms_s : wf_ms_sync (@nil (string * (@dvalue Pa * cert_expr))) ms_s)
    by (unfold ms_s; destruct (expr_has_freeze s); cbn; trivial).
  assert (Hms_t : wf_ms_sync (@nil (string * (@dvalue Pa * cert_expr))) ms_t)
    by (unfold ms_t; destruct (expr_has_freeze t); cbn; trivial).
  destruct (blast_cert_expr_sat s ctx [] [] ms_s penv [] foracle asg0 env0 env1 src_r
              Ebs Hwts (wf_let_rails_sync_nil asg0 _) Hms_s Hps Hctx Henv0)
    as (asg1 & vs & Evs & _ & Henv1 & Hwfs & Hms_v).
  destruct (blast_cert_expr_sat t ctx [] [] ms_t penv [] foracle asg1 env1 env2 tgt_r
              Ebt Hwtt (wf_let_rails_sync_nil asg1 _) Hms_t Hpt Hctx Henv1)
    as (asg2 & vt & Evt & Hs12 & Henv2 & Hwft & Hmt_v).
  unfold eval_closed_cert_expr; rewrite Evs, Evt; cbn [refine_eou_dvalue].
  fold sz in Hwfs, Hms_v; rewrite <- Hbw in Hwft, Hmt_v.
  pose proof (wf_rail_bound_mono sz _ _ src_r (proj1 Hs12) Hwfs) as Hwfs2.
  pose proof (rail_matches_dvalue_agree sz _ asg1 asg2 src_r vs (proj1 (proj2 Hs12)) Hwfs Hms_v) as Hms2.
  unfold rail_matches_dvalue in Hms2, Hmt_v.
  destruct (eval_rail_psn asg2 src_r) eqn:Eps; [subst vs; apply dvalue_refines_poison_l |].
  assert (Hlt_wf : wf_lit_bound (bs_next_var (be_st env2)) lit_true)
    by (cbn; pose proof (proj1 (proj1 (proj1 Henv2))); lia).
  assert (Hlt_ev : eval_lit asg2 lit_true = true)
    by exact (proj1 (proj2 (proj1 Henv2))).
  destruct (blast_refinement_cex_opt_unsat_core sz lit_true src_r tgt_r (be_st env2) asg2
              (proj1 Henv2) Hlt_wf Hwfs2 Hwft (check_cex_unsat_sound _ opt_pf Hchk) Hlt_ev Eps)
    as [Ept Heqv].
  rewrite Ept, Heqv in Hmt_v; subst vs vt; apply dvalue_refines_refl.
Qed.

Definition check_expr_refines_with_lrat
  (ctx : ub_ctx) (src tgt : cert_expr) (opt_pf : option (list lrat_step)) : bool :=
  if check_expr_refines ctx src tgt then true
  else if negb (Pos.eqb (cert_expr_bit_width src) (cert_expr_bit_width tgt) &&
                wt_cert_expr [] src &&
                wt_cert_expr [] tgt)
  then false
  else if check_blast_pair ctx src tgt opt_pf then true
  else if check_wf_let_dag_fast norm_let_expand_budget src &&
          check_wf_let_dag_fast norm_let_expand_budget tgt
  then
    match expand_lets_fueled norm_let_expand_budget src,
          expand_lets_fueled norm_let_expand_budget tgt with
    | Some es, Some et =>
        let ns := normalize_cert_expr ctx es in
        let nt := normalize_cert_expr ctx et in
        check_blast_pair ctx ns nt opt_pf
    | _, _ => false
    end
  else false.

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
  destruct (Pos.eqb (cert_expr_bit_width src) (cert_expr_bit_width tgt) &&
            wt_cert_expr [] src && wt_cert_expr [] tgt) eqn:Ewt;
    cbn [negb] in Hchk; [| discriminate Hchk].
  rewrite !andb_true_iff in Ewt; destruct Ewt as ([Hbw Hwts] & Hwtt).
  destruct (check_blast_pair ctx src tgt opt_pf) eqn:Eraw;
    [exact (check_blast_pair_sound ctx src tgt opt_pf penv foracle
              Hbw Hwts Hwtt Eraw Hps Hpt Hctx) |].
  destruct (check_wf_let_dag_fast norm_let_expand_budget src &&
            check_wf_let_dag_fast norm_let_expand_budget tgt) eqn:Edag;
    [| discriminate Hchk].
  apply andb_true_iff in Edag as [Hdags0 Hdagt0].
  pose proof (check_wf_let_dag_fast_sound norm_let_expand_budget src Hdags0) as Hdags.
  pose proof (check_wf_let_dag_fast_sound norm_let_expand_budget tgt Hdagt0) as Hdagt.
  destruct (expand_lets_fueled norm_let_expand_budget src) as [es |] eqn:Ees; [| discriminate Hchk].
  destruct (expand_lets_fueled norm_let_expand_budget tgt) as [et |] eqn:Eet; [| discriminate Hchk].
  pose proof (expand_lets_fueled_eq norm_let_expand_budget src es Ees) as Hes_eq; subst es.
  pose proof (expand_lets_fueled_eq norm_let_expand_budget tgt et Eet) as Het_eq; subst et.
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
            Pos.eqb (cert_expr_bit_width (normalize_cert_expr ctx (expand_lets src)))
                    (cert_expr_bit_width (normalize_cert_expr ctx (expand_lets tgt))) = true)
    by (apply Pos.eqb_eq; congruence).
  apply (refine_eou_compat _ _ _ _ Heq_src Heq_tgt).
  exact (check_blast_pair_sound ctx
           (normalize_cert_expr ctx (expand_lets src))
           (normalize_cert_expr ctx (expand_lets tgt))
           opt_pf penv foracle Hbw_norm Hwt_ns Hwt_nt Hchk Hp_ns Hp_nt Hctx).
Qed.
