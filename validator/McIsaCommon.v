(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Shared ISA-Agnostic Bitvector, ABI & Symbolic Expression Utilities ([CertValidator.McIsaCommon])

    Provides bit slicing, signed extension, argument/return width helpers,
    first-wins [pos_trie] instruction indexing and visited-set operations,
    [eval_closed_cert_expr] bitvector lemmas, and [wf_sym_expr] proofs shared
    between [Rv64Sem], [A64CoreSem], and [McFormat]. *)

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
  Numeric.Zbits
  Numeric.Integers
  Syntax.LLVMAst
  Syntax.DynamicTypes
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.Operations.Compare
  Semantics.Operations.Conversion
  Semantics.Operations.Select.

From CertValidator Require Import
  LratCore
  AigGates
  CertFormatAst
  AlgRulesEval.

Unset Implicit Arguments.
Unset Strict Implicit.
Set Default Goal Selector "!".

#[local] Arguments Pos.eqb _ _ : simpl nomatch.
#[local] Arguments Pos.ltb _ _ : simpl nomatch.
#[local] Arguments Pos.leb _ _ : simpl nomatch.
#[local] Arguments N.eqb _ _ : simpl nomatch.
#[local] Arguments N.ltb _ _ : simpl nomatch.
#[local] Arguments N.leb _ _ : simpl nomatch.
#[local] Arguments N.div _ _ : simpl nomatch.
#[local] Arguments N.modulo _ _ : simpl nomatch.
#[local] Arguments Z.eqb _ _ : simpl nomatch.
#[local] Arguments Z.ltb _ _ : simpl nomatch.
#[local] Arguments Z.leb _ _ : simpl nomatch.
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

(** ** 1. Bit-Level Helpers & Relative Offsets *)

Definition bit_slice (v lo len : N) : N :=
  N.modulo (N.div v (N.pow 2%N lo)) (N.pow 2%N len).

Definition sext_z (v bits : N) : Z :=
  let m := Z.pow 2 (Z.of_N bits) in
  let h := Z.pow 2 (Z.of_N bits - 1) in
  let zv := ((Z.of_N v) mod m)%Z in
  if Z.geb zv h then (zv - m)%Z else zv.

Definition rv_mask_shamt (w : positive) (z : Z) : @Integers.bit_int w :=
  @Integers.repr w (z mod Z.pos w).

Definition add_rel_off (pc : N) (rel : Z) : option N :=
  let sum := (Z.of_N pc + rel)%Z in
  if Z.geb sum 0%Z then Some (Z.to_N sum) else None.

(** ** 2. Argument Width Specs, Shared [cert_expr] Constructors & Return Truncation *)

Variant rv_arg_ext : Set :=
| RAE_None
| RAE_SignExt
| RAE_ZeroExt.

Record rv_arg_spec : Set := mk_rv_arg_spec {
  ras_name : string;
  ras_width : positive;
  ras_ext : rv_arg_ext;
}.

Definition rv_supported_arg_width (w : positive) : bool :=
  match w with
  | 1%positive | 8%positive | 16%positive | 32%positive | 64%positive => true
  | _ => false
  end.

Lemma rv_supported_arg_width_lt64 : forall w,
  rv_supported_arg_width w = true ->
  (w =? 64)%positive = false ->
  (w <? 64)%positive = true.
Proof.
  intros w Hw Hne.
  do 7 (destruct w as [w|w|]; cbn in Hw; try discriminate Hw; try reflexivity).
  all: try (rewrite Pos.eqb_refl in Hne; discriminate Hne).
Qed.

Definition rv_valid_arg_spec (sp : rv_arg_spec) : bool :=
  rv_supported_arg_width (ras_width sp) && negb (starts_with_dollar (ras_name sp)).

Definition z_to_bv_N (w : positive) (z : Z) : N :=
  Z.to_N (z mod @Integers.modulus w).

Definition ce_bv_z (w : positive) (z : Z) : cert_expr :=
  CE_BvConst w (z_to_bv_N w z).

Definition ce_all_ones (w : positive) : cert_expr :=
  CE_BvConst w (all_ones_N w).

Definition ce_int_min (w : positive) : cert_expr :=
  CE_BvConst w (Z.to_N (@Integers.half_modulus w)).

Definition ce_trunc64_32 (e : cert_expr) : cert_expr :=
  CE_Cast CCK_Trunc 64%positive 32%positive no_cast_flags e.

Definition ce_sext32_64 (e : cert_expr) : cert_expr :=
  CE_Cast CCK_SExt 32%positive 64%positive no_cast_flags e.

Definition ce_zext64_128 (e : cert_expr) : cert_expr :=
  CE_Cast CCK_ZExt 64%positive 128%positive no_cast_flags e.

Definition ce_sext64_128 (e : cert_expr) : cert_expr :=
  CE_Cast CCK_SExt 64%positive 128%positive no_cast_flags e.

Definition ce_trunc128_64 (e : cert_expr) : cert_expr :=
  CE_Cast CCK_Trunc 128%positive 64%positive no_cast_flags e.

Definition rv_trunc_ret_expr (ret_w : positive) (a0_e : cert_expr) : cert_expr :=
  if Pos.eqb ret_w 64%positive then a0_e
  else CE_Cast CCK_Trunc 64%positive ret_w no_cast_flags a0_e.

Definition rv_trunc_ret_val (ret_w : positive) (a0 : @Integers.bit_int 64)
  : @Integers.bit_int ret_w :=
  if Pos.eqb ret_w 64%positive then
    @Integers.repr ret_w (@Integers.unsigned 64 a0)
  else
    @Integers.repr ret_w (@Integers.unsigned 64 a0).

(** *** 4.1 First-Wins [pos_trie] Instruction Index & Visited Set *)

Fixpoint lookup_by_key {A : Type} (key_of : A -> N) (xs : list A) (k : N)
  {struct xs} : option A :=
  match xs with
  | [] => None
  | x :: rest => if N.eqb (key_of x) k then Some x else lookup_by_key key_of rest k
  end.

Fixpoint pt_of_list_first_acc {A : Type} (key_of : A -> N)
  (im : pos_trie A) (xs : list A) {struct xs} : pos_trie A :=
  match xs with
  | [] => im
  | x :: rest =>
      let k := N.succ_pos (key_of x) in
      match pt_get k im with
      | Some _ => pt_of_list_first_acc key_of im rest
      | None => pt_of_list_first_acc key_of (pt_set k x im) rest
      end
  end.

Definition pt_of_list_first {A : Type} (key_of : A -> N) (xs : list A)
  : pos_trie A :=
  pt_of_list_first_acc key_of (@PT_Empty A) xs.

Lemma pt_of_list_first_acc_get :
  forall {A : Type} (key_of : A -> N) (xs : list A) (im : pos_trie A) (k : N),
    pt_get (N.succ_pos k) (pt_of_list_first_acc key_of im xs) =
    match pt_get (N.succ_pos k) im with
    | Some d => Some d
    | None => lookup_by_key key_of xs k
    end.
Proof.
  intros A key_of xs; induction xs as [| x rest IH];
    intros im k; cbn [pt_of_list_first_acc lookup_by_key].
  - destruct (pt_get (N.succ_pos k) im); reflexivity.
  - destruct (pt_get (N.succ_pos (key_of x)) im) eqn:Ex.
    + rewrite IH; destruct (pt_get (N.succ_pos k) im) eqn:Ek; try reflexivity.
      destruct (N.eqb (key_of x) k) eqn:Heq; [| reflexivity].
      apply N.eqb_eq in Heq; rewrite Heq, Ek in Ex; discriminate Ex.
    + rewrite IH.
      destruct (N.eqb (key_of x) k) eqn:Heq.
      * apply N.eqb_eq in Heq; subst k.
        rewrite Ex, pt_get_set_same; reflexivity.
      * apply N.eqb_neq in Heq.
        assert (Hneq : N.succ_pos k <> N.succ_pos (key_of x)).
        { intro Hinj; apply Heq; symmetry.
          destruct k as [| pk], (key_of x) as [| pm]; cbn in Hinj.
          - reflexivity.
          - destruct pm; discriminate Hinj.
          - destruct pk; discriminate Hinj.
          - f_equal; exact (Pos.succ_inj _ _ Hinj). }
        rewrite (pt_get_set_other _ _ _ _ Hneq); reflexivity.
Qed.

Lemma pt_of_list_first_get :
  forall {A : Type} (key_of : A -> N) (xs : list A) (k : N),
    pt_get (N.succ_pos k) (pt_of_list_first key_of xs) = lookup_by_key key_of xs k.
Proof.
  intros A key_of xs k; unfold pt_of_list_first.
  rewrite pt_of_list_first_acc_get, pt_get_empty; reflexivity.
Qed.

Definition pt_has_n (pc : N) (vis : pos_trie unit) : bool :=
  match pt_get (N.succ_pos pc) vis with
  | Some _ => true
  | None => false
  end.

Definition pt_add_n (pc : N) (vis : pos_trie unit) : pos_trie unit :=
  pt_set (N.succ_pos pc) tt vis.

Fixpoint pt_of_visited_acc (acc : pos_trie unit) (xs : list N) {struct xs} : pos_trie unit :=
  match xs with
  | [] => acc
  | pc :: rest => pt_of_visited_acc (pt_add_n pc acc) rest
  end.

Definition pt_of_visited (xs : list N) : pos_trie unit :=
  pt_of_visited_acc (@PT_Empty unit) xs.

(** ** 3. Bitvector Arithmetic & [eval_closed_cert_expr] Equivalence Lemmas *)

Lemma eval_ce_bv_z :
  forall {Pa : Params} (penv : param_env Pa) foracle w z,
    eval_closed_cert_expr penv foracle (ce_bv_z w z) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w z))).
Proof.
  intros Pa penv foracle w z.
  unfold eval_closed_cert_expr, ce_bv_z, z_to_bv_N; cbn [eval_cert_expr].
  pose proof (@Integers.modulus_pos w) as Hm.
  assert (Hmod : (0 <= z mod @Integers.modulus w)%Z) by (apply Z.mod_pos_bound; lia).
  rewrite (Z2N.id _ Hmod).
  f_equal; f_equal; f_equal.
  apply Integers.eqm_samerepr, Integers.eqm_sym.
  apply Integers.eqmod_mod.
Qed.

Lemma eval_ce_all_ones :
  forall {Pa : Params} (penv : param_env Pa) foracle w,
    eval_closed_cert_expr penv foracle (ce_all_ones w) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.mone w))).
Proof.
  intros Pa penv foracle w.
  unfold eval_closed_cert_expr, ce_all_ones; cbn [eval_cert_expr].
  rewrite repr_all_ones_N; reflexivity.
Qed.

Lemma eval_ce_int_min :
  forall {Pa : Params} (penv : param_env Pa) foracle w,
    eval_closed_cert_expr penv foracle (ce_int_min w) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (@Integers.min_signed w)))).
Proof.
  intros Pa penv foracle w.
  unfold eval_closed_cert_expr, ce_int_min; cbn [eval_cert_expr].
  pose proof (@Integers.half_modulus_pos w) as Hhm.
  rewrite (Z2N.id (@Integers.half_modulus w) ltac:(lia)).
  do 3 f_equal.
  apply Integers.eqm_samerepr.
  unfold Integers.eqm, Integers.min_signed.
  exists 1%Z.
  rewrite Integers.half_modulus_modulus; lia.
Qed.

Lemma eval_ce_const :
  forall {Pa : Params} (penv : param_env Pa) foracle w v,
    eval_closed_cert_expr penv foracle (CE_BvConst w v) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N v)))).
Proof.
  intros; reflexivity.
Qed.

Lemma eval_ce_trunc :
  forall {Pa : Params} (penv : param_env Pa) foracle fw tw o vo,
    (tw <? fw)%positive = true ->
    eval_closed_cert_expr penv foracle o = raise_ret (DVALUE_Base (@DVALUE_I Pa fw vo)) ->
    eval_closed_cert_expr penv foracle (CE_Cast CCK_Trunc fw tw no_cast_flags o) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa tw (@Integers.repr tw (@Integers.unsigned fw vo)))).
Proof.
  intros Pa penv foracle fw tw o vo Hlt Ho.
  unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
  rewrite Ho; cbn - [andb Pos.ltb Pos.eqb Integers.repr Integers.unsigned Integers.signed].
  rewrite Pos.eqb_refl, Hlt; reflexivity.
Qed.

Lemma eval_ce_sext :
  forall {Pa : Params} (penv : param_env Pa) foracle fw tw o vo,
    (fw <? tw)%positive = true ->
    eval_closed_cert_expr penv foracle o = raise_ret (DVALUE_Base (@DVALUE_I Pa fw vo)) ->
    eval_closed_cert_expr penv foracle (CE_Cast CCK_SExt fw tw no_cast_flags o) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa tw (@Integers.repr tw (@Integers.signed fw vo)))).
Proof.
  intros Pa penv foracle fw tw o vo Hlt Ho.
  unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
  rewrite Ho; cbn - [andb Pos.ltb Pos.eqb Integers.repr Integers.unsigned Integers.signed].
  rewrite Pos.eqb_refl, Hlt; reflexivity.
Qed.

Lemma eval_ce_zext :
  forall {Pa : Params} (penv : param_env Pa) foracle fw tw o vo,
    (fw <? tw)%positive = true ->
    eval_closed_cert_expr penv foracle o = raise_ret (DVALUE_Base (@DVALUE_I Pa fw vo)) ->
    eval_closed_cert_expr penv foracle (CE_Cast CCK_ZExt fw tw no_cast_flags o) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa tw (@Integers.repr tw (@Integers.unsigned fw vo)))).
Proof.
  intros Pa penv foracle fw tw o vo Hlt Ho.
  unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
  rewrite Ho; cbn - [andb Pos.ltb Pos.eqb Integers.repr Integers.unsigned Integers.signed].
  rewrite Pos.eqb_refl, Hlt; reflexivity.
Qed.

Lemma eval_ce_icmp_eq_bool :
  forall {Pa : Params} (penv : param_env Pa) foracle pr w l r vl vr,
    eval_closed_cert_expr penv foracle l = raise_ret (DVALUE_Base (@DVALUE_I Pa w vl)) ->
    eval_closed_cert_expr penv foracle r = raise_ret (DVALUE_Base (@DVALUE_I Pa w vr)) ->
    eval_closed_cert_expr penv foracle (CE_ICmp pr false w l r) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
      (if match pr with
          | CIP_Eq => @Integers.eq w vl vr
          | CIP_Ne => negb (@Integers.eq w vl vr)
          | CIP_Ult => @Integers.ltu w vl vr
          | CIP_Ule => negb (@Integers.ltu w vr vl)
          | CIP_Ugt => @Integers.ltu w vr vl
          | CIP_Uge => negb (@Integers.ltu w vl vr)
          | CIP_Slt => @Integers.lt w vl vr
          | CIP_Sle => negb (@Integers.lt w vr vl)
          | CIP_Sgt => @Integers.lt w vr vl
          | CIP_Sge => negb (@Integers.lt w vl vr)
          end
       then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle pr w l r vl vr Hl Hr.
  unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
  rewrite Hl, Hr; cbn [eou_bind].
  unfold eval_icmp; rewrite eval_icmp_base_same_width.
  destruct pr; cbn - [Integers.eq Integers.lt Integers.ltu Integers.one Integers.zero].
  - destruct (@Integers.eq w vl vr); reflexivity.
  - destruct (@Integers.eq w vl vr); reflexivity.
  - destruct (@Integers.ltu w vl vr); reflexivity.
  - destruct (@Integers.ltu w vr vl); reflexivity.
  - destruct (@Integers.ltu w vr vl); reflexivity.
  - destruct (@Integers.ltu w vl vr); reflexivity.
  - destruct (@Integers.lt w vl vr); reflexivity.
  - destruct (@Integers.lt w vr vl); reflexivity.
  - destruct (@Integers.lt w vr vl); reflexivity.
  - destruct (@Integers.lt w vl vr); reflexivity.
Qed.

Lemma eval_ce_select_int :
  forall {Pa : Params} (penv : param_env Pa) foracle w c t f (b : bool) vt vf,
    eval_closed_cert_expr penv foracle c =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle t = raise_ret (DVALUE_Base (@DVALUE_I Pa w vt)) ->
    eval_closed_cert_expr penv foracle f = raise_ret (DVALUE_Base (@DVALUE_I Pa w vf)) ->
    eval_closed_cert_expr penv foracle (CE_Select w c t f) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (if b then vt else vf))).
Proof.
  intros Pa penv foracle w c t f [|] vt vf Hc Ht Hf;
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
    rewrite Hc, Ht, Hf; cbn [eou_bind eval_select eval_select_base_dvalue].
  - rewrite (@Integers.unsigned_one 1%positive); reflexivity.
  - rewrite (@Integers.unsigned_zero 1%positive); reflexivity.
Qed.

Lemma eval_ce_binop :
  forall {Pa : Params} (penv : param_env Pa) foracle op w fl l r,
    eval_closed_cert_expr penv foracle (CE_BinOp op w fl l r) =
    eou_bind (eval_closed_cert_expr penv foracle l) (fun vl =>
    eou_bind (eval_closed_cert_expr penv foracle r) (fun vr =>
    @eval_iop Pa (cert_to_ibinop op fl) vl vr)).
Proof.
  intros; reflexivity.
Qed.

Lemma z_mod_pos_lt_modulus :
  forall (w : positive) (z : Z),
    (Z.pos w < @Integers.modulus w)%Z ->
    (@Integers.unsigned w (@Integers.repr w (z mod Z.pos w)) >=? Z.pos w)%Z = false /\
    @Integers.repr w (z mod Z.pos w) = rv_mask_shamt w z.
Proof.
  intros w z Hlt.
  pose proof (Z.mod_pos_bound z (Z.pos w) ltac:(lia)) as Hb.
  rewrite (@Integers.unsigned_repr w (z mod Z.pos w)).
  - split; [rewrite Z.geb_leb; apply Z.leb_gt; lia | reflexivity].
  - pose proof (@Integers.modulus_pos w); unfold Integers.max_unsigned; lia.
Qed.

Lemma mod_lt_32_64 :
  forall w, (w = 32%positive \/ w = 64%positive) -> (Z.pos w < @Integers.modulus w)%Z.
Proof.
  intros w [-> | ->]; compute; reflexivity.
Qed.

Lemma integers_eq_zero_iff :
  forall (w : positive) (v : @Integers.bit_int w),
    @Integers.eq w v (@Integers.zero w) = true <-> @Integers.unsigned w v = 0%Z.
Proof.
  intros w v; pose proof (@Integers.eq_spec w v (@Integers.zero w)) as Hsp.
  destruct (@Integers.eq w v (@Integers.zero w)); split; intro H.
  - subst v; apply (@Integers.unsigned_zero w).
  - reflexivity.
  - discriminate H.
  - exfalso; apply Hsp; rewrite <- (@Integers.repr_unsigned w v), H; reflexivity.
Qed.

Lemma integers_signed_zero_iff :
  forall (w : positive) (v : @Integers.bit_int w),
    @Integers.signed w v = 0%Z <-> @Integers.unsigned w v = 0%Z.
Proof.
  intros w v.
  pose proof (@Integers.unsigned_range w v) as Hrng.
  pose proof (@Integers.half_modulus_pos w) as Hhm.
  pose proof (@Integers.half_modulus_modulus w) as Hhmm.
  unfold Integers.signed.
  match goal with |- context [if ?c then _ else _] => destruct c end; split; intro H; lia.
Qed.

Lemma unsigned_half_modulus_signed_min :
  forall (w : positive) (v : @Integers.bit_int w),
    @Integers.unsigned w v = @Integers.unsigned w (@Integers.repr w (@Integers.min_signed w)) <->
    @Integers.signed w v = @Integers.min_signed w.
Proof.
  intros w v.
  pose proof (@Integers.unsigned_range w v) as Hrng.
  pose proof (@Integers.half_modulus_pos w) as Hhm.
  unfold Integers.min_signed.
  rewrite Integers.unsigned_repr_eq.
  pose proof (@Integers.half_modulus_modulus w) as Hhmm.
  assert (Hrep : ((- @Integers.half_modulus w) mod @Integers.modulus w)%Z = @Integers.half_modulus w).
  { rewrite <- (Z.mod_add (- @Integers.half_modulus w) 1 (@Integers.modulus w)) by lia.
    replace (- @Integers.half_modulus w + 1 * @Integers.modulus w)%Z with (@Integers.half_modulus w) by lia.
    apply Z.mod_small; lia. }
  rewrite Hrep.
  unfold Integers.signed.
  match goal with |- context [if ?c then _ else _] => destruct c end; split; intro H; lia.
Qed.

Lemma unsigned_mone_signed_neg1 :
  forall (w : positive) (v : @Integers.bit_int w),
    @Integers.unsigned w v = @Integers.unsigned w (@Integers.mone w) <->
    @Integers.signed w v = (-1)%Z.
Proof.
  intros w v.
  pose proof (@Integers.unsigned_range w v) as Hrng.
  pose proof (@Integers.half_modulus_pos w) as Hhm.
  pose proof (@Integers.half_modulus_modulus w) as Hhmm.
  rewrite (@Integers.unsigned_mone w).
  unfold Integers.max_unsigned, Integers.signed.
  match goal with |- context [if ?c then _ else _] => destruct c end; split; intro H; lia.
Qed.

Lemma integers_eq_min_signed_iff :
  forall (w : positive) (v : @Integers.bit_int w),
    @Integers.eq w v (@Integers.repr w (@Integers.min_signed w)) = true <->
    @Integers.signed w v = @Integers.min_signed w.
Proof.
  intros w v.
  pose proof (@Integers.eq_spec w v (@Integers.repr w (@Integers.min_signed w))) as Hsp.
  destruct (@Integers.eq w v (@Integers.repr w (@Integers.min_signed w))); split; intro H.
  - subst v; apply (unsigned_half_modulus_signed_min w _); reflexivity.
  - reflexivity.
  - discriminate H.
  - exfalso; apply Hsp; rewrite <- (@Integers.repr_unsigned w v), <- (@Integers.repr_unsigned w (@Integers.repr w (@Integers.min_signed w))); f_equal.
    apply (unsigned_half_modulus_signed_min w v); exact H.
Qed.

Lemma integers_eq_mone_iff :
  forall (w : positive) (v : @Integers.bit_int w),
    @Integers.eq w v (@Integers.mone w) = true <-> @Integers.signed w v = (-1)%Z.
Proof.
  intros w v.
  pose proof (@Integers.eq_spec w v (@Integers.mone w)) as Hsp.
  destruct (@Integers.eq w v (@Integers.mone w)); split; intro H.
  - subst v; apply (unsigned_mone_signed_neg1 w _); reflexivity.
  - reflexivity.
  - discriminate H.
  - exfalso; apply Hsp; rewrite <- (@Integers.repr_unsigned w v).
    apply (unsigned_mone_signed_neg1 w v) in H; rewrite H.
    apply (@Integers.repr_unsigned w).
Qed.

Lemma mul_hi64_eq :
  forall p : Z,
    @Integers.repr 64%positive
      (@Integers.unsigned 128%positive
         (@Integers.shru 128%positive (@Integers.repr 128%positive p) (@Integers.repr 128%positive 64%Z))) =
    @Integers.repr 64%positive (Z.shiftr p 64%Z).
Proof.
  intro p.
  unfold Integers.shru.
  rewrite (@Integers.unsigned_repr 128%positive 64%Z) by (compute; split; discriminate).
  apply Integers.same_bits_eq; intros i Hi.
  rewrite !(@Integers.testbit_repr _ _ i Hi).
  assert (Hi64 : (0 <= i < 64)%Z) by (replace 64%Z with (@Integers.zwordsize 64%positive) by reflexivity; exact Hi).
  rewrite (@Integers.unsigned_repr 128%positive (Z.shiftr (@Integers.unsigned 128%positive (@Integers.repr 128%positive p)) 64%Z)).
  - rewrite !Z.shiftr_spec by lia.
    rewrite (@Integers.unsigned_repr_eq 128%positive p).
    change (@Integers.modulus 128%positive) with (2 ^ 128)%Z.
    rewrite Z.mod_pow2_bits_low by lia.
    reflexivity.
  - pose proof (@Integers.unsigned_range 128%positive (@Integers.repr 128%positive p)) as Hr.
    rewrite Z.shiftr_div_pow2 by lia.
    change (@Integers.modulus 128%positive) with (2 ^ 128)%Z in Hr.
    change (@Integers.max_unsigned 128%positive) with (2 ^ 128 - 1)%Z.
    split; [apply Z.div_pos; lia |].
    apply Z.lt_le_pred, Z.div_lt_upper_bound; lia.
Qed.

Lemma land_mask_w_mod :
  forall w (x : @Integers.bit_int w),
    (w = 32%positive \/ w = 64%positive) ->
    @Integers.repr w (Z.land (@Integers.unsigned w x) (Z.pos w - 1)) = rv_mask_shamt w (@Integers.unsigned w x) /\
    (@Integers.unsigned w (@Integers.repr w (Z.land (@Integers.unsigned w x) (Z.pos w - 1))) >=? Z.pos w)%Z = false.
Proof.
  intros w x Hw.
  assert (Hland : Z.land (@Integers.unsigned w x) (Z.pos w - 1) = ((@Integers.unsigned w x) mod Z.pos w)%Z).
  { destruct Hw as [-> | ->].
    - replace (Z.pos 32 - 1)%Z with (Z.ones 5) by reflexivity.
      rewrite Z.land_ones by lia; reflexivity.
    - replace (Z.pos 64 - 1)%Z with (Z.ones 6) by reflexivity.
      rewrite Z.land_ones by lia; reflexivity. }
  rewrite Hland.
  pose proof (z_mod_pos_lt_modulus w (@Integers.unsigned w x) (mod_lt_32_64 w Hw)) as [Hlt Heq].
  split; [exact Heq | exact Hlt].
Qed.

(** ** 4. Well-Formedness Helpers for Symbolic Expressions *)

Definition wf_sym_expr (allowed : list (string * positive)) (w : positive) (e : cert_expr) : Prop :=
  wt_cert_expr [] e = true /\
  cert_expr_bit_width e = w /\
  is_let_free_expr e = true /\
  vars_subset_b (collect_free_vars [] e) allowed = true.

Lemma wf_sym_bv_const : forall allowed w v,
  wf_sym_expr allowed w (CE_BvConst w v).
Proof.
  intros; repeat split; try reflexivity; cbn; rewrite Pos.eqb_refl; reflexivity.
Qed.

Lemma wf_sym_bv_z : forall allowed w z,
  wf_sym_expr allowed w (ce_bv_z w z).
Proof.
  intros; apply wf_sym_bv_const.
Qed.

Lemma vars_subset_app : forall vs1 vs2 allowed,
  vars_subset_b vs1 allowed = true ->
  vars_subset_b vs2 allowed = true ->
  vars_subset_b (vs1 ++ vs2) allowed = true.
Proof.
  intros vs1 vs2 allowed H1 H2.
  unfold vars_subset_b in *; rewrite forallb_app, H1, H2; reflexivity.
Qed.

Lemma wf_sym_binop : forall allowed op w a b,
  w <> 1%positive \/ (op = CB_And \/ op = CB_Or) ->
  wf_sym_expr allowed w a ->
  wf_sym_expr allowed w b ->
  wf_sym_expr allowed w (CE_BinOp op w no_binop_flags a b).
Proof.
  intros allowed op w a b Hw1 (Hta & Hwa & Hlfa & Hva) (Htb & Hwb & Hlfb & Hvb).
  split; [| split; [| split]]; cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars].
  - destruct op; rewrite Hta, Htb, Hwa, Hwb, !Pos.eqb_refl; reflexivity.
  - reflexivity.
  - rewrite Hlfa, Hlfb; reflexivity.
  - apply vars_subset_app; assumption.
Qed.

Lemma wf_sym_icmp : forall allowed pr w a b,
  wf_sym_expr allowed w a ->
  wf_sym_expr allowed w b ->
  wf_sym_expr allowed 1%positive (CE_ICmp pr false w a b).
Proof.
  intros allowed pr w a b (Hta & Hwa & Hlfa & Hva) (Htb & Hwb & Hlfb & Hvb).
  split; [| split; [| split]]; cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars].
  - rewrite Hta, Htb, Hwa, Hwb, !Pos.eqb_refl; reflexivity.
  - reflexivity.
  - rewrite Hlfa, Hlfb; reflexivity.
  - apply vars_subset_app; assumption.
Qed.

Lemma wf_sym_select : forall allowed w c t f,
  wf_sym_expr allowed 1%positive c ->
  wf_sym_expr allowed w t ->
  wf_sym_expr allowed w f ->
  wf_sym_expr allowed w (CE_Select w c t f).
Proof.
  intros allowed w c t f (Htc & Hwc & Hlfc & Hvc) (Htt & Hwt & Hlft & Hvt) (Htf & Hwf & Hlff & Hvf).
  split; [| split; [| split]]; cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars].
  - rewrite Htc, Htt, Htf, Hwc, Hwt, Hwf, !Pos.eqb_refl; reflexivity.
  - reflexivity.
  - rewrite Hlfc, Hlft, Hlff; reflexivity.
  - apply vars_subset_app; [exact Hvc | apply vars_subset_app; assumption].
Qed.

Lemma wf_sym_cast : forall allowed k fw tw o,
  ((match k with
    | CCK_ZExt | CCK_SExt => (fw <? tw)%positive
    | CCK_Trunc => (tw <? fw)%positive
    end) = true) ->
  wf_sym_expr allowed fw o ->
  wf_sym_expr allowed tw (CE_Cast k fw tw no_cast_flags o).
Proof.
  intros allowed k fw tw o Hlt (Hto & Hwo & Hlfo & Hvo).
  split; [| split; [| split]]; cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars].
  - rewrite Hto, Hwo, Pos.eqb_refl; destruct k; rewrite Hlt; reflexivity.
  - reflexivity.
  - exact Hlfo.
  - exact Hvo.
Qed.
