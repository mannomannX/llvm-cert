(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified Byte-Addressed Private Stack-Frame Memory Model ([CertValidator.McFrameMem])

    Implements the shared concrete and symbolic stack-frame memory model for
    Phase [8.3a] Milestone M3 across both [RISC-V] ([Rv64Sem]) and [AArch64]
    ([A64CoreSem]):
    1. Access widths ([mc_mem_size]) and 64 KiB frame geometry with 16-byte
       aligned [SP0] offset normalization ([mc_addr_to_off_add], [mc_add_ptr_off]).
    2. Concrete little-endian byte-addressed stack memory ([mc_stack_mem],
       [mc_stk_store], [mc_stk_load]) with zero-axiom disjointness and
       read-after-write soundness ([mc_stk_load_store_disjoint],
       [mc_stk_load_store_same]).
    3. Interval-disjoint symbolic stack domain ([mc_sym_val], [mc_sym_stack])
       tracking symbolic 64-bit values ([MSV_Expr]), callee-saved register saves
       ([MSV_SavedReg]), and frame-relative pointers ([MSV_StackPtr]), with
       complete well-formedness and relational agreement proofs. *)

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
  Semantics.Operations.Conversion.

From CertValidator Require Import
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
#[local] Arguments Integers.add : simpl never.
#[local] Arguments Integers.sub : simpl never.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** 1. Memory Widths & Frame Geometry *)

Variant mc_mem_size : Set :=
| MS_1
| MS_2
| MS_4
| MS_8.

Definition mc_mem_bytes (sz : mc_mem_size) : N :=
  match sz with
  | MS_1 => 1%N
  | MS_2 => 2%N
  | MS_4 => 4%N
  | MS_8 => 8%N
  end.

Definition mc_mem_bytes_Z (sz : mc_mem_size) : Z :=
  Z.of_N (mc_mem_bytes sz).

Definition mc_mem_bits (sz : mc_mem_size) : positive :=
  match sz with
  | MS_1 => 8%positive
  | MS_2 => 16%positive
  | MS_4 => 32%positive
  | MS_8 => 64%positive
  end.

Definition mc_mem_size_eqb (a b : mc_mem_size) : bool :=
  match a, b with
  | MS_1, MS_1 | MS_2, MS_2 | MS_4, MS_4 | MS_8, MS_8 => true
  | _, _ => false
  end.

Lemma mc_mem_size_eqb_eq : forall a b, mc_mem_size_eqb a b = true <-> a = b.
Proof.
  intros [] []; cbn; split; intro H; try reflexivity; discriminate H.
Qed.

Definition mc_frame_cap : Z := 65536%Z.

Definition mc_valid_sp0 (sp0 : @Integers.bit_int 64%positive) : Prop :=
  (mc_frame_cap <= @Integers.unsigned 64%positive sp0)%Z /\
  (@Integers.unsigned 64%positive sp0 mod 16 = 0)%Z.

Definition mc_addr_to_off (sp0 addr : @Integers.bit_int 64%positive) : Z :=
  (@Integers.unsigned 64%positive addr - @Integers.unsigned 64%positive sp0)%Z.

Definition mc_slot_in_frame (sp_off off : Z) (sz : mc_mem_size) : bool :=
  Z.leb (- mc_frame_cap) sp_off &&
  Z.leb sp_off off &&
  Z.leb (off + mc_mem_bytes_Z sz) 0%Z &&
  Z.eqb (Z.modulo off (mc_mem_bytes_Z sz)) 0%Z.

Definition mc_sp_aligned16 (sp_off : Z) : bool :=
  Z.leb (- mc_frame_cap) sp_off &&
  Z.leb sp_off 0%Z &&
  Z.eqb (Z.modulo sp_off 16%Z) 0%Z.

Lemma mc_slot_in_frame_mono : forall sp1 sp2 off sz,
  (sp1 <= sp2)%Z ->
  (- mc_frame_cap <= sp1)%Z ->
  mc_slot_in_frame sp2 off sz = true ->
  mc_slot_in_frame sp1 off sz = true.
Proof.
  intros sp1 sp2 off sz Hle Hcap H.
  unfold mc_slot_in_frame in *.
  rewrite !andb_true_iff in H |- *.
  destruct H as (((_ & Hsp2) & Hzero) & Hmod).
  apply Z.leb_le in Hsp2.
  repeat split; [apply Z.leb_le; exact Hcap | apply Z.leb_le; lia | exact Hzero | exact Hmod].
Qed.

Lemma mc_addr_to_off_add : forall sp0 off,
  (mc_frame_cap <= @Integers.unsigned 64%positive sp0)%Z ->
  (- mc_frame_cap <= off <= 0)%Z ->
  mc_addr_to_off sp0 (@Integers.add 64%positive sp0 (@Integers.repr 64%positive off)) = off.
Proof.
  intros sp0 off Hcap Hrng.
  unfold mc_addr_to_off, Integers.add.
  pose proof (@Integers.unsigned_range 64%positive sp0) as Hsp_rng.
  rewrite !(@Integers.unsigned_repr_eq 64%positive).
  change (@Integers.modulus 64%positive) with (2 ^ 64)%Z in *.
  rewrite Zplus_mod_idemp_r, Z.mod_small; [lia | unfold mc_frame_cap in *; lia].
Qed.

Lemma mc_add_ptr_off : forall sp0 off delta,
  @Integers.add 64%positive
    (@Integers.add 64%positive sp0 (@Integers.repr 64%positive off))
    (@Integers.repr 64%positive delta) =
  @Integers.add 64%positive sp0 (@Integers.repr 64%positive (off + delta)).
Proof.
  intros sp0 off delta.
  rewrite !Integers.add_assoc; f_equal.
  unfold Integers.add.
  apply Integers.eqm_samerepr.
  apply Integers.eqm_add; apply Integers.eqm_sym, Integers.eqm_unsigned_repr.
Qed.

Lemma mc_slot_in_frame_bounds : forall sp_off off sz,
  mc_slot_in_frame sp_off off sz = true ->
  (- mc_frame_cap <= sp_off /\ sp_off <= off /\ off + mc_mem_bytes_Z sz <= 0 /\
   Z.modulo off (mc_mem_bytes_Z sz) = 0)%Z.
Proof.
  intros sp_off off sz H; unfold mc_slot_in_frame in H.
  rewrite !andb_true_iff in H; destruct H as (((H1 & H2) & H3) & H4).
  apply Z.leb_le in H1; apply Z.leb_le in H2; apply Z.leb_le in H3; apply Z.eqb_eq in H4.
  repeat split; assumption.
Qed.

Lemma mc_add_ptr_zero : forall sp0,
  @Integers.add 64%positive sp0 (@Integers.repr 64%positive 0%Z) = sp0.
Proof.
  intro sp0; unfold Integers.add.
  rewrite (@Integers.unsigned_repr 64%positive 0%Z)
    by (change (@Integers.max_unsigned 64%positive) with (2 ^ 64 - 1)%Z; lia).
  rewrite Z.add_0_r; apply Integers.repr_unsigned.
Qed.

Lemma mc_sub_ptr_off : forall sp0 off delta,
  @Integers.sub 64%positive
    (@Integers.add 64%positive sp0 (@Integers.repr 64%positive off))
    (@Integers.repr 64%positive delta) =
  @Integers.add 64%positive sp0 (@Integers.repr 64%positive (off - delta)).
Proof.
  intros sp0 off delta; unfold Integers.sub, Integers.add.
  apply Integers.eqm_samerepr.
  apply Integers.eqm_trans with
    ((@Integers.unsigned 64%positive sp0 + @Integers.unsigned 64%positive (@Integers.repr 64%positive off)) -
     @Integers.unsigned 64%positive (@Integers.repr 64%positive delta))%Z.
  - apply Integers.eqm_sub; [apply Integers.eqm_sym, Integers.eqm_unsigned_repr | apply Integers.eqm_refl].
  - apply Integers.eqm_trans with (@Integers.unsigned 64%positive sp0 + (off - delta))%Z.
    + replace ((@Integers.unsigned 64%positive sp0 + @Integers.unsigned 64%positive (@Integers.repr 64%positive off)) -
               @Integers.unsigned 64%positive (@Integers.repr 64%positive delta))%Z
        with (@Integers.unsigned 64%positive sp0 +
              (@Integers.unsigned 64%positive (@Integers.repr 64%positive off) -
               @Integers.unsigned 64%positive (@Integers.repr 64%positive delta)))%Z by lia.
      apply Integers.eqm_add; [apply Integers.eqm_refl |].
      apply Integers.eqm_sub; apply Integers.eqm_sym, Integers.eqm_unsigned_repr.
    + apply Integers.eqm_add; [apply Integers.eqm_refl | apply Integers.eqm_unsigned_repr].
Qed.

(** ** 2. Concrete Byte-Addressed Private Stack Memory ([mc_stack_mem]) *)

Definition mc_stack_mem : Type := Z -> N.

Definition mc_empty_stack : mc_stack_mem := fun _ => 0%N.

Fixpoint mc_stk_read_bytes (m : mc_stack_mem) (off : Z) (n : nat) {struct n} : N :=
  match n with
  | O => 0%N
  | S n' => (N.modulo (m off) 256%N + 256%N * mc_stk_read_bytes m (off + 1)%Z n')%N
  end.

Fixpoint mc_stk_write_bytes (m : mc_stack_mem) (off : Z) (n : nat) (v : N) {struct n} : mc_stack_mem :=
  match n with
  | O => m
  | S n' =>
      let m' := mc_stk_write_bytes m (off + 1)%Z n' (N.div v 256%N) in
      fun z => if Z.eqb z off then N.modulo v 256%N else m' z
  end.

Definition mc_stk_store
  (m : mc_stack_mem) (off : Z) (sz : mc_mem_size) (v : @Integers.bit_int 64%positive)
  : mc_stack_mem :=
  mc_stk_write_bytes m off (N.to_nat (mc_mem_bytes sz)) (Z.to_N (@Integers.unsigned 64%positive v)).

Definition mc_stk_load
  (m : mc_stack_mem) (off : Z) (sz : mc_mem_size) (is_signed : bool)
  : @Integers.bit_int 64%positive :=
  let raw := mc_stk_read_bytes m off (N.to_nat (mc_mem_bytes sz)) in
  match sz with
  | MS_8 => @Integers.repr 64%positive (Z.of_N raw)
  | _ =>
      let w := mc_mem_bits sz in
      let vw := @Integers.repr w (Z.of_N raw) in
      @Integers.repr 64%positive (if is_signed then @Integers.signed w vw else @Integers.unsigned w vw)
  end.

Lemma mc_stk_write_bytes_outside : forall m off n v z,
  (z < off \/ off + Z.of_nat n <= z)%Z ->
  mc_stk_write_bytes m off n v z = m z.
Proof.
  intros m off n; revert m off; induction n as [| n' IH]; intros m off v z Hout; cbn [mc_stk_write_bytes].
  - reflexivity.
  - destruct (Z.eqb z off) eqn:Ezo.
    + apply Z.eqb_eq in Ezo; lia.
    + apply IH; lia.
Qed.

Lemma mc_stk_read_bytes_ext : forall m1 m2 off n,
  (forall z, (off <= z < off + Z.of_nat n)%Z -> m1 z = m2 z) ->
  mc_stk_read_bytes m1 off n = mc_stk_read_bytes m2 off n.
Proof.
  intros m1 m2 off n; revert off; induction n as [| n' IH]; intros off Hext;
    cbn [mc_stk_read_bytes]; [reflexivity |].
  rewrite (Hext off ltac:(lia)), (IH (off + 1)%Z ltac:(intros z Hz; apply Hext; lia)); reflexivity.
Qed.

Lemma mc_stk_read_write_disjoint : forall m off1 n1 v off2 n2,
  (off2 + Z.of_nat n2 <= off1 \/ off1 + Z.of_nat n1 <= off2)%Z ->
  mc_stk_read_bytes (mc_stk_write_bytes m off1 n1 v) off2 n2 = mc_stk_read_bytes m off2 n2.
Proof.
  intros m off1 n1 v off2 n2 Hdisj.
  apply mc_stk_read_bytes_ext; intros z Hz.
  apply mc_stk_write_bytes_outside; lia.
Qed.

Lemma mc_stk_read_bytes_bound : forall m off n,
  (mc_stk_read_bytes m off n < N.pow 256%N (N.of_nat n))%N.
Proof.
  intros m off n; revert off; induction n as [| n' IH]; intros off; cbn [mc_stk_read_bytes].
  - lia.
  - pose proof (N.mod_lt (m off) 256%N ltac:(discriminate)) as Hm.
    pose proof (IH (off + 1)%Z) as Hrec.
    replace (N.of_nat (S n')) with (N.succ (N.of_nat n')) by lia.
    rewrite N.pow_succ_r'.
    nia.
Qed.

Lemma mc_stk_read_write_same : forall m off n v,
  mc_stk_read_bytes (mc_stk_write_bytes m off n v) off n = N.modulo v (N.pow 256%N (N.of_nat n)).
Proof.
  intros m off n; revert m off; induction n as [| n' IH]; intros m off v;
    cbn [mc_stk_read_bytes mc_stk_write_bytes].
  - rewrite N.mod_1_r; reflexivity.
  - rewrite Z.eqb_refl, N.Div0.mod_mod.
    assert (Hext :
      mc_stk_read_bytes
        (fun z => if Z.eqb z off then N.modulo v 256%N
                  else mc_stk_write_bytes m (off + 1)%Z n' (N.div v 256%N) z)
        (off + 1)%Z n' =
      mc_stk_read_bytes (mc_stk_write_bytes m (off + 1)%Z n' (N.div v 256%N)) (off + 1)%Z n').
    { apply mc_stk_read_bytes_ext; intros z Hz.
      destruct (Z.eqb z off) eqn:Ezo; [apply Z.eqb_eq in Ezo; lia | reflexivity]. }
    rewrite Hext, IH.
    replace (N.of_nat (S n')) with (1 + N.of_nat n')%N by lia.
    rewrite N.pow_add_r, N.pow_1_r.
    set (b := N.pow 256%N (N.of_nat n')).
    assert (Hb : (1 <= b)%N)
      by (unfold b; pose proof (N.pow_nonzero 256%N (N.of_nat n') ltac:(discriminate)); lia).
    pose proof (N.div_mod v 256%N ltac:(discriminate)) as Hdm1.
    set (q := (v / 256)%N) in *; set (r := (v mod 256)%N) in *.
    pose proof (N.div_mod q b ltac:(lia)) as Hdm2.
    set (qq := (q / b)%N) in *; set (qr := (q mod b)%N) in *.
    pose proof (N.mod_lt v 256%N ltac:(discriminate)) as Hr.
    pose proof (N.mod_lt q b ltac:(lia)) as Hqr.
    fold r in Hr; fold qr in Hqr.
    assert (Hv : v = ((r + 256 * qr) + qq * (256 * b))%N) by lia.
    rewrite Hv, N.Div0.mod_add; rewrite N.mod_small by nia; reflexivity.
Qed.

Lemma mc_stk_load_store_disjoint : forall m off1 sz1 off2 sz2 is_signed v,
  (off2 + mc_mem_bytes_Z sz2 <= off1 \/ off1 + mc_mem_bytes_Z sz1 <= off2)%Z ->
  mc_stk_load (mc_stk_store m off1 sz1 v) off2 sz2 is_signed = mc_stk_load m off2 sz2 is_signed.
Proof.
  intros m off1 sz1 off2 sz2 is_signed v Hdisj.
  unfold mc_stk_load, mc_stk_store, mc_mem_bytes_Z in *.
  rewrite mc_stk_read_write_disjoint by lia; reflexivity.
Qed.

Lemma mc_stk_load_store_same : forall m off sz is_signed v,
  mc_stk_load (mc_stk_store m off sz v) off sz is_signed =
  match sz with
  | MS_8 => v
  | _ =>
      let w := mc_mem_bits sz in
      let vw := @Integers.repr w (@Integers.unsigned 64%positive v) in
      @Integers.repr 64%positive (if is_signed then @Integers.signed w vw else @Integers.unsigned w vw)
  end.
Proof.
  intros m off sz is_signed v.
  unfold mc_stk_load, mc_stk_store.
  rewrite mc_stk_read_write_same.
  pose proof (@Integers.unsigned_range 64%positive v) as Hrng.
  assert (Hmod8 : N.pow 256%N (N.of_nat (N.to_nat (mc_mem_bytes MS_8))) = Z.to_N (@Integers.modulus 64%positive))
    by (compute; reflexivity).
  assert (Hmod1 : N.pow 256%N (N.of_nat (N.to_nat (mc_mem_bytes MS_1))) = Z.to_N (@Integers.modulus 8%positive))
    by (compute; reflexivity).
  assert (Hmod2 : N.pow 256%N (N.of_nat (N.to_nat (mc_mem_bytes MS_2))) = Z.to_N (@Integers.modulus 16%positive))
    by (compute; reflexivity).
  assert (Hmod4 : N.pow 256%N (N.of_nat (N.to_nat (mc_mem_bytes MS_4))) = Z.to_N (@Integers.modulus 32%positive))
    by (compute; reflexivity).
  destruct sz.
  - rewrite Hmod1.
    cbn [mc_mem_bits].
    assert (Heq : @Integers.repr 8%positive (Z.of_N (Z.to_N (@Integers.unsigned 64%positive v) mod Z.to_N (@Integers.modulus 8%positive))) =
                  @Integers.repr 8%positive (@Integers.unsigned 64%positive v)).
    { rewrite N2Z.inj_mod, !Z2N.id by (try pose proof (@Integers.modulus_pos 8%positive); lia).
      apply Integers.eqm_samerepr, Integers.eqm_sym, Integers.eqmod_mod. }
    rewrite Heq; reflexivity.
  - rewrite Hmod2.
    cbn [mc_mem_bits].
    assert (Heq : @Integers.repr 16%positive (Z.of_N (Z.to_N (@Integers.unsigned 64%positive v) mod Z.to_N (@Integers.modulus 16%positive))) =
                  @Integers.repr 16%positive (@Integers.unsigned 64%positive v)).
    { rewrite N2Z.inj_mod, !Z2N.id by (try pose proof (@Integers.modulus_pos 16%positive); lia).
      apply Integers.eqm_samerepr, Integers.eqm_sym, Integers.eqmod_mod. }
    rewrite Heq; reflexivity.
  - rewrite Hmod4.
    cbn [mc_mem_bits].
    assert (Heq : @Integers.repr 32%positive (Z.of_N (Z.to_N (@Integers.unsigned 64%positive v) mod Z.to_N (@Integers.modulus 32%positive))) =
                  @Integers.repr 32%positive (@Integers.unsigned 64%positive v)).
    { rewrite N2Z.inj_mod, !Z2N.id by (try pose proof (@Integers.modulus_pos 32%positive); lia).
      apply Integers.eqm_samerepr, Integers.eqm_sym, Integers.eqmod_mod. }
    rewrite Heq; reflexivity.
  - rewrite Hmod8, N.mod_small.
    + rewrite Z2N.id by lia; apply Integers.repr_unsigned.
    + change (@Integers.modulus 64%positive) with (2 ^ 64)%Z in Hrng |- *; lia.
Qed.

Lemma mc_stk_load_ms8_signed_irrel : forall m off b1 b2,
  mc_stk_load m off MS_8 b1 = mc_stk_load m off MS_8 b2.
Proof. intros m off b1 b2; reflexivity. Qed.

(** ** 3. Symbolic Value & Abstract Stack Domain ([mc_sym_val], [mc_sym_stack]) *)

Variant mc_sym_val : Set :=
| MSV_Undef
| MSV_Expr (e : cert_expr)
| MSV_SavedReg (r : N)
| MSV_StackPtr (off : Z).

Definition mc_sym_stack : Type := list (Z * mc_mem_size * mc_sym_val).

Definition mc_intervals_disjoint (o1 : Z) (s1 : mc_mem_size) (o2 : Z) (s2 : mc_mem_size) : bool :=
  Z.leb (o1 + mc_mem_bytes_Z s1) o2 || Z.leb (o2 + mc_mem_bytes_Z s2) o1.

Lemma mc_intervals_disjoint_spec : forall o1 s1 o2 s2,
  mc_intervals_disjoint o1 s1 o2 s2 = true <->
  (o1 + mc_mem_bytes_Z s1 <= o2 \/ o2 + mc_mem_bytes_Z s2 <= o1)%Z.
Proof.
  intros o1 s1 o2 s2; unfold mc_intervals_disjoint.
  rewrite orb_true_iff, !Z.leb_le; reflexivity.
Qed.

Definition mc_sym_stk_store
  (off : Z) (sz : mc_mem_size) (v : mc_sym_val) (stk : mc_sym_stack)
  : mc_sym_stack :=
  let kept := List.filter (fun '(o, s, _) => mc_intervals_disjoint off sz o s) stk in
  match v with
  | MSV_Undef => kept
  | _ => (off, sz, v) :: kept
  end.

Definition mc_sym_stk_prune (sp_off : Z) (stk : mc_sym_stack) : mc_sym_stack :=
  List.filter (fun '(o, _, _) => Z.leb sp_off o) stk.

Definition mc_sym_load_expr (sz : mc_mem_size) (is_signed : bool) (e64 : cert_expr) : cert_expr :=
  match sz with
  | MS_8 => e64
  | _ =>
      let w := mc_mem_bits sz in
      let tr := CE_Cast CCK_Trunc 64%positive w no_cast_flags e64 in
      CE_Cast (if is_signed then CCK_SExt else CCK_ZExt) w 64%positive no_cast_flags tr
  end.

Fixpoint mc_sym_stk_load
  (off : Z) (sz : mc_mem_size) (is_signed : bool) (stk : mc_sym_stack)
  {struct stk} : option mc_sym_val :=
  match stk with
  | [] => None
  | (o, s, v) :: rest =>
      if Z.eqb o off && mc_mem_size_eqb s sz then
        match v with
        | MSV_Expr e => Some (MSV_Expr (mc_sym_load_expr sz is_signed e))
        | MSV_SavedReg r =>
            match sz with MS_8 => Some (MSV_SavedReg r) | _ => None end
        | MSV_StackPtr p =>
            match sz with MS_8 => Some (MSV_StackPtr p) | _ => None end
        | MSV_Undef => None
        end
      else mc_sym_stk_load off sz is_signed rest
  end.

Definition mc_sym_val_wf (allowed : list (string * positive)) (sv : mc_sym_val) : Prop :=
  match sv with
  | MSV_Expr e =>
      wt_cert_expr [] e = true /\
      cert_expr_bit_width e = 64%positive /\
      is_let_free_expr e = true /\
      vars_subset_b (collect_free_vars [] e) allowed = true
  | MSV_StackPtr off => (- mc_frame_cap <= off <= 0)%Z
  | MSV_SavedReg _ | MSV_Undef => True
  end.

Definition mc_sym_val_agrees {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (read_init : N -> @Integers.bit_int 64%positive)
  (sp0 : @Integers.bit_int 64%positive)
  (sv : mc_sym_val) (v : @Integers.bit_int 64%positive) : Prop :=
  match sv with
  | MSV_Undef => True
  | MSV_Expr e =>
      eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v))
  | MSV_SavedReg r => v = read_init r
  | MSV_StackPtr off =>
      (- mc_frame_cap <= off <= 0)%Z /\
      v = @Integers.add 64%positive sp0 (@Integers.repr 64%positive off)
  end.

Definition mc_sym_stack_wf
  (allowed : list (string * positive)) (sp_off : Z) (stk : mc_sym_stack) : Prop :=
  Forall (fun '(o, s, sv) => mc_slot_in_frame sp_off o s = true /\ mc_sym_val_wf allowed sv) stk.

Definition mc_sym_stack_agrees {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (read_init : N -> @Integers.bit_int 64%positive)
  (sp0 : @Integers.bit_int 64%positive)
  (astk : mc_sym_stack) (mstk : mc_stack_mem) : Prop :=
  Forall (fun '(o, s, sv) =>
    match sv with
    | MSV_Undef => True
    | MSV_Expr e =>
        exists v64 : @Integers.bit_int 64%positive,
          eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) /\
          mc_stk_load mstk o s false =
            (match s with
             | MS_8 => v64
             | _ =>
                 let w := mc_mem_bits s in
                 @Integers.repr 64%positive (@Integers.unsigned w (@Integers.repr w (@Integers.unsigned 64%positive v64)))
             end) /\
          mc_stk_load mstk o s true =
            (match s with
             | MS_8 => v64
             | _ =>
                 let w := mc_mem_bits s in
                 @Integers.repr 64%positive (@Integers.signed w (@Integers.repr w (@Integers.unsigned 64%positive v64)))
             end)
    | MSV_SavedReg r =>
        s = MS_8 /\ mc_stk_load mstk o MS_8 false = read_init r
    | MSV_StackPtr p =>
        s = MS_8 /\
        (- mc_frame_cap <= p <= 0)%Z /\
        mc_stk_load mstk o MS_8 false = @Integers.add 64%positive sp0 (@Integers.repr 64%positive p)
    end) astk.

Lemma mc_sym_stack_wf_empty : forall allowed sp_off,
  mc_sym_stack_wf allowed sp_off [].
Proof. intros; constructor. Qed.

Lemma mc_sym_stack_agrees_empty {Pa : Params} :
  forall (penv : param_env Pa) foracle read_init sp0 mstk,
    mc_sym_stack_agrees penv foracle read_init sp0 [] mstk.
Proof. intros; constructor. Qed.

Lemma mc_sym_load_expr_wf : forall allowed sz is_signed e,
  mc_sym_val_wf allowed (MSV_Expr e) ->
  mc_sym_val_wf allowed (MSV_Expr (mc_sym_load_expr sz is_signed e)).
Proof.
  intros allowed sz is_signed e (Hwt & Hbw & Hlf & Hfv).
  destruct sz; unfold mc_sym_val_wf; cbn [mc_sym_load_expr mc_mem_bits];
    [| | | repeat split; assumption].
  all: destruct is_signed;
    cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr
         collect_free_vars ccf_nneg ccf_nuw ccf_nsw no_cast_flags];
    rewrite Hwt, Hbw, Hlf, Hfv; repeat split; reflexivity.
Qed.

Lemma mc_sym_load_expr_sound {Pa : Params} :
  forall penv foracle sz is_signed e (v64 : @Integers.bit_int 64%positive),
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) ->
    eval_closed_cert_expr penv foracle (mc_sym_load_expr sz is_signed e) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive
      (match sz with
       | MS_8 => v64
       | _ =>
           let w := mc_mem_bits sz in
           let vw := @Integers.repr w (@Integers.unsigned 64%positive v64) in
           @Integers.repr 64%positive (if is_signed then @Integers.signed w vw else @Integers.unsigned w vw)
       end))).
Proof.
  intros penv foracle sz is_signed e v64 He.
  destruct sz; cbn [mc_sym_load_expr]; [| | | exact He].
  all: cbn [mc_mem_bits]; destruct is_signed;
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
    rewrite He;
    cbn - [Integers.repr Integers.unsigned Integers.signed];
    reflexivity.
Qed.

Lemma mc_sym_stk_store_wf : forall allowed sp_off off sz v stk,
  mc_slot_in_frame sp_off off sz = true ->
  mc_sym_val_wf allowed v ->
  mc_sym_stack_wf allowed sp_off stk ->
  mc_sym_stack_wf allowed sp_off (mc_sym_stk_store off sz v stk).
Proof.
  intros allowed sp_off off sz v stk Hslot Hvwf Hstk.
  unfold mc_sym_stk_store, mc_sym_stack_wf in *.
  assert (Hkept : Forall (fun '(o, s, sv) => mc_slot_in_frame sp_off o s = true /\ mc_sym_val_wf allowed sv)
                    (List.filter (fun '(o, s, _) => mc_intervals_disjoint off sz o s) stk)).
  { apply Forall_forall; intros [[o s] sv] Hin.
    apply filter_In in Hin as [Hin _].
    rewrite Forall_forall in Hstk; exact (Hstk (o, s, sv) Hin). }
  destruct v; try (constructor; [split; assumption | exact Hkept]).
  exact Hkept.
Qed.

Lemma mc_sym_stk_store_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle read_init sp0 off sz sv v astk mstk,
    (match sv with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end) ->
    mc_sym_val_agrees penv foracle read_init sp0 sv v ->
    mc_sym_stack_agrees penv foracle read_init sp0 astk mstk ->
    mc_sym_stack_agrees penv foracle read_init sp0
      (mc_sym_stk_store off sz sv astk) (mc_stk_store mstk off sz v).
Proof.
  intros penv foracle read_init sp0 off sz sv v astk mstk Hsz Hv Hag.
  unfold mc_sym_stk_store, mc_sym_stack_agrees in *.
  assert (Hkept :
    Forall (fun '(o, s, sv0) =>
      match sv0 with
      | MSV_Undef => True
      | MSV_Expr e =>
          exists v64,
            eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) /\
            mc_stk_load (mc_stk_store mstk off sz v) o s false =
              (match s with MS_8 => v64 | _ => @Integers.repr 64%positive (@Integers.unsigned (mc_mem_bits s) (@Integers.repr (mc_mem_bits s) (@Integers.unsigned 64%positive v64))) end) /\
            mc_stk_load (mc_stk_store mstk off sz v) o s true =
              (match s with MS_8 => v64 | _ => @Integers.repr 64%positive (@Integers.signed (mc_mem_bits s) (@Integers.repr (mc_mem_bits s) (@Integers.unsigned 64%positive v64))) end)
      | MSV_SavedReg r => s = MS_8 /\ mc_stk_load (mc_stk_store mstk off sz v) o MS_8 false = read_init r
      | MSV_StackPtr p => s = MS_8 /\ (- mc_frame_cap <= p <= 0)%Z /\
          mc_stk_load (mc_stk_store mstk off sz v) o MS_8 false = @Integers.add 64%positive sp0 (@Integers.repr 64%positive p)
      end)
      (List.filter (fun '(o, s, _) => mc_intervals_disjoint off sz o s) astk)).
  { apply Forall_forall; intros [[o s] sv0] Hin.
    apply filter_In in Hin as [Hin Hdis].
    apply mc_intervals_disjoint_spec in Hdis.
    rewrite Forall_forall in Hag; pose proof (Hag (o, s, sv0) Hin) as Hentry.
    destruct sv0; try exact Hentry.
    - destruct Hentry as (v64 & He & Hlu & Hls).
      exists v64; split; [exact He | split].
      + rewrite (mc_stk_load_store_disjoint mstk off sz o s false v ltac:(lia)); exact Hlu.
      + rewrite (mc_stk_load_store_disjoint mstk off sz o s true v ltac:(lia)); exact Hls.
    - destruct Hentry as [Hs Hld]; subst s; split; [reflexivity |].
      rewrite (mc_stk_load_store_disjoint mstk off sz o MS_8 false v ltac:(lia)); exact Hld.
    - destruct Hentry as (Hms & Hrng & Hld); subst s; split; [reflexivity | split; [exact Hrng |]].
      rewrite (mc_stk_load_store_disjoint mstk off sz o MS_8 false v ltac:(lia)); exact Hld. }
  destruct sv; try exact Hkept; constructor; try exact Hkept.
  - cbn [mc_sym_val_agrees] in Hv; exists v; split; [exact Hv |].
    rewrite !mc_stk_load_store_same; split; reflexivity.
  - subst sz; split; [reflexivity |]; rewrite mc_stk_load_store_same; exact Hv.
  - subst sz; destruct Hv as [Hrng Heqv]; split; [reflexivity | split; [exact Hrng |]].
    rewrite mc_stk_load_store_same; exact Heqv.
Qed.

Lemma mc_sym_stk_prune_wf : forall allowed sp_old sp_new stk,
  (- mc_frame_cap <= sp_new)%Z ->
  mc_sym_stack_wf allowed sp_old stk ->
  mc_sym_stack_wf allowed sp_new (mc_sym_stk_prune sp_new stk).
Proof.
  intros allowed sp_old sp_new stk Hcap Hstk.
  unfold mc_sym_stk_prune, mc_sym_stack_wf in *.
  apply Forall_forall; intros [[o s] sv] Hin.
  apply filter_In in Hin as [Hin Hle].
  rewrite Forall_forall in Hstk; destruct (Hstk (o, s, sv) Hin) as [Hslot Hvwf].
  split; [| exact Hvwf].
  unfold mc_slot_in_frame in Hslot |- *.
  rewrite !andb_true_iff in Hslot |- *; destruct Hslot as (((_ & _) & Hz) & Hmod).
  repeat split; [apply Z.leb_le; exact Hcap | exact Hle | exact Hz | exact Hmod].
Qed.

Lemma mc_sym_stk_prune_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle read_init sp0 sp_new astk mstk,
    mc_sym_stack_agrees penv foracle read_init sp0 astk mstk ->
    mc_sym_stack_agrees penv foracle read_init sp0 (mc_sym_stk_prune sp_new astk) mstk.
Proof.
  intros penv foracle read_init sp0 sp_new astk mstk Hag.
  unfold mc_sym_stk_prune, mc_sym_stack_agrees in *.
  apply Forall_forall; intros [[o s] sv] Hin.
  apply filter_In in Hin as [Hin _].
  rewrite Forall_forall in Hag; exact (Hag (o, s, sv) Hin).
Qed.

Lemma mc_sym_stk_load_wf : forall allowed sp_off off sz is_signed stk sv,
  mc_sym_stack_wf allowed sp_off stk ->
  mc_sym_stk_load off sz is_signed stk = Some sv ->
  mc_sym_val_wf allowed sv.
Proof.
  intros allowed sp_off off sz is_signed stk sv Hstk Hld.
  induction stk as [| [[o s] sv0] rest IH]; cbn [mc_sym_stk_load] in Hld; [discriminate Hld |].
  unfold mc_sym_stack_wf in Hstk; rewrite Forall_cons_iff in Hstk.
  destruct Hstk as [[Hslot Hwf0] Hrest].
  destruct (Z.eqb o off && mc_mem_size_eqb s sz); [| exact (IH Hrest Hld)].
  destruct sv0; try discriminate Hld.
  - inversion Hld; subst sv; exact (mc_sym_load_expr_wf _ _ _ _ Hwf0).
  - destruct sz; try discriminate Hld; inversion Hld; subst sv; exact I.
  - destruct sz; try discriminate Hld; inversion Hld; subst sv; exact Hwf0.
Qed.

Lemma mc_sym_stk_load_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle read_init sp0 off sz is_signed astk mstk sv,
    mc_sym_stack_agrees penv foracle read_init sp0 astk mstk ->
    mc_sym_stk_load off sz is_signed astk = Some sv ->
    mc_sym_val_agrees penv foracle read_init sp0 sv (mc_stk_load mstk off sz is_signed).
Proof.
  intros penv foracle read_init sp0 off sz is_signed astk mstk sv Hag Hld.
  induction astk as [| [[o s] sv0] rest IH]; cbn [mc_sym_stk_load] in Hld; [discriminate Hld |].
  unfold mc_sym_stack_agrees in Hag; rewrite Forall_cons_iff in Hag.
  destruct Hag as [Hentry Hrest].
  destruct (Z.eqb o off && mc_mem_size_eqb s sz) eqn:Eeq; [| exact (IH Hrest Hld)].
  apply andb_true_iff in Eeq as [Eo Es].
  apply Z.eqb_eq in Eo; apply mc_mem_size_eqb_eq in Es; subst o s.
  destruct sv0; try discriminate Hld.
  - inversion Hld; subst sv; clear Hld.
    destruct Hentry as (v64 & He & Hlu & Hls).
    cbn [mc_sym_val_agrees].
    rewrite (mc_sym_load_expr_sound penv foracle sz is_signed e v64 He).
    destruct sz; destruct is_signed; try (rewrite Hlu; reflexivity); try (rewrite Hls; reflexivity).
  - destruct sz; try discriminate Hld; inversion Hld; subst sv.
    rewrite (mc_stk_load_ms8_signed_irrel mstk off is_signed false).
    destruct Hentry as [_ Hmv]; exact Hmv.
  - destruct sz; try discriminate Hld; inversion Hld; subst sv.
    rewrite (mc_stk_load_ms8_signed_irrel mstk off is_signed false).
    exact (proj2 Hentry).
Qed.
