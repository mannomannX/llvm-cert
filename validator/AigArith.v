(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * [CertValidator.AigArith]: 2-Rail Arithmetic, Shift, Cast & ICmp Bit-Blast Encoders

    Builds on [CertValidator.LratCore] and [CertValidator.AigGates] to provide
    [bools_to_Z] arithmetic/bit-slicing/MSB bridge lemmas and complete monotone
    2-rail encoders (addition, subtraction, multiplication, shifts, casts,
    integer comparisons, and select/freeze) proved sound against Vellvm's
    [@Integers.bit_int] semantics. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  List
  Bool
  Lia.
Import ListNotations.

From Vellvm Require
  Numeric.Rocqlib.
From Vellvm Require Import
  Numeric.Zbits
  Numeric.Integers.
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

Local Open Scope bool_scope.
Local Open Scope list_scope.

Lemma xorb_false_iff : forall b1 b2 : bool, xorb b1 b2 = false <-> b1 = b2.
Proof.
  intros [] []; cbn; split; intros H; try reflexivity; discriminate.
Qed.

From CertValidator Require Import LratCore AigGates.

(** *** 6.2 [bools_to_Z] Arithmetic, Bit-Slicing, and MSB Bridge Lemmas *)

Definition b2z (b : bool) : Z := if b then 1%Z else 0%Z.

Lemma bools_to_Z_cons : forall b bs,
  bools_to_Z (b :: bs) = (2 * bools_to_Z bs + b2z b)%Z.
Proof.
  intros b bs; cbn [bools_to_Z]; rewrite Integers.Zshiftin_spec; reflexivity.
Qed.

Lemma bools_to_Z_range : forall bs,
  (0 <= bools_to_Z bs < 2 ^ Z.of_nat (List.length bs))%Z.
Proof.
  induction bs as [| b rest IH]; [cbn [bools_to_Z List.map List.length Z.of_nat]; rewrite Z.pow_0_r; lia |].
  cbn [List.length]; rewrite Nat2Z.inj_succ, Z.pow_succ_r, bools_to_Z_cons by lia.
  destruct b; cbn [b2z]; lia.
Qed.

Lemma bools_to_Z_inj : forall bs1 bs2,
  List.length bs1 = List.length bs2 ->
  bools_to_Z bs1 = bools_to_Z bs2 ->
  bs1 = bs2.
Proof.
  induction bs1 as [| b1 r1 IH]; intros [| b2 r2] Hlen Heq;
    try discriminate; [reflexivity |].
  cbn [bools_to_Z] in Heq.
  apply Integers.Zshiftin_inj in Heq as [-> Heqr].
  f_equal; apply IH; [cbn in Hlen; lia | exact Heqr].
Qed.

Lemma bools_to_Z_bit_int_to_bools : forall sz (x : @Integers.bit_int sz),
  bools_to_Z (bit_int_to_bools sz x) = @Integers.unsigned sz x.
Proof.
  intros sz x.
  pose proof (f_equal (@Integers.unsigned sz) (bit_int_to_bools_repr sz x)) as H.
  rewrite @Integers.unsigned_repr in H; [exact H |].
  pose proof (bools_to_Z_range (bit_int_to_bools sz x)) as Hr.
  rewrite bit_int_to_bools_length, positive_nat_Z in Hr.
  unfold Integers.max_unsigned; rewrite modulus_pow_sz; lia.
Qed.

Lemma unsigned_eval_rail_val : forall sz assign r,
  List.length (rbv_bits r) = Pos.to_nat sz ->
  @Integers.unsigned sz (eval_rail_val sz assign r) =
  bools_to_Z (List.map (eval_lit assign) (rbv_bits r)).
Proof.
  intros sz assign r Hlen; unfold eval_rail_val; apply @Integers.unsigned_repr.
  pose proof (bools_to_Z_range (List.map (eval_lit assign) (rbv_bits r))) as Hr.
  rewrite length_map, Hlen, positive_nat_Z in Hr.
  unfold Integers.max_unsigned; rewrite modulus_pow_sz; lia.
Qed.

Lemma map_eval_lit_eq_bit_int_to_bools : forall sz assign r,
  List.length (rbv_bits r) = Pos.to_nat sz ->
  List.map (eval_lit assign) (rbv_bits r) =
  bit_int_to_bools sz (eval_rail_val sz assign r).
Proof.
  intros sz assign r Hlen; apply bools_to_Z_inj.
  - rewrite length_map, Hlen, bit_int_to_bools_length; reflexivity.
  - rewrite bools_to_Z_bit_int_to_bools, unsigned_eval_rail_val by exact Hlen; reflexivity.
Qed.

Lemma bools_to_Z_app : forall xs ys,
  bools_to_Z (xs ++ ys) =
  (bools_to_Z xs + 2 ^ Z.of_nat (List.length xs) * bools_to_Z ys)%Z.
Proof.
  induction xs as [| b rx IH]; intros ys;
    [cbn [app bools_to_Z List.length Z.of_nat]; rewrite Z.pow_0_r; lia |].
  cbn [app List.length]; rewrite !bools_to_Z_cons, IH, Nat2Z.inj_succ, Z.pow_succ_r by lia; ring.
Qed.

Lemma bools_to_Z_repeat_false : forall n,
  bools_to_Z (List.repeat false n) = 0%Z.
Proof.
  induction n as [| n' IH]; cbn [List.repeat];
    [reflexivity | rewrite bools_to_Z_cons, IH; reflexivity].
Qed.

Lemma bools_to_Z_repeat_true : forall n,
  bools_to_Z (List.repeat true n) = (2 ^ Z.of_nat n - 1)%Z.
Proof.
  induction n as [| n' IH]; cbn [List.repeat];
    [reflexivity | rewrite bools_to_Z_cons, IH, Nat2Z.inj_succ, Z.pow_succ_r by lia; cbn [b2z]; lia].
Qed.

Lemma bools_to_Z_repeat_b : forall b n,
  bools_to_Z (List.repeat b n) = (b2z b * (2 ^ Z.of_nat n - 1))%Z.
Proof.
  intros [|] n;
    [rewrite bools_to_Z_repeat_true; cbn [b2z]; ring | rewrite bools_to_Z_repeat_false; cbn [b2z]; ring].
Qed.

Lemma bools_to_Z_zero_iff : forall bs,
  (bools_to_Z bs =? 0)%Z = negb (existsb (fun b : bool => b) bs).
Proof.
  induction bs as [| b rest IH]; [reflexivity |].
  rewrite bools_to_Z_cons; cbn [existsb negb].
  pose proof (bools_to_Z_range rest) as Hr.
  destruct b; cbn [b2z].
  - destruct (Z.eqb_spec (2 * bools_to_Z rest + 1) 0); [lia | reflexivity].
  - cbn [orb]; rewrite <- IH.
    destruct (Z.eqb_spec (2 * bools_to_Z rest + 0) 0),
             (Z.eqb_spec (bools_to_Z rest) 0); try reflexivity; lia.
Qed.

Lemma existsb_xorb_false_iff : forall s bs,
  existsb (xorb s) bs = false <-> bs = List.repeat s (List.length bs).
Proof.
  intros s bs; induction bs as [| b rest IH]; cbn [existsb List.repeat List.length].
  - split; intros _; reflexivity.
  - rewrite orb_false_iff, xorb_false_iff, IH; split.
    + intros [<- H]; f_equal; exact H.
    + intros Heq; injection Heq as <- Heqr; split; [reflexivity | exact Heqr].
Qed.

Lemma bools_to_Z_eq_repeat_iff : forall bs s,
  (bools_to_Z bs =? b2z s * (2 ^ Z.of_nat (List.length bs) - 1))%Z =
  negb (existsb (xorb s) bs).
Proof.
  intros bs s; rewrite <- bools_to_Z_repeat_b.
  destruct (existsb (xorb s) bs) eqn:Hex; cbn [negb].
  - destruct (Z.eqb_spec (bools_to_Z bs) (bools_to_Z (List.repeat s (List.length bs))))
      as [Heq | _]; [| reflexivity].
    apply bools_to_Z_inj in Heq; [| symmetry; apply repeat_length].
    apply (proj2 (existsb_xorb_false_iff s bs)) in Heq; congruence.
  - apply (proj1 (existsb_xorb_false_iff s bs)) in Hex.
    rewrite <- Hex, Z.eqb_refl; reflexivity.
Qed.

Lemma bools_to_Z_negb : forall bs,
  (bools_to_Z bs + bools_to_Z (List.map negb bs) = 2 ^ Z.of_nat (List.length bs) - 1)%Z.
Proof.
  induction bs as [| b rest IH]; [cbn [bools_to_Z List.map List.length Z.of_nat]; rewrite Z.pow_0_r; lia |].
  cbn [List.map List.length];
    rewrite !bools_to_Z_cons, Nat2Z.inj_succ, Z.pow_succ_r by lia.
  destruct b; cbn [negb b2z]; lia.
Qed.

Lemma map_eval_neg_lits : forall bound asg ls,
  wf_lits_bound bound ls ->
  List.map (eval_lit asg) (List.map neg_lit ls) =
  List.map negb (List.map (eval_lit asg) ls).
Proof.
  intros bound asg ls Hwf; induction Hwf as [| l r Hl Hr IH]; [reflexivity |].
  cbn; rewrite (eval_neg_lit_nonzero asg l (wf_lit_bound_nonzero bound l Hl)), IH; reflexivity.
Qed.

Lemma wf_lits_bound_app : forall bound l1 l2,
  wf_lits_bound bound l1 ->
  wf_lits_bound bound l2 ->
  wf_lits_bound bound (l1 ++ l2).
Proof.
  intros bound l1 l2 H1 H2; unfold wf_lits_bound; apply Forall_app; split; assumption.
Qed.

Lemma wf_lits_bound_repeat : forall bound l n,
  wf_lit_bound bound l ->
  wf_lits_bound bound (List.repeat l n).
Proof.
  intros bound l n Hl; induction n as [| n' IH]; cbn; constructor; [exact Hl | exact IH].
Qed.

Lemma wf_lits_bound_firstn : forall bound n ls,
  wf_lits_bound bound ls ->
  wf_lits_bound bound (List.firstn n ls).
Proof.
  intros bound n; induction n as [| n' IH]; intros [| x r] Hwf; cbn;
    [constructor | constructor | constructor |].
  inversion Hwf as [| ? ? Hx Hr]; subst.
  constructor; [exact Hx | exact (IH r Hr)].
Qed.

Lemma wf_lits_bound_skipn : forall bound n ls,
  wf_lits_bound bound ls ->
  wf_lits_bound bound (List.skipn n ls).
Proof.
  intros bound n; induction n as [| n' IH]; intros [| x r] Hwf; cbn;
    try exact Hwf; inversion Hwf as [| ? ? _ Hr]; subst; exact (IH r Hr).
Qed.

Lemma wf_lits_bound_nth : forall bound k ls d,
  wf_lits_bound bound ls ->
  wf_lit_bound bound d ->
  wf_lit_bound bound (List.nth k ls d).
Proof.
  intros bound k ls d Hwf Hd; revert k.
  induction Hwf as [| x r Hx Hr IH]; intros [| k']; cbn;
    [exact Hd | exact Hd | exact Hx | exact (IH k')].
Qed.

Lemma map_firstn_eq : forall {A B : Type} (f : A -> B) n (ls : list A),
  List.map f (List.firstn n ls) = List.firstn n (List.map f ls).
Proof.
  intros A B f n; induction n as [| n' IH]; intros [| x r]; cbn;
    [reflexivity | reflexivity | reflexivity | f_equal; apply IH].
Qed.

Lemma map_skipn_eq : forall {A B : Type} (f : A -> B) n (ls : list A),
  List.map f (List.skipn n ls) = List.skipn n (List.map f ls).
Proof.
  intros A B f n; induction n as [| n' IH]; intros [| x r]; cbn;
    [reflexivity | reflexivity | reflexivity | apply IH].
Qed.

Lemma map_repeat_eq : forall {A B : Type} (f : A -> B) (x : A) n,
  List.map f (List.repeat x n) = List.repeat (f x) n.
Proof.
  intros A B f x n; induction n as [| n' IH]; cbn; [reflexivity | f_equal; exact IH].
Qed.

Lemma nth_firstn_lt : forall {A : Type} (d : A) k n (ls : list A),
  (k < n)%nat ->
  List.nth k (List.firstn n ls) d = List.nth k ls d.
Proof.
  intros A d k; induction k as [| k' IH]; intros [| n'] [| x r] Hlt; cbn;
    try lia; try reflexivity; apply IH; lia.
Qed.

Lemma nth_skipn_eq : forall {A : Type} (d : A) k n (ls : list A),
  List.nth k (List.skipn n ls) d = List.nth (n + k) ls d.
Proof.
  intros A d k n; induction n as [| n' IH]; intros [| x r]; cbn;
    [reflexivity | reflexivity | destruct k; reflexivity | apply IH].
Qed.

Lemma nth_repeat_lt : forall {A : Type} (d x : A) k n,
  (k < n)%nat ->
  List.nth k (List.repeat x n) d = x.
Proof.
  intros A d x k; induction k as [| k' IH]; intros [| n'] Hlt; cbn;
    [lia | reflexivity | lia | apply IH; lia].
Qed.

Definition msb_of (sz : positive) (x : @Integers.bit_int sz) : bool :=
  List.nth (Pos.to_nat sz - 1) (bit_int_to_bools sz x) false.

Definition msb_lit (r : rail_bv) : lit :=
  List.nth (Pos.to_nat (rbv_width r) - 1) (rbv_bits r) lit_false.

Lemma wf_msb_lit : forall sz bound r,
  (2 <= bound)%positive ->
  wf_rail_bound sz bound r ->
  wf_lit_bound bound (msb_lit r).
Proof.
  intros sz bound r Hge2 (_ & Hbs & _); unfold msb_lit.
  exact (wf_lits_bound_nth bound _ _ lit_false Hbs (wf_lit_bound_false bound Hge2)).
Qed.

Lemma eval_msb_lit : forall sz assign r,
  wf_rail_bv sz r ->
  eval_lit assign (msb_lit r) = msb_of sz (eval_rail_val sz assign r).
Proof.
  intros sz assign r [Hw Hlen]; unfold msb_lit, msb_of; rewrite Hw.
  pose proof (Pos2Nat.is_pos sz) as Hpos.
  assert (Hlt : (Pos.to_nat sz - 1 < List.length (rbv_bits r))%nat) by lia.
  rewrite <- (map_nth (eval_lit assign) (rbv_bits r) lit_false (Pos.to_nat sz - 1)).
  rewrite (nth_indep _ (eval_lit assign lit_false) false)
    by (rewrite length_map; exact Hlt).
  rewrite (map_eval_lit_eq_bit_int_to_bools sz assign r Hlen); reflexivity.
Qed.

Lemma msb_of_sign_cond : forall sz (x : @Integers.bit_int sz),
  msb_of sz x =
  (if Numeric.Rocqlib.zlt (@Integers.unsigned sz x) (@Integers.half_modulus sz)
   then false else true).
Proof.
  intros sz x; unfold msb_of.
  pose proof (Pos2Nat.is_pos sz) as Hpos.
  assert (Hlt : (Pos.to_nat sz - 1 < Pos.to_nat sz)%nat) by lia.
  rewrite bit_int_to_bools_nth by exact Hlt.
  replace (Z.of_nat (Pos.to_nat sz - 1)) with (@Integers.zwordsize sz - 1)%Z
    by (unfold Integers.zwordsize; rewrite Nat2Z.inj_sub, positive_nat_Z by lia; reflexivity).
  apply @Integers.sign_bit_of_unsigned.
Qed.

Lemma msb_of_unsigned_bounds : forall sz (x : @Integers.bit_int sz),
  if msb_of sz x
  then (@Integers.half_modulus sz <= @Integers.unsigned sz x < 2 * @Integers.half_modulus sz)%Z
  else (0 <= @Integers.unsigned sz x < @Integers.half_modulus sz)%Z.
Proof.
  intros sz x; rewrite msb_of_sign_cond.
  pose proof (@Integers.unsigned_range sz x) as Hur.
  pose proof (@Integers.half_modulus_modulus sz) as Hhm.
  destruct (Numeric.Rocqlib.zlt (@Integers.unsigned sz x) (@Integers.half_modulus sz)); lia.
Qed.

Lemma signed_eq_unsigned_msb : forall sz (x : @Integers.bit_int sz),
  @Integers.signed sz x =
  (@Integers.unsigned sz x - b2z (msb_of sz x) * @Integers.modulus sz)%Z.
Proof.
  intros sz x; unfold Integers.signed; rewrite msb_of_sign_cond.
  destruct (Numeric.Rocqlib.zlt (@Integers.unsigned sz x) (@Integers.half_modulus sz));
    cbn [b2z]; lia.
Qed.

Lemma lt_zero_eq_msb : forall sz (x : @Integers.bit_int sz),
  @Integers.lt sz x (@Integers.zero sz) = msb_of sz x.
Proof.
  intros sz x; unfold Integers.lt; rewrite @Integers.signed_zero.
  unfold Integers.signed; rewrite msb_of_sign_cond.
  pose proof (@Integers.unsigned_range sz x) as Hur.
  destruct (Numeric.Rocqlib.zlt (@Integers.unsigned sz x) (@Integers.half_modulus sz)),
           (Numeric.Rocqlib.zlt _ 0%Z); try reflexivity; lia.
Qed.

Lemma signed_lt_zero_eq_msb : forall sz (x : @Integers.bit_int sz),
  (@Integers.signed sz x <? 0)%Z = msb_of sz x.
Proof.
  intros sz x; unfold Integers.signed; rewrite msb_of_sign_cond.
  pose proof (@Integers.unsigned_range sz x) as Hur.
  destruct (Numeric.Rocqlib.zlt (@Integers.unsigned sz x) (@Integers.half_modulus sz));
    match goal with |- context [(?u <? 0)%Z] => destruct (Z.ltb_spec u 0%Z) end; try reflexivity; lia.
Qed.

Lemma unsigned_negative_eq_msb : forall sz (x : @Integers.bit_int sz),
  @Integers.unsigned sz (@Integers.negative sz x) = b2z (msb_of sz x).
Proof.
  intros sz x; unfold Integers.negative; rewrite lt_zero_eq_msb.
  destruct (msb_of sz x);
    [apply @Integers.unsigned_one | apply @Integers.unsigned_zero].
Qed.

Lemma eq_one_cond : forall sz (c : bool),
  @Integers.eq sz (if c then @Integers.one sz else @Integers.zero sz) (@Integers.one sz) = c.
Proof.
  intros sz [|]; unfold Integers.eq, Numeric.Rocqlib.zeq;
    rewrite ?(@Integers.unsigned_one sz), ?(@Integers.unsigned_zero sz);
    destruct (Z.eq_dec _ _); try reflexivity; lia.
Qed.

Lemma eq_zero_else_one_cond : forall sz (c : bool),
  @Integers.eq sz (if c then @Integers.zero sz else @Integers.one sz) (@Integers.one sz) = negb c.
Proof.
  intros sz [|]; [exact (eq_one_cond sz false) | exact (eq_one_cond sz true)].
Qed.

Lemma eq_zero_one : forall sz,
  @Integers.eq sz (@Integers.zero sz) (@Integers.one sz) = false.
Proof. intros sz; exact (eq_one_cond sz false). Qed.

Lemma eq_one_one : forall sz,
  @Integers.eq sz (@Integers.one sz) (@Integers.one sz) = true.
Proof. intros sz; exact (eq_one_cond sz true). Qed.

Lemma div_low_high_pow2 : forall lo hi p,
  (0 < p)%Z -> (0 <= lo < p)%Z ->
  ((lo + p * hi) / p = hi)%Z.
Proof.
  intros lo hi p Hp Hlo; symmetry; apply (Zdiv_unique (lo + p * hi) p hi lo); lia.
Qed.

Lemma mod_low_high_pow2 : forall lo hi p,
  (0 < p)%Z -> (0 <= lo < p)%Z ->
  ((lo + p * hi) mod p = lo)%Z.
Proof.
  intros lo hi p Hp Hlo; symmetry; apply (Zmod_unique (lo + p * hi) p hi lo); lia.
Qed.

Lemma nat_lt_pow2 : forall n,
  (Z.of_nat n < 2 ^ Z.of_nat n)%Z.
Proof.
  induction n as [| m IH]; [cbn; lia | rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; lia].
Qed.

Lemma existsb_id_map_f : forall {A : Type} (f : A -> bool) (ls : list A),
  existsb (fun b : bool => b) (List.map f ls) = existsb f ls.
Proof.
  intros A f ls; induction ls as [| x r IH]; [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

(** *** 6.3 Verified 2-Rail Bitwise, Arithmetic, Shift, Conversion, [icmp], and [select] Encoders *)

Definition blast_and_rail_opt (sz : positive) (a b : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let '(bits, st1) := map2_emit emit_and2_opt (rbv_bits a) (rbv_bits b) st in
  let '(psn, st2)  := emit_or2_opt (rbv_psn a) (rbv_psn b) st1 in
  (mk_rail_bv sz bits psn, st2).

Theorem blast_and_rail_opt_step : forall sz a b asg st out st',
  sat_blast_st asg st ->
  wf_rail_bound sz (bs_next_var st) a ->
  wf_rail_bound sz (bs_next_var st) b ->
  blast_and_rail_opt sz a b st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_rail_bound sz (bs_next_var st') out /\
    eval_rail_psn asg' out = (eval_rail_psn asg a || eval_rail_psn asg b) /\
    eval_rail_val sz asg' out =
    @Integers.and sz (eval_rail_val sz asg a) (eval_rail_val sz asg b).
Proof.
  intros sz a b asg st out st' Hsat
         ([Hwa Hla] & Hba & Hpa) ([Hwb Hlb] & Hbb & Hpb) Hbl.
  unfold blast_and_rail_opt in Hbl.
  destruct (map2_emit emit_and2_opt (rbv_bits a) (rbv_bits b) st) as [bits st1] eqn:Hm.
  destruct (emit_or2_opt (rbv_psn a) (rbv_psn b) st1) as [psn st2] eqn:Hp.
  inversion Hbl; subst out st2; clear Hbl.
  assert (Hlen_ab : List.length (rbv_bits a) = List.length (rbv_bits b)) by congruence.
  destruct (map2_emit_step emit_and2_opt andb emit_and2_opt_step _ _ asg st bits st1
              Hlen_ab Hba Hbb Hsat Hm)
    as (asg1 & Hs1 & Hblen & Hbwf & Hbev).
  destruct (emit_or2_opt_step asg1 (rbv_psn a) (rbv_psn b) st1 psn st' (proj2 (proj2 Hs1))
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpa)
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpb) Hp)
    as (asg2 & Hs2 & Hpwf & Hpev).
  pose proof (step_spec_trans st st1 st' asg asg1 asg2 Hs1 Hs2) as Hs12.
  exists asg2; split; [exact Hs12 | split].
  - split; [split; [reflexivity | cbn; congruence] |
            split; [exact (wf_lits_bound_mono _ _ bits (proj1 Hs2) Hbwf) | exact Hpwf]].
  - split.
    + unfold eval_rail_psn; cbn [rbv_psn]; rewrite Hpev,
        (step_spec_eval_lit st st1 asg asg1 (rbv_psn a) Hs1 Hpa),
        (step_spec_eval_lit st st1 asg asg1 (rbv_psn b) Hs1 Hpb); reflexivity.
    + apply @Integers.same_bits_eq; intros i Hi.
      rewrite @Integers.bits_and by exact Hi.
      rewrite !eval_rail_val_testbit by exact Hi.
      cbn [rbv_bits]; rewrite (step_spec_eval_lits st1 st' asg1 asg2 bits Hs2 Hbwf), Hbev.
      apply list_map2_nth; [rewrite !length_map; exact Hlen_ab |].
      rewrite length_map, Hla; unfold Integers.zwordsize in Hi; lia.
Qed.

Definition blast_xor_rail_opt (sz : positive) (a b : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let '(bits, st1) := map2_emit emit_xor2_opt (rbv_bits a) (rbv_bits b) st in
  let '(psn, st2)  := emit_or2_opt (rbv_psn a) (rbv_psn b) st1 in
  (mk_rail_bv sz bits psn, st2).

Theorem blast_xor_rail_opt_step : forall sz a b asg st out st',
  sat_blast_st asg st ->
  wf_rail_bound sz (bs_next_var st) a ->
  wf_rail_bound sz (bs_next_var st) b ->
  blast_xor_rail_opt sz a b st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_rail_bound sz (bs_next_var st') out /\
    eval_rail_psn asg' out = (eval_rail_psn asg a || eval_rail_psn asg b) /\
    eval_rail_val sz asg' out =
    @Integers.xor sz (eval_rail_val sz asg a) (eval_rail_val sz asg b).
Proof.
  intros sz a b asg st out st' Hsat
         ([Hwa Hla] & Hba & Hpa) ([Hwb Hlb] & Hbb & Hpb) Hbl.
  unfold blast_xor_rail_opt in Hbl.
  destruct (map2_emit emit_xor2_opt (rbv_bits a) (rbv_bits b) st) as [bits st1] eqn:Hm.
  destruct (emit_or2_opt (rbv_psn a) (rbv_psn b) st1) as [psn st2] eqn:Hp.
  inversion Hbl; subst out st2; clear Hbl.
  assert (Hlen_ab : List.length (rbv_bits a) = List.length (rbv_bits b)) by congruence.
  destruct (map2_emit_step emit_xor2_opt xorb emit_xor2_opt_step _ _ asg st bits st1
              Hlen_ab Hba Hbb Hsat Hm)
    as (asg1 & Hs1 & Hblen & Hbwf & Hbev).
  destruct (emit_or2_opt_step asg1 (rbv_psn a) (rbv_psn b) st1 psn st' (proj2 (proj2 Hs1))
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpa)
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpb) Hp)
    as (asg2 & Hs2 & Hpwf & Hpev).
  pose proof (step_spec_trans st st1 st' asg asg1 asg2 Hs1 Hs2) as Hs12.
  exists asg2; split; [exact Hs12 | split].
  - split; [split; [reflexivity | cbn; congruence] |
            split; [exact (wf_lits_bound_mono _ _ bits (proj1 Hs2) Hbwf) | exact Hpwf]].
  - split.
    + unfold eval_rail_psn; cbn [rbv_psn]; rewrite Hpev,
        (step_spec_eval_lit st st1 asg asg1 (rbv_psn a) Hs1 Hpa),
        (step_spec_eval_lit st st1 asg asg1 (rbv_psn b) Hs1 Hpb); reflexivity.
    + apply @Integers.same_bits_eq; intros i Hi.
      rewrite @Integers.bits_xor by exact Hi.
      rewrite !eval_rail_val_testbit by exact Hi.
      cbn [rbv_bits]; rewrite (step_spec_eval_lits st1 st' asg1 asg2 bits Hs2 Hbwf), Hbev.
      apply list_map2_nth; [rewrite !length_map; exact Hlen_ab |].
      rewrite length_map, Hla; unfold Integers.zwordsize in Hi; lia.
Qed.

Lemma or_eq_xor_iff_disjoint : forall sz assign a b,
  wf_rail_bv sz a ->
  wf_rail_bv sz b ->
  negb (@Integers.eq sz (@Integers.or sz (eval_rail_val sz assign a) (eval_rail_val sz assign b))
                        (@Integers.xor sz (eval_rail_val sz assign a) (eval_rail_val sz assign b))) =
  existsb (fun x : bool => x)
          (list_map2 andb (List.map (eval_lit assign) (rbv_bits a))
                          (List.map (eval_lit assign) (rbv_bits b))).
Proof.
  intros sz assign a b [_ Hla] [_ Hlb].
  set (va := eval_rail_val sz assign a).
  set (vb := eval_rail_val sz assign b).
  set (ba := List.map (eval_lit assign) (rbv_bits a)).
  set (bb := List.map (eval_lit assign) (rbv_bits b)).
  assert (Hlen_ab : List.length ba = List.length bb)
    by (unfold ba, bb; rewrite !length_map; congruence).
  assert (Hlen_a : List.length ba = Pos.to_nat sz)
    by (unfold ba; rewrite length_map; exact Hla).
  destruct (existsb (fun x : bool => x) (list_map2 andb ba bb)) eqn:Hex.
  - apply existsb_exists in Hex as [z [Hin Hz]]; subst z.
    destruct (In_nth _ _ false Hin) as [k [Hk Hnth]].
    rewrite list_map2_length in Hk by exact Hlen_ab.
    rewrite list_map2_nth in Hnth by assumption.
    apply andb_true_iff in Hnth as [Hka Hkb].
    assert (Hi : (0 <= Z.of_nat k < @Integers.zwordsize sz)%Z)
      by (unfold Integers.zwordsize; rewrite <- positive_nat_Z; lia).
    assert (Hdiff : @Integers.or sz va vb <> @Integers.xor sz va vb).
    { intros Heq.
      pose proof (f_equal (fun v => @Integers.testbit sz v (Z.of_nat k)) Heq) as Htb;
        cbn beta in Htb.
      rewrite @Integers.bits_or, @Integers.bits_xor in Htb by exact Hi.
      unfold va, vb in Htb; rewrite !eval_rail_val_testbit_nat in Htb by lia.
      fold ba bb in Htb; rewrite Hka, Hkb in Htb; discriminate Htb. }
    unfold Integers.eq, Numeric.Rocqlib.zeq.
    destruct (Z.eq_dec (@Integers.unsigned sz (@Integers.or sz va vb))
                       (@Integers.unsigned sz (@Integers.xor sz va vb))) as [Hu | _];
      [| reflexivity].
    exfalso; apply Hdiff.
    rewrite <- (@Integers.repr_unsigned sz (@Integers.or sz va vb)),
            <- (@Integers.repr_unsigned sz (@Integers.xor sz va vb)), Hu; reflexivity.
  - assert (Heq : @Integers.or sz va vb = @Integers.xor sz va vb).
    { apply @Integers.same_bits_eq; intros i Hi.
      rewrite @Integers.bits_or, @Integers.bits_xor by exact Hi.
      unfold va, vb; rewrite !eval_rail_val_testbit by exact Hi; fold ba bb.
      assert (Hk : (Z.to_nat i < List.length ba)%nat)
        by (unfold Integers.zwordsize in Hi; lia).
      assert (Hand_f : List.nth (Z.to_nat i) ba false && List.nth (Z.to_nat i) bb false = false).
      { rewrite <- (list_map2_nth andb ba bb (Z.to_nat i) Hlen_ab Hk).
        destruct (List.nth (Z.to_nat i) (list_map2 andb ba bb) false) eqn:Enth; [| reflexivity].
        assert (Hex_t : existsb (fun x : bool => x) (list_map2 andb ba bb) = true).
        { apply existsb_exists; exists true; split; [| reflexivity].
          rewrite <- Enth; apply nth_In; rewrite list_map2_length by exact Hlen_ab; exact Hk. }
        congruence. }
      destruct (List.nth (Z.to_nat i) ba false), (List.nth (Z.to_nat i) bb false);
        try reflexivity; discriminate Hand_f. }
    rewrite Heq; unfold Integers.eq, Numeric.Rocqlib.zeq.
    destruct (Z.eq_dec _ _); [reflexivity | congruence].
Qed.

Definition blast_or_disjoint_rail (dj : bool) (sz : positive) (a b : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let '(bits, st1) := map2_emit emit_or2_opt (rbv_bits a) (rbv_bits b) st in
  let '(base_psn, st2) := emit_or2_opt (rbv_psn a) (rbv_psn b) st1 in
  if dj then
    let '(and_bits, st3) := map2_emit emit_and2_opt (rbv_bits a) (rbv_bits b) st2 in
    let '(ov_psn, st4)   := emit_or_list_opt and_bits st3 in
    let '(psn, st5)      := emit_or2_opt base_psn ov_psn st4 in
    (mk_rail_bv sz bits psn, st5)
  else
    (mk_rail_bv sz bits base_psn, st2).

Theorem blast_or_disjoint_rail_step : forall dj sz a b asg st out st',
  sat_blast_st asg st ->
  wf_rail_bound sz (bs_next_var st) a ->
  wf_rail_bound sz (bs_next_var st) b ->
  blast_or_disjoint_rail dj sz a b st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_rail_bound sz (bs_next_var st') out /\
    eval_rail_psn asg' out =
      ((eval_rail_psn asg a || eval_rail_psn asg b) ||
       (dj && negb (@Integers.eq sz
                      (@Integers.or sz (eval_rail_val sz asg a) (eval_rail_val sz asg b))
                      (@Integers.xor sz (eval_rail_val sz asg a) (eval_rail_val sz asg b))))) /\
    eval_rail_val sz asg' out =
      @Integers.or sz (eval_rail_val sz asg a) (eval_rail_val sz asg b).
Proof.
  intros dj sz a b asg st out st' Hsat
         ([Hwa Hla] & Hba & Hpa) ([Hwb Hlb] & Hbb & Hpb) Hbl.
  unfold blast_or_disjoint_rail in Hbl.
  destruct (map2_emit emit_or2_opt (rbv_bits a) (rbv_bits b) st) as [bits st1] eqn:Hm.
  destruct (emit_or2_opt (rbv_psn a) (rbv_psn b) st1) as [base_psn st2] eqn:Hbp.
  assert (Hlen_ab : List.length (rbv_bits a) = List.length (rbv_bits b)) by congruence.
  destruct (map2_emit_step emit_or2_opt orb emit_or2_opt_step _ _ asg st bits st1
              Hlen_ab Hba Hbb Hsat Hm)
    as (asg1 & Hs1 & Hblen & Hbwf & Hbev).
  destruct (emit_or2_opt_step asg1 (rbv_psn a) (rbv_psn b) st1 base_psn st2 (proj2 (proj2 Hs1))
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpa)
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpb) Hbp)
    as (asg2 & Hs2 & Hbp_wf & Hbp_ev).
  pose proof (step_spec_trans st st1 st2 asg asg1 asg2 Hs1 Hs2) as Hs12.
  destruct dj.
  - destruct (map2_emit emit_and2_opt (rbv_bits a) (rbv_bits b) st2) as [and_bits st3] eqn:Hma.
    destruct (emit_or_list_opt and_bits st3) as [ov_psn st4] eqn:Hov.
    destruct (emit_or2_opt base_psn ov_psn st4) as [psn st5] eqn:Hp.
    inversion Hbl; subst out st5; clear Hbl.
    destruct (map2_emit_step emit_and2_opt andb emit_and2_opt_step _ _ asg2 st2 and_bits st3
                Hlen_ab
                (wf_lits_bound_mono _ _ _ (proj1 Hs12) Hba)
                (wf_lits_bound_mono _ _ _ (proj1 Hs12) Hbb)
                (proj2 (proj2 Hs2)) Hma)
      as (asg3 & Hs3 & _ & Hand_wf & Hand_ev).
    destruct (emit_or_list_opt_step and_bits asg3 st3 ov_psn st4 Hand_wf (proj2 (proj2 Hs3)) Hov)
      as (asg4 & Hs4 & Hov_wf & Hov_ev).
    pose proof (step_spec_trans st2 st3 st4 asg2 asg3 asg4 Hs3 Hs4) as Hs24.
    destruct (emit_or2_opt_step asg4 base_psn ov_psn st4 psn st' (proj2 (proj2 Hs4))
                (wf_lit_bound_mono _ _ _ (proj1 Hs24) Hbp_wf) Hov_wf Hp)
      as (asg5 & Hs5 & Hpwf & Hpev).
    pose proof (step_spec_trans st1 st2 st4 asg1 asg2 asg4 Hs2 Hs24) as Hs14.
    pose proof (step_spec_trans st1 st4 st' asg1 asg4 asg5 Hs14 Hs5) as Hs15.
    pose proof (step_spec_trans st st1 st' asg asg1 asg5 Hs1 Hs15) as Hs05.
    exists asg5; split; [exact Hs05 | split].
    + split; [split; [reflexivity | cbn; congruence] |
              split; [exact (wf_lits_bound_mono _ _ bits (proj1 Hs15) Hbwf) | exact Hpwf]].
    + split.
      * unfold eval_rail_psn; cbn [rbv_psn]; cbn [andb].
        rewrite Hpev,
                (step_spec_eval_lit st2 st4 asg2 asg4 base_psn Hs24 Hbp_wf),
                Hbp_ev,
                (step_spec_eval_lit st st1 asg asg1 (rbv_psn a) Hs1 Hpa),
                (step_spec_eval_lit st st1 asg asg1 (rbv_psn b) Hs1 Hpb),
                Hov_ev, Hand_ev,
                (step_spec_eval_lits st st2 asg asg2 (rbv_bits a) Hs12 Hba),
                (step_spec_eval_lits st st2 asg asg2 (rbv_bits b) Hs12 Hbb),
                <- (or_eq_xor_iff_disjoint sz asg a b (conj Hwa Hla) (conj Hwb Hlb));
          reflexivity.
      * apply @Integers.same_bits_eq; intros i Hi.
        rewrite @Integers.bits_or by exact Hi.
        rewrite !eval_rail_val_testbit by exact Hi.
        cbn [rbv_bits]; rewrite (step_spec_eval_lits st1 st' asg1 asg5 bits Hs15 Hbwf), Hbev.
        apply list_map2_nth; [rewrite !length_map; exact Hlen_ab |].
        rewrite length_map, Hla; unfold Integers.zwordsize in Hi; lia.
  - inversion Hbl; subst out st2; clear Hbl.
    exists asg2; split; [exact Hs12 | split].
    + split; [split; [reflexivity | cbn; congruence] |
              split; [exact (wf_lits_bound_mono _ _ bits (proj1 Hs2) Hbwf) | exact Hbp_wf]].
    + split.
      * unfold eval_rail_psn; cbn [rbv_psn]; cbn [andb]; rewrite orb_false_r, Hbp_ev,
          (step_spec_eval_lit st st1 asg asg1 (rbv_psn a) Hs1 Hpa),
          (step_spec_eval_lit st st1 asg asg1 (rbv_psn b) Hs1 Hpb); reflexivity.
      * apply @Integers.same_bits_eq; intros i Hi.
        rewrite @Integers.bits_or by exact Hi.
        rewrite !eval_rail_val_testbit by exact Hi.
        cbn [rbv_bits]; rewrite (step_spec_eval_lits st1 st' asg1 asg2 bits Hs2 Hbwf), Hbev.
        apply list_map2_nth; [rewrite !length_map; exact Hlen_ab |].
        rewrite length_map, Hla; unfold Integers.zwordsize in Hi; lia.
Qed.

Fixpoint emit_ripple_add (cin : lit) (xs ys : list lit) (st : blast_state)
  {struct xs} : (list lit * lit) * blast_state :=
  match xs, ys with
  | x :: rx, y :: ry =>
      let '(xy_xor, st1) := emit_xor2_opt x y st in
      let '(sum_b, st2)  := emit_xor2_opt xy_xor cin st1 in
      let '(xy_and, st3) := emit_and2_opt x y st2 in
      let '(xc_and, st4) := emit_and2_opt xy_xor cin st3 in
      let '(cout1, st5)  := emit_or2_opt xy_and xc_and st4 in
      let '((rest_sum, cout), st6) := emit_ripple_add cout1 rx ry st5 in
      ((sum_b :: rest_sum, cout), st6)
  | _, _ => (([], cin), st)
  end.

Lemma full_adder_b2z : forall bx by0 bc,
  (b2z (xorb (xorb bx by0) bc) + 2 * b2z ((bx && by0) || (xorb bx by0 && bc)) =
   b2z bx + b2z by0 + b2z bc)%Z.
Proof.
  intros [|] [|] [|]; reflexivity.
Qed.

Lemma emit_ripple_add_step : forall xs ys cin asg st sums cout st',
  List.length xs = List.length ys ->
  wf_lit_bound (bs_next_var st) cin ->
  wf_lits_bound (bs_next_var st) xs ->
  wf_lits_bound (bs_next_var st) ys ->
  sat_blast_st asg st ->
  emit_ripple_add cin xs ys st = ((sums, cout), st') ->
  exists asg',
    step_spec st st' asg asg' /\
    List.length sums = List.length xs /\
    wf_lits_bound (bs_next_var st') sums /\
    wf_lit_bound (bs_next_var st') cout /\
    (bools_to_Z (List.map (eval_lit asg') sums) +
     2 ^ Z.of_nat (List.length xs) * b2z (eval_lit asg' cout) =
     bools_to_Z (List.map (eval_lit asg) xs) +
     bools_to_Z (List.map (eval_lit asg) ys) +
     b2z (eval_lit asg cin))%Z.
Proof.
  induction xs as [| x rx IH]; intros [| y ry] cin asg st sums cout st' Hlen Hcin Hwx Hwy Hsat Hrip;
    try discriminate; cbn [emit_ripple_add] in Hrip.
  - inversion Hrip; subst sums cout st'; exists asg; split;
      [exact (step_spec_refl _ asg Hsat) | split; [reflexivity | split; [constructor |
       split; [exact Hcin | cbn [List.map List.length Z.of_nat bools_to_Z]; rewrite Z.pow_0_r; lia]]]].
  - inversion Hwx as [| ? ? Hx Hwrx]; subst.
    inversion Hwy as [| ? ? Hy Hwry]; subst.
    injection Hlen as Hlen'.
    destruct (emit_xor2_opt x y st) as [xy_xor st1] eqn:Eg1.
    destruct (emit_xor2_opt xy_xor cin st1) as [sum_b st2] eqn:Eg2.
    destruct (emit_and2_opt x y st2) as [xy_and st3] eqn:Eg3.
    destruct (emit_and2_opt xy_xor cin st3) as [xc_and st4] eqn:Eg4.
    destruct (emit_or2_opt xy_and xc_and st4) as [cout1 st5] eqn:Eg5.
    destruct (emit_ripple_add cout1 rx ry st5) as [[rest_sum cout2] st6] eqn:Eg6.
    inversion Hrip; subst sums cout2 st6; clear Hrip.
    destruct (emit_xor2_opt_step asg x y st xy_xor st1 Hsat Hx Hy Eg1)
      as (asg1 & Hs1 & Hw_xx & Hev_xx).
    destruct (emit_xor2_opt_step asg1 xy_xor cin st1 sum_b st2 (proj2 (proj2 Hs1))
                Hw_xx (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hcin) Eg2)
      as (asg2 & Hs2 & Hw_sb & Hev_sb).
    pose proof (step_spec_trans st st1 st2 asg asg1 asg2 Hs1 Hs2) as Hs02.
    destruct (emit_and2_opt_step asg2 x y st2 xy_and st3 (proj2 (proj2 Hs2))
                (wf_lit_bound_mono _ _ _ (proj1 Hs02) Hx)
                (wf_lit_bound_mono _ _ _ (proj1 Hs02) Hy) Eg3)
      as (asg3 & Hs3 & Hw_xa & Hev_xa).
    pose proof (step_spec_trans st1 st2 st3 asg1 asg2 asg3 Hs2 Hs3) as Hs13.
    pose proof (step_spec_trans st st1 st3 asg asg1 asg3 Hs1 Hs13) as Hs03.
    destruct (emit_and2_opt_step asg3 xy_xor cin st3 xc_and st4 (proj2 (proj2 Hs3))
                (wf_lit_bound_mono _ _ _ (proj1 Hs13) Hw_xx)
                (wf_lit_bound_mono _ _ _ (proj1 Hs03) Hcin) Eg4)
      as (asg4 & Hs4 & Hw_xc & Hev_xc).
    pose proof (step_spec_trans st2 st3 st4 asg2 asg3 asg4 Hs3 Hs4) as Hs24.
    destruct (emit_or2_opt_step asg4 xy_and xc_and st4 cout1 st5 (proj2 (proj2 Hs4))
                (wf_lit_bound_mono _ _ _ (proj1 Hs4) Hw_xa) Hw_xc Eg5)
      as (asg5 & Hs5 & Hw_c1 & Hev_c1).
    pose proof (step_spec_trans st2 st4 st5 asg2 asg4 asg5 Hs24 Hs5) as Hs25.
    pose proof (step_spec_trans st st2 st5 asg asg2 asg5 Hs02 Hs25) as Hs05.
    destruct (IH ry cout1 asg5 st5 rest_sum cout st' Hlen' Hw_c1
                (wf_lits_bound_mono _ _ _ (proj1 Hs05) Hwrx)
                (wf_lits_bound_mono _ _ _ (proj1 Hs05) Hwry)
                (proj2 (proj2 Hs5)) Eg6)
      as (asg6 & Hs6 & Hlen_r & Hwf_r & Hwf_c & Heq_r).
    pose proof (step_spec_trans st2 st5 st' asg2 asg5 asg6 Hs25 Hs6) as Hs26.
    pose proof (step_spec_trans st st5 st' asg asg5 asg6 Hs05 Hs6) as Hs06.
    exists asg6; split; [exact Hs06 | split; [cbn; rewrite Hlen_r; reflexivity | split]].
    + constructor; [exact (wf_lit_bound_mono _ _ _ (proj1 Hs26) Hw_sb) | exact Hwf_r].
    + split; [exact Hwf_c |].
      cbn [List.map List.length];
        rewrite !bools_to_Z_cons, Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite (step_spec_eval_lit st2 st' asg2 asg6 sum_b Hs26 Hw_sb),
              Hev_sb, Hev_xx,
              (step_spec_eval_lit st st1 asg asg1 cin Hs1 Hcin).
      rewrite (step_spec_eval_lits st st5 asg asg5 rx Hs05 Hwrx),
              (step_spec_eval_lits st st5 asg asg5 ry Hs05 Hwry) in Heq_r.
      rewrite Hev_c1,
              (step_spec_eval_lit st3 st4 asg3 asg4 xy_and Hs4 Hw_xa),
              Hev_xa,
              (step_spec_eval_lit st st2 asg asg2 x Hs02 Hx),
              (step_spec_eval_lit st st2 asg asg2 y Hs02 Hy),
              Hev_xc,
              (step_spec_eval_lit st1 st3 asg1 asg3 xy_xor Hs13 Hw_xx),
              Hev_xx,
              (step_spec_eval_lit st st3 asg asg3 cin Hs03 Hcin) in Heq_r.
      pose proof (full_adder_b2z (eval_lit asg x) (eval_lit asg y) (eval_lit asg cin)) as Hfa.
      nia.
Qed.

Definition blast_add_rail (nuw nsw : bool) (sz : positive) (a b : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let '((sums, cout), st1) := emit_ripple_add lit_false (rbv_bits a) (rbv_bits b) st in
  let nuw_lit := if nuw then cout else lit_false in
  let '(nsw_lit, st4) :=
      if nsw then
        let sa := msb_lit a in
        let sb := msb_lit b in
        let ss := List.nth (Pos.to_nat sz - 1) sums lit_false in
        let '(x_ab, st2)  := emit_xor2_opt sa sb st1 in
        let '(x_sa, st3)  := emit_xor2_opt ss sa st2 in
        emit_and2_opt (neg_lit x_ab) x_sa st3
      else (lit_false, st1) in
  let '(base_psn, st5) := emit_or2_opt (rbv_psn a) (rbv_psn b) st4 in
  let '(ov_psn, st6)   := emit_or2_opt nuw_lit nsw_lit st5 in
  let '(psn, st7)      := emit_or2_opt base_psn ov_psn st6 in
  (mk_rail_bv sz sums psn, st7).

Theorem blast_add_rail_step : forall nuw nsw sz a b asg st out st',
  sat_blast_st asg st ->
  wf_rail_bound sz (bs_next_var st) a ->
  wf_rail_bound sz (bs_next_var st) b ->
  blast_add_rail nuw nsw sz a b st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_rail_bound sz (bs_next_var st') out /\
    eval_rail_psn asg' out =
      ((eval_rail_psn asg a || eval_rail_psn asg b) ||
       ((nuw && @Integers.eq sz
                  (@Integers.add_carry sz (eval_rail_val sz asg a)
                                          (eval_rail_val sz asg b)
                                          (@Integers.zero sz))
                  (@Integers.one sz)) ||
        (nsw && @Integers.eq sz
                  (@Integers.add_overflow sz (eval_rail_val sz asg a)
                                             (eval_rail_val sz asg b)
                                             (@Integers.zero sz))
                  (@Integers.one sz)))) /\
    eval_rail_val sz asg' out =
      @Integers.add sz (eval_rail_val sz asg a) (eval_rail_val sz asg b).
Proof.
  intros nuw nsw sz a b asg st out st' Hsat
         ([Hwa Hla] & Hba & Hpa) ([Hwb Hlb] & Hbb & Hpb) Hbl.
  unfold blast_add_rail in Hbl; cbn zeta in Hbl.
  destruct (emit_ripple_add lit_false (rbv_bits a) (rbv_bits b) st)
    as [[sums cout] st1] eqn:Hrip; cbn iota zeta in Hbl.
  assert (Hlen_ab : List.length (rbv_bits a) = List.length (rbv_bits b)) by congruence.
  destruct (emit_ripple_add_step (rbv_bits a) (rbv_bits b) lit_false asg st sums cout st1
              Hlen_ab (wf_lit_bound_false _ (proj1 (proj1 Hsat))) Hba Hbb Hsat Hrip)
    as (asg1 & Hs1 & Hlen_s & Hwf_s & Hwf_c & Heq_sum).
  rewrite (sat_eval_lit_false asg _ Hsat) in Heq_sum; cbn [b2z] in Heq_sum.
  set (va := eval_rail_val sz asg a).
  set (vb := eval_rail_val sz asg b).
  assert (Hua : bools_to_Z (List.map (eval_lit asg) (rbv_bits a)) = @Integers.unsigned sz va)
    by (symmetry; exact (unsigned_eval_rail_val sz asg a Hla)).
  assert (Hub : bools_to_Z (List.map (eval_lit asg) (rbv_bits b)) = @Integers.unsigned sz vb)
    by (symmetry; exact (unsigned_eval_rail_val sz asg b Hlb)).
  rewrite Hla, positive_nat_Z, <- modulus_pow_sz, Hua, Hub in Heq_sum.
  set (us := bools_to_Z (List.map (eval_lit asg1) sums)) in *.
  assert (Hus_rng : (0 <= us < @Integers.modulus sz)%Z).
  { unfold us; pose proof (bools_to_Z_range (List.map (eval_lit asg1) sums)) as Hr.
    rewrite length_map, Hlen_s, Hla, positive_nat_Z, <- modulus_pow_sz in Hr; exact Hr. }
  assert (Hus_repr : @Integers.unsigned sz (@Integers.repr sz us) = us)
    by (apply @Integers.unsigned_repr; unfold Integers.max_unsigned; lia).
  assert (Hval_eq : @Integers.repr sz us = @Integers.add sz va vb).
  { unfold Integers.add; apply @Integers.eqm_samerepr.
    exists (- b2z (eval_lit asg1 cout))%Z; nia. }
  assert (Hcarry_eq :
            @Integers.eq sz (@Integers.add_carry sz va vb (@Integers.zero sz)) (@Integers.one sz) =
            eval_lit asg1 cout).
  { unfold Integers.add_carry; rewrite @Integers.unsigned_zero, Z.add_0_r.
    destruct (eval_lit asg1 cout),
             (Numeric.Rocqlib.zlt (@Integers.unsigned sz va + @Integers.unsigned sz vb)
                                  (@Integers.modulus sz));
      rewrite ?eq_zero_one, ?eq_one_one;
      cbn [b2z negb] in *; try reflexivity; nia. }
  set (nuw_lit := if nuw then cout else lit_false) in *.
  assert (Hwf_nuw : wf_lit_bound (bs_next_var st1) nuw_lit)
    by (unfold nuw_lit; destruct nuw; [exact Hwf_c | exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs1)))))]).
  assert (Hev_nuw : eval_lit asg1 nuw_lit =
                    (nuw && @Integers.eq sz (@Integers.add_carry sz va vb (@Integers.zero sz))
                                            (@Integers.one sz))).
  { unfold nuw_lit; destruct nuw;
      [cbn [andb]; symmetry; exact Hcarry_eq
       | exact (sat_eval_lit_false asg1 st1 (proj2 (proj2 Hs1)))]. }
  assert (Hnsw_step :
            exists nsw_lit st4 asg4,
              (if nsw then
                 let sa := msb_lit a in
                 let sb := msb_lit b in
                 let ss := List.nth (Pos.to_nat sz - 1) sums lit_false in
                 let '(x_ab, st2) := emit_xor2_opt sa sb st1 in
                 let '(x_sa, st3) := emit_xor2_opt ss sa st2 in
                 emit_and2_opt (neg_lit x_ab) x_sa st3
               else (lit_false, st1)) = (nsw_lit, st4) /\
              step_spec st1 st4 asg1 asg4 /\
              wf_lit_bound (bs_next_var st4) nsw_lit /\
              eval_lit asg4 nsw_lit =
                (nsw && @Integers.eq sz (@Integers.add_overflow sz va vb (@Integers.zero sz))
                                        (@Integers.one sz))).
  { destruct nsw;
      [| exists lit_false, st1, asg1;
         split; [reflexivity |
         split; [exact (step_spec_refl st1 asg1 (proj2 (proj2 Hs1))) |
         split; [exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs1))))) |
                 exact (sat_eval_lit_false asg1 st1 (proj2 (proj2 Hs1)))]]]].
    cbn zeta; set (sa := msb_lit a); set (sb := msb_lit b);
      set (ss := List.nth (Pos.to_nat sz - 1) sums lit_false).
    assert (Hw_sa : wf_lit_bound (bs_next_var st) sa)
      by exact (wf_msb_lit sz _ a (proj1 (proj1 Hsat)) (conj (conj Hwa Hla) (conj Hba Hpa))).
    assert (Hw_sb : wf_lit_bound (bs_next_var st) sb)
      by exact (wf_msb_lit sz _ b (proj1 (proj1 Hsat)) (conj (conj Hwb Hlb) (conj Hbb Hpb))).
    assert (Hw_ss : wf_lit_bound (bs_next_var st1) ss)
      by exact (wf_lits_bound_nth _ _ sums lit_false Hwf_s
                  (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs1)))))).
    destruct (emit_xor2_opt sa sb st1) as [x_ab st2] eqn:Ex1.
    destruct (emit_xor2_opt ss sa st2) as [x_sa st3] eqn:Ex2.
    destruct (emit_and2_opt (neg_lit x_ab) x_sa st3) as [nsw_l st4] eqn:Ex3.
    destruct (emit_xor2_opt_step asg1 sa sb st1 x_ab st2 (proj2 (proj2 Hs1))
                (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hw_sa)
                (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hw_sb) Ex1)
      as (asg2 & Hs2 & Hw_xab & Hev_xab).
    pose proof (step_spec_trans st st1 st2 asg asg1 asg2 Hs1 Hs2) as Hs02.
    destruct (emit_xor2_opt_step asg2 ss sa st2 x_sa st3 (proj2 (proj2 Hs2))
                (wf_lit_bound_mono _ _ _ (proj1 Hs2) Hw_ss)
                (wf_lit_bound_mono _ _ _ (proj1 Hs02) Hw_sa) Ex2)
      as (asg3 & Hs3 & Hw_xsa & Hev_xsa).
    pose proof (step_spec_trans st2 st3 st3 asg2 asg3 asg3 Hs3 (step_spec_refl _ _ (proj2 (proj2 Hs3)))) as _.
    destruct (emit_and2_opt_step asg3 (neg_lit x_ab) x_sa st3 nsw_l st4 (proj2 (proj2 Hs3))
                (wf_lit_bound_neg _ _ (wf_lit_bound_mono _ _ _ (proj1 Hs3) Hw_xab))
                Hw_xsa Ex3)
      as (asg4 & Hs4 & Hw_nl & Hev_nl).
    pose proof (step_spec_trans st1 st2 st3 asg1 asg2 asg3 Hs2 Hs3) as Hs13.
    pose proof (step_spec_trans st1 st3 st4 asg1 asg3 asg4 Hs13 Hs4) as Hs14.
    exists nsw_l, st4, asg4; split; [reflexivity | split; [exact Hs14 | split; [exact Hw_nl |]]].
    cbn [andb]; rewrite Hev_nl,
      (eval_neg_lit_nonzero asg3 x_ab (wf_lit_bound_nonzero _ _ Hw_xab)),
      (step_spec_eval_lit st2 st3 asg2 asg3 x_ab Hs3 Hw_xab),
      Hev_xab, Hev_xsa,
      (step_spec_eval_lit st st1 asg asg1 sa Hs1 Hw_sa),
      (step_spec_eval_lit st st1 asg asg1 sb Hs1 Hw_sb),
      (step_spec_eval_lit st st2 asg asg2 sa Hs02 Hw_sa),
      (step_spec_eval_lit st1 st2 asg1 asg2 ss Hs2 Hw_ss).
    unfold sa, sb; rewrite (eval_msb_lit sz asg a (conj Hwa Hla)),
                           (eval_msb_lit sz asg b (conj Hwb Hlb)); fold va vb.
    assert (Hev_ss : eval_lit asg1 ss = msb_of sz (@Integers.repr sz us)).
    { exact (eval_msb_lit sz asg1 (mk_rail_bv sz sums lit_false)
               (conj eq_refl (eq_trans Hlen_s Hla))). }
    rewrite Hev_ss.
    unfold Integers.add_overflow; cbn zeta;
      rewrite @Integers.signed_zero, !Z.add_0_r, eq_zero_else_one_cond.
    unfold Integers.min_signed, Integers.max_signed.
    pose proof (msb_of_unsigned_bounds sz va) as Hba_u.
    pose proof (msb_of_unsigned_bounds sz vb) as Hbb_u.
    pose proof (msb_of_unsigned_bounds sz (@Integers.repr sz us)) as Hbs_u.
    rewrite Hus_repr in Hbs_u.
    rewrite (signed_eq_unsigned_msb sz va), (signed_eq_unsigned_msb sz vb).
    pose proof (@Integers.half_modulus_modulus sz) as Hhm.
    pose proof (@Integers.half_modulus_pos sz) as Hhp.
    destruct (msb_of sz va), (msb_of sz vb), (msb_of sz (@Integers.repr sz us)), (eval_lit asg1 cout);
      cbn [b2z xorb negb andb] in *;
      destruct (Numeric.Rocqlib.zle (- @Integers.half_modulus sz) _),
               (Numeric.Rocqlib.zle _ (@Integers.half_modulus sz - 1));
      cbn [Numeric.Rocqlib.proj_sumbool andb negb]; try reflexivity; nia. }
  destruct Hnsw_step as (nsw_l & st4 & asg4 & Hnsw_eq & Hs14 & Hwf_nsw & Hev_nsw).
  cbn iota zeta in Hnsw_eq, Hbl; rewrite Hnsw_eq in Hbl; cbn iota zeta in Hbl; clear Hnsw_eq.
  destruct (emit_or2_opt (rbv_psn a) (rbv_psn b) st4) as [base_psn st5] eqn:Ebp.
  destruct (emit_or2_opt nuw_lit nsw_l st5) as [ov_psn st6] eqn:Eov.
  destruct (emit_or2_opt base_psn ov_psn st6) as [psn st7] eqn:Ep.
  inversion Hbl; subst out st7; clear Hbl.
  pose proof (step_spec_trans st st1 st4 asg asg1 asg4 Hs1 Hs14) as Hs04.
  destruct (emit_or2_opt_step asg4 (rbv_psn a) (rbv_psn b) st4 base_psn st5 (proj2 (proj2 Hs14))
              (wf_lit_bound_mono _ _ _ (proj1 Hs04) Hpa)
              (wf_lit_bound_mono _ _ _ (proj1 Hs04) Hpb) Ebp)
    as (asg5 & Hs45 & Hwf_bp & Hev_bp).
  pose proof (step_spec_trans st1 st4 st5 asg1 asg4 asg5 Hs14 Hs45) as Hs15.
  destruct (emit_or2_opt_step asg5 nuw_lit nsw_l st5 ov_psn st6 (proj2 (proj2 Hs45))
              (wf_lit_bound_mono _ _ _ (proj1 Hs15) Hwf_nuw)
              (wf_lit_bound_mono _ _ _ (proj1 Hs45) Hwf_nsw) Eov)
    as (asg6 & Hs56 & Hwf_ov & Hev_ov).
  pose proof (step_spec_trans st4 st5 st6 asg4 asg5 asg6 Hs45 Hs56) as Hs46.
  destruct (emit_or2_opt_step asg6 base_psn ov_psn st6 psn st' (proj2 (proj2 Hs56))
              (wf_lit_bound_mono _ _ _ (proj1 Hs56) Hwf_bp) Hwf_ov Ep)
    as (asg7 & Hs67 & Hwf_p & Hev_p).
  pose proof (step_spec_trans st1 st5 st6 asg1 asg5 asg6 Hs15 Hs56) as Hs16.
  pose proof (step_spec_trans st1 st6 st' asg1 asg6 asg7 Hs16 Hs67) as Hs17.
  pose proof (step_spec_trans st st1 st' asg asg1 asg7 Hs1 Hs17) as Hs07.
  exists asg7; split; [exact Hs07 | split].
  - split; [split; [reflexivity | cbn; congruence] |
            split; [exact (wf_lits_bound_mono _ _ sums (proj1 Hs17) Hwf_s) | exact Hwf_p]].
  - split.
    + unfold eval_rail_psn; cbn [rbv_psn]; rewrite Hev_p,
        (step_spec_eval_lit st5 st6 asg5 asg6 base_psn Hs56 Hwf_bp),
        Hev_bp,
        (step_spec_eval_lit st st4 asg asg4 (rbv_psn a) Hs04 Hpa),
        (step_spec_eval_lit st st4 asg asg4 (rbv_psn b) Hs04 Hpb),
        Hev_ov,
        (step_spec_eval_lit st1 st5 asg1 asg5 nuw_lit Hs15 Hwf_nuw),
        Hev_nuw,
        (step_spec_eval_lit st4 st5 asg4 asg5 nsw_l Hs45 Hwf_nsw),
        Hev_nsw; reflexivity.
    + unfold eval_rail_val; cbn [rbv_bits];
        rewrite (step_spec_eval_lits st1 st' asg1 asg7 sums Hs17 Hwf_s); exact Hval_eq.
Qed.

Definition blast_sub_rail (nuw nsw : bool) (sz : positive) (a b : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let not_b := List.map neg_lit (rbv_bits b) in
  let '((diffs, cout), st1) := emit_ripple_add lit_true (rbv_bits a) not_b st in
  let nuw_lit := if nuw then neg_lit cout else lit_false in
  let '(nsw_lit, st4) :=
      if nsw then
        let sa := msb_lit a in
        let sb := msb_lit b in
        let sd := List.nth (Pos.to_nat sz - 1) diffs lit_false in
        let '(x_ab, st2) := emit_xor2_opt sa sb st1 in
        let '(x_da, st3) := emit_xor2_opt sd sa st2 in
        emit_and2_opt x_ab x_da st3
      else (lit_false, st1) in
  let '(base_psn, st5) := emit_or2_opt (rbv_psn a) (rbv_psn b) st4 in
  let '(ov_psn, st6)   := emit_or2_opt nuw_lit nsw_lit st5 in
  let '(psn, st7)      := emit_or2_opt base_psn ov_psn st6 in
  (mk_rail_bv sz diffs psn, st7).

Theorem blast_sub_rail_step : forall nuw nsw sz a b asg st out st',
  sat_blast_st asg st ->
  wf_rail_bound sz (bs_next_var st) a ->
  wf_rail_bound sz (bs_next_var st) b ->
  blast_sub_rail nuw nsw sz a b st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_rail_bound sz (bs_next_var st') out /\
    eval_rail_psn asg' out =
      ((eval_rail_psn asg a || eval_rail_psn asg b) ||
       ((nuw && @Integers.eq sz
                  (@Integers.sub_borrow sz (eval_rail_val sz asg a)
                                           (eval_rail_val sz asg b)
                                           (@Integers.zero sz))
                  (@Integers.one sz)) ||
        (nsw && @Integers.eq sz
                  (@Integers.sub_overflow sz (eval_rail_val sz asg a)
                                              (eval_rail_val sz asg b)
                                              (@Integers.zero sz))
                  (@Integers.one sz)))) /\
    eval_rail_val sz asg' out =
      @Integers.sub sz (eval_rail_val sz asg a) (eval_rail_val sz asg b).
Proof.
  intros nuw nsw sz a b asg st out st' Hsat
         ([Hwa Hla] & Hba & Hpa) ([Hwb Hlb] & Hbb & Hpb) Hbl.
  unfold blast_sub_rail in Hbl; cbn zeta in Hbl.
  set (not_b := List.map neg_lit (rbv_bits b)) in *.
  destruct (emit_ripple_add lit_true (rbv_bits a) not_b st)
    as [[diffs cout] st1] eqn:Hrip; cbn iota zeta in Hbl.
  assert (Hlen_anb : List.length (rbv_bits a) = List.length not_b)
    by (unfold not_b; rewrite length_map; congruence).
  destruct (emit_ripple_add_step (rbv_bits a) not_b lit_true asg st diffs cout st1
              Hlen_anb (wf_lit_bound_true _ (proj1 (proj1 Hsat)))
              Hba (wf_lits_bound_neg _ _ Hbb) Hsat Hrip)
    as (asg1 & Hs1 & Hlen_d & Hwf_d & Hwf_c & Heq_diff).
  rewrite (sat_eval_lit_true asg _ Hsat) in Heq_diff; cbn [b2z] in Heq_diff.
  unfold not_b in Heq_diff;
    rewrite (map_eval_neg_lits _ asg (rbv_bits b) Hbb) in Heq_diff.
  pose proof (bools_to_Z_negb (List.map (eval_lit asg) (rbv_bits b))) as Hnb.
  rewrite length_map, Hlb, positive_nat_Z, <- modulus_pow_sz in Hnb.
  set (va := eval_rail_val sz asg a).
  set (vb := eval_rail_val sz asg b).
  assert (Hua : bools_to_Z (List.map (eval_lit asg) (rbv_bits a)) = @Integers.unsigned sz va)
    by (symmetry; exact (unsigned_eval_rail_val sz asg a Hla)).
  assert (Hub : bools_to_Z (List.map (eval_lit asg) (rbv_bits b)) = @Integers.unsigned sz vb)
    by (symmetry; exact (unsigned_eval_rail_val sz asg b Hlb)).
  rewrite Hla, positive_nat_Z, <- modulus_pow_sz, Hua in Heq_diff; rewrite Hub in Hnb.
  set (ud := bools_to_Z (List.map (eval_lit asg1) diffs)) in *.
  assert (Hud_eq : (@Integers.unsigned sz va - @Integers.unsigned sz vb =
                    ud + @Integers.modulus sz * (b2z (eval_lit asg1 cout) - 1))%Z) by nia.
  assert (Hud_rng : (0 <= ud < @Integers.modulus sz)%Z).
  { unfold ud; pose proof (bools_to_Z_range (List.map (eval_lit asg1) diffs)) as Hr.
    rewrite length_map, Hlen_d, Hla, positive_nat_Z, <- modulus_pow_sz in Hr; exact Hr. }
  assert (Hud_repr : @Integers.unsigned sz (@Integers.repr sz ud) = ud)
    by (apply @Integers.unsigned_repr; unfold Integers.max_unsigned; lia).
  assert (Hval_eq : @Integers.repr sz ud = @Integers.sub sz va vb).
  { unfold Integers.sub; apply @Integers.eqm_samerepr.
    exists (1 - b2z (eval_lit asg1 cout))%Z; nia. }
  assert (Hborrow_eq :
            @Integers.eq sz (@Integers.sub_borrow sz va vb (@Integers.zero sz)) (@Integers.one sz) =
            negb (eval_lit asg1 cout)).
  { unfold Integers.sub_borrow; rewrite @Integers.unsigned_zero, Z.sub_0_r.
    destruct (eval_lit asg1 cout),
             (Numeric.Rocqlib.zlt (@Integers.unsigned sz va - @Integers.unsigned sz vb) 0%Z);
      rewrite ?eq_zero_one, ?eq_one_one;
      cbn [b2z negb] in *; try reflexivity; nia. }
  set (nuw_lit := if nuw then neg_lit cout else lit_false) in *.
  assert (Hwf_nuw : wf_lit_bound (bs_next_var st1) nuw_lit)
    by (unfold nuw_lit; destruct nuw;
        [exact (wf_lit_bound_neg _ _ Hwf_c)
         | exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs1)))))]).
  assert (Hev_nuw : eval_lit asg1 nuw_lit =
                    (nuw && @Integers.eq sz (@Integers.sub_borrow sz va vb (@Integers.zero sz))
                                            (@Integers.one sz))).
  { unfold nuw_lit; destruct nuw;
      [cbn [andb]; rewrite (eval_neg_lit_nonzero asg1 cout (wf_lit_bound_nonzero _ _ Hwf_c));
       symmetry; exact Hborrow_eq
       | exact (sat_eval_lit_false asg1 st1 (proj2 (proj2 Hs1)))]. }
  assert (Hnsw_step :
            exists nsw_lit st4 asg4,
              (if nsw then
                 let sa := msb_lit a in
                 let sb := msb_lit b in
                 let sd := List.nth (Pos.to_nat sz - 1) diffs lit_false in
                 let '(x_ab, st2) := emit_xor2_opt sa sb st1 in
                 let '(x_da, st3) := emit_xor2_opt sd sa st2 in
                 emit_and2_opt x_ab x_da st3
               else (lit_false, st1)) = (nsw_lit, st4) /\
              step_spec st1 st4 asg1 asg4 /\
              wf_lit_bound (bs_next_var st4) nsw_lit /\
              eval_lit asg4 nsw_lit =
                (nsw && @Integers.eq sz (@Integers.sub_overflow sz va vb (@Integers.zero sz))
                                        (@Integers.one sz))).
  { destruct nsw;
      [| exists lit_false, st1, asg1;
         split; [reflexivity |
         split; [exact (step_spec_refl st1 asg1 (proj2 (proj2 Hs1))) |
         split; [exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs1))))) |
                 exact (sat_eval_lit_false asg1 st1 (proj2 (proj2 Hs1)))]]]].
    cbn zeta; set (sa := msb_lit a); set (sb := msb_lit b);
      set (sd := List.nth (Pos.to_nat sz - 1) diffs lit_false).
    assert (Hw_sa : wf_lit_bound (bs_next_var st) sa)
      by exact (wf_msb_lit sz _ a (proj1 (proj1 Hsat)) (conj (conj Hwa Hla) (conj Hba Hpa))).
    assert (Hw_sb : wf_lit_bound (bs_next_var st) sb)
      by exact (wf_msb_lit sz _ b (proj1 (proj1 Hsat)) (conj (conj Hwb Hlb) (conj Hbb Hpb))).
    assert (Hw_sd : wf_lit_bound (bs_next_var st1) sd)
      by exact (wf_lits_bound_nth _ _ diffs lit_false Hwf_d
                  (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs1)))))).
    destruct (emit_xor2_opt sa sb st1) as [x_ab st2] eqn:Ex1.
    destruct (emit_xor2_opt sd sa st2) as [x_da st3] eqn:Ex2.
    destruct (emit_and2_opt x_ab x_da st3) as [nsw_l st4] eqn:Ex3.
    destruct (emit_xor2_opt_step asg1 sa sb st1 x_ab st2 (proj2 (proj2 Hs1))
                (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hw_sa)
                (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hw_sb) Ex1)
      as (asg2 & Hs2 & Hw_xab & Hev_xab).
    pose proof (step_spec_trans st st1 st2 asg asg1 asg2 Hs1 Hs2) as Hs02.
    destruct (emit_xor2_opt_step asg2 sd sa st2 x_da st3 (proj2 (proj2 Hs2))
                (wf_lit_bound_mono _ _ _ (proj1 Hs2) Hw_sd)
                (wf_lit_bound_mono _ _ _ (proj1 Hs02) Hw_sa) Ex2)
      as (asg3 & Hs3 & Hw_xda & Hev_xda).
    destruct (emit_and2_opt_step asg3 x_ab x_da st3 nsw_l st4 (proj2 (proj2 Hs3))
                (wf_lit_bound_mono _ _ _ (proj1 Hs3) Hw_xab)
                Hw_xda Ex3)
      as (asg4 & Hs4 & Hw_nl & Hev_nl).
    pose proof (step_spec_trans st1 st2 st3 asg1 asg2 asg3 Hs2 Hs3) as Hs13.
    pose proof (step_spec_trans st1 st3 st4 asg1 asg3 asg4 Hs13 Hs4) as Hs14.
    exists nsw_l, st4, asg4; split; [reflexivity | split; [exact Hs14 | split; [exact Hw_nl |]]].
    cbn [andb]; rewrite Hev_nl,
      (step_spec_eval_lit st2 st3 asg2 asg3 x_ab Hs3 Hw_xab),
      Hev_xab, Hev_xda,
      (step_spec_eval_lit st st1 asg asg1 sa Hs1 Hw_sa),
      (step_spec_eval_lit st st1 asg asg1 sb Hs1 Hw_sb),
      (step_spec_eval_lit st st2 asg asg2 sa Hs02 Hw_sa),
      (step_spec_eval_lit st1 st2 asg1 asg2 sd Hs2 Hw_sd).
    unfold sa, sb; rewrite (eval_msb_lit sz asg a (conj Hwa Hla)),
                           (eval_msb_lit sz asg b (conj Hwb Hlb)); fold va vb.
    assert (Hev_sd : eval_lit asg1 sd = msb_of sz (@Integers.repr sz ud)).
    { exact (eval_msb_lit sz asg1 (mk_rail_bv sz diffs lit_false)
               (conj eq_refl (eq_trans Hlen_d Hla))). }
    rewrite Hev_sd.
    unfold Integers.sub_overflow; cbn zeta;
      rewrite @Integers.signed_zero, !Z.sub_0_r, eq_zero_else_one_cond.
    unfold Integers.min_signed, Integers.max_signed.
    pose proof (msb_of_unsigned_bounds sz va) as Hba_u.
    pose proof (msb_of_unsigned_bounds sz vb) as Hbb_u.
    pose proof (msb_of_unsigned_bounds sz (@Integers.repr sz ud)) as Hbd_u.
    rewrite Hud_repr in Hbd_u.
    rewrite (signed_eq_unsigned_msb sz va), (signed_eq_unsigned_msb sz vb).
    pose proof (@Integers.half_modulus_modulus sz) as Hhm.
    pose proof (@Integers.half_modulus_pos sz) as Hhp.
    destruct (msb_of sz va), (msb_of sz vb), (msb_of sz (@Integers.repr sz ud)), (eval_lit asg1 cout);
      cbn [b2z xorb negb andb] in *;
      destruct (Numeric.Rocqlib.zle (- @Integers.half_modulus sz) _),
               (Numeric.Rocqlib.zle _ (@Integers.half_modulus sz - 1));
      cbn [Numeric.Rocqlib.proj_sumbool andb negb]; try reflexivity; nia. }
  destruct Hnsw_step as (nsw_l & st4 & asg4 & Hnsw_eq & Hs14 & Hwf_nsw & Hev_nsw).
  cbn iota zeta in Hnsw_eq, Hbl; rewrite Hnsw_eq in Hbl; cbn iota zeta in Hbl; clear Hnsw_eq.
  destruct (emit_or2_opt (rbv_psn a) (rbv_psn b) st4) as [base_psn st5] eqn:Ebp.
  destruct (emit_or2_opt nuw_lit nsw_l st5) as [ov_psn st6] eqn:Eov.
  destruct (emit_or2_opt base_psn ov_psn st6) as [psn st7] eqn:Ep.
  inversion Hbl; subst out st7; clear Hbl.
  pose proof (step_spec_trans st st1 st4 asg asg1 asg4 Hs1 Hs14) as Hs04.
  destruct (emit_or2_opt_step asg4 (rbv_psn a) (rbv_psn b) st4 base_psn st5 (proj2 (proj2 Hs14))
              (wf_lit_bound_mono _ _ _ (proj1 Hs04) Hpa)
              (wf_lit_bound_mono _ _ _ (proj1 Hs04) Hpb) Ebp)
    as (asg5 & Hs45 & Hwf_bp & Hev_bp).
  pose proof (step_spec_trans st1 st4 st5 asg1 asg4 asg5 Hs14 Hs45) as Hs15.
  destruct (emit_or2_opt_step asg5 nuw_lit nsw_l st5 ov_psn st6 (proj2 (proj2 Hs45))
              (wf_lit_bound_mono _ _ _ (proj1 Hs15) Hwf_nuw)
              (wf_lit_bound_mono _ _ _ (proj1 Hs45) Hwf_nsw) Eov)
    as (asg6 & Hs56 & Hwf_ov & Hev_ov).
  destruct (emit_or2_opt_step asg6 base_psn ov_psn st6 psn st' (proj2 (proj2 Hs56))
              (wf_lit_bound_mono _ _ _ (proj1 Hs56) Hwf_bp) Hwf_ov Ep)
    as (asg7 & Hs67 & Hwf_p & Hev_p).
  pose proof (step_spec_trans st1 st5 st6 asg1 asg5 asg6 Hs15 Hs56) as Hs16.
  pose proof (step_spec_trans st1 st6 st' asg1 asg6 asg7 Hs16 Hs67) as Hs17.
  pose proof (step_spec_trans st st1 st' asg asg1 asg7 Hs1 Hs17) as Hs07.
  exists asg7; split; [exact Hs07 | split].
  - split; [split; [reflexivity | cbn; congruence] |
            split; [exact (wf_lits_bound_mono _ _ diffs (proj1 Hs17) Hwf_d) | exact Hwf_p]].
  - split.
    + unfold eval_rail_psn; cbn [rbv_psn]; rewrite Hev_p,
        (step_spec_eval_lit st5 st6 asg5 asg6 base_psn Hs56 Hwf_bp),
        Hev_bp,
        (step_spec_eval_lit st st4 asg asg4 (rbv_psn a) Hs04 Hpa),
        (step_spec_eval_lit st st4 asg asg4 (rbv_psn b) Hs04 Hpb),
        Hev_ov,
        (step_spec_eval_lit st1 st5 asg1 asg5 nuw_lit Hs15 Hwf_nuw),
        Hev_nuw,
        (step_spec_eval_lit st4 st5 asg4 asg5 nsw_l Hs45 Hwf_nsw),
        Hev_nsw; reflexivity.
    + unfold eval_rail_val; cbn [rbv_bits];
        rewrite (step_spec_eval_lits st1 st' asg1 asg7 diffs Hs17 Hwf_d); exact Hval_eq.
Qed.

Fixpoint emit_xor_const_lits (s : lit) (hs : list lit) (st : blast_state)
  {struct hs} : list lit * blast_state :=
  match hs with
  | [] => ([], st)
  | h :: rest =>
      let '(xh, st1) := emit_xor2_opt s h st in
      let '(xrest, st2) := emit_xor_const_lits s rest st1 in
      (xh :: xrest, st2)
  end.

Lemma emit_xor_const_lits_step : forall s hs asg st xhs st',
  wf_lit_bound (bs_next_var st) s ->
  wf_lits_bound (bs_next_var st) hs ->
  sat_blast_st asg st ->
  emit_xor_const_lits s hs st = (xhs, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_lits_bound (bs_next_var st') xhs /\
    List.map (eval_lit asg') xhs =
    List.map (xorb (eval_lit asg s)) (List.map (eval_lit asg) hs).
Proof.
  intros s hs; induction hs as [| h rest IH]; intros asg st xhs st' Hws Hwh Hsat He; cbn [emit_xor_const_lits] in He.
  - inversion He; subst; exists asg; split;
      [exact (step_spec_refl _ asg Hsat) | split; [constructor | reflexivity]].
  - inversion Hwh as [| ? ? Hh Hwrest]; subst.
    destruct (emit_xor2_opt s h st) as [xh st1] eqn:Ex1.
    destruct (emit_xor_const_lits s rest st1) as [xrest st2] eqn:Ex2.
    inversion He; subst xhs st2; clear He.
    destruct (emit_xor2_opt_step asg s h st xh st1 Hsat Hws Hh Ex1)
      as (asg1 & Hs1 & Hw_xh & Hev_xh).
    destruct (IH asg1 st1 xrest st'
                (wf_lit_bound_mono _ _ s (proj1 Hs1) Hws)
                (wf_lits_bound_mono _ _ rest (proj1 Hs1) Hwrest)
                (proj2 (proj2 Hs1)) Ex2)
      as (asg2 & Hs2 & Hw_xr & Hev_xr).
    exists asg2; split; [exact (step_spec_trans st st1 st' asg asg1 asg2 Hs1 Hs2) | split].
    + constructor; [exact (wf_lit_bound_mono _ _ xh (proj1 Hs2) Hw_xh) | exact Hw_xr].
    + cbn; rewrite (step_spec_eval_lit st1 st' asg1 asg2 xh Hs2 Hw_xh), Hev_xh, Hev_xr,
                   (step_spec_eval_lit st st1 asg asg1 s Hs1 Hws),
                   (step_spec_eval_lits st st1 asg asg1 rest Hs1 Hwrest); reflexivity.
Qed.

Fixpoint emit_eq_const_bits (k_val : Z) (bs : list lit) (st : blast_state)
  {struct bs} : lit * blast_state :=
  match bs with
  | [] => (lit_true, st)
  | b :: rest =>
      let want := if Z.odd k_val then b else neg_lit b in
      let '(rest_eq, st1) := emit_eq_const_bits (Z.div2 k_val) rest st in
      emit_and2_opt want rest_eq st1
  end.

Fixpoint eq_Z_bools (k_val : Z) (bs : list bool) {struct bs} : bool :=
  match bs with
  | [] => true
  | b :: rest => Bool.eqb b (Z.odd k_val) && eq_Z_bools (Z.div2 k_val) rest
  end.

Lemma eq_Z_bools_spec : forall bs k_val,
  (0 <= k_val < 2 ^ Z.of_nat (List.length bs))%Z ->
  eq_Z_bools k_val bs = (bools_to_Z bs =? k_val)%Z.
Proof.
  induction bs as [| b rest IH]; intros k_val Hk; cbn [eq_Z_bools List.length] in *.
  - assert (k_val = 0)%Z by (cbn in Hk; lia); subst k_val; reflexivity.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hk by lia.
    pose proof (Integers.Zdecomp k_val) as Hdec.
    rewrite Integers.Zshiftin_spec in Hdec.
    assert (Hk2 : (0 <= Z.div2 k_val < 2 ^ Z.of_nat (List.length rest))%Z)
      by (destruct (Z.odd k_val); lia).
    rewrite (IH (Z.div2 k_val) Hk2), bools_to_Z_cons.
    destruct b, (Z.odd k_val); cbn [Bool.eqb b2z andb];
      destruct (Z.eqb_spec (bools_to_Z rest) (Z.div2 k_val));
      match goal with |- context [(?u =? k_val)%Z] => destruct (Z.eqb_spec u k_val) end;
      try reflexivity; lia.
Qed.

Lemma emit_eq_const_bits_step : forall bs k_val asg st out st',
  wf_lits_bound (bs_next_var st) bs ->
  sat_blast_st asg st ->
  emit_eq_const_bits k_val bs st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_lit_bound (bs_next_var st') out /\
    eval_lit asg' out = eq_Z_bools k_val (List.map (eval_lit asg) bs).
Proof.
  induction bs as [| b rest IH]; intros k_val asg st out st' Hwf Hsat He; cbn [emit_eq_const_bits] in He.
  - inversion He; subst; exists asg; split;
      [exact (step_spec_refl _ asg Hsat) | split;
       [exact (wf_lit_bound_true _ (proj1 (proj1 Hsat))) | exact (sat_eval_lit_true asg _ Hsat)]].
  - inversion Hwf as [| ? ? Hb Hwrest]; subst.
    set (want := if Z.odd k_val then b else neg_lit b) in *.
    assert (Hww : wf_lit_bound (bs_next_var st) want)
      by (unfold want; destruct (Z.odd k_val); [exact Hb | exact (wf_lit_bound_neg _ b Hb)]).
    destruct (emit_eq_const_bits (Z.div2 k_val) rest st) as [rest_eq st1] eqn:Er.
    destruct (IH (Z.div2 k_val) asg st rest_eq st1 Hwrest Hsat Er)
      as (asg1 & Hs1 & Hw_re & Hev_re).
    destruct (emit_and2_opt_step asg1 want rest_eq st1 out st' (proj2 (proj2 Hs1))
                (wf_lit_bound_mono _ _ want (proj1 Hs1) Hww) Hw_re He)
      as (asg2 & Hs2 & Hw_out & Hev_out).
    exists asg2; split; [exact (step_spec_trans st st1 st' asg asg1 asg2 Hs1 Hs2) | split; [exact Hw_out |]].
    cbn [List.map eq_Z_bools]; rewrite Hev_out, Hev_re,
      (step_spec_eval_lit st st1 asg asg1 want Hs1 Hww).
    f_equal; unfold want.
    destruct (Z.odd k_val).
    + destruct (eval_lit asg b); reflexivity.
    + rewrite (eval_neg_lit_nonzero asg b (wf_lit_bound_nonzero _ b Hb));
        destruct (eval_lit asg b); reflexivity.
Qed.

Fixpoint mux_shift_table
  (sz : positive)
  (fn_k : nat -> blast_state -> (list lit * lit) * blast_state)
  (b_bits : list lit)
  (rem_k : nat)
  (st : blast_state) {struct rem_k} : (list lit * lit) * blast_state :=
  match rem_k with
  | O => ((List.repeat lit_false (Pos.to_nat sz), lit_true), st)
  | S r' =>
      let k := (Pos.to_nat sz - S r')%nat in
      let '((bits_k, psn_k), st1) := fn_k k st in
      let '(eq_k, st2) := emit_eq_const_bits (Z.of_nat k) b_bits st1 in
      let '((rest_bits, rest_psn), st3) := mux_shift_table sz fn_k b_bits r' st2 in
      let '(out_bits, st4) := mux_bits_list_opt eq_k bits_k rest_bits st3 in
      let '(out_psn, st5)  := emit_mux2_opt eq_k psn_k rest_psn st4 in
      ((out_bits, out_psn), st5)
  end.

Lemma len_firstn_le : forall {A : Type} n (ls : list A),
  (n <= List.length ls)%nat -> List.length (List.firstn n ls) = n.
Proof.
  intros A n; induction n as [| n' IH]; intros [| x r] Hle; cbn in *;
    [reflexivity | reflexivity | lia | f_equal; apply IH; lia].
Qed.

Lemma len_skipn_eq : forall {A : Type} n (ls : list A),
  List.length (List.skipn n ls) = (List.length ls - n)%nat.
Proof.
  intros A n; induction n as [| n' IH]; intros [| x r]; cbn;
    [reflexivity | lia | reflexivity | apply IH].
Qed.

Lemma nth_app_l : forall {A : Type} (d : A) k (l1 l2 : list A),
  (k < List.length l1)%nat -> List.nth k (l1 ++ l2) d = List.nth k l1 d.
Proof.
  intros A d k l1; revert k; induction l1 as [| x r IH]; intros [| k'] l2 Hlt; cbn in *;
    [lia | lia | reflexivity | apply IH; lia].
Qed.

Lemma nth_app_r : forall {A : Type} (d : A) k (l1 l2 : list A),
  (List.length l1 <= k)%nat ->
  List.nth k (l1 ++ l2) d = List.nth (k - List.length l1) l2 d.
Proof.
  intros A d k l1; revert k; induction l1 as [| x r IH]; intros [| k'] l2 Hle; cbn in *;
    [reflexivity | reflexivity | lia | apply IH; lia].
Qed.

Lemma firstn_skipn_eq : forall {A : Type} n (ls : list A),
  List.firstn n ls ++ List.skipn n ls = ls.
Proof.
  intros A n; induction n as [| n' IH]; intros [| x r]; cbn;
    [reflexivity | reflexivity | reflexivity | f_equal; apply IH].
Qed.

Lemma mux_shift_table_step :
  forall (sz : positive)
         (fn_k : nat -> blast_state -> (list lit * lit) * blast_state)
         (spec_bits : nat -> list bool)
         (spec_psn : nat -> bool)
         (b_bits : list lit)
         (Hlen_b : List.length b_bits = Pos.to_nat sz)
         (rem_k : nat) (asg : positive -> bool) (st : blast_state)
         (out_bits : list lit) (out_psn : lit) (st' : blast_state),
    (rem_k <= Pos.to_nat sz)%nat ->
    wf_lits_bound (bs_next_var st) b_bits ->
    sat_blast_st asg st ->
    (forall k asg0 st0 bk pk st1,
       (k < Pos.to_nat sz)%nat ->
       step_spec st st0 asg asg0 ->
       fn_k k st0 = ((bk, pk), st1) ->
       exists asg1,
         step_spec st0 st1 asg0 asg1 /\
         List.length bk = Pos.to_nat sz /\
         wf_lits_bound (bs_next_var st1) bk /\
         wf_lit_bound (bs_next_var st1) pk /\
         List.map (eval_lit asg1) bk = spec_bits k /\
         eval_lit asg1 pk = spec_psn k) ->
    mux_shift_table sz fn_k b_bits rem_k st = ((out_bits, out_psn), st') ->
    exists asg',
      step_spec st st' asg asg' /\
      List.length out_bits = Pos.to_nat sz /\
      wf_lits_bound (bs_next_var st') out_bits /\
      wf_lit_bound (bs_next_var st') out_psn /\
      (let ub := bools_to_Z (List.map (eval_lit asg) b_bits) in
       if (Z.of_nat (Pos.to_nat sz - rem_k) <=? ub)%Z && (ub <? Z.pos sz)%Z
       then List.map (eval_lit asg') out_bits = spec_bits (Z.to_nat ub) /\
            eval_lit asg' out_psn = spec_psn (Z.to_nat ub)
       else eval_lit asg' out_psn = true).
Proof.
  intros sz fn_k spec_bits spec_psn b_bits Hlen_b rem_k.
  induction rem_k as [| r' IH]; intros asg st out_bits out_psn st' Hle Hwfb Hsat Hfn Hmux;
    cbn [mux_shift_table] in Hmux.
  - inversion Hmux; subst; clear Hmux.
    pose proof (proj1 (proj1 Hsat)) as Hge2.
    exists asg; split; [exact (step_spec_refl _ asg Hsat) | split].
    + apply repeat_length.
    + split; [exact (wf_lits_bound_repeat _ _ _ (wf_lit_bound_false _ Hge2)) | split].
      * exact (wf_lit_bound_true _ Hge2).
      * cbn zeta; rewrite Nat.sub_0_r, positive_nat_Z.
        set (ub := bools_to_Z (List.map (eval_lit asg) b_bits)).
        destruct (Z.leb_spec (Z.pos sz) ub), (Z.ltb_spec ub (Z.pos sz));
          cbn [andb]; try lia; exact (sat_eval_lit_true asg _ Hsat).
  - set (k := (Pos.to_nat sz - S r')%nat) in *.
    assert (Hk : (k < Pos.to_nat sz)%nat) by lia.
    destruct (fn_k k st) as [[bits_k psn_k] st1] eqn:Ef; cbn iota zeta in Hmux.
    destruct (emit_eq_const_bits (Z.of_nat k) b_bits st1) as [eq_k st2] eqn:Eeq.
    destruct (mux_shift_table sz fn_k b_bits r' st2) as [[rest_bits rest_psn] st3] eqn:Er; cbn iota zeta in Hmux.
    destruct (mux_bits_list_opt eq_k bits_k rest_bits st3) as [ob st4] eqn:Em1.
    destruct (emit_mux2_opt eq_k psn_k rest_psn st4) as [op st5] eqn:Em2.
    inversion Hmux; subst out_bits out_psn st5; clear Hmux.
    destruct (Hfn k asg st bits_k psn_k st1 Hk (step_spec_refl _ asg Hsat) Ef)
      as (asg1 & Hs1 & Hlen_bk & Hwf_bk & Hwf_pk & Hev_bk & Hev_pk).
    destruct (emit_eq_const_bits_step b_bits (Z.of_nat k) asg1 st1 eq_k st2
                (wf_lits_bound_mono _ _ _ (proj1 Hs1) Hwfb)
                (proj2 (proj2 Hs1)) Eeq)
      as (asg2 & Hs2 & Hwf_eqk & Hev_eqk).
    pose proof (step_spec_trans st st1 st2 asg asg1 asg2 Hs1 Hs2) as Hs02.
    destruct (IH asg2 st2 rest_bits rest_psn st3 (ltac:(lia))
                (wf_lits_bound_mono _ _ _ (proj1 Hs02) Hwfb)
                (proj2 (proj2 Hs2))
                (fun k0 a0 s0 bk0 pk0 s1 Hk0 Hs20 =>
                   Hfn k0 a0 s0 bk0 pk0 s1 Hk0
                       (step_spec_trans st st2 s0 asg asg2 a0 Hs02 Hs20))
                Er)
      as (asg3 & Hs3 & Hlen_rb & Hwf_rb & Hwf_rp & Hspec_r).
    pose proof (step_spec_trans st1 st2 st3 asg1 asg2 asg3 Hs2 Hs3) as Hs13.
    destruct (mux_bits_list_opt_step bits_k rest_bits eq_k asg3 st3 ob st4
                (eq_trans Hlen_bk (eq_sym Hlen_rb))
                (wf_lit_bound_mono _ _ _ (proj1 Hs3) Hwf_eqk)
                (wf_lits_bound_mono _ _ _ (proj1 Hs13) Hwf_bk)
                Hwf_rb (proj2 (proj2 Hs3)) Em1)
      as (asg4 & Hs4 & Hlen_ob & Hwf_ob & Hev_ob).
    pose proof (step_spec_trans st2 st3 st4 asg2 asg3 asg4 Hs3 Hs4) as Hs24.
    pose proof (step_spec_trans st1 st3 st4 asg1 asg3 asg4 Hs13 Hs4) as Hs14.
    destruct (emit_mux2_opt_step asg4 eq_k psn_k rest_psn st4 op st' (proj2 (proj2 Hs4))
                (wf_lit_bound_mono _ _ _ (proj1 Hs24) Hwf_eqk)
                (wf_lit_bound_mono _ _ _ (proj1 Hs14) Hwf_pk)
                (wf_lit_bound_mono _ _ _ (proj1 Hs4) Hwf_rp) Em2)
      as (asg5 & Hs5 & Hwf_op & Hev_op).
    pose proof (step_spec_trans st3 st4 st' asg3 asg4 asg5 Hs4 Hs5) as Hs35.
    pose proof (step_spec_trans st st2 st3 asg asg2 asg3 Hs02 Hs3) as Hs03.
    pose proof (step_spec_trans st st3 st' asg asg3 asg5 Hs03 Hs35) as Hs05.
    exists asg5; split; [exact Hs05 | split; [congruence | split]].
    + exact (wf_lits_bound_mono _ _ _ (proj1 Hs5) Hwf_ob).
    + split; [exact Hwf_op |].
      cbn zeta in *.
      rewrite (step_spec_eval_lits st st2 asg asg2 b_bits Hs02 Hwfb) in Hspec_r.
      rewrite (step_spec_eval_lits st st1 asg asg1 b_bits Hs1 Hwfb) in Hev_eqk.
      assert (Hk_pow : (0 <= Z.of_nat k < 2 ^ Z.of_nat (List.length (List.map (eval_lit asg) b_bits)))%Z).
      { rewrite length_map, Hlen_b; pose proof (nat_lt_pow2 (Pos.to_nat sz)); lia. }
      rewrite (eq_Z_bools_spec _ _ Hk_pow) in Hev_eqk.
      rewrite (step_spec_eval_lits st4 st' asg4 asg5 ob Hs5 Hwf_ob),
              Hev_ob, Hev_op,
              (step_spec_eval_lit st2 st3 asg2 asg3 eq_k Hs3 Hwf_eqk),
              (step_spec_eval_lit st2 st4 asg2 asg4 eq_k Hs24 Hwf_eqk),
              Hev_eqk,
              (step_spec_eval_lits st1 st3 asg1 asg3 bits_k Hs13 Hwf_bk),
              Hev_bk,
              (step_spec_eval_lit st1 st4 asg1 asg4 psn_k Hs14 Hwf_pk),
              Hev_pk,
              (step_spec_eval_lit st3 st4 asg3 asg4 rest_psn Hs4 Hwf_rp).
      set (ub := bools_to_Z (List.map (eval_lit asg) b_bits)) in *.
      fold k.
      destruct (Z.eqb_spec ub (Z.of_nat k)) as [Heq_ub | Hneq_ub].
      * rewrite Heq_ub, Nat2Z.id.
        assert (Hcond : ((Z.of_nat k <=? Z.of_nat k)%Z && (Z.of_nat k <? Z.pos sz)%Z) = true).
        { rewrite Z.leb_refl; cbn [andb]; apply Z.ltb_lt; rewrite <- positive_nat_Z; lia. }
        rewrite Hcond; split; reflexivity.
      * replace (Pos.to_nat sz - r')%nat with (S k) in Hspec_r by lia.
        destruct (Z.leb_spec (Z.of_nat k) ub),
                 (Z.leb_spec (Z.of_nat (S k)) ub),
                 (Z.ltb_spec ub (Z.pos sz));
          cbn [andb] in *; try exact Hspec_r; lia.
Qed.

Definition blast_shl_k (nuw nsw : bool) (sz : positive) (xs : list lit) (k : nat) (st : blast_state)
  : (list lit * lit) * blast_state :=
  let n := Pos.to_nat sz in
  let lo := List.firstn (n - k) xs in
  let hi := List.skipn (n - k) xs in
  let bits_k := List.repeat lit_false k ++ lo in
  let '(nuw_l, st1) := if nuw then emit_or_list_opt hi st else (lit_false, st) in
  let '(nsw_l, st3) :=
      if nsw then
        let s_res := List.nth (n - 1 - k) xs lit_false in
        let '(xhs, st2) := emit_xor_const_lits s_res hi st1 in
        emit_or_list_opt xhs st2
      else (lit_false, st1) in
  let '(psn_k, st4) := emit_or2_opt nuw_l nsw_l st3 in
  ((bits_k, psn_k), st4).

Definition blast_shl_rail (nuw nsw : bool) (sz : positive) (a b : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let '((bits, sh_psn), st1) :=
      mux_shift_table sz (blast_shl_k nuw nsw sz (rbv_bits a)) (rbv_bits b) (Pos.to_nat sz) st in
  let '(ab_psn, st2) := emit_or2_opt (rbv_psn a) (rbv_psn b) st1 in
  let '(psn, st3)    := emit_or2_opt ab_psn sh_psn st2 in
  (mk_rail_bv sz bits psn, st3).

Theorem blast_shl_rail_step : forall nuw nsw sz a b asg st out st',
  sat_blast_st asg st ->
  wf_rail_bound sz (bs_next_var st) a ->
  wf_rail_bound sz (bs_next_var st) b ->
  blast_shl_rail nuw nsw sz a b st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_rail_bound sz (bs_next_var st') out /\
    eval_rail_psn asg' out =
      ((eval_rail_psn asg a || eval_rail_psn asg b) ||
       (let va := eval_rail_val sz asg a in
        let vb := eval_rail_val sz asg b in
        if (@Integers.unsigned sz vb >=? Z.pos sz)%Z then true
        else
          let res := @Integers.shl sz va vb in
          let nuw_p := nuw && (Z.shiftl (@Integers.unsigned sz va) (@Integers.unsigned sz vb) >?
                               @Integers.unsigned sz res)%Z in
          let nsw_p := nsw && negb (Z.shiftr (@Integers.unsigned sz va)
                                             (Z.pos sz - @Integers.unsigned sz vb) =?
                                    @Integers.unsigned sz (@Integers.negative sz res) *
                                    (2 ^ @Integers.unsigned sz vb - 1))%Z in
          nuw_p || nsw_p)) /\
    ((@Integers.unsigned sz (eval_rail_val sz asg b) >=? Z.pos sz)%Z = false ->
     eval_rail_val sz asg' out =
     @Integers.shl sz (eval_rail_val sz asg a) (eval_rail_val sz asg b)).
Proof.
  intros nuw nsw sz a b asg st out st' Hsat
         ([Hwa Hla] & Hba & Hpa) ([Hwb Hlb] & Hbb & Hpb) Hbl.
  unfold blast_shl_rail in Hbl; cbn zeta in Hbl.
  destruct (mux_shift_table sz (blast_shl_k nuw nsw sz (rbv_bits a))
                            (rbv_bits b) (Pos.to_nat sz) st)
    as [[bits sh_psn] st1] eqn:Hmux; cbn iota zeta in Hbl.
  destruct (emit_or2_opt (rbv_psn a) (rbv_psn b) st1) as [ab_psn st2] eqn:Eab.
  destruct (emit_or2_opt ab_psn sh_psn st2) as [psn st3] eqn:Ep.
  inversion Hbl; subst out st3; clear Hbl.
  set (n := Pos.to_nat sz).
  set (ba := List.map (eval_lit asg) (rbv_bits a)).
  set (spec_bits := fun k => List.repeat false k ++ List.firstn (n - k) ba).
  set (spec_psn := fun k =>
         let hi := List.skipn (n - k) ba in
         let s_res := List.nth (n - 1 - k) ba false in
         (nuw && existsb (fun x : bool => x) hi) ||
         (nsw && existsb (xorb s_res) hi)).
  destruct (mux_shift_table_step sz (blast_shl_k nuw nsw sz (rbv_bits a))
              spec_bits spec_psn (rbv_bits b) Hlb n asg st bits sh_psn st1
              (Nat.le_refl n) Hbb Hsat)
    as (asg1 & Hs1 & Hlen_bits & Hwf_bits & Hwf_shp & Hspec_mux); [| exact Hmux |].
  { intros k asg0 st0 bk pk s1 Hk Hs0 Efk.
    unfold blast_shl_k in Efk; cbn zeta in Efk; fold n in Efk.
    pose proof (proj2 (proj2 Hs0)) as Hsat0.
    pose proof (wf_lits_bound_mono _ _ (rbv_bits a) (proj1 Hs0) Hba) as Hba0.
    pose proof (step_spec_eval_lits st st0 asg asg0 (rbv_bits a) Hs0 Hba) as Hev_ba0.
    set (lo := List.firstn (n - k) (rbv_bits a)) in *.
    set (hi := List.skipn (n - k) (rbv_bits a)) in *.
    assert (Hw_hi0 : wf_lits_bound (bs_next_var st0) hi)
      by exact (wf_lits_bound_skipn _ _ _ Hba0).
    assert (Hnuw_step :
              exists nuw_l s01 asg01,
                (if nuw then emit_or_list_opt hi st0 else (lit_false, st0)) = (nuw_l, s01) /\
                step_spec st0 s01 asg0 asg01 /\
                wf_lit_bound (bs_next_var s01) nuw_l /\
                eval_lit asg01 nuw_l = (nuw && existsb (fun x : bool => x) (List.skipn (n - k) ba))).
    { destruct nuw.
      - destruct (emit_or_list_opt hi st0) as [nl s01] eqn:Enl.
        destruct (emit_or_list_opt_step hi asg0 st0 nl s01 Hw_hi0 Hsat0 Enl)
          as (a01 & Hs01 & Hw_nl & Hev_nl).
        exists nl, s01, a01;
          split; [reflexivity | split; [exact Hs01 | split; [exact Hw_nl |]]].
        cbn [andb]; rewrite Hev_nl; unfold hi; rewrite map_skipn_eq, Hev_ba0; reflexivity.
      - exists lit_false, st0, asg0;
          split; [reflexivity |
          split; [exact (step_spec_refl st0 asg0 Hsat0) |
          split; [exact (wf_lit_bound_false _ (proj1 (proj1 Hsat0))) |
                  exact (sat_eval_lit_false asg0 st0 Hsat0)]]]. }
    destruct Hnuw_step as (nuw_l & s01 & asg01 & Hnuw_eq & Hs01 & Hw_nuw & Hev_nuw).
    cbn iota zeta in Hnuw_eq, Efk; rewrite Hnuw_eq in Efk; cbn iota zeta in Efk; clear Hnuw_eq.
    assert (Hnsw_step :
              exists nsw_l s03 asg03,
                (if nsw then
                   let s_res := List.nth (n - 1 - k) (rbv_bits a) lit_false in
                   let '(xhs, s02) := emit_xor_const_lits s_res hi s01 in
                   emit_or_list_opt xhs s02
                 else (lit_false, s01)) = (nsw_l, s03) /\
                step_spec s01 s03 asg01 asg03 /\
                wf_lit_bound (bs_next_var s03) nsw_l /\
                eval_lit asg03 nsw_l =
                  (nsw && existsb (xorb (List.nth (n - 1 - k) ba false)) (List.skipn (n - k) ba))).
    { destruct nsw.
      - cbn zeta; set (s_res := List.nth (n - 1 - k) (rbv_bits a) lit_false).
        assert (Hw_sr : wf_lit_bound (bs_next_var s01) s_res).
        { unfold s_res; apply wf_lits_bound_nth;
            [exact (wf_lits_bound_mono _ _ _ (proj1 Hs01) Hba0)
             | exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs01)))))]. }
        destruct (emit_xor_const_lits s_res hi s01) as [xhs s02] eqn:Exhs.
        destruct (emit_or_list_opt xhs s02) as [nl s03] eqn:Enl.
        destruct (emit_xor_const_lits_step s_res hi asg01 s01 xhs s02
                    Hw_sr (wf_lits_bound_mono _ _ _ (proj1 Hs01) Hw_hi0)
                    (proj2 (proj2 Hs01)) Exhs)
          as (a02 & Hs12 & Hw_xhs & Hev_xhs).
        destruct (emit_or_list_opt_step xhs a02 s02 nl s03 Hw_xhs (proj2 (proj2 Hs12)) Enl)
          as (a03 & Hs23 & Hw_nl & Hev_nl).
        pose proof (step_spec_trans s01 s02 s03 asg01 a02 a03 Hs12 Hs23) as Hs13.
        exists nl, s03, a03; split; [reflexivity | split; [exact Hs13 | split; [exact Hw_nl |]]].
        cbn [andb]; rewrite Hev_nl, Hev_xhs, existsb_id_map_f,
          (step_spec_eval_lits st0 s01 asg0 asg01 hi Hs01 Hw_hi0).
        unfold hi; rewrite map_skipn_eq, Hev_ba0.
        assert (Hsr_ev : eval_lit asg01 s_res = List.nth (n - 1 - k) ba false).
        { unfold s_res; pose proof (step_spec_trans st st0 s01 asg asg0 asg01 Hs0 Hs01) as Hs001.
          rewrite (step_spec_eval_lit st s01 asg asg01 _ Hs001
                     (wf_lits_bound_nth _ _ _ lit_false Hba
                        (wf_lit_bound_false _ (proj1 (proj1 Hsat))))).
          rewrite <- (map_nth (eval_lit asg) (rbv_bits a) lit_false (n - 1 - k)).
          rewrite (nth_indep _ (eval_lit asg lit_false) false)
            by (rewrite length_map, Hla; fold n; lia).
          reflexivity. }
        rewrite Hsr_ev; reflexivity.
      - exists lit_false, s01, asg01;
          split; [reflexivity |
          split; [exact (step_spec_refl s01 asg01 (proj2 (proj2 Hs01))) |
          split; [exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs01))))) |
                  exact (sat_eval_lit_false asg01 s01 (proj2 (proj2 Hs01)))]]]. }
    destruct Hnsw_step as (nsw_l & s03 & asg03 & Hnsw_eq & Hs13 & Hw_nsw & Hev_nsw).
    cbn iota zeta in Hnsw_eq, Efk; rewrite Hnsw_eq in Efk; cbn iota zeta in Efk; clear Hnsw_eq.
    destruct (emit_or2_opt nuw_l nsw_l s03) as [pk0 s04] eqn:Epk.
    inversion Efk; subst bk pk s1; clear Efk.
    destruct (emit_or2_opt_step asg03 nuw_l nsw_l s03 pk0 s04 (proj2 (proj2 Hs13))
                (wf_lit_bound_mono _ _ _ (proj1 Hs13) Hw_nuw) Hw_nsw Epk)
      as (a04 & Hs34 & Hw_pk0 & Hev_pk0).
    pose proof (step_spec_trans st0 s01 s03 asg0 asg01 asg03 Hs01 Hs13) as Hs03.
    pose proof (step_spec_trans st0 s03 s04 asg0 asg03 a04 Hs03 Hs34) as Hs04.
    exists a04; split; [exact Hs04 | split].
    - rewrite length_app, repeat_length; unfold lo;
        rewrite len_firstn_le by (rewrite Hla; fold n; lia); lia.
    - split.
      + apply wf_lits_bound_app.
        * exact (wf_lits_bound_repeat _ _ _ (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs04)))))).
        * exact (wf_lits_bound_mono _ _ _ (proj1 Hs04) (wf_lits_bound_firstn _ _ _ Hba0)).
      + split; [exact Hw_pk0 | split].
        * rewrite map_app, map_repeat_eq, (sat_eval_lit_false a04 s04 (proj2 (proj2 Hs04))).
          unfold lo; rewrite (step_spec_eval_lits st0 s04 asg0 a04 _ Hs04 (wf_lits_bound_firstn _ _ _ Hba0)),
                             map_firstn_eq, Hev_ba0; reflexivity.
        * rewrite Hev_pk0,
                  (step_spec_eval_lit s01 s03 asg01 asg03 nuw_l Hs13 Hw_nuw),
                  Hev_nuw, Hev_nsw; reflexivity. }
  destruct (emit_or2_opt_step asg1 (rbv_psn a) (rbv_psn b) st1 ab_psn st2 (proj2 (proj2 Hs1))
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpa)
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpb) Eab)
    as (asg2 & Hs2 & Hwf_ab & Hev_ab).
  destruct (emit_or2_opt_step asg2 ab_psn sh_psn st2 psn st' (proj2 (proj2 Hs2))
              Hwf_ab (wf_lit_bound_mono _ _ _ (proj1 Hs2) Hwf_shp) Ep)
    as (asg3 & Hs3 & Hwf_p & Hev_p).
  pose proof (step_spec_trans st1 st2 st' asg1 asg2 asg3 Hs2 Hs3) as Hs13.
  pose proof (step_spec_trans st st1 st' asg asg1 asg3 Hs1 Hs13) as Hs03.
  cbn zeta in Hspec_mux; fold n in Hspec_mux; rewrite Nat.sub_diag in Hspec_mux; cbn [Z.of_nat] in Hspec_mux.
  set (va := eval_rail_val sz asg a).
  set (vb := eval_rail_val sz asg b).
  assert (Hub_eq : bools_to_Z (List.map (eval_lit asg) (rbv_bits b)) = @Integers.unsigned sz vb)
    by (symmetry; exact (unsigned_eval_rail_val sz asg b Hlb)).
  rewrite Hub_eq in Hspec_mux.
  pose proof (@Integers.unsigned_range sz vb) as Hub_rng.
  assert (Hle0 : (0 <=? @Integers.unsigned sz vb)%Z = true) by (apply Z.leb_le; lia).
  rewrite Hle0 in Hspec_mux; cbn [andb] in Hspec_mux.
  assert (Hk_spec :
            (@Integers.unsigned sz vb <? Z.pos sz)%Z = true ->
            spec_psn (Z.to_nat (@Integers.unsigned sz vb)) =
              (let res := @Integers.shl sz va vb in
               let nuw_p := nuw && (Z.shiftl (@Integers.unsigned sz va) (@Integers.unsigned sz vb) >?
                                    @Integers.unsigned sz res)%Z in
               let nsw_p := nsw && negb (Z.shiftr (@Integers.unsigned sz va)
                                                  (Z.pos sz - @Integers.unsigned sz vb) =?
                                         @Integers.unsigned sz (@Integers.negative sz res) *
                                         (2 ^ @Integers.unsigned sz vb - 1))%Z in
               nuw_p || nsw_p) /\
            @Integers.repr sz (bools_to_Z (spec_bits (Z.to_nat (@Integers.unsigned sz vb)))) =
              @Integers.shl sz va vb).
  { intros Hlt_sz; apply Z.ltb_lt in Hlt_sz.
    set (k := Z.to_nat (@Integers.unsigned sz vb)).
    assert (Hk_z : Z.of_nat k = @Integers.unsigned sz vb) by (unfold k; rewrite Z2Nat.id; lia).
    assert (Hk_n : (k < n)%nat) by (unfold n; rewrite <- positive_nat_Z in Hlt_sz; lia).
    assert (Hba_len : List.length ba = n) by (unfold ba, n; rewrite length_map; exact Hla).
    set (lo := List.firstn (n - k) ba); set (hi := List.skipn (n - k) ba).
    assert (Hlo_len : List.length lo = (n - k)%nat)
      by (unfold lo; apply len_firstn_le; lia).
    assert (Hhi_len : List.length hi = k)
      by (unfold hi; rewrite len_skipn_eq, Hba_len; lia).
    assert (Hua_split : (@Integers.unsigned sz va =
                         bools_to_Z lo + 2 ^ Z.of_nat (n - k) * bools_to_Z hi)%Z).
    { unfold va; rewrite (unsigned_eval_rail_val sz asg a Hla); fold ba.
      rewrite <- (firstn_skipn_eq (n - k) ba) at 1; fold lo hi.
      rewrite bools_to_Z_app, Hlo_len; reflexivity. }
    assert (Hsb_z : (bools_to_Z (spec_bits k) = 2 ^ Z.of_nat k * bools_to_Z lo)%Z).
    { unfold spec_bits; fold lo; rewrite bools_to_Z_app, bools_to_Z_repeat_false, repeat_length; ring. }
    assert (Hsb_len : List.length (spec_bits k) = n)
      by (unfold spec_bits; fold lo; rewrite length_app, repeat_length, Hlo_len; lia).
    assert (Hshl_z : (Z.shiftl (@Integers.unsigned sz va) (@Integers.unsigned sz vb) =
                      bools_to_Z (spec_bits k) + @Integers.modulus sz * bools_to_Z hi)%Z).
    { rewrite <- Hk_z, Z.shiftl_mul_pow2, Hua_split, Hsb_z by lia.
      replace (@Integers.modulus sz) with (2 ^ Z.of_nat (n - k) * 2 ^ Z.of_nat k)%Z.
      - ring.
      - rewrite <- Z.pow_add_r by lia; replace (Z.of_nat (n - k) + Z.of_nat k)%Z with (Z.pos sz)
          by (unfold n; rewrite <- Nat2Z.inj_add, Nat.sub_add, positive_nat_Z by lia; reflexivity).
        symmetry; apply modulus_pow_sz. }
    assert (Hres_eq : @Integers.repr sz (bools_to_Z (spec_bits k)) = @Integers.shl sz va vb).
    { unfold Integers.shl; rewrite Hshl_z; apply @Integers.eqm_samerepr.
      exists (- bools_to_Z hi)%Z; nia. }
    assert (Hures : @Integers.unsigned sz (@Integers.shl sz va vb) = bools_to_Z (spec_bits k)).
    { rewrite <- Hres_eq; apply @Integers.unsigned_repr.
      pose proof (bools_to_Z_range (spec_bits k)) as Hr; rewrite Hsb_len in Hr.
      unfold n in Hr; rewrite positive_nat_Z, <- modulus_pow_sz in Hr.
      unfold Integers.max_unsigned; lia. }
    split; [| exact Hres_eq].
    unfold spec_psn; fold hi; cbn zeta.
    f_equal.
    - f_equal.
      rewrite Hshl_z, Hures.
      pose proof (bools_to_Z_range hi) as Hhi_r.
      pose proof (@Integers.modulus_pos sz) as Hmp.
      rewrite Z.gtb_ltb;
      replace (existsb (fun x : bool => x) hi) with (negb (bools_to_Z hi =? 0)%Z)
        by (rewrite bools_to_Z_zero_iff, Bool.negb_involutive; reflexivity).
      destruct (Z.eqb_spec (bools_to_Z hi) 0%Z),
               (Z.ltb_spec (bools_to_Z (spec_bits k))
                           (bools_to_Z (spec_bits k) + @Integers.modulus sz * bools_to_Z hi));
        cbn [negb]; try reflexivity; nia.
    - f_equal.
      replace (Z.pos sz - @Integers.unsigned sz vb)%Z with (Z.of_nat (n - k))
        by (unfold n; rewrite <- Hk_z, Nat2Z.inj_sub, positive_nat_Z by lia; reflexivity).
      rewrite Z.shiftr_div_pow2, Hua_split by lia.
      pose proof (bools_to_Z_range lo) as Hlo_r; rewrite Hlo_len in Hlo_r.
      rewrite (div_low_high_pow2 (bools_to_Z lo) (bools_to_Z hi) (2 ^ Z.of_nat (n - k)))
        by lia.
      rewrite unsigned_negative_eq_msb, <- Hk_z, <- Hhi_len.
      assert (Hmsb_res : msb_of sz (@Integers.shl sz va vb) = List.nth (n - 1 - k) ba false).
      { unfold msb_of; fold n; rewrite <- Hres_eq.
        assert (Hbits_res : bit_int_to_bools sz (@Integers.repr sz (bools_to_Z (spec_bits k))) =
                            spec_bits k).
        { apply bools_to_Z_inj; [rewrite bit_int_to_bools_length; symmetry; exact Hsb_len |].
          rewrite bools_to_Z_bit_int_to_bools, Hres_eq; exact Hures. }
        rewrite Hbits_res; unfold spec_bits.
        rewrite nth_app_r by (rewrite repeat_length; lia).
        rewrite repeat_length, nth_firstn_lt by lia; reflexivity. }
      rewrite Hmsb_res, bools_to_Z_eq_repeat_iff, Bool.negb_involutive, Hhi_len; reflexivity. }
  exists asg3; split; [exact Hs03 | split].
  - split; [split; [reflexivity | cbn; exact Hlen_bits] |
            split; [exact (wf_lits_bound_mono _ _ bits (proj1 Hs13) Hwf_bits) | exact Hwf_p]].
  - split.
    + unfold eval_rail_psn; cbn [rbv_psn]; cbn zeta; fold va vb.
      rewrite Hev_p, Hev_ab,
              (step_spec_eval_lit st st1 asg asg1 (rbv_psn a) Hs1 Hpa),
              (step_spec_eval_lit st st1 asg asg1 (rbv_psn b) Hs1 Hpb),
              (step_spec_eval_lit st1 st2 asg1 asg2 sh_psn Hs2 Hwf_shp).
      destruct (Z.geb_spec (@Integers.unsigned sz vb) (Z.pos sz)) as [Hge | Hlt].
      * assert (Hltb_f : (@Integers.unsigned sz vb <? Z.pos sz)%Z = false) by (apply Z.ltb_ge; lia).
        rewrite Hltb_f in Hspec_mux; rewrite Hspec_mux, !orb_true_r; reflexivity.
      * assert (Hltb_t : (@Integers.unsigned sz vb <? Z.pos sz)%Z = true) by (apply Z.ltb_lt; lia).
        rewrite Hltb_t in Hspec_mux; destruct Hspec_mux as [_ Hpsn_eq].
        rewrite Hpsn_eq, (proj1 (Hk_spec Hltb_t)); reflexivity.
    + intros Hge_f; fold vb in Hge_f.
      assert (Hltb_t : (@Integers.unsigned sz vb <? Z.pos sz)%Z = true)
        by (destruct (Z.geb_spec (@Integers.unsigned sz vb) (Z.pos sz)); [discriminate Hge_f | apply Z.ltb_lt; lia]).
      rewrite Hltb_t in Hspec_mux; destruct Hspec_mux as [Hbits_eq _].
      unfold eval_rail_val; cbn [rbv_bits];
        rewrite (step_spec_eval_lits st1 st' asg1 asg3 bits Hs13 Hwf_bits), Hbits_eq.
      exact (proj2 (Hk_spec Hltb_t)).
Qed.

Definition blast_lshr_k (ex : bool) (sz : positive) (xs : list lit) (k : nat) (st : blast_state)
  : (list lit * lit) * blast_state :=
  let lo := List.firstn k xs in
  let hi := List.skipn k xs in
  let bits_k := hi ++ List.repeat lit_false k in
  let '(psn_k, st1) := if ex then emit_or_list_opt lo st else (lit_false, st) in
  ((bits_k, psn_k), st1).

Definition blast_lshr_rail (ex : bool) (sz : positive) (a b : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let '((bits, sh_psn), st1) :=
      mux_shift_table sz (blast_lshr_k ex sz (rbv_bits a)) (rbv_bits b) (Pos.to_nat sz) st in
  let '(ab_psn, st2) := emit_or2_opt (rbv_psn a) (rbv_psn b) st1 in
  let '(psn, st3)    := emit_or2_opt ab_psn sh_psn st2 in
  (mk_rail_bv sz bits psn, st3).

Theorem blast_lshr_rail_step : forall ex sz a b asg st out st',
  sat_blast_st asg st ->
  wf_rail_bound sz (bs_next_var st) a ->
  wf_rail_bound sz (bs_next_var st) b ->
  blast_lshr_rail ex sz a b st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_rail_bound sz (bs_next_var st') out /\
    eval_rail_psn asg' out =
      ((eval_rail_psn asg a || eval_rail_psn asg b) ||
       (let va := eval_rail_val sz asg a in
        let vb := eval_rail_val sz asg b in
        if (@Integers.unsigned sz vb >=? Z.pos sz)%Z then true
        else ex && negb ((@Integers.unsigned sz va mod (2 ^ @Integers.unsigned sz vb)) =? 0)%Z)) /\
    ((@Integers.unsigned sz (eval_rail_val sz asg b) >=? Z.pos sz)%Z = false ->
     eval_rail_val sz asg' out =
     @Integers.shru sz (eval_rail_val sz asg a) (eval_rail_val sz asg b)).
Proof.
  intros ex sz a b asg st out st' Hsat
         ([Hwa Hla] & Hba & Hpa) ([Hwb Hlb] & Hbb & Hpb) Hbl.
  unfold blast_lshr_rail in Hbl; cbn zeta in Hbl.
  destruct (mux_shift_table sz (blast_lshr_k ex sz (rbv_bits a))
                            (rbv_bits b) (Pos.to_nat sz) st)
    as [[bits sh_psn] st1] eqn:Hmux; cbn iota zeta in Hbl.
  destruct (emit_or2_opt (rbv_psn a) (rbv_psn b) st1) as [ab_psn st2] eqn:Eab.
  destruct (emit_or2_opt ab_psn sh_psn st2) as [psn st3] eqn:Ep.
  inversion Hbl; subst out st3; clear Hbl.
  set (n := Pos.to_nat sz).
  set (ba := List.map (eval_lit asg) (rbv_bits a)).
  set (spec_bits := fun k => List.skipn k ba ++ List.repeat false k).
  set (spec_psn := fun k => ex && existsb (fun x : bool => x) (List.firstn k ba)).
  destruct (mux_shift_table_step sz (blast_lshr_k ex sz (rbv_bits a))
              spec_bits spec_psn (rbv_bits b) Hlb n asg st bits sh_psn st1
              (Nat.le_refl n) Hbb Hsat)
    as (asg1 & Hs1 & Hlen_bits & Hwf_bits & Hwf_shp & Hspec_mux); [| exact Hmux |].
  { intros k asg0 st0 bk pk s1 Hk Hs0 Efk.
    unfold blast_lshr_k in Efk; cbn zeta in Efk.
    pose proof (proj2 (proj2 Hs0)) as Hsat0.
    pose proof (wf_lits_bound_mono _ _ (rbv_bits a) (proj1 Hs0) Hba) as Hba0.
    pose proof (step_spec_eval_lits st st0 asg asg0 (rbv_bits a) Hs0 Hba) as Hev_ba0.
    destruct ex.
    - destruct (emit_or_list_opt (List.firstn k (rbv_bits a)) st0) as [pk0 s01] eqn:Epk.
      inversion Efk; subst bk pk s1; clear Efk.
      destruct (emit_or_list_opt_step (List.firstn k (rbv_bits a)) asg0 st0 pk0 s01
                  (wf_lits_bound_firstn _ _ _ Hba0) Hsat0 Epk)
        as (a01 & Hs01 & Hw_pk & Hev_pk).
      exists a01; split; [exact Hs01 | split].
      + rewrite length_app, len_skipn_eq, repeat_length, Hla; fold n; lia.
      + split.
        * apply wf_lits_bound_app;
            [exact (wf_lits_bound_mono _ _ _ (proj1 Hs01) (wf_lits_bound_skipn _ _ _ Hba0))
             | exact (wf_lits_bound_repeat _ _ _ (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs01))))))].
        * split; [exact Hw_pk | split].
          -- rewrite map_app, map_repeat_eq, (sat_eval_lit_false a01 s01 (proj2 (proj2 Hs01))),
                     (step_spec_eval_lits st0 s01 asg0 a01 _ Hs01 (wf_lits_bound_skipn _ _ _ Hba0)),
                     map_skipn_eq, Hev_ba0; reflexivity.
          -- cbn [spec_psn andb]; rewrite Hev_pk, map_firstn_eq, Hev_ba0; reflexivity.
    - inversion Efk; subst bk pk s1; clear Efk.
      exists asg0; split; [exact (step_spec_refl st0 asg0 Hsat0) | split].
      + rewrite length_app, len_skipn_eq, repeat_length, Hla; fold n; lia.
      + split.
        * apply wf_lits_bound_app;
            [exact (wf_lits_bound_skipn _ _ _ Hba0)
             | exact (wf_lits_bound_repeat _ _ _ (wf_lit_bound_false _ (proj1 (proj1 Hsat0))))].
        * split; [exact (wf_lit_bound_false _ (proj1 (proj1 Hsat0))) | split].
          -- rewrite map_app, map_repeat_eq, (sat_eval_lit_false asg0 st0 Hsat0),
                     map_skipn_eq, Hev_ba0; reflexivity.
          -- exact (sat_eval_lit_false asg0 st0 Hsat0). }
  destruct (emit_or2_opt_step asg1 (rbv_psn a) (rbv_psn b) st1 ab_psn st2 (proj2 (proj2 Hs1))
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpa)
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpb) Eab)
    as (asg2 & Hs2 & Hwf_ab & Hev_ab).
  destruct (emit_or2_opt_step asg2 ab_psn sh_psn st2 psn st' (proj2 (proj2 Hs2))
              Hwf_ab (wf_lit_bound_mono _ _ _ (proj1 Hs2) Hwf_shp) Ep)
    as (asg3 & Hs3 & Hwf_p & Hev_p).
  pose proof (step_spec_trans st1 st2 st' asg1 asg2 asg3 Hs2 Hs3) as Hs13.
  pose proof (step_spec_trans st st1 st' asg asg1 asg3 Hs1 Hs13) as Hs03.
  cbn zeta in Hspec_mux; fold n in Hspec_mux; rewrite Nat.sub_diag in Hspec_mux; cbn [Z.of_nat] in Hspec_mux.
  set (va := eval_rail_val sz asg a); set (vb := eval_rail_val sz asg b).
  assert (Hub_eq : bools_to_Z (List.map (eval_lit asg) (rbv_bits b)) = @Integers.unsigned sz vb)
    by (symmetry; exact (unsigned_eval_rail_val sz asg b Hlb)).
  rewrite Hub_eq in Hspec_mux.
  pose proof (@Integers.unsigned_range sz vb) as Hub_rng.
  assert (Hle0 : (0 <=? @Integers.unsigned sz vb)%Z = true) by (apply Z.leb_le; lia).
  rewrite Hle0 in Hspec_mux; cbn [andb] in Hspec_mux.
  assert (Hk_spec :
            (@Integers.unsigned sz vb <? Z.pos sz)%Z = true ->
            spec_psn (Z.to_nat (@Integers.unsigned sz vb)) =
              (ex && negb ((@Integers.unsigned sz va mod (2 ^ @Integers.unsigned sz vb)) =? 0)%Z) /\
            @Integers.repr sz (bools_to_Z (spec_bits (Z.to_nat (@Integers.unsigned sz vb)))) =
              @Integers.shru sz va vb).
  { intros Hlt_sz; apply Z.ltb_lt in Hlt_sz.
    set (k := Z.to_nat (@Integers.unsigned sz vb)).
    assert (Hk_z : Z.of_nat k = @Integers.unsigned sz vb) by (unfold k; rewrite Z2Nat.id; lia).
    assert (Hk_n : (k < n)%nat) by (unfold n; rewrite <- positive_nat_Z in Hlt_sz; lia).
    assert (Hba_len : List.length ba = n) by (unfold ba, n; rewrite length_map; exact Hla).
    set (lo := List.firstn k ba); set (hi := List.skipn k ba).
    assert (Hlo_len : List.length lo = k) by (unfold lo; apply len_firstn_le; lia).
    assert (Hua_split : (@Integers.unsigned sz va =
                         bools_to_Z lo + 2 ^ Z.of_nat k * bools_to_Z hi)%Z).
    { unfold va; rewrite (unsigned_eval_rail_val sz asg a Hla); fold ba.
      rewrite <- (firstn_skipn_eq k ba) at 1; fold lo hi.
      rewrite bools_to_Z_app, Hlo_len; reflexivity. }
    pose proof (bools_to_Z_range lo) as Hlo_r; rewrite Hlo_len in Hlo_r.
    split.
    - unfold spec_psn; fold lo; f_equal.
      rewrite <- Hk_z, Hua_split, (mod_low_high_pow2 (bools_to_Z lo) (bools_to_Z hi) (2 ^ Z.of_nat k)) by lia.
      rewrite bools_to_Z_zero_iff, Bool.negb_involutive; reflexivity.
    - unfold Integers.shru, spec_bits; fold hi.
      rewrite bools_to_Z_app, bools_to_Z_repeat_false, Z.mul_0_r, Z.add_0_r.
      rewrite <- Hk_z, Z.shiftr_div_pow2, Hua_split by lia.
      rewrite (div_low_high_pow2 (bools_to_Z lo) (bools_to_Z hi) (2 ^ Z.of_nat k)) by lia; reflexivity. }
  exists asg3; split; [exact Hs03 | split].
  - split; [split; [reflexivity | cbn; exact Hlen_bits] |
            split; [exact (wf_lits_bound_mono _ _ bits (proj1 Hs13) Hwf_bits) | exact Hwf_p]].
  - split.
    + unfold eval_rail_psn; cbn [rbv_psn]; cbn zeta; fold va vb.
      rewrite Hev_p, Hev_ab,
              (step_spec_eval_lit st st1 asg asg1 (rbv_psn a) Hs1 Hpa),
              (step_spec_eval_lit st st1 asg asg1 (rbv_psn b) Hs1 Hpb),
              (step_spec_eval_lit st1 st2 asg1 asg2 sh_psn Hs2 Hwf_shp).
      destruct (Z.geb_spec (@Integers.unsigned sz vb) (Z.pos sz)) as [Hge | Hlt].
      * assert (Hltb_f : (@Integers.unsigned sz vb <? Z.pos sz)%Z = false) by (apply Z.ltb_ge; lia).
        rewrite Hltb_f in Hspec_mux; rewrite Hspec_mux, !orb_true_r; reflexivity.
      * assert (Hltb_t : (@Integers.unsigned sz vb <? Z.pos sz)%Z = true) by (apply Z.ltb_lt; lia).
        rewrite Hltb_t in Hspec_mux; destruct Hspec_mux as [_ Hpsn_eq].
        rewrite Hpsn_eq, (proj1 (Hk_spec Hltb_t)); reflexivity.
    + intros Hge_f; fold vb in Hge_f.
      assert (Hltb_t : (@Integers.unsigned sz vb <? Z.pos sz)%Z = true)
        by (destruct (Z.geb_spec (@Integers.unsigned sz vb) (Z.pos sz)); [discriminate Hge_f | apply Z.ltb_lt; lia]).
      rewrite Hltb_t in Hspec_mux; destruct Hspec_mux as [Hbits_eq _].
      unfold eval_rail_val; cbn [rbv_bits];
        rewrite (step_spec_eval_lits st1 st' asg1 asg3 bits Hs13 Hwf_bits), Hbits_eq.
      exact (proj2 (Hk_spec Hltb_t)).
Qed.

Definition blast_ashr_k (ex : bool) (sz : positive) (xs : list lit) (k : nat) (st : blast_state)
  : (list lit * lit) * blast_state :=
  let lo := List.firstn k xs in
  let hi := List.skipn k xs in
  let msb := List.nth (Pos.to_nat sz - 1) xs lit_false in
  let bits_k := hi ++ List.repeat msb k in
  let '(psn_k, st1) := if ex then emit_or_list_opt lo st else (lit_false, st) in
  ((bits_k, psn_k), st1).

Definition blast_ashr_rail (ex : bool) (sz : positive) (a b : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let '((bits, sh_psn), st1) :=
      mux_shift_table sz (blast_ashr_k ex sz (rbv_bits a)) (rbv_bits b) (Pos.to_nat sz) st in
  let '(ab_psn, st2) := emit_or2_opt (rbv_psn a) (rbv_psn b) st1 in
  let '(psn, st3)    := emit_or2_opt ab_psn sh_psn st2 in
  (mk_rail_bv sz bits psn, st3).

Theorem blast_ashr_rail_step : forall ex sz a b asg st out st',
  sat_blast_st asg st ->
  wf_rail_bound sz (bs_next_var st) a ->
  wf_rail_bound sz (bs_next_var st) b ->
  blast_ashr_rail ex sz a b st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_rail_bound sz (bs_next_var st') out /\
    eval_rail_psn asg' out =
      ((eval_rail_psn asg a || eval_rail_psn asg b) ||
       (let va := eval_rail_val sz asg a in
        let vb := eval_rail_val sz asg b in
        if (@Integers.unsigned sz vb >=? Z.pos sz)%Z then true
        else ex && negb ((@Integers.unsigned sz va mod (2 ^ @Integers.unsigned sz vb)) =? 0)%Z)) /\
    ((@Integers.unsigned sz (eval_rail_val sz asg b) >=? Z.pos sz)%Z = false ->
     eval_rail_val sz asg' out =
     @Integers.shr sz (eval_rail_val sz asg a) (eval_rail_val sz asg b)).
Proof.
  intros ex sz a b asg st out st' Hsat
         ([Hwa Hla] & Hba & Hpa) ([Hwb Hlb] & Hbb & Hpb) Hbl.
  unfold blast_ashr_rail in Hbl; cbn zeta in Hbl.
  destruct (mux_shift_table sz (blast_ashr_k ex sz (rbv_bits a))
                            (rbv_bits b) (Pos.to_nat sz) st)
    as [[bits sh_psn] st1] eqn:Hmux; cbn iota zeta in Hbl.
  destruct (emit_or2_opt (rbv_psn a) (rbv_psn b) st1) as [ab_psn st2] eqn:Eab.
  destruct (emit_or2_opt ab_psn sh_psn st2) as [psn st3] eqn:Ep.
  inversion Hbl; subst out st3; clear Hbl.
  set (n := Pos.to_nat sz).
  set (ba := List.map (eval_lit asg) (rbv_bits a)).
  set (b_msb := List.nth (n - 1) ba false).
  set (spec_bits := fun k => List.skipn k ba ++ List.repeat b_msb k).
  set (spec_psn := fun k => ex && existsb (fun x : bool => x) (List.firstn k ba)).
  destruct (mux_shift_table_step sz (blast_ashr_k ex sz (rbv_bits a))
              spec_bits spec_psn (rbv_bits b) Hlb n asg st bits sh_psn st1
              (Nat.le_refl n) Hbb Hsat)
    as (asg1 & Hs1 & Hlen_bits & Hwf_bits & Hwf_shp & Hspec_mux); [| exact Hmux |].
  { intros k asg0 st0 bk pk s1 Hk Hs0 Efk.
    unfold blast_ashr_k in Efk; cbn zeta in Efk; fold n in Efk.
    pose proof (proj2 (proj2 Hs0)) as Hsat0.
    pose proof (wf_lits_bound_mono _ _ (rbv_bits a) (proj1 Hs0) Hba) as Hba0.
    pose proof (step_spec_eval_lits st st0 asg asg0 (rbv_bits a) Hs0 Hba) as Hev_ba0.
    set (msb_l := List.nth (n - 1) (rbv_bits a) lit_false) in *.
    assert (Hw_msbl : wf_lit_bound (bs_next_var st) msb_l)
      by exact (wf_lits_bound_nth _ _ _ lit_false Hba (wf_lit_bound_false _ (proj1 (proj1 Hsat)))).
    assert (Hev_msbl : forall aX sX, step_spec st sX asg aX -> eval_lit aX msb_l = b_msb).
    { intros aX sX HsX; rewrite (step_spec_eval_lit st sX asg aX msb_l HsX Hw_msbl).
      unfold msb_l, b_msb, ba; pose proof (Pos2Nat.is_pos sz) as Hpos.
      rewrite <- (map_nth (eval_lit asg) (rbv_bits a) lit_false (n - 1)).
      apply nth_indep; rewrite length_map, Hla; fold n; lia. }
    destruct ex.
    - destruct (emit_or_list_opt (List.firstn k (rbv_bits a)) st0) as [pk0 s01] eqn:Epk.
      inversion Efk; subst bk pk s1; clear Efk.
      destruct (emit_or_list_opt_step (List.firstn k (rbv_bits a)) asg0 st0 pk0 s01
                  (wf_lits_bound_firstn _ _ _ Hba0) Hsat0 Epk)
        as (a01 & Hs01 & Hw_pk & Hev_pk).
      pose proof (step_spec_trans st st0 s01 asg asg0 a01 Hs0 Hs01) as Hs001.
      exists a01; split; [exact Hs01 | split].
      + rewrite length_app, len_skipn_eq, repeat_length, Hla; fold n; lia.
      + split.
        * apply wf_lits_bound_app;
            [exact (wf_lits_bound_mono _ _ _ (proj1 Hs01) (wf_lits_bound_skipn _ _ _ Hba0))
             | exact (wf_lits_bound_repeat _ _ _ (wf_lit_bound_mono _ _ _ (proj1 Hs001) Hw_msbl))].
        * split; [exact Hw_pk | split].
          -- rewrite map_app, map_repeat_eq, (Hev_msbl a01 s01 Hs001),
                     (step_spec_eval_lits st0 s01 asg0 a01 _ Hs01 (wf_lits_bound_skipn _ _ _ Hba0)),
                     map_skipn_eq, Hev_ba0; reflexivity.
          -- cbn [spec_psn andb]; rewrite Hev_pk, map_firstn_eq, Hev_ba0; reflexivity.
    - inversion Efk; subst bk pk s1; clear Efk.
      exists asg0; split; [exact (step_spec_refl st0 asg0 Hsat0) | split].
      + rewrite length_app, len_skipn_eq, repeat_length, Hla; fold n; lia.
      + split.
        * apply wf_lits_bound_app;
            [exact (wf_lits_bound_skipn _ _ _ Hba0)
             | exact (wf_lits_bound_repeat _ _ _ (wf_lit_bound_mono _ _ _ (proj1 Hs0) Hw_msbl))].
        * split; [exact (wf_lit_bound_false _ (proj1 (proj1 Hsat0))) | split].
          -- rewrite map_app, map_repeat_eq, (Hev_msbl asg0 st0 Hs0),
                     map_skipn_eq, Hev_ba0; reflexivity.
          -- exact (sat_eval_lit_false asg0 st0 Hsat0). }
  destruct (emit_or2_opt_step asg1 (rbv_psn a) (rbv_psn b) st1 ab_psn st2 (proj2 (proj2 Hs1))
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpa)
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpb) Eab)
    as (asg2 & Hs2 & Hwf_ab & Hev_ab).
  destruct (emit_or2_opt_step asg2 ab_psn sh_psn st2 psn st' (proj2 (proj2 Hs2))
              Hwf_ab (wf_lit_bound_mono _ _ _ (proj1 Hs2) Hwf_shp) Ep)
    as (asg3 & Hs3 & Hwf_p & Hev_p).
  pose proof (step_spec_trans st1 st2 st' asg1 asg2 asg3 Hs2 Hs3) as Hs13.
  pose proof (step_spec_trans st st1 st' asg asg1 asg3 Hs1 Hs13) as Hs03.
  cbn zeta in Hspec_mux; fold n in Hspec_mux; rewrite Nat.sub_diag in Hspec_mux; cbn [Z.of_nat] in Hspec_mux.
  set (va := eval_rail_val sz asg a); set (vb := eval_rail_val sz asg b).
  assert (Hub_eq : bools_to_Z (List.map (eval_lit asg) (rbv_bits b)) = @Integers.unsigned sz vb)
    by (symmetry; exact (unsigned_eval_rail_val sz asg b Hlb)).
  rewrite Hub_eq in Hspec_mux.
  pose proof (@Integers.unsigned_range sz vb) as Hub_rng.
  assert (Hle0 : (0 <=? @Integers.unsigned sz vb)%Z = true) by (apply Z.leb_le; lia).
  rewrite Hle0 in Hspec_mux; cbn [andb] in Hspec_mux.
  assert (Hk_spec :
            (@Integers.unsigned sz vb <? Z.pos sz)%Z = true ->
            spec_psn (Z.to_nat (@Integers.unsigned sz vb)) =
              (ex && negb ((@Integers.unsigned sz va mod (2 ^ @Integers.unsigned sz vb)) =? 0)%Z) /\
            @Integers.repr sz (bools_to_Z (spec_bits (Z.to_nat (@Integers.unsigned sz vb)))) =
              @Integers.shr sz va vb).
  { intros Hlt_sz; apply Z.ltb_lt in Hlt_sz.
    set (k := Z.to_nat (@Integers.unsigned sz vb)).
    assert (Hk_z : Z.of_nat k = @Integers.unsigned sz vb) by (unfold k; rewrite Z2Nat.id; lia).
    assert (Hk_n : (k < n)%nat) by (unfold n; rewrite <- positive_nat_Z in Hlt_sz; lia).
    assert (Hba_len : List.length ba = n) by (unfold ba, n; rewrite length_map; exact Hla).
    set (lo := List.firstn k ba); set (hi := List.skipn k ba).
    assert (Hlo_len : List.length lo = k) by (unfold lo; apply len_firstn_le; lia).
    assert (Hua_split : (@Integers.unsigned sz va =
                         bools_to_Z lo + 2 ^ Z.of_nat k * bools_to_Z hi)%Z).
    { unfold va; rewrite (unsigned_eval_rail_val sz asg a Hla); fold ba.
      rewrite <- (firstn_skipn_eq k ba) at 1; fold lo hi.
      rewrite bools_to_Z_app, Hlo_len; reflexivity. }
    pose proof (bools_to_Z_range lo) as Hlo_r; rewrite Hlo_len in Hlo_r.
    split.
    - unfold spec_psn; fold lo; f_equal.
      rewrite <- Hk_z, Hua_split, (mod_low_high_pow2 (bools_to_Z lo) (bools_to_Z hi) (2 ^ Z.of_nat k)) by lia.
      rewrite bools_to_Z_zero_iff, Bool.negb_involutive; reflexivity.
    - apply @Integers.same_bits_eq; intros i Hi.
      rewrite @Integers.testbit_repr by exact Hi.
      rewrite @Integers.bits_shr by exact Hi.
      replace i with (Z.of_nat (Z.to_nat i)) at 1 by (rewrite Z2Nat.id; lia).
      rewrite bools_to_Z_testbit; unfold spec_bits.
      assert (Hi_n : (Z.to_nat i < n)%nat)
        by (unfold n; unfold Integers.zwordsize in Hi; lia).
      assert (Hsk_len : List.length (List.skipn k ba) = (n - k)%nat)
        by (rewrite len_skipn_eq, Hba_len; reflexivity).
      destruct (Numeric.Rocqlib.zlt (i + @Integers.unsigned sz vb) (@Integers.zwordsize sz)) as [Hlt_i | Hge_i].
      + assert (Hi_nk : (Z.to_nat i < List.length (List.skipn k ba))%nat)
          by (rewrite Hsk_len; unfold n; unfold Integers.zwordsize in Hlt_i; lia).
        rewrite nth_app_l by exact Hi_nk.
        rewrite nth_skipn_eq.
        unfold va; rewrite eval_rail_val_testbit by lia; fold ba.
        f_equal; lia.
      + assert (Hge_nk : (List.length (List.skipn k ba) <= Z.to_nat i)%nat)
          by (rewrite Hsk_len; unfold n; unfold Integers.zwordsize in Hge_i; lia).
        rewrite nth_app_r by exact Hge_nk.
        rewrite nth_repeat_lt by (rewrite Hsk_len; lia).
        pose proof (Pos2Nat.is_pos sz) as Hpos.
        unfold va; rewrite eval_rail_val_testbit by (unfold Integers.zwordsize; lia); fold ba.
        unfold b_msb, n; f_equal; unfold Integers.zwordsize; lia. }
  exists asg3; split; [exact Hs03 | split].
  - split; [split; [reflexivity | cbn; exact Hlen_bits] |
            split; [exact (wf_lits_bound_mono _ _ bits (proj1 Hs13) Hwf_bits) | exact Hwf_p]].
  - split.
    + unfold eval_rail_psn; cbn [rbv_psn]; cbn zeta; fold va vb.
      rewrite Hev_p, Hev_ab,
              (step_spec_eval_lit st st1 asg asg1 (rbv_psn a) Hs1 Hpa),
              (step_spec_eval_lit st st1 asg asg1 (rbv_psn b) Hs1 Hpb),
              (step_spec_eval_lit st1 st2 asg1 asg2 sh_psn Hs2 Hwf_shp).
      destruct (Z.geb_spec (@Integers.unsigned sz vb) (Z.pos sz)) as [Hge | Hlt].
      * assert (Hltb_f : (@Integers.unsigned sz vb <? Z.pos sz)%Z = false) by (apply Z.ltb_ge; lia).
        rewrite Hltb_f in Hspec_mux; rewrite Hspec_mux, !orb_true_r; reflexivity.
      * assert (Hltb_t : (@Integers.unsigned sz vb <? Z.pos sz)%Z = true) by (apply Z.ltb_lt; lia).
        rewrite Hltb_t in Hspec_mux; destruct Hspec_mux as [_ Hpsn_eq].
        rewrite Hpsn_eq, (proj1 (Hk_spec Hltb_t)); reflexivity.
    + intros Hge_f; fold vb in Hge_f.
      assert (Hltb_t : (@Integers.unsigned sz vb <? Z.pos sz)%Z = true)
        by (destruct (Z.geb_spec (@Integers.unsigned sz vb) (Z.pos sz)); [discriminate Hge_f | apply Z.ltb_lt; lia]).
      rewrite Hltb_t in Hspec_mux; destruct Hspec_mux as [Hbits_eq _].
      unfold eval_rail_val; cbn [rbv_bits];
        rewrite (step_spec_eval_lits st1 st' asg1 asg3 bits Hs13 Hwf_bits), Hbits_eq.
      exact (proj2 (Hk_spec Hltb_t)).
Qed.

Definition blast_zext_rail (nneg : bool) (fw tw : positive) (a : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let bits := rbv_bits a ++ List.repeat lit_false (Pos.to_nat tw - Pos.to_nat fw) in
  let nneg_l := if nneg then msb_lit a else lit_false in
  let '(psn, st1) := emit_or2_opt (rbv_psn a) nneg_l st in
  (mk_rail_bv tw bits psn, st1).

Theorem blast_zext_rail_step : forall nneg fw tw a asg st out st',
  (fw < tw)%positive ->
  sat_blast_st asg st ->
  wf_rail_bound fw (bs_next_var st) a ->
  blast_zext_rail nneg fw tw a st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_rail_bound tw (bs_next_var st') out /\
    eval_rail_psn asg' out =
      (eval_rail_psn asg a ||
       (nneg && (@Integers.signed fw (eval_rail_val fw asg a) <? 0)%Z)) /\
    eval_rail_val tw asg' out =
      @Integers.repr tw (@Integers.unsigned fw (eval_rail_val fw asg a)).
Proof.
  intros nneg fw tw a asg st out st' Hlt Hsat ([Hwa Hla] & Hba & Hpa) Hbl.
  unfold blast_zext_rail in Hbl; cbn zeta in Hbl.
  set (nneg_l := if nneg then msb_lit a else lit_false) in *.
  assert (Hw_nl : wf_lit_bound (bs_next_var st) nneg_l)
    by (unfold nneg_l; destruct nneg;
        [exact (wf_msb_lit fw _ a (proj1 (proj1 Hsat)) (conj (conj Hwa Hla) (conj Hba Hpa)))
         | exact (wf_lit_bound_false _ (proj1 (proj1 Hsat)))]).
  destruct (emit_or2_opt (rbv_psn a) nneg_l st) as [psn st1] eqn:Ep.
  inversion Hbl; subst out st1; clear Hbl.
  destruct (emit_or2_opt_step asg (rbv_psn a) nneg_l st psn st' Hsat Hpa Hw_nl Ep)
    as (asg1 & Hs1 & Hwf_p & Hev_p).
  exists asg1; split; [exact Hs1 | split].
  - split; [split; [reflexivity | cbn; rewrite length_app, repeat_length, Hla; lia] | split].
    + apply wf_lits_bound_app;
        [exact (wf_lits_bound_mono _ _ _ (proj1 Hs1) Hba)
         | exact (wf_lits_bound_repeat _ _ _ (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs1))))))].
    + exact Hwf_p.
  - split.
    + unfold eval_rail_psn; cbn [rbv_psn]; rewrite Hev_p; f_equal.
      unfold nneg_l; destruct nneg;
        [cbn [andb]; rewrite (eval_msb_lit fw asg a (conj Hwa Hla)), signed_lt_zero_eq_msb; reflexivity
         | exact (sat_eval_lit_false asg _ Hsat)].
    + unfold eval_rail_val at 1; cbn [rbv_bits].
      rewrite map_app, map_repeat_eq, (sat_eval_lit_false asg1 st' (proj2 (proj2 Hs1))),
              (step_spec_eval_lits st st' asg asg1 (rbv_bits a) Hs1 Hba),
              bools_to_Z_app, bools_to_Z_repeat_false, Z.mul_0_r, Z.add_0_r,
              (unsigned_eval_rail_val fw asg a Hla); reflexivity.
Qed.

Definition blast_sext_rail (fw tw : positive) (a : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let msb := msb_lit a in
  let bits := rbv_bits a ++ List.repeat msb (Pos.to_nat tw - Pos.to_nat fw) in
  (mk_rail_bv tw bits (rbv_psn a), st).

Theorem blast_sext_rail_step : forall fw tw a asg st out st',
  (fw < tw)%positive ->
  sat_blast_st asg st ->
  wf_rail_bound fw (bs_next_var st) a ->
  blast_sext_rail fw tw a st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_rail_bound tw (bs_next_var st') out /\
    eval_rail_psn asg' out = eval_rail_psn asg a /\
    eval_rail_val tw asg' out =
      @Integers.repr tw (@Integers.signed fw (eval_rail_val fw asg a)).
Proof.
  intros fw tw a asg st out st' Hlt Hsat ([Hwa Hla] & Hba & Hpa) Hbl.
  unfold blast_sext_rail in Hbl; inversion Hbl; subst out st'; clear Hbl.
  exists asg; split; [exact (step_spec_refl _ asg Hsat) | split].
  - split; [split; [reflexivity | cbn; rewrite length_app, repeat_length, Hla; lia] | split].
    + apply wf_lits_bound_app;
        [exact Hba
         | exact (wf_lits_bound_repeat _ _ _
                    (wf_msb_lit fw _ a (proj1 (proj1 Hsat)) (conj (conj Hwa Hla) (conj Hba Hpa))))].
    + exact Hpa.
  - split; [reflexivity |].
    unfold eval_rail_val at 1; cbn [rbv_bits].
    rewrite map_app, map_repeat_eq, (eval_msb_lit fw asg a (conj Hwa Hla)),
            bools_to_Z_app, bools_to_Z_repeat_b, length_map, Hla, positive_nat_Z.
    set (va := eval_rail_val fw asg a).
    rewrite <- (unsigned_eval_rail_val fw asg a Hla); fold va.
    replace (Z.of_nat (Pos.to_nat tw - Pos.to_nat fw)) with (Z.pos tw - Z.pos fw)%Z
      by (rewrite Nat2Z.inj_sub, !positive_nat_Z by lia; reflexivity).
    apply @Integers.eqm_samerepr.
    rewrite signed_eq_unsigned_msb, modulus_pow_sz.
    exists (b2z (msb_of fw va)).
    rewrite modulus_pow_sz.
    replace (2 ^ Z.pos tw)%Z with (2 ^ Z.pos fw * 2 ^ (Z.pos tw - Z.pos fw))%Z
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    ring.
Qed.

Definition blast_trunc_rail (nuw nsw : bool) (fw tw : positive) (a : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let lo := List.firstn (Pos.to_nat tw) (rbv_bits a) in
  let hi := List.skipn (Pos.to_nat tw) (rbv_bits a) in
  let '(nuw_l, st1) := if nuw then emit_or_list_opt hi st else (lit_false, st) in
  let '(nsw_l, st3) :=
      if nsw then
        let s_lo := List.nth (Pos.to_nat tw - 1) lo lit_false in
        let '(xhs, st2) := emit_xor_const_lits s_lo hi st1 in
        emit_or_list_opt xhs st2
      else (lit_false, st1) in
  let '(ov_psn, st4) := emit_or2_opt nuw_l nsw_l st3 in
  let '(psn, st5)    := emit_or2_opt (rbv_psn a) ov_psn st4 in
  (mk_rail_bv tw lo psn, st5).

Theorem blast_trunc_rail_step : forall nuw nsw fw tw a asg st out st',
  (tw < fw)%positive ->
  sat_blast_st asg st ->
  wf_rail_bound fw (bs_next_var st) a ->
  blast_trunc_rail nuw nsw fw tw a st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_rail_bound tw (bs_next_var st') out /\
    eval_rail_psn asg' out =
      (eval_rail_psn asg a ||
       (let va := eval_rail_val fw asg a in
        let res := @Integers.repr tw (@Integers.unsigned fw va) in
        (nuw && negb (Z.eqb (@Integers.unsigned tw res) (@Integers.unsigned fw va))) ||
        (nsw && negb (Z.eqb (@Integers.signed tw res) (@Integers.signed fw va))))) /\
    eval_rail_val tw asg' out =
      @Integers.repr tw (@Integers.unsigned fw (eval_rail_val fw asg a)).
Proof.
  intros nuw nsw fw tw a asg st out st' Hlt Hsat ([Hwa Hla] & Hba & Hpa) Hbl.
  unfold blast_trunc_rail in Hbl; cbn zeta in Hbl.
  set (lo := List.firstn (Pos.to_nat tw) (rbv_bits a)) in *.
  set (hi := List.skipn (Pos.to_nat tw) (rbv_bits a)) in *.
  set (ba := List.map (eval_lit asg) (rbv_bits a)).
  set (b_lo := List.firstn (Pos.to_nat tw) ba).
  set (b_hi := List.skipn (Pos.to_nat tw) ba).
  assert (Hw_hi : wf_lits_bound (bs_next_var st) hi) by exact (wf_lits_bound_skipn _ _ _ Hba).
  assert (Hnuw_step :
            exists nuw_l st1 asg1,
              (if nuw then emit_or_list_opt hi st else (lit_false, st)) = (nuw_l, st1) /\
              step_spec st st1 asg asg1 /\
              wf_lit_bound (bs_next_var st1) nuw_l /\
              eval_lit asg1 nuw_l = (nuw && existsb (fun x : bool => x) b_hi)).
  { destruct nuw.
    - destruct (emit_or_list_opt hi st) as [nl st1] eqn:Enl.
      destruct (emit_or_list_opt_step hi asg st nl st1 Hw_hi Hsat Enl)
        as (a1 & Hs1 & Hw_nl & Hev_nl).
      exists nl, st1, a1;
        split; [reflexivity | split; [exact Hs1 | split; [exact Hw_nl |]]].
      cbn [andb]; rewrite Hev_nl; unfold hi, b_hi, ba; rewrite map_skipn_eq; reflexivity.
    - exists lit_false, st, asg;
        split; [reflexivity |
        split; [exact (step_spec_refl _ asg Hsat) |
        split; [exact (wf_lit_bound_false _ (proj1 (proj1 Hsat))) |
                exact (sat_eval_lit_false asg _ Hsat)]]]. }
  destruct Hnuw_step as (nuw_l & st1 & asg1 & Hnuw_eq & Hs1 & Hwf_nuw & Hev_nuw).
  cbn iota zeta in Hnuw_eq, Hbl; rewrite Hnuw_eq in Hbl; cbn iota zeta in Hbl; clear Hnuw_eq.
  set (b_slo := List.nth (Pos.to_nat tw - 1) b_lo false).
  assert (Hnsw_step :
            exists nsw_l st3 asg3,
              (if nsw then
                 let s_lo := List.nth (Pos.to_nat tw - 1) lo lit_false in
                 let '(xhs, st2) := emit_xor_const_lits s_lo hi st1 in
                 emit_or_list_opt xhs st2
               else (lit_false, st1)) = (nsw_l, st3) /\
              step_spec st1 st3 asg1 asg3 /\
              wf_lit_bound (bs_next_var st3) nsw_l /\
              eval_lit asg3 nsw_l = (nsw && existsb (xorb b_slo) b_hi)).
  { destruct nsw.
    - cbn zeta; set (s_lo := List.nth (Pos.to_nat tw - 1) lo lit_false).
      assert (Hw_slo0 : wf_lit_bound (bs_next_var st) s_lo)
        by exact (wf_lits_bound_nth _ _ lo lit_false (wf_lits_bound_firstn _ _ _ Hba)
                    (wf_lit_bound_false _ (proj1 (proj1 Hsat)))).
      destruct (emit_xor_const_lits s_lo hi st1) as [xhs st2] eqn:Exhs.
      destruct (emit_or_list_opt xhs st2) as [nl st3] eqn:Enl.
      destruct (emit_xor_const_lits_step s_lo hi asg1 st1 xhs st2
                  (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hw_slo0)
                  (wf_lits_bound_mono _ _ _ (proj1 Hs1) Hw_hi)
                  (proj2 (proj2 Hs1)) Exhs)
        as (a2 & Hs12 & Hw_xhs & Hev_xhs).
      destruct (emit_or_list_opt_step xhs a2 st2 nl st3 Hw_xhs (proj2 (proj2 Hs12)) Enl)
        as (a3 & Hs23 & Hw_nl & Hev_nl).
      pose proof (step_spec_trans st1 st2 st3 asg1 a2 a3 Hs12 Hs23) as Hs13.
      exists nl, st3, a3; split; [reflexivity | split; [exact Hs13 | split; [exact Hw_nl |]]].
      cbn [andb]; rewrite Hev_nl, Hev_xhs, existsb_id_map_f,
        (step_spec_eval_lit st st1 asg asg1 s_lo Hs1 Hw_slo0),
        (step_spec_eval_lits st st1 asg asg1 hi Hs1 Hw_hi).
      unfold hi, b_hi, ba; rewrite map_skipn_eq.
      assert (Hev_slo : eval_lit asg s_lo = b_slo).
      { unfold s_lo, b_slo, b_lo, lo, ba.
        pose proof (Pos2Nat.is_pos tw) as Hptw.
        rewrite <- (map_nth (eval_lit asg) (List.firstn (Pos.to_nat tw) (rbv_bits a)) lit_false
                       (Pos.to_nat tw - 1)), map_firstn_eq.
        apply nth_indep; rewrite len_firstn_le by (rewrite length_map, Hla; lia); lia. }
      rewrite Hev_slo; reflexivity.
    - exists lit_false, st1, asg1;
        split; [reflexivity |
        split; [exact (step_spec_refl st1 asg1 (proj2 (proj2 Hs1))) |
        split; [exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs1))))) |
                exact (sat_eval_lit_false asg1 st1 (proj2 (proj2 Hs1)))]]]. }
  destruct Hnsw_step as (nsw_l & st3 & asg3 & Hnsw_eq & Hs13 & Hwf_nsw & Hev_nsw).
  cbn iota zeta in Hnsw_eq, Hbl; rewrite Hnsw_eq in Hbl; cbn iota zeta in Hbl; clear Hnsw_eq.
  destruct (emit_or2_opt nuw_l nsw_l st3) as [ov_psn st4] eqn:Eov.
  destruct (emit_or2_opt (rbv_psn a) ov_psn st4) as [psn st5] eqn:Ep.
  inversion Hbl; subst out st5; clear Hbl.
  destruct (emit_or2_opt_step asg3 nuw_l nsw_l st3 ov_psn st4 (proj2 (proj2 Hs13))
              (wf_lit_bound_mono _ _ _ (proj1 Hs13) Hwf_nuw) Hwf_nsw Eov)
    as (asg4 & Hs34 & Hwf_ov & Hev_ov).
  pose proof (step_spec_trans st st1 st3 asg asg1 asg3 Hs1 Hs13) as Hs03.
  pose proof (step_spec_trans st st3 st4 asg asg3 asg4 Hs03 Hs34) as Hs04.
  destruct (emit_or2_opt_step asg4 (rbv_psn a) ov_psn st4 psn st' (proj2 (proj2 Hs34))
              (wf_lit_bound_mono _ _ _ (proj1 Hs04) Hpa) Hwf_ov Ep)
    as (asg5 & Hs45 & Hwf_p & Hev_p).
  pose proof (step_spec_trans st st4 st' asg asg4 asg5 Hs04 Hs45) as Hs05.
  set (va := eval_rail_val fw asg a).
  set (res := @Integers.repr tw (@Integers.unsigned fw va)).
  assert (Hlo_len : List.length b_lo = Pos.to_nat tw)
    by (unfold b_lo, ba; apply len_firstn_le; rewrite length_map, Hla; lia).
  assert (Hhi_len : List.length b_hi = (Pos.to_nat fw - Pos.to_nat tw)%nat)
    by (unfold b_hi, ba; rewrite len_skipn_eq, length_map, Hla; reflexivity).
  assert (Hua_split : (@Integers.unsigned fw va =
                       bools_to_Z b_lo + 2 ^ Z.pos tw * bools_to_Z b_hi)%Z).
  { unfold va; rewrite (unsigned_eval_rail_val fw asg a Hla); fold ba.
    rewrite <- (firstn_skipn_eq (Pos.to_nat tw) ba) at 1; fold b_lo b_hi.
    rewrite bools_to_Z_app, Hlo_len, positive_nat_Z; reflexivity. }
  assert (Hres_eq : @Integers.repr tw (bools_to_Z b_lo) = res).
  { unfold res; rewrite Hua_split; apply @Integers.eqm_samerepr.
    exists (- bools_to_Z b_hi)%Z; rewrite modulus_pow_sz; ring. }
  assert (Hures : @Integers.unsigned tw res = bools_to_Z b_lo).
  { rewrite <- Hres_eq; apply @Integers.unsigned_repr.
    pose proof (bools_to_Z_range b_lo) as Hr; rewrite Hlo_len, positive_nat_Z, <- modulus_pow_sz in Hr.
    unfold Integers.max_unsigned; lia. }
  exists asg5; split; [exact Hs05 | split].
  - split; [split; [reflexivity | cbn; unfold lo; apply len_firstn_le; rewrite Hla; lia] |
            split; [exact (wf_lits_bound_mono _ _ _ (proj1 Hs05) (wf_lits_bound_firstn _ _ _ Hba))
                    | exact Hwf_p]].
  - split.
    + unfold eval_rail_psn; cbn [rbv_psn]; cbn zeta; fold va res.
      rewrite Hev_p,
              (step_spec_eval_lit st st4 asg asg4 (rbv_psn a) Hs04 Hpa),
              Hev_ov,
              (step_spec_eval_lit st1 st3 asg1 asg3 nuw_l Hs13 Hwf_nuw),
              Hev_nuw, Hev_nsw.
      f_equal; f_equal.
      * f_equal; rewrite Hua_split, Hures;
          replace (existsb (fun x : bool => x) b_hi) with (negb (bools_to_Z b_hi =? 0)%Z)
            by (rewrite bools_to_Z_zero_iff, Bool.negb_involutive; reflexivity).
        pose proof (@Integers.modulus_pos tw) as Hmpt; rewrite modulus_pow_sz in Hmpt.
        destruct (Z.eqb_spec (bools_to_Z b_hi) 0%Z),
                 (Z.eqb_spec (bools_to_Z b_lo) (bools_to_Z b_lo + 2 ^ Z.pos tw * bools_to_Z b_hi));
          cbn [negb]; try reflexivity; nia.
      * f_equal.
        assert (Hmsb_res : msb_of tw res = b_slo).
        { unfold msb_of, b_slo.
          assert (Hb_res : bit_int_to_bools tw res = b_lo).
          { apply bools_to_Z_inj; [rewrite bit_int_to_bools_length, Hlo_len; reflexivity |].
            rewrite bools_to_Z_bit_int_to_bools; exact Hures. }
          rewrite Hb_res; reflexivity. }
        set (k := (Pos.to_nat fw - Pos.to_nat tw)%nat) in *.
        assert (Hk_pos : (1 <= k)%nat) by lia.
        assert (Hmsb_va : msb_of fw va = List.nth (k - 1) b_hi false).
        { unfold msb_of; assert (Hba_eq : bit_int_to_bools fw va = ba)
            by (symmetry; exact (map_eval_lit_eq_bit_int_to_bools fw asg a Hla)).
          rewrite Hba_eq, <- (firstn_skipn_eq (Pos.to_nat tw) ba); fold b_lo b_hi.
          rewrite nth_app_r by (rewrite Hlo_len; lia).
          rewrite Hlo_len; f_equal; lia. }
        rewrite (signed_eq_unsigned_msb tw res), (signed_eq_unsigned_msb fw va),
                Hmsb_res, Hmsb_va, Hures, Hua_split, !modulus_pow_sz.
        replace (2 ^ Z.pos fw)%Z with (2 ^ Z.pos tw * 2 ^ Z.of_nat k)%Z
          by (rewrite <- Z.pow_add_r by lia; f_equal; unfold k;
              rewrite Nat2Z.inj_sub, !positive_nat_Z by lia; lia).
        pose proof (bools_to_Z_range b_hi) as Hhi_r; rewrite Hhi_len in Hhi_r.
        pose proof (@Integers.modulus_pos tw) as Hmpt; rewrite modulus_pow_sz in Hmpt.
        assert (Hk2 : (2 <= 2 ^ Z.of_nat k)%Z)
          by (replace (Z.of_nat k) with (Z.succ (Z.of_nat (k - 1))) by lia;
              rewrite Z.pow_succ_r by lia; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat (k - 1))); lia).
        set (b_sfa := List.nth (k - 1) b_hi false).
        assert (Hin_sfa : In b_sfa b_hi)
          by (unfold b_sfa; apply nth_In; rewrite Hhi_len; lia).
        assert (Hrep := bools_to_Z_eq_repeat_iff b_hi b_slo); rewrite Hhi_len in Hrep.
        destruct b_sfa eqn:Esfa, b_slo eqn:Eslo.
        -- replace (existsb (xorb true) b_hi) with (negb (bools_to_Z b_hi =? b2z true * (2 ^ Z.of_nat k - 1))%Z)
             by (rewrite Hrep, Bool.negb_involutive; reflexivity).
           cbn [b2z];
             destruct (Z.eqb_spec (bools_to_Z b_hi) (1 * (2 ^ Z.of_nat k - 1))),
                      (Z.eqb_spec (bools_to_Z b_lo - 1 * 2 ^ Z.pos tw)
                                  (bools_to_Z b_lo + 2 ^ Z.pos tw * bools_to_Z b_hi -
                                   1 * (2 ^ Z.pos tw * 2 ^ Z.of_nat k)));
             cbn [negb]; try reflexivity; nia.
        -- assert (Hex_t : existsb (xorb false) b_hi = true)
             by (apply existsb_exists; exists true; split; [exact Hin_sfa | reflexivity]).
           rewrite Hex_t; cbn [b2z];
             destruct (Z.eqb_spec (bools_to_Z b_lo - 0 * 2 ^ Z.pos tw)
                                  (bools_to_Z b_lo + 2 ^ Z.pos tw * bools_to_Z b_hi -
                                   1 * (2 ^ Z.pos tw * 2 ^ Z.of_nat k)));
             [nia | reflexivity].
        -- assert (Hex_t : existsb (xorb true) b_hi = true)
             by (apply existsb_exists; exists false; split; [exact Hin_sfa | reflexivity]).
           rewrite Hex_t; cbn [b2z];
             destruct (Z.eqb_spec (bools_to_Z b_lo - 1 * 2 ^ Z.pos tw)
                                  (bools_to_Z b_lo + 2 ^ Z.pos tw * bools_to_Z b_hi -
                                   0 * (2 ^ Z.pos tw * 2 ^ Z.of_nat k)));
             [nia | reflexivity].
        -- replace (existsb (xorb false) b_hi) with (negb (bools_to_Z b_hi =? b2z false * (2 ^ Z.of_nat k - 1))%Z)
             by (rewrite Hrep, Bool.negb_involutive; reflexivity).
           cbn [b2z];
             destruct (Z.eqb_spec (bools_to_Z b_hi) (0 * (2 ^ Z.of_nat k - 1))),
                      (Z.eqb_spec (bools_to_Z b_lo - 0 * 2 ^ Z.pos tw)
                                  (bools_to_Z b_lo + 2 ^ Z.pos tw * bools_to_Z b_hi -
                                   0 * (2 ^ Z.pos tw * 2 ^ Z.of_nat k)));
             cbn [negb]; try reflexivity; nia.
    + unfold eval_rail_val at 1; cbn [rbv_bits].
      unfold lo; rewrite (step_spec_eval_lits st st' asg asg5 _ Hs05 (wf_lits_bound_firstn _ _ _ Hba)),
                         map_firstn_eq; exact Hres_eq.
Qed.

Fixpoint emit_ult_borrow (bin : lit) (xs ys : list lit) (st : blast_state)
  {struct xs} : lit * blast_state :=
  match xs, ys with
  | x :: rx, y :: ry =>
      let '(nx_y, st1)   := emit_and2_opt (neg_lit x) y st in
      let '(xy_xor, st2) := emit_xor2_opt x y st1 in
      let '(eq_b, st3)   := emit_and2_opt (neg_lit xy_xor) bin st2 in
      let '(b1, st4)     := emit_or2_opt nx_y eq_b st3 in
      emit_ult_borrow b1 rx ry st4
  | _, _ => (bin, st)
  end.

Lemma emit_ult_borrow_step : forall xs ys bin asg st out st',
  List.length xs = List.length ys ->
  wf_lit_bound (bs_next_var st) bin ->
  wf_lits_bound (bs_next_var st) xs ->
  wf_lits_bound (bs_next_var st) ys ->
  sat_blast_st asg st ->
  emit_ult_borrow bin xs ys st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_lit_bound (bs_next_var st') out /\
    eval_lit asg' out =
      (bools_to_Z (List.map (eval_lit asg) xs) <?
       bools_to_Z (List.map (eval_lit asg) ys) + b2z (eval_lit asg bin))%Z.
Proof.
  induction xs as [| x rx IH]; intros [| y ry] bin asg st out st' Hlen Hbin Hwx Hwy Hsat He;
    try discriminate; cbn [emit_ult_borrow] in He.
  - inversion He; subst out st'; exists asg; split;
      [exact (step_spec_refl _ asg Hsat) | split; [exact Hbin |]].
    destruct (eval_lit asg bin); reflexivity.
  - inversion Hwx as [| ? ? Hx Hwrx]; subst.
    inversion Hwy as [| ? ? Hy Hwry]; subst.
    injection Hlen as Hlen'.
    destruct (emit_and2_opt (neg_lit x) y st) as [nx_y st1] eqn:Eg1.
    destruct (emit_xor2_opt x y st1) as [xy_xor st2] eqn:Eg2.
    destruct (emit_and2_opt (neg_lit xy_xor) bin st2) as [eq_b st3] eqn:Eg3.
    destruct (emit_or2_opt nx_y eq_b st3) as [b1 st4] eqn:Eg4.
    destruct (emit_and2_opt_step asg (neg_lit x) y st nx_y st1 Hsat
                (wf_lit_bound_neg _ x Hx) Hy Eg1)
      as (asg1 & Hs1 & Hw_nxy & Hev_nxy).
    destruct (emit_xor2_opt_step asg1 x y st1 xy_xor st2 (proj2 (proj2 Hs1))
                (wf_lit_bound_mono _ _ x (proj1 Hs1) Hx)
                (wf_lit_bound_mono _ _ y (proj1 Hs1) Hy) Eg2)
      as (asg2 & Hs2 & Hw_xx & Hev_xx).
    pose proof (step_spec_trans st st1 st2 asg asg1 asg2 Hs1 Hs2) as Hs02.
    destruct (emit_and2_opt_step asg2 (neg_lit xy_xor) bin st2 eq_b st3 (proj2 (proj2 Hs2))
                (wf_lit_bound_neg _ _ Hw_xx)
                (wf_lit_bound_mono _ _ bin (proj1 Hs02) Hbin) Eg3)
      as (asg3 & Hs3 & Hw_eqb & Hev_eqb).
    pose proof (step_spec_trans st1 st2 st3 asg1 asg2 asg3 Hs2 Hs3) as Hs13.
    destruct (emit_or2_opt_step asg3 nx_y eq_b st3 b1 st4 (proj2 (proj2 Hs3))
                (wf_lit_bound_mono _ _ _ (proj1 Hs13) Hw_nxy) Hw_eqb Eg4)
      as (asg4 & Hs4 & Hw_b1 & Hev_b1).
    pose proof (step_spec_trans st st2 st3 asg asg2 asg3 Hs02 Hs3) as Hs03.
    pose proof (step_spec_trans st st3 st4 asg asg3 asg4 Hs03 Hs4) as Hs04.
    destruct (IH ry b1 asg4 st4 out st' Hlen' Hw_b1
                (wf_lits_bound_mono _ _ _ (proj1 Hs04) Hwrx)
                (wf_lits_bound_mono _ _ _ (proj1 Hs04) Hwry)
                (proj2 (proj2 Hs4)) He)
      as (asg5 & Hs5 & Hw_out & Hev_out).
    exists asg5; split; [exact (step_spec_trans st st4 st' asg asg4 asg5 Hs04 Hs5) | split; [exact Hw_out |]].
    cbn [List.map]; rewrite !bools_to_Z_cons, Hev_out,
      (step_spec_eval_lits st st4 asg asg4 rx Hs04 Hwrx),
      (step_spec_eval_lits st st4 asg asg4 ry Hs04 Hwry),
      Hev_b1,
      (step_spec_eval_lit st1 st3 asg1 asg3 nx_y Hs13 Hw_nxy),
      Hev_nxy,
      (eval_neg_lit_nonzero asg x (wf_lit_bound_nonzero _ x Hx)),
      Hev_eqb,
      (eval_neg_lit_nonzero asg2 xy_xor (wf_lit_bound_nonzero _ _ Hw_xx)),
      Hev_xx,
      (step_spec_eval_lit st st1 asg asg1 x Hs1 Hx),
      (step_spec_eval_lit st st1 asg asg1 y Hs1 Hy),
      (step_spec_eval_lit st st2 asg asg2 bin Hs02 Hbin).
    destruct (eval_lit asg x), (eval_lit asg y), (eval_lit asg bin);
      cbn [negb xorb andb orb b2z];
      repeat match goal with |- context [(?u <? ?v)%Z] => destruct (Z.ltb_spec u v) end;
      try reflexivity; lia.
Qed.

Definition flip_msb_rail_bits (sz : positive) (r : rail_bv) : list lit :=
  List.firstn (Pos.to_nat sz - 1) (rbv_bits r) ++ [neg_lit (msb_lit r)].

Lemma flip_msb_rail_bits_eval : forall sz asg st r,
  sat_blast_st asg st ->
  wf_rail_bound sz (bs_next_var st) r ->
  List.length (flip_msb_rail_bits sz r) = Pos.to_nat sz /\
  wf_lits_bound (bs_next_var st) (flip_msb_rail_bits sz r) /\
  bools_to_Z (List.map (eval_lit asg) (flip_msb_rail_bits sz r)) =
  (@Integers.signed sz (eval_rail_val sz asg r) + @Integers.half_modulus sz)%Z.
Proof.
  intros sz asg st r Hsat ([Hwr Hlr] & Hbr & Hpr).
  pose proof (Pos2Nat.is_pos sz) as Hpos.
  pose proof (proj1 (proj1 Hsat)) as Hge2.
  assert (Hw_msb : wf_lit_bound (bs_next_var st) (msb_lit r))
    by exact (wf_msb_lit sz _ r Hge2 (conj (conj Hwr Hlr) (conj Hbr Hpr))).
  split.
  - unfold flip_msb_rail_bits; rewrite length_app, len_firstn_le by lia; cbn; lia.
  - split.
    + unfold flip_msb_rail_bits; apply wf_lits_bound_app;
        [exact (wf_lits_bound_firstn _ _ _ Hbr)
         | constructor; [exact (wf_lit_bound_neg _ _ Hw_msb) | constructor]].
    + unfold flip_msb_rail_bits; rewrite map_app, map_firstn_eq; cbn [List.map].
      rewrite (eval_neg_lit_nonzero asg (msb_lit r) (wf_lit_bound_nonzero _ _ Hw_msb)),
              (eval_msb_lit sz asg r (conj Hwr Hlr)).
      set (vr := eval_rail_val sz asg r).
      set (br := List.map (eval_lit asg) (rbv_bits r)).
      assert (Hbr_len : List.length br = Pos.to_nat sz)
        by (unfold br; rewrite length_map; exact Hlr).
      assert (Hlo_len : List.length (List.firstn (Pos.to_nat sz - 1) br) = (Pos.to_nat sz - 1)%nat)
        by (apply len_firstn_le; lia).
      assert (Hskip_one : List.skipn (Pos.to_nat sz - 1) br = [msb_of sz vr]).
      { assert (Hsl : List.length (List.skipn (Pos.to_nat sz - 1) br) = 1%nat)
          by (rewrite len_skipn_eq, Hbr_len; lia).
        destruct (List.skipn (Pos.to_nat sz - 1) br) as [| b0 [| b1 r1]] eqn:Esk;
          try discriminate Hsl.
        f_equal.
        change b0 with (List.nth 0 [b0] false); rewrite <- Esk, nth_skipn_eq, Nat.add_0_r.
        unfold br; rewrite (map_eval_lit_eq_bit_int_to_bools sz asg r Hlr); reflexivity. }
      assert (Hur : (@Integers.unsigned sz vr =
                     bools_to_Z (List.firstn (Pos.to_nat sz - 1) br) +
                     2 ^ Z.of_nat (Pos.to_nat sz - 1) * b2z (msb_of sz vr))%Z).
      { unfold vr at 1; rewrite (unsigned_eval_rail_val sz asg r Hlr); fold br.
        rewrite <- (firstn_skipn_eq (Pos.to_nat sz - 1) br) at 1;
        rewrite Hskip_one, bools_to_Z_app, Hlo_len, bools_to_Z_cons; cbn [bools_to_Z]; nia. }
      assert (Hhm_pow : (2 ^ Z.of_nat (Pos.to_nat sz - 1) = @Integers.half_modulus sz)%Z).
      { pose proof (@Integers.half_modulus_modulus sz) as Hhm.
        rewrite modulus_pow_sz, <- (positive_nat_Z sz) in Hhm.
        replace (Pos.to_nat sz) with (S (Pos.to_nat sz - 1)) in Hhm by lia.
        rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hhm by lia; lia. }
      rewrite bools_to_Z_app, Hlo_len, bools_to_Z_cons; cbn [bools_to_Z].
      rewrite (signed_eq_unsigned_msb sz vr), (@Integers.half_modulus_modulus sz), Hur, Hhm_pow.
      destruct (msb_of sz vr); cbn [b2z negb]; nia.
Qed.

Definition emit_cmp_lt_rail (is_signed : bool) (sz : positive) (a b : rail_bv) (st : blast_state)
  : lit * blast_state :=
  if is_signed
  then emit_ult_borrow lit_false (flip_msb_rail_bits sz a) (flip_msb_rail_bits sz b) st
  else emit_ult_borrow lit_false (rbv_bits a) (rbv_bits b) st.

Lemma emit_cmp_lt_rail_step : forall is_signed sz a b asg st out st',
  sat_blast_st asg st ->
  wf_rail_bound sz (bs_next_var st) a ->
  wf_rail_bound sz (bs_next_var st) b ->
  emit_cmp_lt_rail is_signed sz a b st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_lit_bound (bs_next_var st') out /\
    eval_lit asg' out =
      (if is_signed
       then @Integers.lt sz (eval_rail_val sz asg a) (eval_rail_val sz asg b)
       else @Integers.ltu sz (eval_rail_val sz asg a) (eval_rail_val sz asg b)).
Proof.
  intros is_signed sz a b asg st out st' Hsat Hwa Hwb He.
  unfold emit_cmp_lt_rail in He.
  destruct is_signed.
  - destruct (flip_msb_rail_bits_eval sz asg st a Hsat Hwa) as (Hla & Hwfa & Hza).
    destruct (flip_msb_rail_bits_eval sz asg st b Hsat Hwb) as (Hlb & Hwfb & Hzb).
    destruct (emit_ult_borrow_step _ _ lit_false asg st out st'
                (eq_trans Hla (eq_sym Hlb))
                (wf_lit_bound_false _ (proj1 (proj1 Hsat)))
                Hwfa Hwfb Hsat He)
      as (asg1 & Hs1 & Hwf_out & Hev_out).
    exists asg1; split; [exact Hs1 | split; [exact Hwf_out |]].
    rewrite Hev_out, (sat_eval_lit_false asg _ Hsat), Hza, Hzb; cbn [b2z].
    unfold Integers.lt.
    match goal with |- context [(?u <? ?v)%Z] => destruct (Z.ltb_spec u v) end;
      destruct (Numeric.Rocqlib.zlt _ _); try reflexivity; lia.
  - destruct Hwa as ([_ Hla] & Hba & _), Hwb as ([_ Hlb] & Hbb & _).
    destruct (emit_ult_borrow_step _ _ lit_false asg st out st'
                (eq_trans Hla (eq_sym Hlb))
                (wf_lit_bound_false _ (proj1 (proj1 Hsat)))
                Hba Hbb Hsat He)
      as (asg1 & Hs1 & Hwf_out & Hev_out).
    exists asg1; split; [exact Hs1 | split; [exact Hwf_out |]].
    rewrite Hev_out, (sat_eval_lit_false asg _ Hsat),
            <- (unsigned_eval_rail_val sz asg a Hla),
            <- (unsigned_eval_rail_val sz asg b Hlb); cbn [b2z].
    unfold Integers.ltu.
    match goal with |- context [(?u <? ?v)%Z] => destruct (Z.ltb_spec u v) end;
      destruct (Numeric.Rocqlib.zlt _ _); try reflexivity; lia.
Qed.

Definition blast_icmp_rail
  (ss is_signed : bool) (c : Integers.comparison) (sz : positive) (a b : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let '(res_bit, st2) :=
      match c with
      | Integers.Ceq =>
          let '(xb, st1) := map2_emit emit_xor2_opt (rbv_bits a) (rbv_bits b) st in
          let '(df, st2) := emit_or_list_opt xb st1 in
          (neg_lit df, st2)
      | Integers.Cne =>
          let '(xb, st1) := map2_emit emit_xor2_opt (rbv_bits a) (rbv_bits b) st in
          emit_or_list_opt xb st1
      | Integers.Clt =>
          emit_cmp_lt_rail is_signed sz a b st
      | Integers.Cle =>
          let '(gt_b, st1) := emit_cmp_lt_rail is_signed sz b a st in
          (neg_lit gt_b, st1)
      | Integers.Cgt =>
          emit_cmp_lt_rail is_signed sz b a st
      | Integers.Cge =>
          let '(lt_b, st1) := emit_cmp_lt_rail is_signed sz a b st in
          (neg_lit lt_b, st1)
      end in
  let '(ss_l, st3)   := if ss then emit_xor2_opt (msb_lit a) (msb_lit b) st2 else (lit_false, st2) in
  let '(ab_psn, st4) := emit_or2_opt (rbv_psn a) (rbv_psn b) st3 in
  let '(psn, st5)    := emit_or2_opt ab_psn ss_l st4 in
  (mk_rail_bv 1%positive [res_bit] psn, st5).

Lemma eq_rail_xor_spec : forall sz assign a b,
  wf_rail_bv sz a ->
  wf_rail_bv sz b ->
  existsb (fun x : bool => x)
          (list_map2 xorb (List.map (eval_lit assign) (rbv_bits a))
                          (List.map (eval_lit assign) (rbv_bits b))) =
  negb (@Integers.eq sz (eval_rail_val sz assign a) (eval_rail_val sz assign b)).
Proof.
  intros sz assign a b [Hwa Hla] [Hwb Hlb].
  set (ba := List.map (eval_lit assign) (rbv_bits a)).
  set (bb := List.map (eval_lit assign) (rbv_bits b)).
  assert (Hlen_ab : List.length ba = List.length bb)
    by (unfold ba, bb; rewrite !length_map; congruence).
  destruct (existsb (fun x : bool => x) (list_map2 xorb ba bb)) eqn:Hex.
  - apply existsb_exists in Hex as [z [Hin Hz]]; subst z.
    destruct (In_nth _ _ false Hin) as [k [Hk Hnth]].
    rewrite list_map2_length in Hk by exact Hlen_ab.
    rewrite list_map2_nth in Hnth by assumption.
    assert (Hk_sz : (k < Pos.to_nat sz)%nat)
      by (unfold ba in Hk; rewrite length_map, Hla in Hk; exact Hk).
    unfold Integers.eq, Numeric.Rocqlib.zeq.
    destruct (Z.eq_dec (@Integers.unsigned sz (eval_rail_val sz assign a))
                       (@Integers.unsigned sz (eval_rail_val sz assign b))) as [Hu | _];
      [| reflexivity].
    assert (Heqv : eval_rail_val sz assign a = eval_rail_val sz assign b)
      by (rewrite <- (@Integers.repr_unsigned sz (eval_rail_val sz assign a)),
                  <- (@Integers.repr_unsigned sz (eval_rail_val sz assign b)), Hu; reflexivity).
    pose proof (eval_rail_val_testbit_nat sz assign a k Hk_sz) as Hta.
    pose proof (eval_rail_val_testbit_nat sz assign b k Hk_sz) as Htb.
    fold ba in Hta; fold bb in Htb; rewrite Heqv, Htb in Hta.
    rewrite <- Hta, Bool.xorb_nilpotent in Hnth; discriminate Hnth.
  - assert (Heqv : eval_rail_val sz assign a = eval_rail_val sz assign b).
    { apply @Integers.same_bits_eq; intros i Hi.
      rewrite !eval_rail_val_testbit by exact Hi; fold ba bb.
      assert (Hk : (Z.to_nat i < List.length ba)%nat)
        by (unfold ba; rewrite length_map, Hla; unfold Integers.zwordsize in Hi; lia).
      assert (Hx_f : xorb (List.nth (Z.to_nat i) ba false) (List.nth (Z.to_nat i) bb false) = false).
      { rewrite <- (list_map2_nth xorb ba bb (Z.to_nat i) Hlen_ab Hk).
        destruct (List.nth (Z.to_nat i) (list_map2 xorb ba bb) false) eqn:Enth; [| reflexivity].
        assert (Hex_t : existsb (fun x : bool => x) (list_map2 xorb ba bb) = true).
        { apply existsb_exists; exists true; split; [| reflexivity].
          rewrite <- Enth; apply nth_In; rewrite list_map2_length by exact Hlen_ab; exact Hk. }
        congruence. }
      apply (proj1 (xorb_false_iff _ _)) in Hx_f; exact Hx_f. }
    rewrite Heqv; unfold Integers.eq, Numeric.Rocqlib.zeq.
    destruct (Z.eq_dec _ _); [reflexivity | congruence].
Qed.

Theorem blast_icmp_rail_step : forall ss is_signed c sz a b asg st out st',
  sat_blast_st asg st ->
  wf_rail_bound sz (bs_next_var st) a ->
  wf_rail_bound sz (bs_next_var st) b ->
  blast_icmp_rail ss is_signed c sz a b st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_rail_bound 1%positive (bs_next_var st') out /\
    eval_rail_psn asg' out =
      ((eval_rail_psn asg a || eval_rail_psn asg b) ||
       (ss && xorb (msb_of sz (eval_rail_val sz asg a))
                   (msb_of sz (eval_rail_val sz asg b)))) /\
    eval_rail_val 1%positive asg' out =
      (if (if is_signed
           then @Integers.cmp sz c (eval_rail_val sz asg a) (eval_rail_val sz asg b)
           else @Integers.cmpu sz c (eval_rail_val sz asg a) (eval_rail_val sz asg b))
       then @Integers.one 1%positive
       else @Integers.zero 1%positive).
Proof.
  intros ss is_signed c sz a b asg st out st' Hsat Hwa Hwb Hbl.
  destruct Hwa as ([Hwa_w Hla] & Hba & Hpa), Hwb as ([Hwb_w Hlb] & Hbb & Hpb).
  assert (Hwa_f : wf_rail_bound sz (bs_next_var st) a)
    by exact (conj (conj Hwa_w Hla) (conj Hba Hpa)).
  assert (Hwb_f : wf_rail_bound sz (bs_next_var st) b)
    by exact (conj (conj Hwb_w Hlb) (conj Hbb Hpb)).
  unfold blast_icmp_rail in Hbl; cbn zeta in Hbl.
  assert (Hres_step :
            exists res_bit st2 asg2,
              match c with
              | Integers.Ceq =>
                  let '(xb, st1) := map2_emit emit_xor2_opt (rbv_bits a) (rbv_bits b) st in
                  let '(df, st2) := emit_or_list_opt xb st1 in
                  (neg_lit df, st2)
              | Integers.Cne =>
                  let '(xb, st1) := map2_emit emit_xor2_opt (rbv_bits a) (rbv_bits b) st in
                  emit_or_list_opt xb st1
              | Integers.Clt => emit_cmp_lt_rail is_signed sz a b st
              | Integers.Cle =>
                  let '(gt_b, st1) := emit_cmp_lt_rail is_signed sz b a st in
                  (neg_lit gt_b, st1)
              | Integers.Cgt => emit_cmp_lt_rail is_signed sz b a st
              | Integers.Cge =>
                  let '(lt_b, st1) := emit_cmp_lt_rail is_signed sz a b st in
                  (neg_lit lt_b, st1)
              end = (res_bit, st2) /\
              step_spec st st2 asg asg2 /\
              wf_lit_bound (bs_next_var st2) res_bit /\
              eval_lit asg2 res_bit =
                (if is_signed
                 then @Integers.cmp sz c (eval_rail_val sz asg a) (eval_rail_val sz asg b)
                 else @Integers.cmpu sz c (eval_rail_val sz asg a) (eval_rail_val sz asg b))).
  { destruct c.
    - (* Ceq *)
      destruct (map2_emit emit_xor2_opt (rbv_bits a) (rbv_bits b) st) as [xb st1] eqn:Exb.
      destruct (emit_or_list_opt xb st1) as [df st2] eqn:Edf.
      destruct (map2_emit_step emit_xor2_opt xorb emit_xor2_opt_step _ _ asg st xb st1
                  (eq_trans Hla (eq_sym Hlb)) Hba Hbb Hsat Exb)
        as (a1 & Hs1 & _ & Hw_xb & Hev_xb).
      destruct (emit_or_list_opt_step xb a1 st1 df st2 Hw_xb (proj2 (proj2 Hs1)) Edf)
        as (a2 & Hs2 & Hw_df & Hev_df).
      exists (neg_lit df), st2, a2; split; [reflexivity | split;
        [exact (step_spec_trans st st1 st2 asg a1 a2 Hs1 Hs2) | split;
         [exact (wf_lit_bound_neg _ _ Hw_df) |]]].
      rewrite (eval_neg_lit_nonzero a2 df (wf_lit_bound_nonzero _ _ Hw_df)),
              Hev_df, Hev_xb,
              (eq_rail_xor_spec sz asg a b (conj Hwa_w Hla) (conj Hwb_w Hlb)),
              Bool.negb_involutive.
      destruct is_signed; reflexivity.
    - (* Cne *)
      destruct (map2_emit emit_xor2_opt (rbv_bits a) (rbv_bits b) st) as [xb st1] eqn:Exb.
      destruct (emit_or_list_opt xb st1) as [df st2] eqn:Edf.
      destruct (map2_emit_step emit_xor2_opt xorb emit_xor2_opt_step _ _ asg st xb st1
                  (eq_trans Hla (eq_sym Hlb)) Hba Hbb Hsat Exb)
        as (a1 & Hs1 & _ & Hw_xb & Hev_xb).
      destruct (emit_or_list_opt_step xb a1 st1 df st2 Hw_xb (proj2 (proj2 Hs1)) Edf)
        as (a2 & Hs2 & Hw_df & Hev_df).
      exists df, st2, a2; split; [reflexivity | split;
        [exact (step_spec_trans st st1 st2 asg a1 a2 Hs1 Hs2) | split; [exact Hw_df |]]].
      rewrite Hev_df, Hev_xb, (eq_rail_xor_spec sz asg a b (conj Hwa_w Hla) (conj Hwb_w Hlb)).
      destruct is_signed; reflexivity.
    - (* Clt *)
      destruct (emit_cmp_lt_rail is_signed sz a b st) as [lt_b st2] eqn:Elt.
      destruct (emit_cmp_lt_rail_step is_signed sz a b asg st lt_b st2 Hsat Hwa_f Hwb_f Elt)
        as (a2 & Hs2 & Hw_lt & Hev_lt).
      exists lt_b, st2, a2; split; [reflexivity | split; [exact Hs2 | split; [exact Hw_lt |]]].
      rewrite Hev_lt; destruct is_signed; reflexivity.
    - (* Cle *)
      destruct (emit_cmp_lt_rail is_signed sz b a st) as [gt_b st2] eqn:Egt.
      destruct (emit_cmp_lt_rail_step is_signed sz b a asg st gt_b st2 Hsat Hwb_f Hwa_f Egt)
        as (a2 & Hs2 & Hw_gt & Hev_gt).
      exists (neg_lit gt_b), st2, a2; split; [reflexivity | split; [exact Hs2 | split;
        [exact (wf_lit_bound_neg _ _ Hw_gt) |]]].
      rewrite (eval_neg_lit_nonzero a2 gt_b (wf_lit_bound_nonzero _ _ Hw_gt)), Hev_gt;
        destruct is_signed; reflexivity.
    - (* Cgt *)
      destruct (emit_cmp_lt_rail is_signed sz b a st) as [gt_b st2] eqn:Egt.
      destruct (emit_cmp_lt_rail_step is_signed sz b a asg st gt_b st2 Hsat Hwb_f Hwa_f Egt)
        as (a2 & Hs2 & Hw_gt & Hev_gt).
      exists gt_b, st2, a2; split; [reflexivity | split; [exact Hs2 | split; [exact Hw_gt |]]].
      rewrite Hev_gt; destruct is_signed; reflexivity.
    - (* Cge *)
      destruct (emit_cmp_lt_rail is_signed sz a b st) as [lt_b st2] eqn:Elt.
      destruct (emit_cmp_lt_rail_step is_signed sz a b asg st lt_b st2 Hsat Hwa_f Hwb_f Elt)
        as (a2 & Hs2 & Hw_lt & Hev_lt).
      exists (neg_lit lt_b), st2, a2; split; [reflexivity | split; [exact Hs2 | split;
        [exact (wf_lit_bound_neg _ _ Hw_lt) |]]].
      rewrite (eval_neg_lit_nonzero a2 lt_b (wf_lit_bound_nonzero _ _ Hw_lt)), Hev_lt;
        destruct is_signed; reflexivity. }
  destruct Hres_step as (res_bit & st2 & asg2 & Hres_eq & Hs02 & Hwf_rb & Hev_rb).
  cbn iota zeta in Hres_eq, Hbl; rewrite Hres_eq in Hbl; cbn iota zeta in Hbl; clear Hres_eq.
  assert (Hss_step :
            exists ss_l st3 asg3,
              (if ss then emit_xor2_opt (msb_lit a) (msb_lit b) st2 else (lit_false, st2)) = (ss_l, st3) /\
              step_spec st2 st3 asg2 asg3 /\
              wf_lit_bound (bs_next_var st3) ss_l /\
              eval_lit asg3 ss_l =
                (ss && xorb (msb_of sz (eval_rail_val sz asg a))
                            (msb_of sz (eval_rail_val sz asg b)))).
  { destruct ss.
    - assert (Hw_ma : wf_lit_bound (bs_next_var st) (msb_lit a))
        by exact (wf_msb_lit sz _ a (proj1 (proj1 Hsat)) Hwa_f).
      assert (Hw_mb : wf_lit_bound (bs_next_var st) (msb_lit b))
        by exact (wf_msb_lit sz _ b (proj1 (proj1 Hsat)) Hwb_f).
      destruct (emit_xor2_opt (msb_lit a) (msb_lit b) st2) as [sl st3] eqn:Esl.
      destruct (emit_xor2_opt_step asg2 (msb_lit a) (msb_lit b) st2 sl st3 (proj2 (proj2 Hs02))
                  (wf_lit_bound_mono _ _ _ (proj1 Hs02) Hw_ma)
                  (wf_lit_bound_mono _ _ _ (proj1 Hs02) Hw_mb) Esl)
        as (a3 & Hs23 & Hw_sl & Hev_sl).
      exists sl, st3, a3; split; [reflexivity | split; [exact Hs23 | split; [exact Hw_sl |]]].
      cbn [andb]; rewrite Hev_sl,
        (step_spec_eval_lit st st2 asg asg2 (msb_lit a) Hs02 Hw_ma),
        (step_spec_eval_lit st st2 asg asg2 (msb_lit b) Hs02 Hw_mb),
        (eval_msb_lit sz asg a (conj Hwa_w Hla)),
        (eval_msb_lit sz asg b (conj Hwb_w Hlb)); reflexivity.
    - exists lit_false, st2, asg2;
        split; [reflexivity |
        split; [exact (step_spec_refl st2 asg2 (proj2 (proj2 Hs02))) |
        split; [exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs02))))) |
                exact (sat_eval_lit_false asg2 st2 (proj2 (proj2 Hs02)))]]]. }
  destruct Hss_step as (ss_l & st3 & asg3 & Hss_eq & Hs23 & Hwf_ss & Hev_ss).
  cbn iota zeta in Hss_eq, Hbl; rewrite Hss_eq in Hbl; cbn iota zeta in Hbl; clear Hss_eq.
  destruct (emit_or2_opt (rbv_psn a) (rbv_psn b) st3) as [ab_psn st4] eqn:Eab.
  destruct (emit_or2_opt ab_psn ss_l st4) as [psn st5] eqn:Ep.
  inversion Hbl; subst out st5; clear Hbl.
  pose proof (step_spec_trans st st2 st3 asg asg2 asg3 Hs02 Hs23) as Hs03.
  destruct (emit_or2_opt_step asg3 (rbv_psn a) (rbv_psn b) st3 ab_psn st4 (proj2 (proj2 Hs23))
              (wf_lit_bound_mono _ _ _ (proj1 Hs03) Hpa)
              (wf_lit_bound_mono _ _ _ (proj1 Hs03) Hpb) Eab)
    as (asg4 & Hs34 & Hwf_ab & Hev_ab).
  destruct (emit_or2_opt_step asg4 ab_psn ss_l st4 psn st' (proj2 (proj2 Hs34))
              Hwf_ab (wf_lit_bound_mono _ _ _ (proj1 Hs34) Hwf_ss) Ep)
    as (asg5 & Hs45 & Hwf_p & Hev_p).
  pose proof (step_spec_trans st3 st4 st' asg3 asg4 asg5 Hs34 Hs45) as Hs35.
  pose proof (step_spec_trans st2 st3 st' asg2 asg3 asg5 Hs23 Hs35) as Hs25.
  pose proof (step_spec_trans st st2 st' asg asg2 asg5 Hs02 Hs25) as Hs05.
  exists asg5; split; [exact Hs05 | split].
  - split; [split; [reflexivity | reflexivity] | split].
    + constructor; [exact (wf_lit_bound_mono _ _ _ (proj1 Hs25) Hwf_rb) | constructor].
    + exact Hwf_p.
  - split.
    + unfold eval_rail_psn; cbn [rbv_psn]; rewrite Hev_p, Hev_ab,
        (step_spec_eval_lit st st3 asg asg3 (rbv_psn a) Hs03 Hpa),
        (step_spec_eval_lit st st3 asg asg3 (rbv_psn b) Hs03 Hpb),
        (step_spec_eval_lit st3 st4 asg3 asg4 ss_l Hs34 Hwf_ss),
        Hev_ss; reflexivity.
    + unfold eval_rail_val at 1; unfold Integers.one, Integers.zero; cbn [rbv_bits List.map].
      rewrite (step_spec_eval_lit st2 st' asg2 asg5 res_bit Hs25 Hwf_rb), Hev_rb.
      destruct (if is_signed
                then @Integers.cmp sz c (eval_rail_val sz asg a) (eval_rail_val sz asg b)
                else @Integers.cmpu sz c (eval_rail_val sz asg a) (eval_rail_val sz asg b));
        reflexivity.
Qed.

Definition blast_select_rail_opt
  (sz : positive) (cond t_val f_val : rail_bv) (st : blast_state) : rail_bv * blast_state :=
  let cbit := List.hd lit_false (rbv_bits cond) in
  let '(bits, st1) := mux_bits_list_opt cbit (rbv_bits t_val) (rbv_bits f_val) st in
  let '(br_psn, st2) := emit_mux2_opt cbit (rbv_psn t_val) (rbv_psn f_val) st1 in
  let '(psn, st3) := emit_or2_opt (rbv_psn cond) br_psn st2 in
  (mk_rail_bv sz bits psn, st3).

Theorem blast_select_rail_opt_step : forall sz cond tv fv asg st out st',
  sat_blast_st asg st ->
  wf_rail_bound 1%positive (bs_next_var st) cond ->
  wf_rail_bound sz (bs_next_var st) tv ->
  wf_rail_bound sz (bs_next_var st) fv ->
  blast_select_rail_opt sz cond tv fv st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_rail_bound sz (bs_next_var st') out /\
    eval_rail_psn asg' out =
      (eval_rail_psn asg cond ||
       (if @Integers.eq 1%positive (eval_rail_val 1%positive asg cond) (@Integers.one 1%positive)
        then eval_rail_psn asg tv
        else eval_rail_psn asg fv)) /\
    eval_rail_val sz asg' out =
      (if @Integers.eq 1%positive (eval_rail_val 1%positive asg cond) (@Integers.one 1%positive)
       then eval_rail_val sz asg tv
       else eval_rail_val sz asg fv).
Proof.
  intros sz cond tv fv asg st out st' Hsat
         ([_ Hlc] & Hbc & Hpc) ([Hwt Hlt] & Hbt & Hpt) ([Hwf Hlf] & Hbf & Hpf) Hbl.
  unfold blast_select_rail_opt in Hbl; cbn zeta in Hbl.
  set (cbit := List.hd lit_false (rbv_bits cond)) in *.
  assert (Hc_decomp : exists c0, rbv_bits cond = [c0]).
  { destruct (rbv_bits cond) as [| c0 [| c1 cr]]; try discriminate Hlc.
    exists c0; reflexivity. }
  destruct Hc_decomp as [c0 Hc0_eq].
  assert (Hcbit_eq : cbit = c0) by (unfold cbit; rewrite Hc0_eq; reflexivity).
  assert (Hw_cbit : wf_lit_bound (bs_next_var st) cbit)
    by (rewrite Hcbit_eq; rewrite Hc0_eq in Hbc; inversion Hbc; assumption).
  destruct (mux_bits_list_opt cbit (rbv_bits tv) (rbv_bits fv) st) as [bits st1] eqn:Em1.
  destruct (emit_mux2_opt cbit (rbv_psn tv) (rbv_psn fv) st1) as [br_psn st2] eqn:Em2.
  destruct (emit_or2_opt (rbv_psn cond) br_psn st2) as [psn st3] eqn:Ep.
  inversion Hbl; subst out st3; clear Hbl.
  destruct (mux_bits_list_opt_step (rbv_bits tv) (rbv_bits fv) cbit asg st bits st1
              (eq_trans Hlt (eq_sym Hlf)) Hw_cbit Hbt Hbf Hsat Em1)
    as (asg1 & Hs1 & Hlen_bits & Hwf_bits & Hev_bits).
  destruct (emit_mux2_opt_step asg1 cbit (rbv_psn tv) (rbv_psn fv) st1 br_psn st2 (proj2 (proj2 Hs1))
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hw_cbit)
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpt)
              (wf_lit_bound_mono _ _ _ (proj1 Hs1) Hpf) Em2)
    as (asg2 & Hs2 & Hwf_brp & Hev_brp).
  pose proof (step_spec_trans st st1 st2 asg asg1 asg2 Hs1 Hs2) as Hs02.
  destruct (emit_or2_opt_step asg2 (rbv_psn cond) br_psn st2 psn st' (proj2 (proj2 Hs2))
              (wf_lit_bound_mono _ _ _ (proj1 Hs02) Hpc) Hwf_brp Ep)
    as (asg3 & Hs3 & Hwf_p & Hev_p).
  pose proof (step_spec_trans st1 st2 st' asg1 asg2 asg3 Hs2 Hs3) as Hs13.
  pose proof (step_spec_trans st st1 st' asg asg1 asg3 Hs1 Hs13) as Hs03.
  assert (Hcbit_cond :
            eval_lit asg cbit =
            @Integers.eq 1%positive (eval_rail_val 1%positive asg cond) (@Integers.one 1%positive)).
  { unfold eval_rail_val; rewrite Hc0_eq, Hcbit_eq; cbn [List.map].
    symmetry; destruct (eval_lit asg c0);
      [exact (eq_one_cond 1%positive true) | exact (eq_one_cond 1%positive false)]. }
  exists asg3; split; [exact Hs03 | split].
  - split; [split; [reflexivity | cbn; congruence] |
            split; [exact (wf_lits_bound_mono _ _ _ (proj1 Hs13) Hwf_bits) | exact Hwf_p]].
  - split.
    + unfold eval_rail_psn; cbn [rbv_psn]; rewrite Hev_p,
        (step_spec_eval_lit st st2 asg asg2 (rbv_psn cond) Hs02 Hpc),
        Hev_brp,
        (step_spec_eval_lit st st1 asg asg1 cbit Hs1 Hw_cbit),
        (step_spec_eval_lit st st1 asg asg1 (rbv_psn tv) Hs1 Hpt),
        (step_spec_eval_lit st st1 asg asg1 (rbv_psn fv) Hs1 Hpf),
        Hcbit_cond; reflexivity.
    + unfold eval_rail_val at 1; cbn [rbv_bits];
        rewrite (step_spec_eval_lits st1 st' asg1 asg3 bits Hs13 Hwf_bits),
                Hev_bits, Hcbit_cond.
      destruct (@Integers.eq 1%positive (eval_rail_val 1%positive asg cond) (@Integers.one 1%positive));
        reflexivity.
Qed.
