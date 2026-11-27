(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * 2-Rail Bitvector Bridge, Tseitin Gates & Peepholes ([CertValidator.AigGates])

    Purpose:
      Defines the 2-rail [(val_bits, poison_bit)] representation ([rail_bv])
      bridged to [@Integers.bit_int], monotone Tseitin gates, 2-rail encoders,
      monotone [sat_blast_st] peepholes, and counterexample UNSAT checks.

    Trust Contract & Fail-Closed Boundary:
      Fail-closed SAT counterexample queries ([blast_refinement_cex_unsat_sound],
      [blast_refinement_cex_opt_lrat_sound]); returns [true] only when [LRAT] or
      bounded DPLL refutes the counterexample CNF.

    Assumptions:
      Depends on Stdlib, [Vellvm.Numeric.{Rocqlib,Zbits,Integers}], and
      [CertValidator.LratCore]; zero custom axioms.

    Section Outline:
      3. 2-Rail Representation & Bridge; 4. Monotone Tseitin Builder & Encodings
      (4.1 Gates, 4.2 Bitwise/Const, 4.3 Eq/Select/Freeze, 4.4 CEX Queries);
      6. Monotone [sat_blast_st] & Peephole Gates (6.1 Bounds & Combinators). *)

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
  intros [] []; cbn; split;
    intros H; try reflexivity; discriminate.
Qed.

From CertValidator Require Import LratCore.

(** ** 3. 2-Rail [(val_bits, poison_bit)] Representation & Bridge to [@Integers.bit_int] *)

Record rail_bv : Set :=
  mk_rail_bv {
    rbv_width : positive;
    rbv_bits  : list lit;
    rbv_psn   : lit;
  }.

Definition wf_rail_bv (sz : positive) (r : rail_bv) : Prop :=
  rbv_width r = sz /\ List.length (rbv_bits r) = Pos.to_nat sz.

Fixpoint bools_to_Z (bs : list bool) : Z :=
  match bs with
  | [] => 0%Z
  | b :: rest => Integers.Zshiftin b (bools_to_Z rest)
  end.

Lemma bools_to_Z_testbit : forall (bs : list bool) (k : nat),
  Z.testbit (bools_to_Z bs) (Z.of_nat k) = List.nth k bs false.
Proof.
  induction bs as [| b rest IH]; intros [| k']; cbn [bools_to_Z List.nth].
  - apply Z.testbit_0_l.
  - apply Z.testbit_0_l.
  - apply Integers.Ztestbit_shiftin_base.
  - rewrite Nat2Z.inj_succ, Integers.Ztestbit_shiftin_succ by lia; apply IH.
Qed.

Definition eval_rail_val (sz : positive) (assign : positive -> bool) (r : rail_bv)
  : @Integers.bit_int sz :=
  @Integers.repr sz (bools_to_Z (List.map (eval_lit assign) (rbv_bits r))).

Definition eval_rail_psn (assign : positive -> bool) (r : rail_bv) : bool :=
  eval_lit assign (rbv_psn r).

Lemma eval_rail_val_testbit_nat : forall sz assign r (k : nat),
  (k < Pos.to_nat sz)%nat ->
  @Integers.testbit sz (eval_rail_val sz assign r) (Z.of_nat k) =
  List.nth k (List.map (eval_lit assign) (rbv_bits r)) false.
Proof.
  intros sz assign r k Hk.
  unfold eval_rail_val.
  rewrite @Integers.testbit_repr.
  - apply bools_to_Z_testbit.
  - unfold Integers.zwordsize; rewrite <- positive_nat_Z; lia.
Qed.

Lemma eval_rail_val_testbit : forall sz assign r (i : Z),
  (0 <= i < @Integers.zwordsize sz)%Z ->
  @Integers.testbit sz (eval_rail_val sz assign r) i =
  List.nth (Z.to_nat i) (List.map (eval_lit assign) (rbv_bits r)) false.
Proof.
  intros sz assign r i Hi.
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by (rewrite Z2Nat.id; lia).
  apply eval_rail_val_testbit_nat.
  unfold Integers.zwordsize in Hi; lia.
Qed.

Definition bit_int_to_bools (sz : positive) (x : @Integers.bit_int sz) : list bool :=
  List.map (fun k => @Integers.testbit sz x (Z.of_nat k)) (List.seq 0 (Pos.to_nat sz)).

Lemma bit_int_to_bools_length : forall sz x,
  List.length (bit_int_to_bools sz x) = Pos.to_nat sz.
Proof.
  intros sz x; unfold bit_int_to_bools; rewrite length_map, length_seq; reflexivity.
Qed.

Lemma bit_int_to_bools_nth : forall sz (x : @Integers.bit_int sz) k,
  (k < Pos.to_nat sz)%nat ->
  List.nth k (bit_int_to_bools sz x) false = @Integers.testbit sz x (Z.of_nat k).
Proof.
  intros sz x k Hlt; unfold bit_int_to_bools.
  set (f := fun j => @Integers.testbit sz x (Z.of_nat j)).
  rewrite (nth_indep _ false (f 0%nat))
    by (subst f; rewrite length_map, length_seq; exact Hlt).
  rewrite map_nth, seq_nth by exact Hlt.
  subst f; cbn [Nat.add]; reflexivity.
Qed.

Theorem bit_int_to_bools_repr : forall sz (x : @Integers.bit_int sz),
  @Integers.repr sz (bools_to_Z (bit_int_to_bools sz x)) = x.
Proof.
  intros sz x.
  apply @Integers.same_bits_eq; intros i Hi.
  rewrite @Integers.testbit_repr by exact Hi.
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by (rewrite Z2Nat.id; lia).
  rewrite bools_to_Z_testbit.
  assert (Hlt : (Z.to_nat i < Pos.to_nat sz)%nat)
    by (unfold Integers.zwordsize in Hi; lia).
  rewrite bit_int_to_bools_nth by exact Hlt.
  rewrite Z2Nat.id by lia; reflexivity.
Qed.

Lemma modulus_pow_sz : forall sz,
  @Integers.modulus sz = (2 ^ Z.pos sz)%Z.
Proof.
  intros sz; rewrite @Integers.modulus_def, two_power_pos_equiv; reflexivity.
Qed.

(** ** 4. Monotone Tseitin Gate Builder & Verified 2-Rail Encodings *)

(** Variable [1] is pinned to [true] via initial unit clause [(1, [1])],
    giving canonical constant literals [lit_true = 1] and [lit_false = -1]. *)
Definition lit_true : lit := Z.pos 1%positive.
Definition lit_false : lit := Z.neg 1%positive.

Record blast_state : Set :=
  mk_blast_state {
    bs_next_var : positive;
    bs_next_cid : positive;
    bs_cnf      : cnf;
  }.

Definition init_blast_state (first_aux_var : positive) : blast_state :=
  mk_blast_state (Pos.max 2%positive first_aux_var)
                 2%positive
                 [(1%positive, [lit_true])].

Lemma eval_cnf_app : forall assign f1 f2,
  eval_cnf assign (f1 ++ f2) = eval_cnf assign f1 && eval_cnf assign f2.
Proof.
  intros assign f1 f2; unfold eval_cnf; apply forallb_app.
Qed.

Lemma init_blast_state_true_const : forall assign first_aux rem,
  eval_cnf assign (bs_cnf (init_blast_state first_aux) ++ rem) = true ->
  eval_lit assign lit_true = true /\ eval_lit assign lit_false = false.
Proof.
  intros assign first_aux rem H; cbn in H.
  rewrite orb_false_r in H; apply andb_true_iff in H as [Hv1 _].
  split; [exact Hv1 | cbn; rewrite Hv1; reflexivity].
Qed.

Definition alloc_var (st : blast_state) : lit * blast_state :=
  (Z.pos (bs_next_var st),
   mk_blast_state (Pos.succ (bs_next_var st)) (bs_next_cid st) (bs_cnf st)).

Fixpoint prepend_clauses_rev (cid : positive) (cls : list clause) (acc : cnf)
  {struct cls} : positive * cnf :=
  match cls with
  | [] => (cid, acc)
  | c :: rest => prepend_clauses_rev (Pos.succ cid) rest ((cid, c) :: acc)
  end.

Definition add_clauses (cls : list clause) (st : blast_state) : blast_state :=
  let '(cid', new_cnf) := prepend_clauses_rev (bs_next_cid st) cls (bs_cnf st) in
  mk_blast_state (bs_next_var st) cid' new_cnf.

Lemma prepend_clauses_rev_pref : forall cid cls acc cid' out,
  prepend_clauses_rev cid cls acc = (cid', out) ->
  exists d, out = d ++ acc.
Proof.
  intros cid cls; revert cid; induction cls as [| c rest IH];
    intros cid acc cid' out H; cbn [prepend_clauses_rev] in H.
  - inversion H; subst; exists []; reflexivity.
  - destruct (IH (Pos.succ cid) ((cid, c) :: acc) cid' out H) as [d Hd].
    exists (d ++ [(cid, c)]); rewrite Hd, <- app_assoc; reflexivity.
Qed.

Lemma add_clauses_pref : forall cls st,
  exists d, bs_cnf (add_clauses cls st) = d ++ bs_cnf st.
Proof.
  intros cls st; unfold add_clauses.
  destruct (prepend_clauses_rev (bs_next_cid st) cls (bs_cnf st)) as [cid' out] eqn:Hp.
  cbn [bs_cnf]; exact (prepend_clauses_rev_pref _ _ _ _ _ Hp).
Qed.

Lemma prepend_clauses_rev_sat_split : forall assign cls cid acc cid' out,
  prepend_clauses_rev cid cls acc = (cid', out) ->
  eval_cnf assign out = true ->
  eval_cnf assign acc = true /\
  forall c, In c cls -> eval_clause assign c = true.
Proof.
  intros assign cls; induction cls as [| c0 cr IH];
    intros cid acc cid' out H Hsat; cbn [prepend_clauses_rev] in H.
  - inversion H; subst; split; [exact Hsat | intros c []].
  - destruct (IH (Pos.succ cid) ((cid, c0) :: acc) cid' out H Hsat) as [Hacc Hcr].
    unfold eval_cnf in Hacc; cbn [forallb] in Hacc.
    apply andb_true_iff in Hacc as [Hc0 Hacc0].
    split; [exact Hacc0 |].
    intros c [<- | Hrest]; [exact Hc0 | exact (Hcr c Hrest)].
Qed.

Lemma add_clauses_sat_split : forall assign cls st,
  eval_cnf assign (bs_cnf (add_clauses cls st)) = true ->
  eval_cnf assign (bs_cnf st) = true /\
  forall c, In c cls -> eval_clause assign c = true.
Proof.
  intros assign cls st H; unfold add_clauses in H.
  destruct (prepend_clauses_rev (bs_next_cid st) cls (bs_cnf st)) as [cid' out] eqn:Happ.
  cbn [bs_cnf] in H; exact (prepend_clauses_rev_sat_split assign cls _ _ cid' out Happ H).
Qed.

(** *** 4.1 Verified Tseitin Gate Primitives ([AND], [OR], [XOR], [MUX], [EQ]) *)

Definition emit_and2 (a b : lit) (st : blast_state) : lit * blast_state :=
  let '(out, st1) := alloc_var st in
  let cls :=
      [ [neg_lit out; a];
        [neg_lit out; b];
        [out; neg_lit a; neg_lit b] ] in
  (out, add_clauses cls st1).

Lemma emit_and2_sound : forall assign a b st out st',
  a <> 0%Z -> b <> 0%Z ->
  emit_and2 a b st = (out, st') ->
  out <> 0%Z /\
  (forall rem,
     eval_cnf assign (bs_cnf st' ++ rem) = true ->
     eval_cnf assign (bs_cnf st) = true /\
     eval_lit assign out = (eval_lit assign a && eval_lit assign b)).
Proof.
  intros assign a b st out st' Ha Hb Hemit.
  unfold emit_and2, alloc_var in Hemit; inversion Hemit; subst out st'; clear Hemit.
  split; [discriminate |].
  intros rem Hsat.
  rewrite eval_cnf_app in Hsat; apply andb_true_iff in Hsat as [Hcls _].
  destruct (add_clauses_sat_split assign _ _ Hcls) as [Hst Hin]; cbn [bs_cnf] in Hst.
  pose proof (Hin _ (or_introl eq_refl)) as C1.
  pose proof (Hin _ (or_intror (or_introl eq_refl))) as C2.
  pose proof (Hin _ (or_intror (or_intror (or_introl eq_refl)))) as C3.
  cbn [eval_clause existsb] in C1, C2, C3.
  rewrite (eval_neg_lit_nonzero assign a Ha), (eval_neg_lit_nonzero assign b Hb) in C3.
  split; [exact Hst |].
  cbn [neg_lit Z.opp eval_lit] in C1, C2, C3 |- *.
  destruct (assign (bs_next_var st)), (eval_lit assign a), (eval_lit assign b);
    cbn in *; try reflexivity; discriminate.
Qed.

Definition emit_or2 (a b : lit) (st : blast_state) : lit * blast_state :=
  let '(out, st1) := alloc_var st in
  let cls :=
      [ [out; neg_lit a];
        [out; neg_lit b];
        [neg_lit out; a; b] ] in
  (out, add_clauses cls st1).

Lemma emit_or2_sound : forall assign a b st out st',
  a <> 0%Z -> b <> 0%Z ->
  emit_or2 a b st = (out, st') ->
  out <> 0%Z /\
  (forall rem,
     eval_cnf assign (bs_cnf st' ++ rem) = true ->
     eval_cnf assign (bs_cnf st) = true /\
     eval_lit assign out = (eval_lit assign a || eval_lit assign b)).
Proof.
  intros assign a b st out st' Ha Hb Hemit.
  unfold emit_or2, alloc_var in Hemit; inversion Hemit; subst out st'; clear Hemit.
  split; [discriminate |].
  intros rem Hsat.
  rewrite eval_cnf_app in Hsat; apply andb_true_iff in Hsat as [Hcls _].
  destruct (add_clauses_sat_split assign _ _ Hcls) as [Hst Hin]; cbn [bs_cnf] in Hst.
  pose proof (Hin _ (or_introl eq_refl)) as C1.
  pose proof (Hin _ (or_intror (or_introl eq_refl))) as C2.
  pose proof (Hin _ (or_intror (or_intror (or_introl eq_refl)))) as C3.
  cbn [eval_clause existsb] in C1, C2, C3.
  rewrite (eval_neg_lit_nonzero assign a Ha) in C1.
  rewrite (eval_neg_lit_nonzero assign b Hb) in C2.
  split; [exact Hst |].
  cbn [neg_lit Z.opp eval_lit] in C1, C2, C3 |- *.
  destruct (assign (bs_next_var st)), (eval_lit assign a), (eval_lit assign b);
    cbn in *; try reflexivity; discriminate.
Qed.

Definition emit_xor2 (a b : lit) (st : blast_state) : lit * blast_state :=
  let '(out, st1) := alloc_var st in
  let cls :=
      [ [neg_lit out; a; b];
        [neg_lit out; neg_lit a; neg_lit b];
        [out; neg_lit a; b];
        [out; a; neg_lit b] ] in
  (out, add_clauses cls st1).

Lemma emit_xor2_sound : forall assign a b st out st',
  a <> 0%Z -> b <> 0%Z ->
  emit_xor2 a b st = (out, st') ->
  out <> 0%Z /\
  (forall rem,
     eval_cnf assign (bs_cnf st' ++ rem) = true ->
     eval_cnf assign (bs_cnf st) = true /\
     eval_lit assign out = xorb (eval_lit assign a) (eval_lit assign b)).
Proof.
  intros assign a b st out st' Ha Hb Hemit.
  unfold emit_xor2, alloc_var in Hemit; inversion Hemit; subst out st'; clear Hemit.
  split; [discriminate |].
  intros rem Hsat.
  rewrite eval_cnf_app in Hsat; apply andb_true_iff in Hsat as [Hcls _].
  destruct (add_clauses_sat_split assign _ _ Hcls) as [Hst Hin]; cbn [bs_cnf] in Hst.
  pose proof (Hin _ (or_introl eq_refl)) as C1.
  pose proof (Hin _ (or_intror (or_introl eq_refl))) as C2.
  pose proof (Hin _ (or_intror (or_intror (or_introl eq_refl)))) as C3.
  pose proof (Hin _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as C4.
  cbn [eval_clause existsb] in C1, C2, C3, C4.
  rewrite (eval_neg_lit_nonzero assign a Ha) in C2, C3.
  rewrite (eval_neg_lit_nonzero assign b Hb) in C2, C4.
  split; [exact Hst |].
  cbn [neg_lit Z.opp eval_lit] in C1, C2, C3, C4 |- *.
  destruct (assign (bs_next_var st)), (eval_lit assign a), (eval_lit assign b);
    cbn in *; try reflexivity; discriminate.
Qed.

Definition emit_mux2 (sel t_lit f_lit : lit) (st : blast_state) : lit * blast_state :=
  let '(out, st1) := alloc_var st in
  let cls :=
      [ [neg_lit sel; neg_lit out; t_lit];
        [neg_lit sel; out; neg_lit t_lit];
        [sel; neg_lit out; f_lit];
        [sel; out; neg_lit f_lit] ] in
  (out, add_clauses cls st1).

Lemma emit_mux2_sound : forall assign sel t_lit f_lit st out st',
  sel <> 0%Z -> t_lit <> 0%Z -> f_lit <> 0%Z ->
  emit_mux2 sel t_lit f_lit st = (out, st') ->
  out <> 0%Z /\
  (forall rem,
     eval_cnf assign (bs_cnf st' ++ rem) = true ->
     eval_cnf assign (bs_cnf st) = true /\
     eval_lit assign out = (if eval_lit assign sel then eval_lit assign t_lit
                            else eval_lit assign f_lit)).
Proof.
  intros assign sel tl fl st out st' Hsel Htl Hfl Hemit.
  unfold emit_mux2, alloc_var in Hemit; inversion Hemit; subst out st'; clear Hemit.
  split; [discriminate |].
  intros rem Hsat.
  rewrite eval_cnf_app in Hsat; apply andb_true_iff in Hsat as [Hcls _].
  destruct (add_clauses_sat_split assign _ _ Hcls) as [Hst Hin]; cbn [bs_cnf] in Hst.
  pose proof (Hin _ (or_introl eq_refl)) as C1.
  pose proof (Hin _ (or_intror (or_introl eq_refl))) as C2.
  pose proof (Hin _ (or_intror (or_intror (or_introl eq_refl)))) as C3.
  pose proof (Hin _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as C4.
  cbn [eval_clause existsb] in C1, C2, C3, C4.
  rewrite (eval_neg_lit_nonzero assign sel Hsel) in C1, C2.
  rewrite (eval_neg_lit_nonzero assign tl Htl) in C2.
  rewrite (eval_neg_lit_nonzero assign fl Hfl) in C4.
  split; [exact Hst |].
  cbn [neg_lit Z.opp eval_lit] in C1, C2, C3, C4 |- *.
  destruct (assign (bs_next_var st)), (eval_lit assign sel),
           (eval_lit assign tl), (eval_lit assign fl);
    cbn in *; try reflexivity; discriminate.
Qed.

(** *** 4.2 Verified 2-Rail Constant, Poison, Bitwise, Equality, Freeze & Counterexample Encoders *)

Definition wf_lits_nonzero (ls : list lit) : Prop :=
  Forall (fun l => l <> 0%Z) ls.

Definition wf_rail_lits (sz : positive) (r : rail_bv) : Prop :=
  wf_rail_bv sz r /\ wf_lits_nonzero (rbv_bits r) /\ rbv_psn r <> 0%Z.

Definition blast_const_rail (sz : positive) (val : N) : rail_bv :=
  let bits := List.map (fun k => if Z.testbit (Z.of_N val) (Z.of_nat k)
                                 then lit_true else lit_false)
                       (List.seq 0 (Pos.to_nat sz)) in
  mk_rail_bv sz bits lit_false.

Lemma blast_const_rail_sound : forall assign sz val first_aux rem,
  eval_cnf assign (bs_cnf (init_blast_state first_aux) ++ rem) = true ->
  wf_rail_lits sz (blast_const_rail sz val) /\
  eval_rail_psn assign (blast_const_rail sz val) = false /\
  eval_rail_val sz assign (blast_const_rail sz val) = @Integers.repr sz (Z.of_N val).
Proof.
  intros assign sz val first_aux rem Hinit.
  destruct (init_blast_state_true_const assign first_aux rem Hinit) as [Ht Hf].
  repeat split.
  - unfold blast_const_rail; cbn; rewrite length_map, length_seq; reflexivity.
  - unfold blast_const_rail, wf_lits_nonzero; cbn.
    apply Forall_forall; intros x Hin.
    apply in_map_iff in Hin as [k [<- _]].
    destruct (Z.testbit (Z.of_N val) (Z.of_nat k)); discriminate.
  - discriminate.
  - exact Hf.
  - apply @Integers.same_bits_eq; intros i Hi.
    rewrite eval_rail_val_testbit by exact Hi.
    rewrite @Integers.testbit_repr by exact Hi.
    unfold blast_const_rail; cbn [rbv_bits].
    rewrite map_map.
    assert (Hlt : (Z.to_nat i < Pos.to_nat sz)%nat)
      by (unfold Integers.zwordsize in Hi; lia).
    set (f := fun x : nat => eval_lit assign (if Z.testbit (Z.of_N val) (Z.of_nat x)
                                              then lit_true else lit_false)).
    rewrite (nth_indep _ false (f 0%nat))
      by (subst f; rewrite length_map, length_seq; exact Hlt).
    rewrite map_nth, seq_nth by exact Hlt.
    subst f; cbn [Nat.add]; rewrite Z2Nat.id by lia.
    destruct (Z.testbit (Z.of_N val) i); [exact Ht | exact Hf].
Qed.

Definition blast_poison_rail (sz : positive) : rail_bv :=
  mk_rail_bv sz (List.repeat lit_false (Pos.to_nat sz)) lit_true.

Lemma blast_poison_rail_sound : forall assign sz first_aux rem,
  eval_cnf assign (bs_cnf (init_blast_state first_aux) ++ rem) = true ->
  wf_rail_lits sz (blast_poison_rail sz) /\
  eval_rail_psn assign (blast_poison_rail sz) = true.
Proof.
  intros assign sz first_aux rem Hinit.
  destruct (init_blast_state_true_const assign first_aux rem Hinit) as [Ht _].
  repeat split.
  - unfold blast_poison_rail; cbn; apply repeat_length.
  - unfold blast_poison_rail, wf_lits_nonzero; cbn.
    apply Forall_forall; intros x Hin.
    apply repeat_spec in Hin; subst x; discriminate.
  - discriminate.
  - exact Ht.
Qed.

Fixpoint map2_emit
  (gate : lit -> lit -> blast_state -> lit * blast_state)
  (xs ys : list lit) (st : blast_state) {struct xs} : list lit * blast_state :=
  match xs, ys with
  | x :: rx, y :: ry =>
      let '(z, st1) := gate x y st in
      let '(zs, st2) := map2_emit gate rx ry st1 in
      (z :: zs, st2)
  | _, _ => ([], st)
  end.

Lemma eval_cnf_pref_rem : forall assign c1 c2 rem d,
  c2 = d ++ c1 ->
  eval_cnf assign (c2 ++ rem) = true ->
  eval_cnf assign (c1 ++ rem) = true.
Proof.
  intros assign c1 c2 rem d -> H.
  rewrite <- app_assoc, eval_cnf_app, andb_true_iff in H.
  exact (proj2 H).
Qed.

Lemma bs_cnf_prefix_step :
  forall (gate : lit -> lit -> blast_state -> lit * blast_state)
         (Hpref : forall x y st z st1, gate x y st = (z, st1) ->
                  exists delta, bs_cnf st1 = delta ++ bs_cnf st)
         xs ys st zs st',
    map2_emit gate xs ys st = (zs, st') ->
    exists delta, bs_cnf st' = delta ++ bs_cnf st.
Proof.
  intros gate Hpref xs.
  induction xs as [| x rx IH]; intros [| y ry] st zs st' Hm; cbn in Hm.
  - inversion Hm; subst; exists []; reflexivity.
  - inversion Hm; subst; exists []; reflexivity.
  - inversion Hm; subst; exists []; reflexivity.
  - destruct (gate x y st) as [z st1] eqn:Hg.
    destruct (map2_emit gate rx ry st1) as [zr st2] eqn:Hmr.
    inversion Hm; subst; clear Hm.
    destruct (Hpref x y st z st1 Hg) as [d1 Hd1].
    destruct (IH ry st1 zr st' Hmr) as [d2 Hd2].
    exists (d2 ++ d1); rewrite Hd2, Hd1, app_assoc; reflexivity.
Qed.

Lemma map2_emit_sound :
  forall (gate : lit -> lit -> blast_state -> lit * blast_state)
         (f_bool : bool -> bool -> bool)
         (Hpref : forall x y st z st1, gate x y st = (z, st1) ->
                  exists delta, bs_cnf st1 = delta ++ bs_cnf st)
         (Hgate : forall assign x y st z st1,
                    x <> 0%Z -> y <> 0%Z ->
                    gate x y st = (z, st1) ->
                    z <> 0%Z /\
                    forall rem, eval_cnf assign (bs_cnf st1 ++ rem) = true ->
                                eval_lit assign z = f_bool (eval_lit assign x) (eval_lit assign y))
         assign xs ys st zs st',
    List.length xs = List.length ys ->
    wf_lits_nonzero xs ->
    wf_lits_nonzero ys ->
    map2_emit gate xs ys st = (zs, st') ->
    List.length zs = List.length xs /\
    wf_lits_nonzero zs /\
    (forall rem (k : nat),
       (k < List.length xs)%nat ->
       eval_cnf assign (bs_cnf st' ++ rem) = true ->
       List.nth k (List.map (eval_lit assign) zs) false =
       f_bool (List.nth k (List.map (eval_lit assign) xs) false)
              (List.nth k (List.map (eval_lit assign) ys) false)).
Proof.
  intros gate f_bool Hpref Hgate assign xs.
  induction xs as [| x rx IH]; intros [| y ry] st zs st' Hlen Hwx Hwy Hm;
    try discriminate; cbn in Hm.
  - inversion Hm; subst; repeat split; [constructor | intros rem k Hk; inversion Hk].
  - inversion Hwx as [| ? ? Hx Hwrx]; subst.
    inversion Hwy as [| ? ? Hy Hwry]; subst.
    injection Hlen as Hlen'.
    destruct (gate x y st) as [z st1] eqn:Hg.
    destruct (map2_emit gate rx ry st1) as [zr st2] eqn:Hmr.
    inversion Hm; subst; clear Hm.
    destruct (Hgate assign x y st z st1 Hx Hy Hg) as [Hz Hz_ev].
    destruct (IH ry st1 zr st' Hlen' Hwrx Hwry Hmr) as (Hzr_len & Hzr_wf & Hzr_ev).
    destruct (bs_cnf_prefix_step gate Hpref rx ry st1 zr st' Hmr) as [d2 Hd2].
    repeat split.
    + cbn; rewrite Hzr_len; reflexivity.
    + constructor; [exact Hz | exact Hzr_wf].
    + intros rem [| k'] Hk Hsat; cbn [List.map List.nth].
      * apply (Hz_ev rem).
        exact (eval_cnf_pref_rem assign _ _ rem d2 Hd2 Hsat).
      * apply (Hzr_ev rem); [cbn in Hk; lia | exact Hsat].
Qed.

Lemma emit_and2_pref : forall x y st z st1,
  emit_and2 x y st = (z, st1) -> exists d, bs_cnf st1 = d ++ bs_cnf st.
Proof.
  intros x y st z st1 H; unfold emit_and2 in H;
    destruct (alloc_var st) as [out st0] eqn:Ha;
    inversion H; subst; clear H;
    unfold alloc_var in Ha; inversion Ha; subst;
    exact (add_clauses_pref _ _).
Qed.

Lemma emit_or2_pref : forall x y st z st1,
  emit_or2 x y st = (z, st1) -> exists d, bs_cnf st1 = d ++ bs_cnf st.
Proof.
  intros x y st z st1 H; unfold emit_or2 in H;
    destruct (alloc_var st) as [out st0] eqn:Ha;
    inversion H; subst; clear H;
    unfold alloc_var in Ha; inversion Ha; subst;
    exact (add_clauses_pref _ _).
Qed.

Lemma emit_xor2_pref : forall x y st z st1,
  emit_xor2 x y st = (z, st1) -> exists d, bs_cnf st1 = d ++ bs_cnf st.
Proof.
  intros x y st z st1 H; unfold emit_xor2 in H;
    destruct (alloc_var st) as [out st0] eqn:Ha;
    inversion H; subst; clear H;
    unfold alloc_var in Ha; inversion Ha; subst;
    exact (add_clauses_pref _ _).
Qed.

Definition blast_and_rail (sz : positive) (a b : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let '(bits, st1) := map2_emit emit_and2 (rbv_bits a) (rbv_bits b) st in
  let '(psn, st2) := emit_or2 (rbv_psn a) (rbv_psn b) st1 in
  (mk_rail_bv sz bits psn, st2).

Theorem blast_and_rail_sound : forall assign sz a b st out st' rem,
  wf_rail_lits sz a -> wf_rail_lits sz b ->
  blast_and_rail sz a b st = (out, st') ->
  eval_cnf assign (bs_cnf st' ++ rem) = true ->
  wf_rail_lits sz out /\
  eval_rail_psn assign out = (eval_rail_psn assign a || eval_rail_psn assign b) /\
  eval_rail_val sz assign out = @Integers.and sz (eval_rail_val sz assign a)
                                                 (eval_rail_val sz assign b).
Proof.
  intros assign sz a b st out st' rem
         ([Hwa Hla] & Hwfa & Hpa) ([Hwb Hlb] & Hwfb & Hpb) Hbl Hsat.
  unfold blast_and_rail in Hbl.
  destruct (map2_emit emit_and2 (rbv_bits a) (rbv_bits b) st) as [bits st1] eqn:Hm.
  destruct (emit_or2 (rbv_psn a) (rbv_psn b) st1) as [psn st2] eqn:Hp.
  inversion Hbl; subst out st2; clear Hbl.
  destruct (emit_or2_pref _ _ _ _ _ Hp) as [dp Hdp].
  destruct (emit_or2_sound assign _ _ _ _ _ Hpa Hpb Hp) as [Hpsn_nz Hpsn_ev].
  destruct (Hpsn_ev rem Hsat) as [_ Hpsn_eq].
  assert (Hsat1 : eval_cnf assign (bs_cnf st1 ++ rem) = true)
    by exact (eval_cnf_pref_rem assign _ _ rem dp Hdp Hsat).
  assert (Hlen_ab : List.length (rbv_bits a) = List.length (rbv_bits b)) by congruence.
  destruct (map2_emit_sound emit_and2 andb emit_and2_pref
              (fun asg x y s0 z s1 Hx Hy Hg =>
                 let (Hz, Hev) := emit_and2_sound asg x y s0 z s1 Hx Hy Hg in
                 conj Hz (fun r0 Hs0 => proj2 (Hev r0 Hs0)))
              assign _ _ _ _ _ Hlen_ab Hwfa Hwfb Hm)
    as (Hblen & Hbwf & Hbev).
  repeat split.
  - cbn; congruence.
  - exact Hbwf.
  - exact Hpsn_nz.
  - exact Hpsn_eq.
  - apply @Integers.same_bits_eq; intros i Hi.
    rewrite @Integers.bits_and by exact Hi.
    rewrite !eval_rail_val_testbit by exact Hi.
    cbn [rbv_bits]; apply (Hbev rem (Z.to_nat i)); [| exact Hsat1].
    rewrite Hla; unfold Integers.zwordsize in Hi; lia.
Qed.

Definition blast_or_rail (sz : positive) (a b : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let '(bits, st1) := map2_emit emit_or2 (rbv_bits a) (rbv_bits b) st in
  let '(psn, st2) := emit_or2 (rbv_psn a) (rbv_psn b) st1 in
  (mk_rail_bv sz bits psn, st2).

Theorem blast_or_rail_sound : forall assign sz a b st out st' rem,
  wf_rail_lits sz a -> wf_rail_lits sz b ->
  blast_or_rail sz a b st = (out, st') ->
  eval_cnf assign (bs_cnf st' ++ rem) = true ->
  wf_rail_lits sz out /\
  eval_rail_psn assign out = (eval_rail_psn assign a || eval_rail_psn assign b) /\
  eval_rail_val sz assign out = @Integers.or sz (eval_rail_val sz assign a)
                                                (eval_rail_val sz assign b).
Proof.
  intros assign sz a b st out st' rem
         ([Hwa Hla] & Hwfa & Hpa) ([Hwb Hlb] & Hwfb & Hpb) Hbl Hsat.
  unfold blast_or_rail in Hbl.
  destruct (map2_emit emit_or2 (rbv_bits a) (rbv_bits b) st) as [bits st1] eqn:Hm.
  destruct (emit_or2 (rbv_psn a) (rbv_psn b) st1) as [psn st2] eqn:Hp.
  inversion Hbl; subst out st2; clear Hbl.
  destruct (emit_or2_pref _ _ _ _ _ Hp) as [dp Hdp].
  destruct (emit_or2_sound assign _ _ _ _ _ Hpa Hpb Hp) as [Hpsn_nz Hpsn_ev].
  destruct (Hpsn_ev rem Hsat) as [_ Hpsn_eq].
  assert (Hsat1 : eval_cnf assign (bs_cnf st1 ++ rem) = true)
    by exact (eval_cnf_pref_rem assign _ _ rem dp Hdp Hsat).
  assert (Hlen_ab : List.length (rbv_bits a) = List.length (rbv_bits b)) by congruence.
  destruct (map2_emit_sound emit_or2 orb emit_or2_pref
              (fun asg x y s0 z s1 Hx Hy Hg =>
                 let (Hz, Hev) := emit_or2_sound asg x y s0 z s1 Hx Hy Hg in
                 conj Hz (fun r0 Hs0 => proj2 (Hev r0 Hs0)))
              assign _ _ _ _ _ Hlen_ab Hwfa Hwfb Hm)
    as (Hblen & Hbwf & Hbev).
  repeat split.
  - cbn; congruence.
  - exact Hbwf.
  - exact Hpsn_nz.
  - exact Hpsn_eq.
  - apply @Integers.same_bits_eq; intros i Hi.
    rewrite @Integers.bits_or by exact Hi.
    rewrite !eval_rail_val_testbit by exact Hi.
    cbn [rbv_bits]; apply (Hbev rem (Z.to_nat i)); [| exact Hsat1].
    rewrite Hla; unfold Integers.zwordsize in Hi; lia.
Qed.

Definition blast_xor_rail (sz : positive) (a b : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let '(bits, st1) := map2_emit emit_xor2 (rbv_bits a) (rbv_bits b) st in
  let '(psn, st2) := emit_or2 (rbv_psn a) (rbv_psn b) st1 in
  (mk_rail_bv sz bits psn, st2).

Theorem blast_xor_rail_sound : forall assign sz a b st out st' rem,
  wf_rail_lits sz a -> wf_rail_lits sz b ->
  blast_xor_rail sz a b st = (out, st') ->
  eval_cnf assign (bs_cnf st' ++ rem) = true ->
  wf_rail_lits sz out /\
  eval_rail_psn assign out = (eval_rail_psn assign a || eval_rail_psn assign b) /\
  eval_rail_val sz assign out = @Integers.xor sz (eval_rail_val sz assign a)
                                                 (eval_rail_val sz assign b).
Proof.
  intros assign sz a b st out st' rem
         ([Hwa Hla] & Hwfa & Hpa) ([Hwb Hlb] & Hwfb & Hpb) Hbl Hsat.
  unfold blast_xor_rail in Hbl.
  destruct (map2_emit emit_xor2 (rbv_bits a) (rbv_bits b) st) as [bits st1] eqn:Hm.
  destruct (emit_or2 (rbv_psn a) (rbv_psn b) st1) as [psn st2] eqn:Hp.
  inversion Hbl; subst out st2; clear Hbl.
  destruct (emit_or2_pref _ _ _ _ _ Hp) as [dp Hdp].
  destruct (emit_or2_sound assign _ _ _ _ _ Hpa Hpb Hp) as [Hpsn_nz Hpsn_ev].
  destruct (Hpsn_ev rem Hsat) as [_ Hpsn_eq].
  assert (Hsat1 : eval_cnf assign (bs_cnf st1 ++ rem) = true)
    by exact (eval_cnf_pref_rem assign _ _ rem dp Hdp Hsat).
  assert (Hlen_ab : List.length (rbv_bits a) = List.length (rbv_bits b)) by congruence.
  destruct (map2_emit_sound emit_xor2 xorb emit_xor2_pref
              (fun asg x y s0 z s1 Hx Hy Hg =>
                 let (Hz, Hev) := emit_xor2_sound asg x y s0 z s1 Hx Hy Hg in
                 conj Hz (fun r0 Hs0 => proj2 (Hev r0 Hs0)))
              assign _ _ _ _ _ Hlen_ab Hwfa Hwfb Hm)
    as (Hblen & Hbwf & Hbev).
  repeat split.
  - cbn; congruence.
  - exact Hbwf.
  - exact Hpsn_nz.
  - exact Hpsn_eq.
  - apply @Integers.same_bits_eq; intros i Hi.
    rewrite @Integers.bits_xor by exact Hi.
    rewrite !eval_rail_val_testbit by exact Hi.
    cbn [rbv_bits]; apply (Hbev rem (Z.to_nat i)); [| exact Hsat1].
    rewrite Hla; unfold Integers.zwordsize in Hi; lia.
Qed.

Fixpoint emit_or_list_acc (acc : lit) (ls : list lit) (st : blast_state)
  {struct ls} : lit * blast_state :=
  match ls with
  | [] => (acc, st)
  | x :: rest =>
      let '(acc1, st1) := emit_or2 acc x st in
      emit_or_list_acc acc1 rest st1
  end.

Definition emit_or_list (ls : list lit) (st : blast_state) : lit * blast_state :=
  match ls with
  | [] => (lit_false, st)
  | x :: rest => emit_or_list_acc x rest st
  end.

Lemma emit_or_list_acc_pref : forall ls acc st out st',
  emit_or_list_acc acc ls st = (out, st') -> exists d, bs_cnf st' = d ++ bs_cnf st.
Proof.
  induction ls as [| x rest IH]; intros acc st out st' H; cbn [emit_or_list_acc] in H.
  - inversion H; subst; exists []; reflexivity.
  - destruct (emit_or2 acc x st) as [acc1 st1] eqn:He.
    destruct (emit_or2_pref acc x st acc1 st1 He) as [d1 Hd1].
    destruct (IH acc1 st1 out st' H) as [d2 Hd2].
    exists (d2 ++ d1); rewrite Hd2, Hd1, app_assoc; reflexivity.
Qed.

Lemma emit_or_list_pref : forall ls st out st',
  emit_or_list ls st = (out, st') -> exists d, bs_cnf st' = d ++ bs_cnf st.
Proof.
  intros [| x rest] st out st' H; cbn [emit_or_list] in H.
  - inversion H; subst; exists []; reflexivity.
  - exact (emit_or_list_acc_pref rest x st out st' H).
Qed.

Lemma emit_or_list_acc_sound : forall assign ls acc st out st' rem,
  acc <> 0%Z ->
  wf_lits_nonzero ls ->
  emit_or_list_acc acc ls st = (out, st') ->
  eval_cnf assign (bs_cnf st' ++ rem) = true ->
  out <> 0%Z /\
  eval_lit assign out = (eval_lit assign acc || existsb (eval_lit assign) ls).
Proof.
  intros assign ls; induction ls as [| x rest IH]; intros acc st out st' rem Hacc Hwf Hemit Hsat;
    cbn [emit_or_list_acc] in Hemit.
  - inversion Hemit; subst; split;
      [exact Hacc | cbn; rewrite orb_false_r; reflexivity].
  - inversion Hwf as [| ? ? Hx Hwfr]; subst.
    destruct (emit_or2 acc x st) as [acc1 st1] eqn:He.
    destruct (emit_or_list_acc_pref rest acc1 st1 out st' Hemit) as [d2 Hd2].
    assert (Hsat1 : eval_cnf assign (bs_cnf st1 ++ rem) = true)
      by exact (eval_cnf_pref_rem assign _ _ rem d2 Hd2 Hsat).
    destruct (emit_or2_sound assign acc x st acc1 st1 Hacc Hx He) as [Hacc1_nz Hacc1_ev].
    destruct (IH acc1 st1 out st' rem Hacc1_nz Hwfr Hemit Hsat) as [Hout_nz Hout_ev].
    split; [exact Hout_nz |].
    rewrite Hout_ev, (proj2 (Hacc1_ev rem Hsat1)); cbn [existsb]; rewrite orb_assoc; reflexivity.
Qed.

Lemma emit_or_list_sound : forall assign ls st out st' rem,
  eval_lit assign lit_false = false ->
  wf_lits_nonzero ls ->
  emit_or_list ls st = (out, st') ->
  eval_cnf assign (bs_cnf st' ++ rem) = true ->
  out <> 0%Z /\
  eval_lit assign out = existsb (eval_lit assign) ls.
Proof.
  intros assign [| x rest] st out st' rem Hlf Hwf Hemit Hsat; cbn [emit_or_list] in Hemit.
  - inversion Hemit; subst; split; [unfold lit_false; discriminate | exact Hlf].
  - inversion Hwf as [| ? ? Hx Hwfr]; subst.
    exact (emit_or_list_acc_sound assign rest x st out st' rem Hx Hwfr Hemit Hsat).
Qed.

(** *** 4.3 Equality, Select, and Freeze 2-Rail Encoders *)

Definition blast_eq_rail (sz : positive) (a b : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let '(xor_bits, st1) := map2_emit emit_xor2 (rbv_bits a) (rbv_bits b) st in
  let '(any_diff, st2) := emit_or_list xor_bits st1 in
  let '(psn, st3)      := emit_or2 (rbv_psn a) (rbv_psn b) st2 in
  (mk_rail_bv 1%positive [neg_lit any_diff] psn, st3).

Fixpoint mux_bits_list (sel : lit) (ts fs : list lit) (st : blast_state)
  {struct ts} : list lit * blast_state :=
  match ts, fs with
  | t :: rt, f :: rf =>
      let '(m, st1) := emit_mux2 sel t f st in
      let '(ms, st2) := mux_bits_list sel rt rf st1 in
      (m :: ms, st2)
  | _, _ => ([], st)
  end.

Definition blast_select_rail (sz : positive) (cond tv fv : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let c_bit := List.hd lit_false (rbv_bits cond) in
  let '(bits, st1)   := mux_bits_list c_bit (rbv_bits tv) (rbv_bits fv) st in
  let '(br_psn, st2) := emit_mux2 c_bit (rbv_psn tv) (rbv_psn fv) st1 in
  let '(psn, st3)    := emit_or2 (rbv_psn cond) br_psn st2 in
  (mk_rail_bv sz bits psn, st3).

Fixpoint alloc_fresh_bits (n : nat) (st : blast_state)
  {struct n} : list lit * blast_state :=
  match n with
  | O => ([], st)
  | S n' =>
      let '(v, st1) := alloc_var st in
      let '(vs, st2) := alloc_fresh_bits n' st1 in
      (v :: vs, st2)
  end.

Definition blast_freeze_rail (sz : positive) (op : rail_bv) (st : blast_state)
  : rail_bv * blast_state :=
  let '(fresh_bits, st1) := alloc_fresh_bits (Pos.to_nat sz) st in
  let '(bits, st2) := mux_bits_list (rbv_psn op) fresh_bits (rbv_bits op) st1 in
  (mk_rail_bv sz bits lit_false, st2).

Lemma mux_bits_list_pref : forall sel ts fs st ms st',
  mux_bits_list sel ts fs st = (ms, st') -> exists d, bs_cnf st' = d ++ bs_cnf st.
Proof.
  intros sel ts.
  induction ts as [| t rt IH]; intros [| f rf] st ms st' H; cbn [mux_bits_list] in H.
  - inversion H; subst; exists []; reflexivity.
  - inversion H; subst; exists []; reflexivity.
  - inversion H; subst; exists []; reflexivity.
  - destruct (emit_mux2 sel t f st) as [m st1] eqn:Hm.
    destruct (mux_bits_list sel rt rf st1) as [mr st2] eqn:Hmr.
    inversion H; subst; clear H.
    assert (Hd1 : exists d1, bs_cnf st1 = d1 ++ bs_cnf st).
    { unfold emit_mux2 in Hm; destruct (alloc_var st) as [out st0] eqn:Ha;
        inversion Hm; subst; clear Hm;
        unfold alloc_var in Ha; inversion Ha; subst;
        exact (add_clauses_pref _ _). }
    destruct Hd1 as [d1 Hd1].
    destruct (IH rf st1 mr st' Hmr) as [d2 Hd2].
    exists (d2 ++ d1); rewrite Hd2, Hd1, app_assoc; reflexivity.
Qed.

Lemma mux_bits_list_sound : forall assign sel ts fs st ms st' rem,
  sel <> 0%Z ->
  List.length ts = List.length fs ->
  wf_lits_nonzero ts ->
  wf_lits_nonzero fs ->
  mux_bits_list sel ts fs st = (ms, st') ->
  eval_cnf assign (bs_cnf st' ++ rem) = true ->
  List.length ms = List.length ts /\
  wf_lits_nonzero ms /\
  List.map (eval_lit assign) ms =
  (if eval_lit assign sel then List.map (eval_lit assign) ts
   else List.map (eval_lit assign) fs).
Proof.
  intros assign sel ts.
  induction ts as [| t rt IH]; intros [| f rf] st ms st' rem Hsel Hlen Hwt Hwf Hm Hsat;
    try discriminate; cbn [mux_bits_list] in Hm.
  - inversion Hm; subst; repeat split; [constructor | destruct (eval_lit assign sel); reflexivity].
  - inversion Hwt as [| ? ? Ht Hwrt]; subst.
    inversion Hwf as [| ? ? Hf Hwrf]; subst.
    injection Hlen as Hlen'.
    destruct (emit_mux2 sel t f st) as [m st1] eqn:He.
    destruct (mux_bits_list sel rt rf st1) as [mr st2] eqn:Hmr.
    inversion Hm; subst; clear Hm.
    destruct (mux_bits_list_pref sel rt rf st1 mr st' Hmr) as [d2 Hd2].
    assert (Hs1 : eval_cnf assign (bs_cnf st1 ++ rem) = true)
      by exact (eval_cnf_pref_rem assign _ _ rem d2 Hd2 Hsat).
    destruct (emit_mux2_sound assign sel t f st m st1 Hsel Ht Hf He) as [Hm_nz Hm_ev].
    destruct (IH rf st1 mr st' rem Hsel Hlen' Hwrt Hwrf Hmr Hsat)
      as (Hmr_len & Hmr_wf & Hmr_ev).
    repeat split.
    + cbn; rewrite Hmr_len; reflexivity.
    + constructor; [exact Hm_nz | exact Hmr_wf].
    + cbn [List.map]; rewrite (proj2 (Hm_ev rem Hs1)), Hmr_ev.
      destruct (eval_lit assign sel); reflexivity.
Qed.

Lemma alloc_fresh_bits_spec : forall n st vs st',
  alloc_fresh_bits n st = (vs, st') ->
  bs_cnf st' = bs_cnf st /\
  List.length vs = n /\
  wf_lits_nonzero vs.
Proof.
  induction n as [| n' IH]; intros st vs st' H; cbn [alloc_fresh_bits] in H.
  - inversion H; subst; repeat split; constructor.
  - destruct (alloc_var st) as [v st1] eqn:Hv.
    destruct (alloc_fresh_bits n' st1) as [vr st2] eqn:Hr.
    inversion H; subst; clear H.
    unfold alloc_var in Hv; inversion Hv; subst v st1; clear Hv.
    destruct (IH _ vr st' Hr) as (Hcnf & Hlen & Hwf).
    cbn [bs_cnf] in Hcnf.
    repeat split; [exact Hcnf | cbn; rewrite Hlen; reflexivity | constructor; [discriminate | exact Hwf]].
Qed.

Theorem blast_freeze_rail_sound : forall assign sz op st out st' rem,
  eval_lit assign lit_false = false ->
  wf_rail_lits sz op ->
  blast_freeze_rail sz op st = (out, st') ->
  eval_cnf assign (bs_cnf st' ++ rem) = true ->
  wf_rail_lits sz out /\
  eval_rail_psn assign out = false /\
  (eval_rail_psn assign op = false ->
   eval_rail_val sz assign out = eval_rail_val sz assign op).
Proof.
  intros assign sz op st out st' rem Hlf ([Hwo Hlo] & Hwfo & Hpo) Hfrz Hsat.
  unfold blast_freeze_rail in Hfrz.
  destruct (alloc_fresh_bits (Pos.to_nat sz) st) as [fresh_bits st1] eqn:Hfb.
  destruct (mux_bits_list (rbv_psn op) fresh_bits (rbv_bits op) st1) as [bits st2] eqn:Hmux.
  inversion Hfrz; subst out st2; clear Hfrz.
  destruct (alloc_fresh_bits_spec _ _ _ _ Hfb) as (_ & Hflen & Hfwf).
  assert (Hlen_eq : List.length fresh_bits = List.length (rbv_bits op)) by congruence.
  destruct (mux_bits_list_sound assign (rbv_psn op) fresh_bits (rbv_bits op)
              st1 bits st' rem Hpo Hlen_eq Hfwf Hwfo Hmux Hsat)
    as (Hblen & Hbwf & Hbev).
  repeat split.
  - cbn; congruence.
  - exact Hbwf.
  - discriminate.
  - exact Hlf.
  - intros Hop_def; unfold eval_rail_psn in Hop_def.
    unfold eval_rail_val; cbn [rbv_bits].
    rewrite Hbev, Hop_def; reflexivity.
Qed.

(** *** 4.4 Refinement Counterexample Query & End-to-End UNSAT Soundness *)

(** Given [src_no_ub : lit] (true when all source UB guards hold),
    [src_r : rail_bv], and [tgt_r : rail_bv] of width [sz], constructs a CNF
    asserting the existence of a refinement counterexample:
      [src_no_ub /\ ~src_psn /\ (tgt_psn \/ (tgt_val <> src_val))]. *)
Definition blast_refinement_cex_gates (sz : positive) (src_no_ub : lit)
                                      (src_r tgt_r : rail_bv) (st : blast_state)
  : lit * blast_state :=
  let '(xor_bits, st1) := map2_emit emit_xor2 (rbv_bits src_r) (rbv_bits tgt_r) st in
  let '(val_diff, st2) := emit_or_list xor_bits st1 in
  let '(bad_tgt, st3)  := emit_or2 (rbv_psn tgt_r) val_diff st2 in
  let '(def_bad, st4)  := emit_and2 (neg_lit (rbv_psn src_r)) bad_tgt st3 in
  emit_and2 src_no_ub def_bad st4.

Definition blast_refinement_cex (sz : positive) (src_no_ub : lit)
                                (src_r tgt_r : rail_bv) (st : blast_state)
  : cnf :=
  let '(cex_lit, st5) := blast_refinement_cex_gates sz src_no_ub src_r tgt_r st in
  bs_cnf (add_clauses [[cex_lit]] st5).

Lemma existsb_xor_bits_diff : forall sz assign src_r tgt_r xor_bits,
  wf_rail_bv sz src_r ->
  wf_rail_bv sz tgt_r ->
  List.length xor_bits = Pos.to_nat sz ->
  (forall k, (k < Pos.to_nat sz)%nat ->
     List.nth k (List.map (eval_lit assign) xor_bits) false =
     xorb (List.nth k (List.map (eval_lit assign) (rbv_bits src_r)) false)
          (List.nth k (List.map (eval_lit assign) (rbv_bits tgt_r)) false)) ->
  existsb (eval_lit assign) xor_bits = false ->
  eval_rail_val sz assign tgt_r = eval_rail_val sz assign src_r.
Proof.
  intros sz assign src_r tgt_r xor_bits [_ Hls] [_ Hlt] Hlx Hxor Hex_false.
  apply @Integers.same_bits_eq; intros i Hi.
  rewrite !eval_rail_val_testbit by exact Hi.
  assert (Hk : (Z.to_nat i < Pos.to_nat sz)%nat)
    by (unfold Integers.zwordsize in Hi; lia).
  pose proof (Hxor (Z.to_nat i) Hk) as Hxk.
  assert (Hxor_k_false : List.nth (Z.to_nat i) (List.map (eval_lit assign) xor_bits) false = false).
  { destruct (existsb (eval_lit assign) xor_bits) eqn:He; [discriminate Hex_false |].
    assert (Hall : forall z, In z xor_bits -> eval_lit assign z = false).
    { intros z Hz; destruct (eval_lit assign z) eqn:Hzv; [| reflexivity].
      assert (Hex_t : existsb (eval_lit assign) xor_bits = true)
        by (apply existsb_exists; exists z; split; assumption).
      congruence. }
    assert (Hin_map : In (List.nth (Z.to_nat i) (List.map (eval_lit assign) xor_bits) false)
                         (List.map (eval_lit assign) xor_bits))
      by (apply nth_In; rewrite length_map, Hlx; exact Hk).
    apply in_map_iff in Hin_map as [z [Hz_eq Hz_in]].
    rewrite <- Hz_eq; exact (Hall z Hz_in). }
  rewrite Hxor_k_false in Hxk; symmetry in Hxk.
  apply (proj1 (xorb_false_iff _ _)) in Hxk; symmetry; exact Hxk.
Qed.

Lemma blast_refinement_cex_unsat_core :
  forall (sz : positive) (src_no_ub : lit) (src_r tgt_r : rail_bv)
         (st : blast_state) (assign : positive -> bool),
    src_no_ub <> 0%Z ->
    wf_rail_lits sz src_r ->
    wf_rail_lits sz tgt_r ->
    (forall a, eval_cnf a (blast_refinement_cex sz src_no_ub src_r tgt_r st) = false) ->
    eval_lit assign lit_false = false ->
    eval_cnf assign (bs_cnf (snd (blast_refinement_cex_gates sz src_no_ub src_r tgt_r st))) = true ->
    eval_lit assign src_no_ub = true ->
    eval_rail_psn assign src_r = false ->
    eval_rail_psn assign tgt_r = false /\
    eval_rail_val sz assign tgt_r = eval_rail_val sz assign src_r.
Proof.
  intros sz src_no_ub src_r tgt_r st assign Hnub
         ([Hws Hls] & Hwfs & Hps) ([Hwt Hlt] & Hwft & Hpt)
         Hunsat Hlf Hgates Hno_ub Hsrc_def.
  pose proof (Hunsat assign) as Hquery_false.
  unfold blast_refinement_cex, blast_refinement_cex_gates in *.
  destruct (map2_emit emit_xor2 (rbv_bits src_r) (rbv_bits tgt_r) st)
    as [xor_bits st1] eqn:Hm.
  destruct (emit_or_list xor_bits st1) as [val_diff st2] eqn:Horl.
  destruct (emit_or2 (rbv_psn tgt_r) val_diff st2) as [bad_tgt st3] eqn:Hbad.
  destruct (emit_and2 (neg_lit (rbv_psn src_r)) bad_tgt st3) as [def_bad st4] eqn:Hdef.
  destruct (emit_and2 src_no_ub def_bad st4) as [cex_lit st5] eqn:Hcex.
  cbn [snd] in Hgates.
  unfold add_clauses in Hquery_false.
  cbn [prepend_clauses_rev bs_cnf] in Hquery_false.
  unfold eval_cnf in Hquery_false; cbn [forallb] in Hquery_false.
  change (forallb (fun '(_, c) => eval_clause assign c) (bs_cnf st5))
    with (eval_cnf assign (bs_cnf st5)) in Hquery_false.
  rewrite Hgates in Hquery_false; cbn in Hquery_false.
  rewrite orb_false_r, andb_true_r in Hquery_false.
  assert (Hlen_st : List.length (rbv_bits src_r) = List.length (rbv_bits tgt_r)) by congruence.
  destruct (map2_emit_sound emit_xor2 xorb emit_xor2_pref
              (fun asg x y s0 z s1 Hx Hy Hg =>
                 let (Hz, Hev) := emit_xor2_sound asg x y s0 z s1 Hx Hy Hg in
                 conj Hz (fun r0 Hs0 => proj2 (Hev r0 Hs0)))
              assign _ _ _ _ _ Hlen_st Hwfs Hwft Hm)
    as (Hxlen & Hxwf & Hxev).
  destruct (emit_or_list_pref _ _ _ _ Horl) as [d2 Hd2].
  destruct (emit_or2_pref _ _ _ _ _ Hbad) as [d3 Hd3].
  destruct (emit_and2_pref _ _ _ _ _ Hdef) as [d4 Hd4].
  destruct (emit_and2_pref _ _ _ _ _ Hcex) as [d5 Hd5].
  assert (Hs5 : eval_cnf assign (bs_cnf st5 ++ []) = true)
    by (rewrite app_nil_r; exact Hgates).
  assert (Hs4 : eval_cnf assign (bs_cnf st4 ++ []) = true)
    by exact (eval_cnf_pref_rem assign _ _ [] d5 Hd5 Hs5).
  assert (Hs3 : eval_cnf assign (bs_cnf st3 ++ []) = true)
    by exact (eval_cnf_pref_rem assign _ _ [] d4 Hd4 Hs4).
  assert (Hs2 : eval_cnf assign (bs_cnf st2 ++ []) = true)
    by exact (eval_cnf_pref_rem assign _ _ [] d3 Hd3 Hs3).
  assert (Hs1 : eval_cnf assign (bs_cnf st1 ++ []) = true)
    by exact (eval_cnf_pref_rem assign _ _ [] d2 Hd2 Hs2).
  destruct (emit_or_list_sound assign xor_bits st1 val_diff st2
              [] Hlf Hxwf Horl Hs2) as [Hvd_nz Hvd_ev].
  destruct (emit_or2_sound assign (rbv_psn tgt_r) val_diff st2 bad_tgt st3
              Hpt Hvd_nz Hbad) as [Hbt_nz Hbt_ev].
  assert (Hnps_nz : neg_lit (rbv_psn src_r) <> 0%Z)
    by (destruct (rbv_psn src_r); cbn; congruence).
  destruct (emit_and2_sound assign (neg_lit (rbv_psn src_r)) bad_tgt st3 def_bad st4
              Hnps_nz Hbt_nz Hdef) as [Hdb_nz Hdb_ev].
  destruct (emit_and2_sound assign src_no_ub def_bad st4 cex_lit st5
              Hnub Hdb_nz Hcex) as [_ Hcex_ev].
  pose proof (proj2 (Hcex_ev [] (eq_ind_r (fun c => eval_cnf assign c = true)
                                          Hgates (app_nil_r (bs_cnf st5))))) as Hcex_eq.
  rewrite Hcex_eq, Hno_ub, (proj2 (Hdb_ev [] Hs4)),
          (eval_neg_lit_nonzero assign (rbv_psn src_r) Hps) in Hquery_false.
  unfold eval_rail_psn in Hsrc_def; rewrite Hsrc_def in Hquery_false; cbn in Hquery_false.
  rewrite (proj2 (Hbt_ev [] Hs3)), Hvd_ev in Hquery_false.
  apply orb_false_iff in Hquery_false as [Htgt_def Hxor_false].
  split; [exact Htgt_def |].
  apply (existsb_xor_bits_diff sz assign src_r tgt_r xor_bits
           (conj Hws Hls) (conj Hwt Hlt)); [congruence | | exact Hxor_false].
  intros k Hk; apply (Hxev [] k); [congruence | exact Hs1].
Qed.

Theorem blast_refinement_cex_unsat_sound :
  forall (sz : positive) (src_no_ub : lit) (src_r tgt_r : rail_bv)
         (st : blast_state) (pf : list lrat_step) (assign : positive -> bool),
    src_no_ub <> 0%Z ->
    wf_rail_lits sz src_r ->
    wf_rail_lits sz tgt_r ->
    check_lrat_unsat (blast_refinement_cex sz src_no_ub src_r tgt_r st) pf = true ->
    eval_lit assign lit_false = false ->
    eval_cnf assign (bs_cnf (snd (blast_refinement_cex_gates sz src_no_ub src_r tgt_r st))) = true ->
    eval_lit assign src_no_ub = true ->
    eval_rail_psn assign src_r = false ->
    eval_rail_psn assign tgt_r = false /\
    eval_rail_val sz assign tgt_r = eval_rail_val sz assign src_r.
Proof.
  intros sz src_no_ub src_r tgt_r st pf assign Hnub Hws Hwt Hunsat.
  exact (blast_refinement_cex_unsat_core sz src_no_ub src_r tgt_r st assign
           Hnub Hws Hwt (check_lrat_unsat_sound _ pf Hunsat)).
Qed.

Theorem blast_refinement_cex_auto_unsat_sound :
  forall (fuel : nat) (sz : positive) (src_no_ub : lit) (src_r tgt_r : rail_bv)
         (st : blast_state) (assign : positive -> bool),
    src_no_ub <> 0%Z ->
    wf_rail_lits sz src_r ->
    wf_rail_lits sz tgt_r ->
    solve_cnf_unsat fuel (blast_refinement_cex sz src_no_ub src_r tgt_r st) = true ->
    eval_lit assign lit_false = false ->
    eval_cnf assign (bs_cnf (snd (blast_refinement_cex_gates sz src_no_ub src_r tgt_r st))) = true ->
    eval_lit assign src_no_ub = true ->
    eval_rail_psn assign src_r = false ->
    eval_rail_psn assign tgt_r = false /\
    eval_rail_val sz assign tgt_r = eval_rail_val sz assign src_r.
Proof.
  intros fuel sz src_no_ub src_r tgt_r st assign Hnub Hws Hwt Hunsat.
  exact (blast_refinement_cex_unsat_core sz src_no_ub src_r tgt_r st assign
           Hnub Hws Hwt (fun a => solve_cnf_unsat_sound fuel _ a Hunsat)).
Qed.

(** ** 6. Monotone [sat_blast_st], Peephole Gates, and Complete 2-Rail Arithmetic/Shift/Cast/ICmp Encoders *)

(** *** 6.1 Monotone Variable Bounds, [step_spec], and Peephole Gate Combinators *)

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

Lemma wf_lit_bound_true : forall bound,
  (2 <= bound)%positive -> wf_lit_bound bound lit_true.
Proof.
  intros bound H; cbn; lia.
Qed.

Lemma wf_lit_bound_false : forall bound,
  (2 <= bound)%positive -> wf_lit_bound bound lit_false.
Proof.
  intros bound H; cbn; lia.
Qed.

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

Lemma wf_lits_bound_neg : forall bound ls,
  wf_lits_bound bound ls -> wf_lits_bound bound (List.map neg_lit ls).
Proof.
  intros bound ls H; induction H as [| x r Hx Hr IH]; cbn; constructor;
    [exact (wf_lit_bound_neg bound x Hx) | exact IH].
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
  - rewrite (eval_lits_agree bound a1 a2 _ Hag Hls); reflexivity.
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

Lemma sat_eval_lit_true : forall asg st,
  sat_blast_st asg st -> eval_lit asg lit_true = true.
Proof.
  intros asg st (_ & Ha1 & _); exact Ha1.
Qed.

Lemma sat_eval_lit_false : forall asg st,
  sat_blast_st asg st -> eval_lit asg lit_false = false.
Proof.
  intros asg st (_ & Ha1 & _); cbn; rewrite Ha1; reflexivity.
Qed.

Lemma init_blast_state_sat :
  sat_blast_st (fun _ => true) (init_blast_state 2%positive).
Proof.
  repeat split.
  - cbn; lia.
  - constructor; [| constructor].
    cbn; constructor; [cbn; lia | constructor].
Qed.

Definition step_spec (st st' : blast_state) (asg asg' : positive -> bool) : Prop :=
  (bs_next_var st <= bs_next_var st')%positive /\
  agree_below (bs_next_var st) asg asg' /\
  sat_blast_st asg' st'.

Lemma step_spec_refl : forall st asg,
  sat_blast_st asg st -> step_spec st st asg asg.
Proof.
  intros st asg Hsat; split; [lia | split; [apply agree_below_refl | exact Hsat]].
Qed.

Lemma step_spec_trans : forall st1 st2 st3 a1 a2 a3,
  step_spec st1 st2 a1 a2 ->
  step_spec st2 st3 a2 a3 ->
  step_spec st1 st3 a1 a3.
Proof.
  intros st1 st2 st3 a1 a2 a3 (Hle12 & Hag12 & _) (Hle23 & Hag23 & Hsat3).
  split; [lia | split; [| exact Hsat3]].
  exact (agree_below_trans _ a1 a2 a3 Hag12 (agree_below_le _ _ a2 a3 Hle12 Hag23)).
Qed.

Lemma step_spec_eval_lit : forall st st' asg asg' l,
  step_spec st st' asg asg' ->
  wf_lit_bound (bs_next_var st) l ->
  eval_lit asg' l = eval_lit asg l.
Proof.
  intros st st' asg asg' l (_ & Hag & _) Hl; symmetry; exact (eval_lit_agree _ asg asg' l Hag Hl).
Qed.

Lemma step_spec_eval_lits : forall st st' asg asg' ls,
  step_spec st st' asg asg' ->
  wf_lits_bound (bs_next_var st) ls ->
  List.map (eval_lit asg') ls = List.map (eval_lit asg) ls.
Proof.
  intros st st' asg asg' ls (_ & Hag & _) Hls; symmetry; exact (eval_lits_agree _ asg asg' ls Hag Hls).
Qed.

Lemma prepend_clauses_rev_sat_intro : forall asg bound cls cid acc cid' out,
  wf_cnf_bound bound acc ->
  eval_cnf asg acc = true ->
  Forall (wf_clause_bound bound) cls ->
  (forall cl, In cl cls -> eval_clause asg cl = true) ->
  prepend_clauses_rev cid cls acc = (cid', out) ->
  wf_cnf_bound bound out /\ eval_cnf asg out = true.
Proof.
  intros asg bound cls; induction cls as [| c rest IH];
    intros cid acc cid' out Hacc Hev HF Hsat Happ; cbn in Happ.
  - inversion Happ; subst; split; assumption.
  - inversion HF as [| ? ? Hc Hrest]; subst.
    apply (IH (Pos.succ cid) ((cid, c) :: acc) cid' out).
    + constructor; [exact Hc | exact Hacc].
    + unfold eval_cnf in Hev |- *; cbn [forallb]; rewrite (Hsat c (or_introl eq_refl)), Hev; reflexivity.
    + exact Hrest.
    + intros cl Hin; exact (Hsat cl (or_intror Hin)).
    + exact Happ.
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
  destruct (prepend_clauses_rev (bs_next_cid st) cls (bs_cnf st)) as [cid' new_cnf] eqn:Happ.
  destruct (prepend_clauses_rev_sat_intro asg (bs_next_var st) cls
              (bs_next_cid st) (bs_cnf st) cid' new_cnf Hwf_st Hev_st Hwf_cls Hcls Happ)
    as [Hwf_new Hev_new].
  repeat split; cbn -[eval_cnf]; assumption.
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
  exists asg1; repeat split; cbn -[eval_cnf set_asg].
  - lia.
  - exact Hag.
  - lia.
  - apply (wf_cnf_bound_mono v (Pos.succ v)); [lia | exact Hwf].
  - unfold asg1; rewrite <- (Hag 1%positive) by lia; exact Ha1.
  - rewrite <- (eval_cnf_agree v asg asg1 (bs_cnf st) Hag Hwf); exact Hev.
  - lia.
  - unfold asg1; apply set_asg_same.
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
  induction bs as [| b br IH]; intros asg st lits st' Hsat Hal; cbn [alloc_fresh_bits List.length] in Hal.
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
                  [[neg_lit vlit; a]; [neg_lit vlit; b];
                   [vlit; neg_lit a; neg_lit b]] st1) =
                bs_next_var st1)
    by (unfold add_clauses; destruct (prepend_clauses_rev _ _ _); reflexivity).
  assert (Hwa1 : wf_lit_bound (bs_next_var st1) a)
    by exact (wf_lit_bound_mono _ _ a Hle1 Hwa).
  assert (Hwb1 : wf_lit_bound (bs_next_var st1) b)
    by exact (wf_lit_bound_mono _ _ b Hle1 Hwb).
  assert (Hcls_wf : Forall (wf_clause_bound (bs_next_var st1))
                      [[neg_lit vlit; a]; [neg_lit vlit; b];
                       [vlit; neg_lit a; neg_lit b]]).
  { repeat constructor; try assumption; apply wf_lit_bound_neg; assumption. }
  assert (Hcls_sat : forall cl,
            In cl [[neg_lit vlit; a]; [neg_lit vlit; b];
                   [vlit; neg_lit a; neg_lit b]] ->
            eval_clause asg1 cl = true).
  { intros cl [<- | [<- | [<- | []]]]; cbn [eval_clause existsb];
      rewrite ?(eval_neg_lit_nonzero asg1 vlit (wf_lit_bound_nonzero _ _ Hwf_v)),
              ?(eval_neg_lit_nonzero asg1 a (wf_lit_bound_nonzero _ _ Hwa1)),
              ?(eval_neg_lit_nonzero asg1 b (wf_lit_bound_nonzero _ _ Hwb1)),
              Hev_v,
              <- ?(eval_lit_agree (bs_next_var st) asg asg1 a Hag1 Hwa),
              <- ?(eval_lit_agree (bs_next_var st) asg asg1 b Hag1 Hwb);
      destruct (eval_lit asg a), (eval_lit asg b); reflexivity. }
  pose proof (add_clauses_sat_intro asg1 st1 _ Hge2_1 Ha1_1 Hwf1 Hcls_wf Hev1 Hcls_sat) as Hadd.
  exists asg1; repeat split; try rewrite Hbs;
    [exact Hle1 | exact Hag1
     | exact (proj1 (proj1 Hadd)) | exact (proj2 (proj1 Hadd))
     | exact (proj1 (proj2 Hadd)) | exact (proj2 (proj2 Hadd))
     | exact Hwf_v].
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
                  [[vlit; neg_lit a]; [vlit; neg_lit b];
                   [neg_lit vlit; a; b]] st1) =
                bs_next_var st1)
    by (unfold add_clauses; destruct (prepend_clauses_rev _ _ _); reflexivity).
  assert (Hwa1 : wf_lit_bound (bs_next_var st1) a)
    by exact (wf_lit_bound_mono _ _ a Hle1 Hwa).
  assert (Hwb1 : wf_lit_bound (bs_next_var st1) b)
    by exact (wf_lit_bound_mono _ _ b Hle1 Hwb).
  assert (Hcls_wf : Forall (wf_clause_bound (bs_next_var st1))
                      [[vlit; neg_lit a]; [vlit; neg_lit b];
                       [neg_lit vlit; a; b]]).
  { repeat constructor; try assumption; apply wf_lit_bound_neg; assumption. }
  assert (Hcls_sat : forall cl,
            In cl [[vlit; neg_lit a]; [vlit; neg_lit b];
                   [neg_lit vlit; a; b]] ->
            eval_clause asg1 cl = true).
  { intros cl [<- | [<- | [<- | []]]]; cbn [eval_clause existsb];
      rewrite ?(eval_neg_lit_nonzero asg1 vlit (wf_lit_bound_nonzero _ _ Hwf_v)),
              ?(eval_neg_lit_nonzero asg1 a (wf_lit_bound_nonzero _ _ Hwa1)),
              ?(eval_neg_lit_nonzero asg1 b (wf_lit_bound_nonzero _ _ Hwb1)),
              Hev_v,
              <- ?(eval_lit_agree (bs_next_var st) asg asg1 a Hag1 Hwa),
              <- ?(eval_lit_agree (bs_next_var st) asg asg1 b Hag1 Hwb);
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
                  [[neg_lit vlit; a; b];
                   [neg_lit vlit; neg_lit a; neg_lit b];
                   [vlit; neg_lit a; b];
                   [vlit; a; neg_lit b]] st1) =
                bs_next_var st1)
    by (unfold add_clauses; destruct (prepend_clauses_rev _ _ _); reflexivity).
  assert (Hwa1 : wf_lit_bound (bs_next_var st1) a)
    by exact (wf_lit_bound_mono _ _ a Hle1 Hwa).
  assert (Hwb1 : wf_lit_bound (bs_next_var st1) b)
    by exact (wf_lit_bound_mono _ _ b Hle1 Hwb).
  assert (Hcls_wf : Forall (wf_clause_bound (bs_next_var st1))
                      [[neg_lit vlit; a; b];
                       [neg_lit vlit; neg_lit a; neg_lit b];
                       [vlit; neg_lit a; b];
                       [vlit; a; neg_lit b]]).
  { repeat constructor; try assumption; apply wf_lit_bound_neg; assumption. }
  assert (Hcls_sat : forall cl,
            In cl [[neg_lit vlit; a; b];
                   [neg_lit vlit; neg_lit a; neg_lit b];
                   [vlit; neg_lit a; b];
                   [vlit; a; neg_lit b]] ->
            eval_clause asg1 cl = true).
  { intros cl [<- | [<- | [<- | [<- | []]]]]; cbn [eval_clause existsb];
      rewrite ?(eval_neg_lit_nonzero asg1 vlit (wf_lit_bound_nonzero _ _ Hwf_v)),
              ?(eval_neg_lit_nonzero asg1 a (wf_lit_bound_nonzero _ _ Hwa1)),
              ?(eval_neg_lit_nonzero asg1 b (wf_lit_bound_nonzero _ _ Hwb1)),
              Hev_v,
              <- ?(eval_lit_agree (bs_next_var st) asg asg1 a Hag1 Hwa),
              <- ?(eval_lit_agree (bs_next_var st) asg asg1 b Hag1 Hwb);
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
    by (unfold add_clauses; destruct (prepend_clauses_rev _ _ _); reflexivity).
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
              <- ?(eval_lit_agree (bs_next_var st) asg asg1 sel Hag1 Hws),
              <- ?(eval_lit_agree (bs_next_var st) asg asg1 tl Hag1 Hwt),
              <- ?(eval_lit_agree (bs_next_var st) asg asg1 fl Hag1 Hwf0);
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

Lemma emit_or_list_acc_sat : forall ls acc asg st out st',
  wf_lit_bound (bs_next_var st) acc ->
  wf_lits_bound (bs_next_var st) ls ->
  sat_blast_st asg st ->
  emit_or_list_acc acc ls st = (out, st') ->
  exists asg',
    (bs_next_var st <= bs_next_var st')%positive /\
    agree_below (bs_next_var st) asg asg' /\
    sat_blast_st asg' st' /\
    wf_lit_bound (bs_next_var st') out.
Proof.
  induction ls as [| x rest IH]; intros acc asg st out st' Hacc Hwf Hsat Hemit;
    cbn [emit_or_list_acc] in Hemit.
  - inversion Hemit; subst; exists asg;
      split; [lia | split; [apply agree_below_refl | split; assumption]].
  - inversion Hwf as [| ? ? Hx Hwfr]; subst.
    destruct (emit_or2 acc x st) as [acc1 st1] eqn:He.
    destruct (emit_or2_sat asg acc x st acc1 st1 Hsat Hacc Hx He)
      as (asg1 & Hle1 & Hag1 & Hsat1 & Hwf_acc1).
    destruct (IH acc1 asg1 st1 out st' Hwf_acc1
                (wf_lits_bound_mono _ _ rest Hle1 Hwfr) Hsat1 Hemit)
      as (asg2 & Hle2 & Hag2 & Hsat2 & Hwf_out).
    exists asg2; split; [lia | split].
    + exact (agree_below_trans _ asg asg1 asg2 Hag1
               (agree_below_le _ _ asg1 asg2 Hle1 Hag2)).
    + split; [exact Hsat2 | exact Hwf_out].
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
  intros [| x rest] asg st out st' Hwf Hsat Hemit; cbn [emit_or_list] in Hemit.
  - inversion Hemit; subst; exists asg;
      split; [lia | split; [apply agree_below_refl | split; [exact Hsat |
      cbn; pose proof (proj1 (proj1 Hsat)); lia]]].
  - inversion Hwf as [| ? ? Hx Hwfr]; subst.
    exact (emit_or_list_acc_sat rest x asg st out st' Hx Hwfr Hsat Hemit).
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
    try discriminate; cbn [mux_bits_list] in Hm.
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

Definition emit_and2_opt (a b : lit) (st : blast_state) : lit * blast_state :=
  if Z.eqb a lit_false || Z.eqb b lit_false then (lit_false, st)
  else if Z.eqb a lit_true then (b, st)
  else if Z.eqb b lit_true then (a, st)
  else if Z.eqb a b then (a, st)
  else if Z.eqb a (neg_lit b) then (lit_false, st)
  else emit_and2 a b st.

Lemma emit_and2_opt_step : forall asg a b st out st',
  sat_blast_st asg st ->
  wf_lit_bound (bs_next_var st) a ->
  wf_lit_bound (bs_next_var st) b ->
  emit_and2_opt a b st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_lit_bound (bs_next_var st') out /\
    eval_lit asg' out = (eval_lit asg a && eval_lit asg b).
Proof.
  intros asg a b st out st' Hsat Hwa Hwb Hemit.
  pose proof (proj1 (proj1 Hsat)) as Hge2.
  unfold emit_and2_opt in Hemit.
  destruct (Z.eqb a lit_false) eqn:Eaf; cbn [orb] in Hemit.
  - apply Z.eqb_eq in Eaf; subst a; inversion Hemit; subst.
    exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
      [exact (wf_lit_bound_false _ Hge2) | rewrite (sat_eval_lit_false asg _ Hsat); reflexivity]].
  - destruct (Z.eqb b lit_false) eqn:Ebf; cbn [orb] in Hemit.
    + apply Z.eqb_eq in Ebf; subst b; inversion Hemit; subst.
      exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
        [exact (wf_lit_bound_false _ Hge2) |
         rewrite (sat_eval_lit_false asg _ Hsat), andb_false_r; reflexivity]].
    + destruct (Z.eqb a lit_true) eqn:Eat.
      * apply Z.eqb_eq in Eat; subst a; inversion Hemit; subst.
        exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
          [exact Hwb | rewrite (sat_eval_lit_true asg _ Hsat); reflexivity]].
      * destruct (Z.eqb b lit_true) eqn:Ebt.
        -- apply Z.eqb_eq in Ebt; subst b; inversion Hemit; subst.
           exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
             [exact Hwa | rewrite (sat_eval_lit_true asg _ Hsat), andb_true_r; reflexivity]].
        -- destruct (Z.eqb a b) eqn:Eab.
           ++ apply Z.eqb_eq in Eab; subst b; inversion Hemit; subst.
              exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
                [exact Hwa | rewrite Bool.andb_diag; reflexivity]].
           ++ destruct (Z.eqb a (neg_lit b)) eqn:Eanb.
              ** apply Z.eqb_eq in Eanb; subst a; inversion Hemit; subst.
                 exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
                   [exact (wf_lit_bound_false _ Hge2) |]].
                 rewrite (sat_eval_lit_false asg _ Hsat),
                         (eval_neg_lit_nonzero asg b (wf_lit_bound_nonzero _ b Hwb)).
                 destruct (eval_lit asg b); reflexivity.
              ** destruct (emit_and2_sat asg a b st out st' Hsat Hwa Hwb Hemit)
                   as (asg' & Hle & Hag & Hsat' & Hwfo).
                 destruct (emit_and2_sound asg' a b st out st'
                             (wf_lit_bound_nonzero _ a Hwa)
                             (wf_lit_bound_nonzero _ b Hwb) Hemit) as [_ Hev].
                 assert (Hcnf : eval_cnf asg' (bs_cnf st' ++ []) = true)
                   by (rewrite app_nil_r; exact (proj2 (proj2 Hsat'))).
                 exists asg'; split; [exact (conj Hle (conj Hag Hsat')) | split; [exact Hwfo |]].
                 rewrite (proj2 (Hev [] Hcnf)),
                         <-(eval_lit_agree _ asg asg' a Hag Hwa),
                         <-(eval_lit_agree _ asg asg' b Hag Hwb); reflexivity.
Qed.

Definition emit_or2_opt (a b : lit) (st : blast_state) : lit * blast_state :=
  if Z.eqb a lit_true || Z.eqb b lit_true then (lit_true, st)
  else if Z.eqb a lit_false then (b, st)
  else if Z.eqb b lit_false then (a, st)
  else if Z.eqb a b then (a, st)
  else if Z.eqb a (neg_lit b) then (lit_true, st)
  else emit_or2 a b st.

Lemma emit_or2_opt_step : forall asg a b st out st',
  sat_blast_st asg st ->
  wf_lit_bound (bs_next_var st) a ->
  wf_lit_bound (bs_next_var st) b ->
  emit_or2_opt a b st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_lit_bound (bs_next_var st') out /\
    eval_lit asg' out = (eval_lit asg a || eval_lit asg b).
Proof.
  intros asg a b st out st' Hsat Hwa Hwb Hemit.
  pose proof (proj1 (proj1 Hsat)) as Hge2.
  unfold emit_or2_opt in Hemit.
  destruct (Z.eqb a lit_true) eqn:Eat; cbn [orb] in Hemit.
  - apply Z.eqb_eq in Eat; subst a; inversion Hemit; subst.
    exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
      [exact (wf_lit_bound_true _ Hge2) | rewrite (sat_eval_lit_true asg _ Hsat); reflexivity]].
  - destruct (Z.eqb b lit_true) eqn:Ebt; cbn [orb] in Hemit.
    + apply Z.eqb_eq in Ebt; subst b; inversion Hemit; subst.
      exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
        [exact (wf_lit_bound_true _ Hge2) |
         rewrite (sat_eval_lit_true asg _ Hsat), orb_true_r; reflexivity]].
    + destruct (Z.eqb a lit_false) eqn:Eaf.
      * apply Z.eqb_eq in Eaf; subst a; inversion Hemit; subst.
        exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
          [exact Hwb | rewrite (sat_eval_lit_false asg _ Hsat); reflexivity]].
      * destruct (Z.eqb b lit_false) eqn:Ebf.
        -- apply Z.eqb_eq in Ebf; subst b; inversion Hemit; subst.
           exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
             [exact Hwa | rewrite (sat_eval_lit_false asg _ Hsat), orb_false_r; reflexivity]].
        -- destruct (Z.eqb a b) eqn:Eab.
           ++ apply Z.eqb_eq in Eab; subst b; inversion Hemit; subst.
              exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
                [exact Hwa | rewrite Bool.orb_diag; reflexivity]].
           ++ destruct (Z.eqb a (neg_lit b)) eqn:Eanb.
              ** apply Z.eqb_eq in Eanb; subst a; inversion Hemit; subst.
                 exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
                   [exact (wf_lit_bound_true _ Hge2) |]].
                 rewrite (sat_eval_lit_true asg _ Hsat),
                         (eval_neg_lit_nonzero asg b (wf_lit_bound_nonzero _ b Hwb)).
                 destruct (eval_lit asg b); reflexivity.
              ** destruct (emit_or2_sat asg a b st out st' Hsat Hwa Hwb Hemit)
                   as (asg' & Hle & Hag & Hsat' & Hwfo).
                 destruct (emit_or2_sound asg' a b st out st'
                             (wf_lit_bound_nonzero _ a Hwa)
                             (wf_lit_bound_nonzero _ b Hwb) Hemit) as [_ Hev].
                 assert (Hcnf : eval_cnf asg' (bs_cnf st' ++ []) = true)
                   by (rewrite app_nil_r; exact (proj2 (proj2 Hsat'))).
                 exists asg'; split; [exact (conj Hle (conj Hag Hsat')) | split; [exact Hwfo |]].
                 rewrite (proj2 (Hev [] Hcnf)),
                         <-(eval_lit_agree _ asg asg' a Hag Hwa),
                         <-(eval_lit_agree _ asg asg' b Hag Hwb); reflexivity.
Qed.

Definition emit_xor2_opt (a b : lit) (st : blast_state) : lit * blast_state :=
  if Z.eqb a lit_false then (b, st)
  else if Z.eqb b lit_false then (a, st)
  else if Z.eqb a lit_true then (neg_lit b, st)
  else if Z.eqb b lit_true then (neg_lit a, st)
  else if Z.eqb a b then (lit_false, st)
  else if Z.eqb a (neg_lit b) then (lit_true, st)
  else emit_xor2 a b st.

Lemma emit_xor2_opt_step : forall asg a b st out st',
  sat_blast_st asg st ->
  wf_lit_bound (bs_next_var st) a ->
  wf_lit_bound (bs_next_var st) b ->
  emit_xor2_opt a b st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_lit_bound (bs_next_var st') out /\
    eval_lit asg' out = xorb (eval_lit asg a) (eval_lit asg b).
Proof.
  intros asg a b st out st' Hsat Hwa Hwb Hemit.
  pose proof (proj1 (proj1 Hsat)) as Hge2.
  unfold emit_xor2_opt in Hemit.
  destruct (Z.eqb a lit_false) eqn:Eaf.
  - apply Z.eqb_eq in Eaf; subst a; inversion Hemit; subst.
    exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
      [exact Hwb | rewrite (sat_eval_lit_false asg _ Hsat); reflexivity]].
  - destruct (Z.eqb b lit_false) eqn:Ebf.
    + apply Z.eqb_eq in Ebf; subst b; inversion Hemit; subst.
      exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
        [exact Hwa | rewrite (sat_eval_lit_false asg _ Hsat), Bool.xorb_false_r; reflexivity]].
    + destruct (Z.eqb a lit_true) eqn:Eat.
      * apply Z.eqb_eq in Eat; subst a; inversion Hemit; subst.
        exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
          [exact (wf_lit_bound_neg _ b Hwb) |
           rewrite (sat_eval_lit_true asg _ Hsat),
                   (eval_neg_lit_nonzero asg b (wf_lit_bound_nonzero _ b Hwb));
           destruct (eval_lit asg b); reflexivity]].
      * destruct (Z.eqb b lit_true) eqn:Ebt.
        -- apply Z.eqb_eq in Ebt; subst b; inversion Hemit; subst.
           exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
             [exact (wf_lit_bound_neg _ a Hwa) |
              rewrite (sat_eval_lit_true asg _ Hsat),
                      (eval_neg_lit_nonzero asg a (wf_lit_bound_nonzero _ a Hwa));
              destruct (eval_lit asg a); reflexivity]].
        -- destruct (Z.eqb a b) eqn:Eab.
           ++ apply Z.eqb_eq in Eab; subst b; inversion Hemit; subst.
              exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
                [exact (wf_lit_bound_false _ Hge2) |
                 rewrite (sat_eval_lit_false asg _ Hsat), Bool.xorb_nilpotent; reflexivity]].
           ++ destruct (Z.eqb a (neg_lit b)) eqn:Eanb.
              ** apply Z.eqb_eq in Eanb; subst a; inversion Hemit; subst.
                 exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
                   [exact (wf_lit_bound_true _ Hge2) |]].
                 rewrite (sat_eval_lit_true asg _ Hsat),
                         (eval_neg_lit_nonzero asg b (wf_lit_bound_nonzero _ b Hwb)).
                 destruct (eval_lit asg b); reflexivity.
              ** destruct (emit_xor2_sat asg a b st out st' Hsat Hwa Hwb Hemit)
                   as (asg' & Hle & Hag & Hsat' & Hwfo).
                 destruct (emit_xor2_sound asg' a b st out st'
                             (wf_lit_bound_nonzero _ a Hwa)
                             (wf_lit_bound_nonzero _ b Hwb) Hemit) as [_ Hev].
                 assert (Hcnf : eval_cnf asg' (bs_cnf st' ++ []) = true)
                   by (rewrite app_nil_r; exact (proj2 (proj2 Hsat'))).
                 exists asg'; split; [exact (conj Hle (conj Hag Hsat')) | split; [exact Hwfo |]].
                 rewrite (proj2 (Hev [] Hcnf)),
                         <-(eval_lit_agree _ asg asg' a Hag Hwa),
                         <-(eval_lit_agree _ asg asg' b Hag Hwb); reflexivity.
Qed.

Definition emit_mux2_opt (sel tl fl : lit) (st : blast_state) : lit * blast_state :=
  if Z.eqb sel lit_true then (tl, st)
  else if Z.eqb sel lit_false then (fl, st)
  else if Z.eqb tl fl then (tl, st)
  else if Z.eqb tl lit_true && Z.eqb fl lit_false then (sel, st)
  else if Z.eqb tl lit_false && Z.eqb fl lit_true then (neg_lit sel, st)
  else emit_mux2 sel tl fl st.

Lemma emit_mux2_opt_step : forall asg sel tl fl st out st',
  sat_blast_st asg st ->
  wf_lit_bound (bs_next_var st) sel ->
  wf_lit_bound (bs_next_var st) tl ->
  wf_lit_bound (bs_next_var st) fl ->
  emit_mux2_opt sel tl fl st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_lit_bound (bs_next_var st') out /\
    eval_lit asg' out = (if eval_lit asg sel then eval_lit asg tl else eval_lit asg fl).
Proof.
  intros asg sel tl fl st out st' Hsat Hws Hwt Hwf Hemit.
  unfold emit_mux2_opt in Hemit.
  destruct (Z.eqb sel lit_true) eqn:Est.
  - apply Z.eqb_eq in Est; subst sel; inversion Hemit; subst out st'.
    exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
      [exact Hwt | rewrite (sat_eval_lit_true asg _ Hsat); reflexivity]].
  - destruct (Z.eqb sel lit_false) eqn:Esf.
    + apply Z.eqb_eq in Esf; subst sel; inversion Hemit; subst out st'.
      exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
        [exact Hwf | rewrite (sat_eval_lit_false asg _ Hsat); reflexivity]].
    + destruct (Z.eqb tl fl) eqn:Etf.
      * apply Z.eqb_eq in Etf; subst fl; inversion Hemit; subst out st'.
        exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
          [exact Hwt | destruct (eval_lit asg sel); reflexivity]].
      * destruct (Z.eqb tl lit_true && Z.eqb fl lit_false) eqn:E10.
        -- apply andb_true_iff in E10 as [Ett Eff];
             apply Z.eqb_eq in Ett; apply Z.eqb_eq in Eff; subst tl fl;
             inversion Hemit; subst out st'.
           exists asg; split; [exact (step_spec_refl _ asg Hsat) | split; [exact Hws |]].
           rewrite (sat_eval_lit_true asg _ Hsat), (sat_eval_lit_false asg _ Hsat).
           destruct (eval_lit asg sel); reflexivity.
        -- destruct (Z.eqb tl lit_false && Z.eqb fl lit_true) eqn:E01.
           ++ apply andb_true_iff in E01 as [Etf0 Eft];
                apply Z.eqb_eq in Etf0; apply Z.eqb_eq in Eft; subst tl fl;
                inversion Hemit; subst out st'.
              exists asg; split; [exact (step_spec_refl _ asg Hsat) | split;
                [exact (wf_lit_bound_neg _ sel Hws) |]].
              rewrite (sat_eval_lit_true asg _ Hsat), (sat_eval_lit_false asg _ Hsat),
                      (eval_neg_lit_nonzero asg sel (wf_lit_bound_nonzero _ sel Hws)).
              destruct (eval_lit asg sel); reflexivity.
           ++ destruct (emit_mux2_sat asg sel tl fl st out st' Hsat Hws Hwt Hwf Hemit)
                as (asg' & Hle & Hag & Hsat' & Hwfo).
              destruct (emit_mux2_sound asg' sel tl fl st out st'
                          (wf_lit_bound_nonzero _ sel Hws)
                          (wf_lit_bound_nonzero _ tl Hwt)
                          (wf_lit_bound_nonzero _ fl Hwf) Hemit) as [_ Hev].
              assert (Hcnf : eval_cnf asg' (bs_cnf st' ++ []) = true)
                by (rewrite app_nil_r; exact (proj2 (proj2 Hsat'))).
              exists asg'; split; [exact (conj Hle (conj Hag Hsat')) | split; [exact Hwfo |]].
              rewrite (proj2 (Hev [] Hcnf)),
                      <-(eval_lit_agree _ asg asg' sel Hag Hws),
                      <-(eval_lit_agree _ asg asg' tl Hag Hwt),
                      <-(eval_lit_agree _ asg asg' fl Hag Hwf); reflexivity.
Qed.

Fixpoint list_map2 {A B C : Type} (f : A -> B -> C) (xs : list A) (ys : list B)
  {struct xs} : list C :=
  match xs, ys with
  | x :: rx, y :: ry => f x y :: list_map2 f rx ry
  | _, _ => []
  end.

Lemma list_map2_length : forall {A B C : Type} (f : A -> B -> C) (xs : list A) (ys : list B),
  List.length xs = List.length ys ->
  List.length (list_map2 f xs ys) = List.length xs.
Proof.
  intros A B C f xs; induction xs as [| x rx IH]; intros [| y ry] Hlen;
    try discriminate; cbn in *; [reflexivity | f_equal; apply IH; lia].
Qed.

Lemma list_map2_nth : forall (f : bool -> bool -> bool) (xs ys : list bool) (k : nat),
  List.length xs = List.length ys ->
  (k < List.length xs)%nat ->
  List.nth k (list_map2 f xs ys) false =
  f (List.nth k xs false) (List.nth k ys false).
Proof.
  intros f xs; induction xs as [| x rx IH]; intros [| y ry] k Hlen Hk;
    try discriminate; [inversion Hk |].
  destruct k as [| k']; [reflexivity | cbn; apply IH; cbn in *; lia].
Qed.

Lemma map2_emit_step :
  forall (gate : lit -> lit -> blast_state -> lit * blast_state)
         (f_bool : bool -> bool -> bool)
         (Hgate : forall asg x y st z st1,
                    sat_blast_st asg st ->
                    wf_lit_bound (bs_next_var st) x ->
                    wf_lit_bound (bs_next_var st) y ->
                    gate x y st = (z, st1) ->
                    exists asg1,
                      step_spec st st1 asg asg1 /\
                      wf_lit_bound (bs_next_var st1) z /\
                      eval_lit asg1 z = f_bool (eval_lit asg x) (eval_lit asg y))
         xs ys asg st zs st',
    List.length xs = List.length ys ->
    wf_lits_bound (bs_next_var st) xs ->
    wf_lits_bound (bs_next_var st) ys ->
    sat_blast_st asg st ->
    map2_emit gate xs ys st = (zs, st') ->
    exists asg',
      step_spec st st' asg asg' /\
      List.length zs = List.length xs /\
      wf_lits_bound (bs_next_var st') zs /\
      List.map (eval_lit asg') zs =
      list_map2 f_bool (List.map (eval_lit asg) xs) (List.map (eval_lit asg) ys).
Proof.
  intros gate f_bool Hgate xs; induction xs as [| x rx IH];
    intros [| y ry] asg st zs st' Hlen Hwx Hwy Hsat Hm;
    try discriminate; cbn in Hm.
  - inversion Hm; subst; exists asg; split;
      [exact (step_spec_refl _ asg Hsat) | split; [reflexivity | split; [constructor | reflexivity]]].
  - inversion Hwx as [| ? ? Hx Hwrx]; subst.
    inversion Hwy as [| ? ? Hy Hwry]; subst.
    injection Hlen as Hlen'.
    destruct (gate x y st) as [z st1] eqn:Hg.
    destruct (map2_emit gate rx ry st1) as [zr st2] eqn:Hmr.
    inversion Hm; subst zs st2; clear Hm.
    destruct (Hgate asg x y st z st1 Hsat Hx Hy Hg)
      as (asg1 & Hs1 & Hz & Hev_z).
    destruct (IH ry asg1 st1 zr st' Hlen'
                (wf_lits_bound_mono _ _ rx (proj1 Hs1) Hwrx)
                (wf_lits_bound_mono _ _ ry (proj1 Hs1) Hwry)
                (proj2 (proj2 Hs1)) Hmr)
      as (asg2 & Hs2 & Hlen_zr & Hwf_zr & Hev_zr).
    exists asg2; split; [exact (step_spec_trans st st1 st' asg asg1 asg2 Hs1 Hs2) | split].
    + cbn; rewrite Hlen_zr; reflexivity.
    + split.
      * constructor; [exact (wf_lit_bound_mono _ _ z (proj1 Hs2) Hz) | exact Hwf_zr].
      * cbn; rewrite (step_spec_eval_lit st1 st' asg1 asg2 z Hs2 Hz), Hev_z, Hev_zr,
                     (step_spec_eval_lits st st1 asg asg1 rx Hs1 Hwrx),
                     (step_spec_eval_lits st st1 asg asg1 ry Hs1 Hwry); reflexivity.
Qed.

Fixpoint emit_or_list_opt_acc (acc : lit) (ls : list lit) (st : blast_state)
  {struct ls} : lit * blast_state :=
  match ls with
  | [] => (acc, st)
  | x :: rest =>
      let '(acc1, st1) := emit_or2_opt acc x st in
      emit_or_list_opt_acc acc1 rest st1
  end.

Definition emit_or_list_opt (ls : list lit) (st : blast_state) : lit * blast_state :=
  match ls with
  | [] => (lit_false, st)
  | x :: rest => emit_or_list_opt_acc x rest st
  end.

Lemma emit_or_list_opt_acc_step : forall ls acc asg st out st',
  wf_lit_bound (bs_next_var st) acc ->
  wf_lits_bound (bs_next_var st) ls ->
  sat_blast_st asg st ->
  emit_or_list_opt_acc acc ls st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_lit_bound (bs_next_var st') out /\
    eval_lit asg' out =
      (eval_lit asg acc || existsb (fun b : bool => b) (List.map (eval_lit asg) ls)).
Proof.
  induction ls as [| x rest IH]; intros acc asg st out st' Hacc Hwf Hsat Hemit;
    cbn [emit_or_list_opt_acc] in Hemit.
  - inversion Hemit; subst; exists asg; split;
      [exact (step_spec_refl _ asg Hsat) | split; [exact Hacc | cbn; rewrite orb_false_r; reflexivity]].
  - inversion Hwf as [| ? ? Hx Hwfr]; subst.
    destruct (emit_or2_opt acc x st) as [acc1 st1] eqn:He.
    destruct (emit_or2_opt_step asg acc x st acc1 st1 Hsat Hacc Hx He)
      as (asg1 & Hs1 & Hwf_acc1 & Hev_acc1).
    destruct (IH acc1 asg1 st1 out st' Hwf_acc1
                (wf_lits_bound_mono _ _ rest (proj1 Hs1) Hwfr) (proj2 (proj2 Hs1)) Hemit)
      as (asg2 & Hs2 & Hwf_out & Hev_out).
    exists asg2; split; [exact (step_spec_trans st st1 st' asg asg1 asg2 Hs1 Hs2) | split; [exact Hwf_out |]].
    cbn [List.map existsb];
      rewrite Hev_out, Hev_acc1, (step_spec_eval_lits st st1 asg asg1 rest Hs1 Hwfr), orb_assoc;
      reflexivity.
Qed.

Lemma emit_or_list_opt_step : forall ls asg st out st',
  wf_lits_bound (bs_next_var st) ls ->
  sat_blast_st asg st ->
  emit_or_list_opt ls st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_lit_bound (bs_next_var st') out /\
    eval_lit asg' out = existsb (fun b : bool => b) (List.map (eval_lit asg) ls).
Proof.
  intros [| x rest] asg st out st' Hwf Hsat Hemit; cbn [emit_or_list_opt] in Hemit.
  - inversion Hemit; subst; exists asg; split;
      [exact (step_spec_refl _ asg Hsat) | split;
       [exact (wf_lit_bound_false _ (proj1 (proj1 Hsat))) | exact (sat_eval_lit_false asg _ Hsat)]].
  - inversion Hwf as [| ? ? Hx Hwfr]; subst.
    exact (emit_or_list_opt_acc_step rest x asg st out st' Hx Hwfr Hsat Hemit).
Qed.

Lemma existsb_id_map_eval_lit : forall asg ls,
  existsb (fun b : bool => b) (List.map (eval_lit asg) ls) = existsb (eval_lit asg) ls.
Proof.
  intros asg ls; induction ls as [| x r IH]; [reflexivity | cbn; rewrite IH; reflexivity].
Qed.

Fixpoint mux_bits_list_opt (sel : lit) (ts fs : list lit) (st : blast_state)
  {struct ts} : list lit * blast_state :=
  match ts, fs with
  | t :: rt, f :: rf =>
      let '(m, st1) := emit_mux2_opt sel t f st in
      let '(ms, st2) := mux_bits_list_opt sel rt rf st1 in
      (m :: ms, st2)
  | _, _ => ([], st)
  end.

Lemma mux_bits_list_opt_step : forall ts fs sel asg st ms st',
  List.length ts = List.length fs ->
  wf_lit_bound (bs_next_var st) sel ->
  wf_lits_bound (bs_next_var st) ts ->
  wf_lits_bound (bs_next_var st) fs ->
  sat_blast_st asg st ->
  mux_bits_list_opt sel ts fs st = (ms, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    List.length ms = List.length ts /\
    wf_lits_bound (bs_next_var st') ms /\
    List.map (eval_lit asg') ms =
    (if eval_lit asg sel then List.map (eval_lit asg) ts else List.map (eval_lit asg) fs).
Proof.
  induction ts as [| t rt IH]; intros [| f rf] sel asg st ms st' Hlen Hsel Hwt Hwf Hsat Hm;
    try discriminate; cbn [mux_bits_list_opt] in Hm.
  - inversion Hm; subst; exists asg; split;
      [exact (step_spec_refl _ asg Hsat) | split; [reflexivity | split;
       [constructor | destruct (eval_lit asg sel); reflexivity]]].
  - inversion Hwt as [| ? ? Ht Hwrt]; subst.
    inversion Hwf as [| ? ? Hf Hwrf]; subst.
    injection Hlen as Hlen'.
    destruct (emit_mux2_opt sel t f st) as [m st1] eqn:He.
    destruct (mux_bits_list_opt sel rt rf st1) as [mr st2] eqn:Hmr.
    inversion Hm; subst ms st2; clear Hm.
    destruct (emit_mux2_opt_step asg sel t f st m st1 Hsat Hsel Ht Hf He)
      as (asg1 & Hs1 & Hwf_m & Hev_m).
    destruct (IH rf sel asg1 st1 mr st' Hlen'
                (wf_lit_bound_mono _ _ sel (proj1 Hs1) Hsel)
                (wf_lits_bound_mono _ _ rt (proj1 Hs1) Hwrt)
                (wf_lits_bound_mono _ _ rf (proj1 Hs1) Hwrf)
                (proj2 (proj2 Hs1)) Hmr)
      as (asg2 & Hs2 & Hlen_mr & Hwf_mr & Hev_mr).
    exists asg2; split; [exact (step_spec_trans st st1 st' asg asg1 asg2 Hs1 Hs2) | split].
    + cbn; rewrite Hlen_mr; reflexivity.
    + split.
      * constructor; [exact (wf_lit_bound_mono _ _ m (proj1 Hs2) Hwf_m) | exact Hwf_mr].
      * cbn; rewrite (step_spec_eval_lit st1 st' asg1 asg2 m Hs2 Hwf_m), Hev_m, Hev_mr,
                     (step_spec_eval_lit st st1 asg asg1 sel Hs1 Hsel),
                     (step_spec_eval_lits st st1 asg asg1 rt Hs1 Hwrt),
                     (step_spec_eval_lits st st1 asg asg1 rf Hs1 Hwrf).
        destruct (eval_lit asg sel); reflexivity.
Qed.

Definition blast_refinement_cex_opt_gates
  (sz : positive) (src_no_ub : lit) (src_r tgt_r : rail_bv) (st : blast_state)
  : lit * blast_state :=
  let '(xor_bits, st1) := map2_emit emit_xor2_opt (rbv_bits src_r) (rbv_bits tgt_r) st in
  let '(val_diff, st2) := emit_or_list_opt xor_bits st1 in
  let '(bad_tgt, st3)  := emit_or2_opt (rbv_psn tgt_r) val_diff st2 in
  let '(def_bad, st4)  := emit_and2_opt (neg_lit (rbv_psn src_r)) bad_tgt st3 in
  emit_and2_opt src_no_ub def_bad st4.

Definition blast_refinement_cex_opt
  (sz : positive) (src_no_ub : lit) (src_r tgt_r : rail_bv) (st : blast_state) : cnf :=
  let '(cex_lit, st5) := blast_refinement_cex_opt_gates sz src_no_ub src_r tgt_r st in
  bs_cnf (add_clauses [[cex_lit]] st5).

Theorem blast_refinement_cex_opt_unsat_core :
  forall (sz : positive) (src_no_ub : lit) (src_r tgt_r : rail_bv)
         (st : blast_state) (asg : positive -> bool),
    sat_blast_st asg st ->
    wf_lit_bound (bs_next_var st) src_no_ub ->
    wf_rail_bound sz (bs_next_var st) src_r ->
    wf_rail_bound sz (bs_next_var st) tgt_r ->
    (forall a, eval_cnf a (blast_refinement_cex_opt sz src_no_ub src_r tgt_r st) = false) ->
    eval_lit asg src_no_ub = true ->
    eval_rail_psn asg src_r = false ->
    eval_rail_psn asg tgt_r = false /\
    eval_rail_val sz asg tgt_r = eval_rail_val sz asg src_r.
Proof.
  intros sz src_no_ub src_r tgt_r st asg Hsat Hnub
         ([Hws Hls] & Hbs & Hps) ([Hwt Hlt] & Hbt & Hpt)
         Hunsat Hev_nub Hsrc_def.
  unfold blast_refinement_cex_opt, blast_refinement_cex_opt_gates in Hunsat.
  destruct (map2_emit emit_xor2_opt (rbv_bits src_r) (rbv_bits tgt_r) st) as [xor_bits st1] eqn:Hm.
  destruct (emit_or_list_opt xor_bits st1) as [val_diff st2] eqn:Horl.
  destruct (emit_or2_opt (rbv_psn tgt_r) val_diff st2) as [bad_tgt st3] eqn:Hbad.
  destruct (emit_and2_opt (neg_lit (rbv_psn src_r)) bad_tgt st3) as [def_bad st4] eqn:Hdef.
  destruct (emit_and2_opt src_no_ub def_bad st4) as [cex_lit st5] eqn:Hcex.
  assert (Hlen_st : List.length (rbv_bits src_r) = List.length (rbv_bits tgt_r)) by congruence.
  destruct (map2_emit_step emit_xor2_opt xorb emit_xor2_opt_step _ _ asg st xor_bits st1
              Hlen_st Hbs Hbt Hsat Hm)
    as (asg1 & Hs1 & Hxlen & Hxwf & Hxev).
  destruct (emit_or_list_opt_step xor_bits asg1 st1 val_diff st2 Hxwf (proj2 (proj2 Hs1)) Horl)
    as (asg2 & Hs2 & Hvd_wf & Hvd_ev).
  pose proof (step_spec_trans st st1 st2 asg asg1 asg2 Hs1 Hs2) as Hs12.
  destruct (emit_or2_opt_step asg2 (rbv_psn tgt_r) val_diff st2 bad_tgt st3 (proj2 (proj2 Hs2))
              (wf_lit_bound_mono _ _ _ (proj1 Hs12) Hpt) Hvd_wf Hbad)
    as (asg3 & Hs3 & Hbt_wf & Hbt_ev).
  pose proof (step_spec_trans st st2 st3 asg asg2 asg3 Hs12 Hs3) as Hs13.
  destruct (emit_and2_opt_step asg3 (neg_lit (rbv_psn src_r)) bad_tgt st3 def_bad st4
              (proj2 (proj2 Hs3))
              (wf_lit_bound_neg _ _ (wf_lit_bound_mono _ _ _ (proj1 Hs13) Hps))
              Hbt_wf Hdef)
    as (asg4 & Hs4 & Hdb_wf & Hdb_ev).
  pose proof (step_spec_trans st st3 st4 asg asg3 asg4 Hs13 Hs4) as Hs14.
  destruct (emit_and2_opt_step asg4 src_no_ub def_bad st4 cex_lit st5 (proj2 (proj2 Hs4))
              (wf_lit_bound_mono _ _ _ (proj1 Hs14) Hnub) Hdb_wf Hcex)
    as (asg5 & Hs5 & _ & Hcex_ev).
  pose proof (Hunsat asg5) as Hqf.
  unfold add_clauses in Hqf; cbn [prepend_clauses_rev bs_cnf] in Hqf.
  unfold eval_cnf in Hqf; cbn [forallb] in Hqf.
  change (forallb (fun '(_, cl) => eval_clause asg5 cl) (bs_cnf st5))
    with (eval_cnf asg5 (bs_cnf st5)) in Hqf.
  rewrite (proj2 (proj2 (proj2 (proj2 Hs5)))) in Hqf; cbn in Hqf.
  rewrite orb_false_r, andb_true_r in Hqf.
  rewrite Hcex_ev,
          (step_spec_eval_lit st st4 asg asg4 src_no_ub Hs14 Hnub),
          Hev_nub, Hdb_ev,
          (eval_neg_lit_nonzero asg3 _ (wf_lit_bound_nonzero _ _ Hps)),
          (step_spec_eval_lit st st3 asg asg3 (rbv_psn src_r) Hs13 Hps) in Hqf.
  unfold eval_rail_psn in Hsrc_def; rewrite Hsrc_def in Hqf; cbn in Hqf.
  rewrite Hbt_ev,
          (step_spec_eval_lit st st2 asg asg2 (rbv_psn tgt_r) Hs12 Hpt),
          Hvd_ev, Hxev in Hqf.
  apply orb_false_iff in Hqf as [Htgt_def Hxor_false].
  split; [exact Htgt_def |].
  pose proof (step_spec_trans st st4 st5 asg asg4 asg5 Hs14 Hs5) as Hs15.
  destruct (eval_rail_agree sz _ asg asg1 src_r (proj1 (proj2 Hs1))
              (conj (conj Hws Hls) (conj Hbs Hps))) as [_ Hvs1].
  destruct (eval_rail_agree sz _ asg asg1 tgt_r (proj1 (proj2 Hs1))
              (conj (conj Hwt Hlt) (conj Hbt Hpt))) as [_ Hvt1].
  rewrite Hvs1, Hvt1.
  apply (existsb_xor_bits_diff sz asg1 src_r tgt_r xor_bits
           (conj Hws Hls) (conj Hwt Hlt)); [congruence | |].
  - intros k Hk;
      rewrite Hxev,
              <- (step_spec_eval_lits st st1 asg asg1 (rbv_bits src_r) Hs1 Hbs),
              <- (step_spec_eval_lits st st1 asg asg1 (rbv_bits tgt_r) Hs1 Hbt).
      apply list_map2_nth; [rewrite !length_map; exact Hlen_st | rewrite length_map, Hls; exact Hk].
  - rewrite <- existsb_id_map_eval_lit, Hxev; exact Hxor_false.
Qed.

Theorem blast_refinement_cex_opt_lrat_sound :
  forall (sz : positive) (src_no_ub : lit) (src_r tgt_r : rail_bv)
         (st : blast_state) (pf : list lrat_step) (asg : positive -> bool),
    sat_blast_st asg st ->
    wf_lit_bound (bs_next_var st) src_no_ub ->
    wf_rail_bound sz (bs_next_var st) src_r ->
    wf_rail_bound sz (bs_next_var st) tgt_r ->
    check_lrat_unsat (blast_refinement_cex_opt sz src_no_ub src_r tgt_r st) pf = true ->
    eval_lit asg src_no_ub = true ->
    eval_rail_psn asg src_r = false ->
    eval_rail_psn asg tgt_r = false /\
    eval_rail_val sz asg tgt_r = eval_rail_val sz asg src_r.
Proof.
  intros sz src_no_ub src_r tgt_r st pf asg Hsat Hnub Hws Hwt Hunsat.
  exact (blast_refinement_cex_opt_unsat_core sz src_no_ub src_r tgt_r st asg
           Hsat Hnub Hws Hwt (check_lrat_unsat_sound _ pf Hunsat)).
Qed.

Theorem blast_refinement_cex_opt_auto_sound :
  forall (fuel : nat) (sz : positive) (src_no_ub : lit) (src_r tgt_r : rail_bv)
         (st : blast_state) (asg : positive -> bool),
    sat_blast_st asg st ->
    wf_lit_bound (bs_next_var st) src_no_ub ->
    wf_rail_bound sz (bs_next_var st) src_r ->
    wf_rail_bound sz (bs_next_var st) tgt_r ->
    solve_cnf_unsat fuel (blast_refinement_cex_opt sz src_no_ub src_r tgt_r st) = true ->
    eval_lit asg src_no_ub = true ->
    eval_rail_psn asg src_r = false ->
    eval_rail_psn asg tgt_r = false /\
    eval_rail_val sz asg tgt_r = eval_rail_val sz asg src_r.
Proof.
  intros fuel sz src_no_ub src_r tgt_r st asg Hsat Hnub Hws Hwt Hunsat.
  exact (blast_refinement_cex_opt_unsat_core sz src_no_ub src_r tgt_r st asg
           Hsat Hnub Hws Hwt (fun a => solve_cnf_unsat_sound fuel _ a Hunsat)).
Qed.

