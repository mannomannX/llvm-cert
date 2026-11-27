(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * [CertValidator.AlgRules] Verified 2-Rail [LRAT] & Auto-DPLL Fallback Refinement Checker

    Re-exports [AlgRulesEval], [AlgRulesNormBinop], and [AlgRulesNormRefines],
    and defines:
    - Tail-recursive Cone-of-Influence ([COI]) clause filtering, AIG variable
      allocation, 2-rail multiplication, operator blasting steps, [select] and
      [CE_Let] blasting, and [ub_ctx] assumption blasting.
    - Verified 2-rail [LRAT] and auto-DPLL fallback refinement checking
      ([check_expr_refines_with_lrat]) backed by
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

From CertValidator.common Require Import
  CoreTactics.

From CertValidator Require Import
  LratCore
  AigGates
  AigArith
  CertFormatAst.
From CertValidator Require Export
  AlgRulesEval
  AlgRulesNormBinop
  AlgRulesNormRefines.
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
      [exact (step_spec_refl _ asg Hsat) | split; [reflexivity | constructor]].
  - assert (Hb_step :
              exists b st1 asg1,
                (if zp idx then (lit_false, st) else alloc_var st) = (b, st1) /\
                step_spec st st1 asg asg1 /\
                wf_lit_bound (bs_next_var st1) b).
    { destruct (zp idx).
      - exists lit_false, st, asg; split; [reflexivity | split;
          [exact (step_spec_refl _ asg Hsat)
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
      [exact (step_spec_refl _ asg Hsat) | split; [reflexivity | split; [constructor | reflexivity]]].
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
          [exact (step_spec_refl _ asg Hsat) | split;
           [exact (wf_lit_bound_false _ (proj1 (proj1 Hsat)))
            | exact (sat_eval_lit_false asg _ Hsat)]]].
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
      [exact (step_spec_refl _ asg Hsat) | split; [reflexivity | split;
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
      [exact (step_spec_refl _ asg Hsat) | split; [apply repeat_length | split]].
    + exact (wf_lits_bound_repeat _ _ _ (wf_lit_bound_false _ (proj1 (proj1 Hsat)))).
    + rewrite map_repeat_eq, (sat_eval_lit_false asg _ Hsat), bools_to_Z_repeat_false.
      exists 0%Z; cbn [List.map bools_to_Z]; lia.
  - inversion Hwx as [| ? ? Hx Hwrx]; subst.
    destruct ys as [| y0 ry].
    + inversion He; subst; exists asg; split;
        [exact (step_spec_refl _ asg Hsat) | split; [reflexivity | split;
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
      { rewrite <- (firstn_skipn_eq m' bys) at 1; rewrite bools_to_Z_app.
        assert (Hfl : List.length (List.firstn m' bys) = m')
          by (unfold bys; apply len_firstn_le; rewrite length_map; lia).
        rewrite Hfl; reflexivity. }
      rewrite map_firstn_eq in Heq_sum; fold bys in Heq_sum.
      assert (Hlo_eq : (bools_to_Z (List.firstn m' bys) =
                        bools_to_Z bys - 2 ^ Z.of_nat m' * bools_to_Z (List.skipn m' bys))%Z)
        by nia.
      rewrite Hlo_eq in Heq_sum.
      rewrite Hlen_ys, Nat2Z.inj_succ, Z.pow_succ_r by lia.
      cbn [List.map]; rewrite bools_to_Z_cons; fold brx.
      exists (k1 - bools_to_Z brx * bools_to_Z (List.skipn m' bys) -
              b2z (eval_lit asg3 cout))%Z.
      nia.
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
  unfold blast_mul_rail in Hbl; cbn zeta in Hbl.
  destruct (emit_mul_bits (rbv_bits a) (rbv_bits b) st) as [prod_bits st1] eqn:Emul.
  destruct (emit_or2_opt (rbv_psn a) (rbv_psn b) st1) as [base_psn st2] eqn:Ebp; cbn iota zeta in Hbl.
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
    rewrite Hk0, ?Hla, ?Hlb, positive_nat_Z, <- modulus_pow_sz,
            <- (unsigned_eval_rail_val sz asg a Hla),
            <- (unsigned_eval_rail_val sz asg b Hlb); unfold va, vb.
    exists k0; ring. }
  destruct (Pos.eqb sz 1%positive || (negb nuw && negb nsw)) eqn:Efast.
  - inversion Hbl; subst out st2; clear Hbl.
    exists asg2; split; [exact Hs02 | split].
    + split; [split; [reflexivity | cbn; congruence] |
              split; [exact (wf_lits_bound_mono _ _ prod_bits (proj1 Hs2) Hwf_pb) | exact Hwf_bp]].
    + split.
      * unfold eval_rail_psn; cbn [rbv_psn]; rewrite Hev_bp,
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
    { destruct nuw;
        [| exists lit_false, st2, asg2;
           split; [reflexivity |
           split; [exact (step_spec_refl st2 asg2 (proj2 (proj2 Hs02))) |
           split; [exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs02))))) |
                   exact (sat_eval_lit_false asg2 st2 (proj2 (proj2 Hs02)))]]]].
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
        exists ku; ring. }
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
    cbn iota zeta in Hnuw_eq, Hbl; rewrite Hnuw_eq in Hbl; cbn iota zeta in Hbl; clear Hnuw_eq.
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
    { destruct nsw;
        [| exists lit_false, st6, asg6;
           split; [reflexivity |
           split; [exact (step_spec_refl st6 asg6 (proj2 (proj2 Hs06))) |
           split; [exact (wf_lit_bound_false _ (proj1 (proj1 (proj2 (proj2 Hs06))))) |
                   exact (sat_eval_lit_false asg6 st6 (proj2 (proj2 Hs06)))]]]].
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
        change (2 ^ 2)%Z with 4%Z in Hhm.
        assert (Hppos : (0 < 2 ^ (Z.pos sz - 2))%Z) by (apply Z.pow_pos_nonneg; lia); lia. }
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
          exists ks; ring. }
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
        rewrite Hmod_dw in Hdm |- *.
        exists (- (@Integers.modulus sz * (rs / (@Integers.modulus sz * @Integers.modulus sz))))%Z.
        nia. }
      change (eval_rail_val dw a9 (mk_rail_bv dw sbits lit_false)) with prod_s.
      rewrite Hres_s_eq, Hs_prod; exact (signed_repr_neq_iff_oob sz rs). }
    destruct Hnsw_step as (nsw_psn & st10 & asg10 & Hnsw_eq & Hs610 & Hwf_nswp & Hev_nswp).
    cbn iota zeta in Hnsw_eq, Hbl; rewrite Hnsw_eq in Hbl; cbn iota zeta in Hbl; clear Hnsw_eq.
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
      * unfold eval_rail_psn; cbn [rbv_psn]; rewrite Esz_gt1, Hev_p,
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
    + unfold eval_iop; rewrite eval_iop_integer_base_same_width; unfold cert_to_ibinop, eval_int_op; cbn - [andb orb].
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
    + unfold eval_iop; rewrite eval_iop_integer_base_same_width; unfold cert_to_ibinop, eval_int_op; cbn - [andb orb].
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
    + unfold eval_iop; rewrite eval_iop_integer_base_same_width; unfold cert_to_ibinop, eval_int_op, dvp, tdb;
        cbn - [andb orb Pos.eqb Integers.mul Integers.unsigned Integers.signed Integers.min_signed Integers.max_signed].
      unfold ov; destruct (Pos.eqb sz 1%positive); [reflexivity |].
      match goal with |- context [if ?b then _ else _] => destruct b; reflexivity end.
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
    unfold eval_iop; rewrite eval_iop_integer_base_same_width;
      unfold cert_to_ibinop, eval_int_op, dvp, tdb;
      cbn - [andb orb negb Pos.eqb Z.geb Z.gtb Z.eqb Z.modulo Z.shiftl Z.shiftr Z.pow
             Integers.shl Integers.shru Integers.shr Integers.unsigned Integers.negative];
      rewrite ?andb_true_r.
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
      * fold res nuw_p.
        destruct nuw_p; [reflexivity |].
        cbn [orb]; unfold nsw_p; destruct (cbf_nsw fl); [| reflexivity].
        cbn [andb]; destruct (negb _); reflexivity.
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
    unfold eval_iop; rewrite eval_iop_integer_base_same_width;
      unfold cert_to_ibinop, eval_int_op, dvp, tdb;
      cbn - [andb orb negb Pos.eqb Z.geb Z.gtb Z.eqb Z.modulo Z.shiftl Z.shiftr Z.pow
             Integers.shl Integers.shru Integers.shr Integers.unsigned Integers.negative];
      rewrite ?andb_true_r.
    destruct (@Integers.unsigned sz vb >=? Z.pos sz)%Z eqn:Ege.
    + exists asg', (DVALUE_Base DVALUE_Poison).
      split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
        unfold rail_matches_dvalue; rewrite Hpsn; reflexivity]]].
    + set (ov := cbf_exact fl && negb ((@Integers.unsigned sz va mod (2 ^ @Integers.unsigned sz vb)) =? 0)%Z) in *.
      exists asg', (if ov then DVALUE_Base DVALUE_Poison
                    else DVALUE_Base (@DVALUE_I Pa sz (@Integers.shru sz va vb))).
      split; [cbn - [andb negb]; fold ov; destruct ov; reflexivity |
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
    unfold eval_iop; rewrite eval_iop_integer_base_same_width;
      unfold cert_to_ibinop, eval_int_op, dvp, tdb;
      cbn - [andb orb negb Pos.eqb Z.geb Z.gtb Z.eqb Z.modulo Z.shiftl Z.shiftr Z.pow
             Integers.shl Integers.shru Integers.shr Integers.unsigned Integers.negative];
      rewrite ?andb_true_r.
    destruct (@Integers.unsigned sz vb >=? Z.pos sz)%Z eqn:Ege.
    + exists asg', (DVALUE_Base DVALUE_Poison).
      split; [reflexivity | split; [exact Hs | split; [exact Hwf_out |
        unfold rail_matches_dvalue; rewrite Hpsn; reflexivity]]].
    + set (ov := cbf_exact fl && negb ((@Integers.unsigned sz va mod (2 ^ @Integers.unsigned sz vb)) =? 0)%Z) in *.
      exists asg', (if ov then DVALUE_Base DVALUE_Poison
                    else DVALUE_Base (@DVALUE_I Pa sz (@Integers.shr sz va vb))).
      split; [cbn - [andb negb]; fold ov; destruct ov; reflexivity |
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
              @eval_int_icmp Pa (@Integers.bit_int sz) _ ss (cert_to_icmp pr) va vb =
              raise_ret (if ssp then DVALUE_Poison
                         else if cb then @DVALUE_I Pa 1%positive (@Integers.one 1%positive)
                         else @DVALUE_I Pa 1%positive (@Integers.zero 1%positive))).
    { destruct pr; cbn in Esc; inversion Esc; subst is_s c;
        unfold cert_to_icmp, eval_int_icmp; cbn - [andb negb msamesign Integers.cmp Integers.cmpu]; fold ssp cb; destruct ssp, cb; reflexivity. }
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
      * cbn - [andb]; rewrite Pos.eqb_refl, Hlt; cbn - [andb]; fold ov; destruct ov; reflexivity.
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
          unfold rail_matches_dvalue; rewrite Hpsn; reflexivity]]].
    + exists asg', (DVALUE_Base (@DVALUE_I Pa tw (@Integers.repr tw (@Integers.signed fw (eval_rail_val fw asg ro))))).
      split; [cbn; rewrite Pos.eqb_refl, Hlt; reflexivity |
      split; [exact Hs | split; [exact Hwf_out |
        unfold rail_matches_dvalue; rewrite Hpsn, Hval; reflexivity]]].
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
      * cbn - [andb orb negb]; rewrite Pos.eqb_refl, Hlt; cbn - [andb orb negb]; fold res ov; destruct ov; reflexivity.
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
    { split; [split; [reflexivity | unfold blast_const_rail; cbn; rewrite length_map, length_seq; reflexivity] | split].
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
    unfold wf_let_rails_sync in Hsync; generalize (Hsync nm); revert Hbl Hwt.
    destruct (lookup_let_rail lr nm) as [[rw r_let] |] eqn:Elr.
    + destruct (lookup_let_width lw nm) as [bw |],
               (lookup_let_val lenv nm) as [dv |];
        intros Hbl Hwt Hsnm; try contradiction.
      destruct (Pos.eqb rw w) eqn:Erw; [| discriminate Hbl].
      apply Pos.eqb_eq in Erw; apply Pos.eqb_eq in Hwt; subst rw bw.
      inversion Hbl; subst out env'; clear Hbl.
      destruct Hsnm as (_ & Hwfdv & Hwfr & Hrm).
      exists asg, dv.
      split; [exact (check_scalar_width_ok w dv Hwfdv) |
      split; [exact (step_spec_refl _ asg (proj1 Henv)) |
      split; [exact Henv | split; [exact Hwfr | exact Hrm]]]].
    + destruct (lookup_let_width lw nm) as [bw |] eqn:Elw;
        [destruct (lookup_let_val lenv nm); intros Hbl Hwt Hsnm; contradiction |].
      destruct (lookup_let_val lenv nm) as [dv0 |];
        [intros Hbl Hwt Hsnm; contradiction | intros Hbl Hwt _].
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
                          | None => raise_error ("unbound variable: " ++ nm)%string
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
           intros nm' w' r' Hlk; cbn - [andb String.eqb Pos.eqb] in Hlk.
           destruct (String.eqb nm' nm && Pos.eqb w' w) eqn:Ehit.
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
           intros nm' w' r' Hlk; cbn - [andb String.eqb Pos.eqb] in Hlk.
           destruct (String.eqb nm' nm && Pos.eqb w' w) eqn:Ehit.
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
        intros w' key' fbits' Hlk; cbn - [andb Pos.eqb cert_expr_eqb] in Hlk.
        destruct (Pos.eqb w' w && cert_expr_eqb key' key) eqn:Ehit.
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
      forall cur_lw seen cur_lr cur_ms cur_le cur_asg cur_env,
        wf_let_binds_step wt_cert_expr cur_lw seen bs = Some lw' ->
        blast_let_binds (fun lr0 ms0 x env0 => blast_cert_expr ctx lr0 ms0 x env0)
                        cur_lr cur_ms bs cur_env = Some (lr', ms_opt', env_b) ->
        wf_let_rails_sync cur_asg (bs_next_var (be_st cur_env)) cur_lw cur_le cur_lr ->
        wf_ms_sync cur_le cur_ms ->
        wf_param_env_for
          (let '(b', vs_xs) := collect_bind_vars collect_free_vars (List.map fst cur_lw) bs in
           vs_xs ++ collect_free_vars b' body) penv ->
        sat_blast_env penv foracle cur_asg cur_env ->
        exists asg_b lenv',
          eval_let_binds (fun ce x => eval_cert_expr penv ce foracle x) cur_le bs =
            raise_ret lenv' /\
          step_spec (be_st cur_env) (be_st env_b) cur_asg asg_b /\
          sat_blast_env penv foracle asg_b env_b /\
          wf_let_rails_sync asg_b (bs_next_var (be_st env_b)) lw' lenv' lr' /\
          wf_ms_sync lenv' ms_opt' /\
          wf_param_env_for (collect_free_vars (List.map fst lw') body) penv).
    { clear Hbl Elw Ebs Hpenv; induction IHbs as [| [bnm be] rx IHbe _ IHrx];
        intros cur_lw seen cur_lr cur_ms cur_le cur_asg cur_env
               Hlw_xs Hbl_xs Hsync_c Hms_c Hpenv_c Henv_c;
        cbn [wf_let_binds_step] in Hlw_xs; cbn [blast_let_binds] in Hbl_xs.
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
            cbn [wf_ms_sync] in Hms_c |- *.
            change (strip_let_sizes ((bnm, (ebe, bsz)) :: ms))
              with ((bnm, ebe) :: strip_let_sizes ms).
            change (let_val_exprs ((bnm, (dv_be, exp_be)) :: cur_le))
              with ((bnm, exp_be) :: let_val_exprs cur_le).
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
    destruct (Hstep_bs lw [] lr ms_opt lenv asg env Elw Ebs Hsync Hms Hpenv Henv)
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

Lemma vars_subset_b_wf_param_env :
  forall {Pa : Params} sub sup (penv : param_env Pa),
    vars_subset_b sub sup = true ->
    wf_param_env_for sup penv ->
    wf_param_env_for sub penv.
Proof.
  intros Pa sub sup penv Hsub Hsup nm0 w0 Hin.
  exact (Hsup nm0 w0 (vars_subset_b_incl _ _ Hsub (nm0, w0) Hin)).
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
    | bs body _ _ ] using cert_expr_ind_nested;
    intros penv foracle v Hlf Hev;
    cbn [is_let_free_expr eval_cert_expr collect_free_vars] in *.
  - intros _ _ [].
  - intros _ _ [].
  - intros nm0 w0 [Heq | []]; inversion Heq; subst nm0 w0.
    destruct (penv nm) as [dv |] eqn:Epm; [| discriminate Hev].
    cbn [lookup_let_val] in Hev; destruct (check_scalar_width_inv w dv v Hev) as [Heq_dv Hwf].
    exists dv; split; [reflexivity | try rewrite Heq_dv; try rewrite <- Heq_dv; exact Hwf].
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
    cbn [ub_assumption_holds] in Hua; destruct Hua as (w_div & i_div & Hev_div & Hnz0).
    pose proof (expand_lets_fueled_eq norm_let_expand_budget div_e ec Eexp) as Hec_eq.
    rewrite <- Hec_eq in Hev_div; unfold eval_closed_cert_expr in Hev_div.
    pose proof (eval_let_free_ret_wf_param_env ec penv foracle _ Hlf Hev_div) as Hpenv_ec.
    assert (Hms_ec : wf_ms_sync (@nil (string * (@dvalue Pa * cert_expr))) ms_ec)
      by (unfold ms_ec; destruct (expr_has_freeze ec); cbn [wf_ms_sync strip_let_sizes let_val_exprs List.map]; trivial).
    destruct (blast_cert_expr_sat ec full_ctx [] [] ms_ec penv [] foracle asg env env1 r_d
                Ebl Hwt (wf_let_rails_sync_nil asg _) Hms_ec Hpenv_ec Hctx Henv)
      as (asg1 & vd & Evd & _ & Henv1 & Hwfr & Hmrd).
    set (sz := cert_expr_bit_width ec) in *.
    rewrite Hev_div in Evd.
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
      by (unfold add_clauses; destruct (prepend_clauses_rev _ _ _); reflexivity).
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
      by (unfold ms_ec; destruct (expr_has_freeze ec); cbn [wf_ms_sync strip_let_sizes let_val_exprs List.map]; trivial).
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
      by (unfold add_clauses; destruct (prepend_clauses_rev _ _ _); reflexivity).
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

Definition default_dpll_fuel : nat := 256%nat.
#[local] Opaque default_dpll_fuel.

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
  set (init_env := mk_blast_env (init_blast_state 2%positive) [] []) in *.
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
    by (unfold ms_s; destruct (expr_has_freeze s); cbn [wf_ms_sync strip_let_sizes let_val_exprs List.map]; trivial).
  assert (Hms_t : wf_ms_sync (@nil (string * (@dvalue Pa * cert_expr))) ms_t)
    by (unfold ms_t; destruct (expr_has_freeze t); cbn [wf_ms_sync strip_let_sizes let_val_exprs List.map]; trivial).
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
        if cert_expr_eqb src ns && cert_expr_eqb tgt nt then false
        else check_blast_pair ctx ns nt opt_pf
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
  pose proof (expand_lets_fueled_eq norm_let_expand_budget tgt et Eet) as Het_eq; subst et; cbn zeta in Hchk.
  destruct (cert_expr_eqb src (normalize_cert_expr ctx (expand_lets src)) &&
            cert_expr_eqb tgt (normalize_cert_expr ctx (expand_lets tgt)));
    [discriminate Hchk |].
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
    by (apply Pos.eqb_eq; rewrite Hb_ns, Hb_nt; unfold expand_lets; rewrite Hb_es, Hb_et; exact Hbw).
  apply (refine_eou_compat _ _ _ _ Heq_src Heq_tgt).
  exact (check_blast_pair_sound ctx
           (normalize_cert_expr ctx (expand_lets src))
           (normalize_cert_expr ctx (expand_lets tgt))
           opt_pf penv foracle Hbw_norm Hwt_ns Hwt_nt Hchk Hp_ns Hp_nt Hctx).
Qed.
