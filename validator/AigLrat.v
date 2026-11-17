(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified 2-Rail [(val_bits, poison_bit)] Bit-Blaster & [LRAT] UNSAT Proof Checker

    Implements:
    1. A self-contained, extraction-ready Linear Reverse Asymmetric Tautology
       ([LRAT]) UNSAT proof checker over integer-indexed CNF clauses
       ([lit := Z], [clause := list lit], [cnf := list (positive * clause)],
       [lrat_step]) backed by an [O(log N)] binary positive-index trie and
       machine-checked soundness theorem [check_lrat_unsat_sound].
    2. A verified 2-rail bitvector representation ([rail_bv]: little-endian
       [rbv_bits : list lit] paired with poison rail [rbv_psn : lit]) bridged
       directly to Vellvm's [@Integers.bit_int sz] ([eval_rail_val],
       [eval_rail_val_testbit], [bit_int_to_bools_repr]).
    3. Verified Tseitin gate and 2-rail operator encoders ([blast_const],
       [blast_poison], [blast_and_rail], [blast_or_rail], [blast_xor_rail],
       [blast_eq_rail], [blast_select_rail], [blast_freeze_rail], and
       [blast_refinement_cex]), together with [Qed.] soundness theorems proving
       that an [LRAT]-verified UNSAT counterexample query implies
       [target_not_poison /\ target_val = source_val] whenever
       [source_not_poison] and [source_no_ub]. *)

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

(** ** 1. Positive-Indexed Binary Trie ([O(log N)] Clause & Trail Maps) *)

Section PosTrie.
  Context {V : Type}.

  Inductive pos_trie : Type :=
  | PT_Empty
  | PT_Node (left_t : pos_trie) (val_opt : option V) (right_t : pos_trie).

  Fixpoint pt_get (p : positive) (t : pos_trie) {struct t} : option V :=
    match t with
    | PT_Empty => None
    | PT_Node l ov r =>
        match p with
        | xH => ov
        | xO q => pt_get q l
        | xI q => pt_get q r
        end
    end.

  Fixpoint pt_set (p : positive) (v : V) (t : pos_trie) {struct p} : pos_trie :=
    match t with
    | PT_Empty =>
        match p with
        | xH => PT_Node PT_Empty (Some v) PT_Empty
        | xO q => PT_Node (pt_set q v PT_Empty) None PT_Empty
        | xI q => PT_Node PT_Empty None (pt_set q v PT_Empty)
        end
    | PT_Node l ov r =>
        match p with
        | xH => PT_Node l (Some v) r
        | xO q => PT_Node (pt_set q v l) ov r
        | xI q => PT_Node l ov (pt_set q v r)
        end
    end.

  Fixpoint pt_rem (p : positive) (t : pos_trie) {struct t} : pos_trie :=
    match t with
    | PT_Empty => PT_Empty
    | PT_Node l ov r =>
        match p with
        | xH => PT_Node l None r
        | xO q => PT_Node (pt_rem q l) ov r
        | xI q => PT_Node l ov (pt_rem q r)
        end
    end.

  Lemma pt_get_empty : forall p, pt_get p PT_Empty = None.
  Proof using Type.
    intros p; reflexivity.
  Qed.

  Lemma pt_get_set_same : forall p v t, pt_get p (pt_set p v t) = Some v.
  Proof using Type.
    induction p as [q IH | q IH |]; intros v [| l ov r]; cbn;
      try reflexivity; apply IH.
  Qed.

  Lemma pt_get_set_other : forall p q v t,
    p <> q -> pt_get p (pt_set q v t) = pt_get p t.
  Proof using Type.
    induction p as [p' IH | p' IH |]; intros [q' | q' |] v [| l ov r] Hneq; cbn;
      try reflexivity;
      try (exfalso; apply Hneq; reflexivity);
      apply IH; intros Heq; subst; apply Hneq; reflexivity.
  Qed.

  Lemma pt_get_rem_sub : forall p q t v,
    pt_get p (pt_rem q t) = Some v -> pt_get p t = Some v.
  Proof using Type.
    induction p as [p' IH | p' IH |]; intros [q' | q' |] [| l ov r] v H; cbn in *;
      try discriminate;
      try exact H;
      eapply IH; exact H.
  Qed.
End PosTrie.

Arguments pos_trie : clear implicits.

(** ** 2. CNF Syntax, Evaluation, and Verified [LRAT] UNSAT Checker *)

Definition lit : Set := Z.
Definition clause : Set := list lit.
Definition cnf : Set := list (positive * clause).

Variant lrat_step : Set :=
| LRAT_Add (cid : positive) (cl : clause) (rup_hints : list positive)
| LRAT_Del (cids : list positive).

Definition eval_lit (assign : positive -> bool) (l : lit) : bool :=
  match l with
  | Z0 => false
  | Z.pos v => assign v
  | Z.neg v => negb (assign v)
  end.

Definition eval_clause (assign : positive -> bool) (c : clause) : bool :=
  existsb (eval_lit assign) c.

Definition eval_cnf (assign : positive -> bool) (f : cnf) : bool :=
  forallb (fun '(_, c) => eval_clause assign c) f.

Definition neg_lit (l : lit) : lit := (- l)%Z.

Lemma eval_neg_lit_nonzero : forall assign (l : lit),
  l <> 0%Z -> eval_lit assign (neg_lit l) = negb (eval_lit assign l).
Proof.
  intros assign [| v | v] Hnz; [congruence | reflexivity | cbn; rewrite negb_involutive; reflexivity].
Qed.

Definition trail_sound (assign : positive -> bool) (trail : pos_trie bool) : Prop :=
  forall v b, pt_get v trail = Some b -> assign v = b.

Lemma trail_sound_empty : forall assign, trail_sound assign PT_Empty.
Proof.
  intros assign v b H; discriminate.
Qed.

Lemma trail_sound_set : forall assign trail v b,
  trail_sound assign trail ->
  assign v = b ->
  trail_sound assign (pt_set v b trail).
Proof.
  intros assign trail v b Htr Hv u bu Hget.
  destruct (Pos.eq_dec u v) as [Heq | Hneq].
  - subst u; rewrite pt_get_set_same in Hget; inversion Hget; subst bu; exact Hv.
  - rewrite pt_get_set_other in Hget by exact Hneq; exact (Htr u bu Hget).
Qed.

Definition lit_status (trail : pos_trie bool) (l : lit) : option bool :=
  match l with
  | Z0 => Some false
  | Z.pos v => pt_get v trail
  | Z.neg v => option_map negb (pt_get v trail)
  end.

Lemma lit_status_sound : forall assign trail l b,
  trail_sound assign trail ->
  lit_status trail l = Some b ->
  eval_lit assign l = b.
Proof.
  intros assign trail [| v | v] b Htr Hs; cbn in *.
  - inversion Hs; reflexivity.
  - exact (Htr v b Hs).
  - destruct (pt_get v trail) as [bv |] eqn:Hg; cbn in Hs; [| discriminate].
    inversion Hs; subst; rewrite (Htr v bv Hg); reflexivity.
Qed.

(** Seeding the negation of a candidate clause [cl]:
    - Returns [None] when [cl] is already a syntactic tautology ([v] and [-v]
      both appear in [cl]), so [eval_clause assign cl = true] unconditionally.
    - Returns [Some trail] recording every variable assignment forced by
      [eval_clause assign cl = false]. *)
Fixpoint seed_neg_clause_aux (trail : pos_trie bool) (cl : clause)
  {struct cl} : option (pos_trie bool) :=
  match cl with
  | [] => Some trail
  | l :: rest =>
      match l with
      | Z0 => seed_neg_clause_aux trail rest
      | Z.pos v =>
          match pt_get v trail with
          | Some true => None
          | Some false => seed_neg_clause_aux trail rest
          | None => seed_neg_clause_aux (pt_set v false trail) rest
          end
      | Z.neg v =>
          match pt_get v trail with
          | Some false => None
          | Some true => seed_neg_clause_aux trail rest
          | None => seed_neg_clause_aux (pt_set v true trail) rest
          end
      end
  end.

Lemma seed_neg_clause_aux_spec : forall assign cl trail,
  trail_sound assign trail ->
  eval_clause assign cl = false ->
  exists trail',
    seed_neg_clause_aux trail cl = Some trail' /\
    trail_sound assign trail'.
Proof.
  intros assign cl.
  induction cl as [| l rest IH]; intros trail Htr Hfalse.
  - exists trail; split; [reflexivity | exact Htr].
  - cbn [eval_clause existsb] in Hfalse.
    apply orb_false_iff in Hfalse as [Hl Hrest].
    destruct l as [| v | v]; cbn [seed_neg_clause_aux].
    + exact (IH trail Htr Hrest).
    + cbn in Hl.
      destruct (pt_get v trail) as [[|] |] eqn:Hg.
      * pose proof (Htr v true Hg) as Htrue; congruence.
      * exact (IH trail Htr Hrest).
      * apply IH; [apply trail_sound_set; [exact Htr | exact Hl] | exact Hrest].
    + cbn in Hl; apply negb_false_iff in Hl.
      destruct (pt_get v trail) as [[|] |] eqn:Hg.
      * exact (IH trail Htr Hrest).
      * pose proof (Htr v false Hg) as Hfalse_v; congruence.
      * apply IH; [apply trail_sound_set; [exact Htr | exact Hl] | exact Hrest].
Qed.

Variant rup_clause_res : Set :=
| RUP_Conflict
| RUP_Unit (ulit : lit)
| RUP_Invalid.

Fixpoint scan_rup_clause (trail : pos_trie bool) (unassigned : option lit) (hcl : clause)
  {struct hcl} : rup_clause_res :=
  match hcl with
  | [] =>
      match unassigned with
      | None => RUP_Conflict
      | Some u => RUP_Unit u
      end
  | l :: rest =>
      match lit_status trail l with
      | Some false => scan_rup_clause trail unassigned rest
      | Some true => RUP_Invalid
      | None =>
          match unassigned with
          | None => scan_rup_clause trail (Some l) rest
          | Some _ => RUP_Invalid
          end
      end
  end.

Lemma scan_rup_clause_conflict : forall assign trail unassigned hcl,
  trail_sound assign trail ->
  (match unassigned with None => True | Some u => eval_lit assign u = true -> False end) ->
  scan_rup_clause trail unassigned hcl = RUP_Conflict ->
  eval_clause assign hcl = false.
Proof.
  intros assign trail unassigned hcl Htr.
  revert unassigned.
  induction hcl as [| l rest IH]; intros unassigned Hno Hs; cbn in Hs.
  - destruct unassigned as [u |]; [discriminate | reflexivity].
  - destruct (lit_status trail l) as [[|] |] eqn:Hls; try discriminate.
    + cbn [eval_clause existsb].
      rewrite (lit_status_sound assign trail l false Htr Hls); cbn.
      exact (IH unassigned Hno Hs).
    + destruct unassigned as [u |]; [discriminate |].
      exfalso.
      clear Hno.
      assert (Hnot_none : forall u0 r0,
                scan_rup_clause trail (Some u0) r0 <> RUP_Conflict).
      { clear; intros u0 r0; revert u0; induction r0 as [| x xr IHxr]; intros u0; cbn.
        - discriminate.
        - destruct (lit_status trail x) as [[|] |]; try discriminate; apply IHxr. }
      exact (Hnot_none l rest Hs).
Qed.

Lemma scan_rup_clause_unit : forall assign trail unassigned hcl u,
  trail_sound assign trail ->
  eval_clause assign hcl = true ->
  scan_rup_clause trail unassigned hcl = RUP_Unit u ->
  (match unassigned with None => False | Some u0 => eval_lit assign u0 = true end) \/
  eval_lit assign u = true.
Proof.
  intros assign trail unassigned hcl u Htr.
  revert unassigned.
  induction hcl as [| l rest IH]; intros unassigned Hsat Hs; cbn in *.
  - discriminate Hsat.
  - apply orb_true_iff in Hsat as [Hl | Hrest].
    + destruct (lit_status trail l) as [[|] |] eqn:Hls; try discriminate.
      * pose proof (lit_status_sound assign trail l false Htr Hls); congruence.
      * destruct unassigned as [u0 |]; [discriminate |].
        assert (Hu_eq : forall x0 r0,
                  scan_rup_clause trail (Some x0) r0 = RUP_Unit u -> x0 = u).
        { clear; intros x0 r0; revert x0; induction r0 as [| y yr IHyr]; intros x0 H; cbn in H.
          - inversion H; reflexivity.
          - destruct (lit_status trail y) as [[|] |]; try discriminate.
            exact (IHyr x0 H). }
        pose proof (Hu_eq l rest Hs) as Heq; subst u; right; exact Hl.
    + destruct (lit_status trail l) as [[|] |] eqn:Hls; try discriminate.
      * exact (IH unassigned Hrest Hs).
      * destruct unassigned as [u0 |]; [discriminate |].
        destruct (IH (Some l) Hrest Hs) as [Hl_true | Hu_true]; [right | right; exact Hu_true].
        assert (Hu_eq : forall x0 r0,
                  scan_rup_clause trail (Some x0) r0 = RUP_Unit u -> x0 = u).
        { clear; intros x0 r0; revert x0; induction r0 as [| y yr IHyr]; intros x0 H; cbn in H.
          - inversion H; reflexivity.
          - destruct (lit_status trail y) as [[|] |]; try discriminate.
            exact (IHyr x0 H). }
        pose proof (Hu_eq l rest Hs) as Heq; subst u; exact Hl_true.
Qed.

Definition db_sat (assign : positive -> bool) (db : pos_trie clause) : Prop :=
  forall cid cl, pt_get cid db = Some cl -> eval_clause assign cl = true.

Fixpoint rup_propagate_hints (db : pos_trie clause) (trail : pos_trie bool)
                             (hints : list positive) {struct hints} : bool :=
  match hints with
  | [] => false
  | hid :: rest =>
      match pt_get hid db with
      | None => false
      | Some hcl =>
          match scan_rup_clause trail None hcl with
          | RUP_Conflict => true
          | RUP_Unit (Z.pos v) => rup_propagate_hints db (pt_set v true trail) rest
          | RUP_Unit (Z.neg v) => rup_propagate_hints db (pt_set v false trail) rest
          | RUP_Unit Z0 | RUP_Invalid => false
          end
      end
  end.

Lemma rup_propagate_hints_sound : forall assign db hints trail,
  db_sat assign db ->
  trail_sound assign trail ->
  rup_propagate_hints db trail hints = true ->
  False.
Proof.
  intros assign db hints.
  induction hints as [| hid rest IH]; intros trail Hdb Htr Hrup; cbn in Hrup.
  - discriminate.
  - destruct (pt_get hid db) as [hcl |] eqn:Hget; [| discriminate].
    pose proof (Hdb hid hcl Hget) as Hhcl_sat.
    destruct (scan_rup_clause trail None hcl) as [| [| v | v] |] eqn:Hscan; try discriminate.
    + pose proof (scan_rup_clause_conflict assign trail None hcl Htr I Hscan) as Hhcl_false.
      congruence.
    + destruct (scan_rup_clause_unit assign trail None hcl (Z.pos v) Htr Hhcl_sat Hscan)
        as [[] | Hv_true].
      cbn in Hv_true.
      exact (IH (pt_set v true trail) Hdb (trail_sound_set assign trail v true Htr Hv_true) Hrup).
    + destruct (scan_rup_clause_unit assign trail None hcl (Z.neg v) Htr Hhcl_sat Hscan)
        as [[] | Hv_true].
      cbn in Hv_true; apply negb_true_iff in Hv_true.
      exact (IH (pt_set v false trail) Hdb (trail_sound_set assign trail v false Htr Hv_true) Hrup).
Qed.

Definition check_rup_clause (db : pos_trie clause) (cl : clause) (hints : list positive) : bool :=
  match seed_neg_clause_aux PT_Empty cl with
  | None => true
  | Some trail0 => rup_propagate_hints db trail0 hints
  end.

Lemma check_rup_clause_sound : forall assign db cl hints,
  db_sat assign db ->
  check_rup_clause db cl hints = true ->
  eval_clause assign cl = true.
Proof.
  intros assign db cl hints Hdb Hrup.
  destruct (eval_clause assign cl) eqn:Hev; [reflexivity |].
  exfalso.
  pose proof (seed_neg_clause_aux_spec assign cl PT_Empty (trail_sound_empty assign) Hev)
    as [trail0 [Hseed Htr0]].
  unfold check_rup_clause in Hrup; rewrite Hseed in Hrup.
  exact (rup_propagate_hints_sound assign db hints trail0 Hdb Htr0 Hrup).
Qed.

Fixpoint load_cnf_db (db : pos_trie clause) (f : cnf) {struct f} : pos_trie clause :=
  match f with
  | [] => db
  | (cid, cl) :: rest => load_cnf_db (pt_set cid cl db) rest
  end.

Lemma load_cnf_db_sat : forall assign f db,
  db_sat assign db ->
  eval_cnf assign f = true ->
  db_sat assign (load_cnf_db db f).
Proof.
  intros assign f.
  induction f as [| [cid cl] rest IH]; intros db Hdb Hf; [exact Hdb |].
  cbn in Hf; apply andb_true_iff in Hf as [Hcl Hrest].
  apply IH; [| exact Hrest].
  intros id c Hget.
  destruct (Pos.eq_dec id cid) as [Heq | Hneq].
  - subst id; rewrite pt_get_set_same in Hget; inversion Hget; subst; exact Hcl.
  - rewrite pt_get_set_other in Hget by exact Hneq; exact (Hdb id c Hget).
Qed.

Fixpoint delete_cids_db (db : pos_trie clause) (cids : list positive)
  {struct cids} : pos_trie clause :=
  match cids with
  | [] => db
  | cid :: rest => delete_cids_db (pt_rem cid db) rest
  end.

Lemma delete_cids_db_sat : forall assign cids db,
  db_sat assign db ->
  db_sat assign (delete_cids_db db cids).
Proof.
  intros assign cids.
  induction cids as [| cid rest IH]; intros db Hdb; [exact Hdb |].
  apply IH; intros id c Hget.
  exact (Hdb id c (pt_get_rem_sub id cid db c Hget)).
Qed.

Definition is_empty_clause (cl : clause) : bool :=
  match cl with
  | [] => true
  | _ :: _ => false
  end.

Fixpoint check_lrat_steps (db : pos_trie clause) (derived_empty : bool) (pf : list lrat_step)
  {struct pf} : bool :=
  match pf with
  | [] => derived_empty
  | step :: rest =>
      match step with
      | LRAT_Del cids =>
          check_lrat_steps (delete_cids_db db cids) derived_empty rest
      | LRAT_Add cid cl hints =>
          if check_rup_clause db cl hints then
            let empty_now := derived_empty || is_empty_clause cl in
            check_lrat_steps (pt_set cid cl db) empty_now rest
          else false
      end
  end.

Definition check_lrat_unsat (f : cnf) (pf : list lrat_step) : bool :=
  check_lrat_steps (load_cnf_db PT_Empty f) false pf.

Lemma check_lrat_steps_sound : forall assign pf db derived_empty,
  db_sat assign db ->
  (derived_empty = true -> False) ->
  check_lrat_steps db derived_empty pf = true ->
  False.
Proof.
  intros assign pf.
  induction pf as [| [cid cl hints | cids] rest IH]; intros db de Hdb Hde Hchk; cbn in Hchk.
  - exact (Hde Hchk).
  - destruct (check_rup_clause db cl hints) eqn:Hrup; [| discriminate].
    pose proof (check_rup_clause_sound assign db cl hints Hdb Hrup) as Hcl_sat.
    assert (Hdb' : db_sat assign (pt_set cid cl db)).
    { intros id c Hget.
      destruct (Pos.eq_dec id cid) as [Heq | Hneq].
      - subst id; rewrite pt_get_set_same in Hget; inversion Hget; subst; exact Hcl_sat.
      - rewrite pt_get_set_other in Hget by exact Hneq; exact (Hdb id c Hget). }
    apply (IH (pt_set cid cl db) (de || is_empty_clause cl) Hdb'); [| exact Hchk].
    intros Hempty.
    apply orb_true_iff in Hempty as [Hde_t | Hcl_emp].
    + exact (Hde Hde_t).
    + destruct cl as [| ? ?]; [cbn in Hcl_sat; discriminate | discriminate Hcl_emp].
  - exact (IH (delete_cids_db db cids) de (delete_cids_db_sat assign cids db Hdb) Hde Hchk).
Qed.

Theorem check_lrat_unsat_sound :
  forall (f : cnf) (pf : list lrat_step),
    check_lrat_unsat f pf = true ->
    forall assign : positive -> bool, eval_cnf assign f = false.
Proof.
  intros f pf Hunsat assign.
  destruct (eval_cnf assign f) eqn:Hev; [| reflexivity].
  exfalso.
  assert (Hdb0 : db_sat assign PT_Empty) by (intros cid cl H; discriminate).
  pose proof (load_cnf_db_sat assign f PT_Empty Hdb0 Hev) as Hdb.
  exact (check_lrat_steps_sound assign pf (load_cnf_db PT_Empty f) false
                                Hdb (fun H => Bool.diff_false_true H) Hunsat).
Qed.

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

Fixpoint append_clauses (cid : positive) (cls : list clause)
  {struct cls} : positive * cnf :=
  match cls with
  | [] => (cid, [])
  | c :: rest =>
      let '(cid', tail_cnf) := append_clauses (Pos.succ cid) rest in
      (cid', (cid, c) :: tail_cnf)
  end.

Definition add_clauses (cls : list clause) (st : blast_state) : blast_state :=
  let '(cid', new_cnf) := append_clauses (bs_next_cid st) cls in
  mk_blast_state (bs_next_var st) cid' (bs_cnf st ++ new_cnf).

Lemma add_clauses_sat_split : forall assign cls st,
  eval_cnf assign (bs_cnf (add_clauses cls st)) = true ->
  eval_cnf assign (bs_cnf st) = true /\
  forall c, In c cls -> eval_clause assign c = true.
Proof.
  intros assign cls st H; unfold add_clauses in H.
  destruct (append_clauses (bs_next_cid st) cls) as [cid' new_cnf] eqn:Happ.
  cbn [bs_cnf] in H; rewrite eval_cnf_app in H; apply andb_true_iff in H as [Hst Hnew].
  split; [exact Hst |].
  clear Hst; revert st cid' new_cnf Happ Hnew.
  induction cls as [| c0 cr IH]; intros st cid' new_cnf Happ Hnew c Hin.
  - inversion Hin.
  - cbn in Happ.
    destruct (append_clauses (Pos.succ (bs_next_cid st)) cr) as [cid2 tail_cnf] eqn:Hcr.
    inversion Happ; subst; clear Happ.
    cbn in Hnew; apply andb_true_iff in Hnew as [Hc0 Htail].
    destruct Hin as [<- | Hrest].
    + exact Hc0.
    + exact (IH (mk_blast_state (bs_next_var st) (Pos.succ (bs_next_cid st)) (bs_cnf st))
                cid' tail_cnf Hcr Htail c Hrest).
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

Lemma bs_cnf_prefix_step :
  forall (gate : lit -> lit -> blast_state -> lit * blast_state)
         (Hpref : forall x y st z st1, gate x y st = (z, st1) ->
                  exists delta, bs_cnf st1 = bs_cnf st ++ delta)
         xs ys st zs st',
    map2_emit gate xs ys st = (zs, st') ->
    exists delta, bs_cnf st' = bs_cnf st ++ delta.
Proof.
  intros gate Hpref xs.
  induction xs as [| x rx IH]; intros [| y ry] st zs st' Hm; cbn in Hm.
  - inversion Hm; subst; exists []; rewrite app_nil_r; reflexivity.
  - inversion Hm; subst; exists []; rewrite app_nil_r; reflexivity.
  - inversion Hm; subst; exists []; rewrite app_nil_r; reflexivity.
  - destruct (gate x y st) as [z st1] eqn:Hg.
    destruct (map2_emit gate rx ry st1) as [zr st2] eqn:Hmr.
    inversion Hm; subst; clear Hm.
    destruct (Hpref x y st z st1 Hg) as [d1 Hd1].
    destruct (IH ry st1 zr st' Hmr) as [d2 Hd2].
    exists (d1 ++ d2); rewrite Hd2, Hd1, app_assoc; reflexivity.
Qed.

Lemma map2_emit_sound :
  forall (gate : lit -> lit -> blast_state -> lit * blast_state)
         (f_bool : bool -> bool -> bool)
         (Hpref : forall x y st z st1, gate x y st = (z, st1) ->
                  exists delta, bs_cnf st1 = bs_cnf st ++ delta)
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
      * apply (Hz_ev (d2 ++ rem)).
        rewrite app_assoc, <- Hd2; exact Hsat.
      * apply (Hzr_ev rem); [cbn in Hk; lia | exact Hsat].
Qed.

Lemma emit_and2_pref : forall x y st z st1,
  emit_and2 x y st = (z, st1) -> exists d, bs_cnf st1 = bs_cnf st ++ d.
Proof.
  intros x y st z st1 H; unfold emit_and2 in H; cbn in H; inversion H; subst; cbn.
  eexists; reflexivity.
Qed.

Lemma emit_or2_pref : forall x y st z st1,
  emit_or2 x y st = (z, st1) -> exists d, bs_cnf st1 = bs_cnf st ++ d.
Proof.
  intros x y st z st1 H; unfold emit_or2 in H; cbn in H; inversion H; subst; cbn.
  eexists; reflexivity.
Qed.

Lemma emit_xor2_pref : forall x y st z st1,
  emit_xor2 x y st = (z, st1) -> exists d, bs_cnf st1 = bs_cnf st ++ d.
Proof.
  intros x y st z st1 H; unfold emit_xor2 in H; cbn in H; inversion H; subst; cbn.
  eexists; reflexivity.
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
  assert (Hsat1 : eval_cnf assign (bs_cnf st1 ++ dp ++ rem) = true)
    by (rewrite app_assoc, <- Hdp; exact Hsat).
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
    cbn [rbv_bits]; apply (Hbev (dp ++ rem) (Z.to_nat i)); [| exact Hsat1].
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
  assert (Hsat1 : eval_cnf assign (bs_cnf st1 ++ dp ++ rem) = true)
    by (rewrite app_assoc, <- Hdp; exact Hsat).
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
    cbn [rbv_bits]; apply (Hbev (dp ++ rem) (Z.to_nat i)); [| exact Hsat1].
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
  assert (Hsat1 : eval_cnf assign (bs_cnf st1 ++ dp ++ rem) = true)
    by (rewrite app_assoc, <- Hdp; exact Hsat).
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
    cbn [rbv_bits]; apply (Hbev (dp ++ rem) (Z.to_nat i)); [| exact Hsat1].
    rewrite Hla; unfold Integers.zwordsize in Hi; lia.
Qed.

Fixpoint emit_or_list (ls : list lit) (st : blast_state)
  {struct ls} : lit * blast_state :=
  match ls with
  | [] => (lit_false, st)
  | [x] => (x, st)
  | x :: rest =>
      let '(sub, st1) := emit_or_list rest st in
      emit_or2 x sub st1
  end.

Lemma emit_or_list_pref : forall ls st out st',
  emit_or_list ls st = (out, st') -> exists d, bs_cnf st' = bs_cnf st ++ d.
Proof.
  induction ls as [| x [| y r] IH]; intros st out st' H.
  - cbn in H; inversion H; subst; exists []; rewrite app_nil_r; reflexivity.
  - cbn in H; inversion H; subst; exists []; rewrite app_nil_r; reflexivity.
  - change ((let '(sub, st1) := emit_or_list (y :: r) st in emit_or2 x sub st1) = (out, st')) in H.
    destruct (emit_or_list (y :: r) st) as [sub st1] eqn:Hs.
    destruct (IH st sub st1 Hs) as [d1 Hd1].
    destruct (emit_or2_pref x sub st1 out st' H) as [d2 Hd2].
    exists (d1 ++ d2); rewrite Hd2, Hd1, app_assoc; reflexivity.
Qed.

Lemma emit_or_list_sound : forall assign ls st out st' rem,
  eval_lit assign lit_false = false ->
  wf_lits_nonzero ls ->
  emit_or_list ls st = (out, st') ->
  eval_cnf assign (bs_cnf st' ++ rem) = true ->
  out <> 0%Z /\
  eval_lit assign out = existsb (eval_lit assign) ls.
Proof.
  intros assign ls.
  induction ls as [| x [| y r] IH]; intros st out st' rem Hlf Hwf Hemit Hsat.
  - cbn in Hemit; inversion Hemit; subst; split; [discriminate | exact Hlf].
  - cbn in Hemit; inversion Hemit; subst; inversion Hwf as [| ? ? Hx _]; subst.
    split; [exact Hx | cbn; rewrite orb_false_r; reflexivity].
  - change ((let '(sub, st1) := emit_or_list (y :: r) st in emit_or2 x sub st1) = (out, st')) in Hemit.
    inversion Hwf as [| ? ? Hx Hwfr]; subst.
    destruct (emit_or_list (y :: r) st) as [sub st1] eqn:Hsub.
    destruct (emit_or2_pref x sub st1 out st' Hemit) as [d2 Hd2].
    assert (Hsat1 : eval_cnf assign (bs_cnf st1 ++ d2 ++ rem) = true)
      by (rewrite app_assoc, <- Hd2; exact Hsat).
    destruct (IH st sub st1 (d2 ++ rem) Hlf Hwfr Hsub Hsat1) as [Hsub_nz Hsub_ev].
    destruct (emit_or2_sound assign x sub st1 out st' Hx Hsub_nz Hemit) as [Hout_nz Hout_ev].
    split; [exact Hout_nz |].
    rewrite (proj2 (Hout_ev rem Hsat)), Hsub_ev; reflexivity.
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
  mux_bits_list sel ts fs st = (ms, st') -> exists d, bs_cnf st' = bs_cnf st ++ d.
Proof.
  intros sel ts.
  induction ts as [| t rt IH]; intros [| f rf] st ms st' H; cbn [mux_bits_list] in H.
  - inversion H; subst; exists []; rewrite app_nil_r; reflexivity.
  - inversion H; subst; exists []; rewrite app_nil_r; reflexivity.
  - inversion H; subst; exists []; rewrite app_nil_r; reflexivity.
  - destruct (emit_mux2 sel t f st) as [m st1] eqn:Hm.
    destruct (mux_bits_list sel rt rf st1) as [mr st2] eqn:Hmr.
    inversion H; subst; clear H.
    assert (Hd1 : exists d1, bs_cnf st1 = bs_cnf st ++ d1).
    { unfold emit_mux2 in Hm; cbn in Hm; inversion Hm; subst; cbn; eexists; reflexivity. }
    destruct Hd1 as [d1 Hd1].
    destruct (IH rf st1 mr st' Hmr) as [d2 Hd2].
    exists (d1 ++ d2); rewrite Hd2, Hd1, app_assoc; reflexivity.
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
    assert (Hs1 : eval_cnf assign (bs_cnf st1 ++ d2 ++ rem) = true)
      by (rewrite app_assoc, <- Hd2; exact Hsat).
    destruct (emit_mux2_sound assign sel t f st m st1 Hsel Ht Hf He) as [Hm_nz Hm_ev].
    destruct (IH rf st1 mr st' rem Hsel Hlen' Hwrt Hwrf Hmr Hsat)
      as (Hmr_len & Hmr_wf & Hmr_ev).
    repeat split.
    + cbn; rewrite Hmr_len; reflexivity.
    + constructor; [exact Hm_nz | exact Hmr_wf].
    + cbn [List.map]; rewrite (proj2 (Hm_ev (d2 ++ rem) Hs1)), Hmr_ev.
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
  cbn [append_clauses bs_cnf] in Hquery_false.
  rewrite eval_cnf_app, Hgates in Hquery_false; cbn in Hquery_false.
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
  assert (Hs4 : eval_cnf assign (bs_cnf st4 ++ d5) = true)
    by (rewrite <- Hd5; exact Hgates).
  assert (Hs3 : eval_cnf assign (bs_cnf st3 ++ d4 ++ d5) = true)
    by (rewrite app_assoc, <- Hd4; exact Hs4).
  assert (Hs2 : eval_cnf assign (bs_cnf st2 ++ d3 ++ d4 ++ d5) = true)
    by (rewrite app_assoc, <- Hd3; exact Hs3).
  assert (Hs1 : eval_cnf assign (bs_cnf st1 ++ d2 ++ d3 ++ d4 ++ d5) = true)
    by (rewrite app_assoc, <- Hd2; exact Hs2).
  destruct (emit_or_list_sound assign xor_bits st1 val_diff st2
              (d3 ++ d4 ++ d5) Hlf Hxwf Horl Hs2) as [Hvd_nz Hvd_ev].
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
  rewrite Hcex_eq, Hno_ub, (proj2 (Hdb_ev d5 Hs4)),
          (eval_neg_lit_nonzero assign (rbv_psn src_r) Hps) in Hquery_false.
  unfold eval_rail_psn in Hsrc_def; rewrite Hsrc_def in Hquery_false; cbn in Hquery_false.
  rewrite (proj2 (Hbt_ev (d4 ++ d5) Hs3)), Hvd_ev in Hquery_false.
  apply orb_false_iff in Hquery_false as [Htgt_def Hxor_false].
  split; [exact Htgt_def |].
  apply (existsb_xor_bits_diff sz assign src_r tgt_r xor_bits
           (conj Hws Hls) (conj Hwt Hlt)); [congruence | | exact Hxor_false].
  intros k Hk; apply (Hxev (d2 ++ d3 ++ d4 ++ d5) k); [congruence | exact Hs1].
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

(** ** 5. Verified Bounded DPLL UNSAT Auto-Solver ([solve_cnf_unsat]) *)

Lemma eval_cnf_rev_append : forall assign f1 f2,
  eval_cnf assign f1 = true ->
  eval_cnf assign f2 = true ->
  eval_cnf assign (List.rev_append f1 f2) = true.
Proof.
  intros assign f1; induction f1 as [| [cid cl] rest IH]; intros f2 H1 H2; cbn in *.
  - exact H2.
  - apply andb_true_iff in H1 as [Hcl Hrest].
    apply IH; [exact Hrest | unfold eval_cnf in H2 |- *; cbn [forallb]; rewrite Hcl, H2; reflexivity].
Qed.

Variant bcp_pass_res : Type :=
| BCP_PassConflict
| BCP_PassOk (trail' : pos_trie bool) (kept_rev : cnf) (prog : bool).

Fixpoint clause_has_true (trail : pos_trie bool) (cl : clause) {struct cl} : bool :=
  match cl with
  | [] => false
  | l :: rest =>
      match lit_status trail l with
      | Some true => true
      | _ => clause_has_true trail rest
      end
  end.

Fixpoint bcp_pass (trail : pos_trie bool) (prog : bool) (kept_rev : cnf) (rem : cnf)
  {struct rem} : bcp_pass_res :=
  match rem with
  | [] => BCP_PassOk trail kept_rev prog
  | (cid, cl) :: rest =>
      if clause_has_true trail cl then
        bcp_pass trail prog kept_rev rest
      else
        match scan_rup_clause trail None cl with
        | RUP_Conflict => BCP_PassConflict
        | RUP_Unit (Z.pos v) => bcp_pass (pt_set v true trail) true kept_rev rest
        | RUP_Unit (Z.neg v) => bcp_pass (pt_set v false trail) true kept_rev rest
        | RUP_Unit Z0 => BCP_PassConflict
        | RUP_Invalid => bcp_pass trail prog ((cid, cl) :: kept_rev) rest
        end
  end.

Lemma bcp_pass_sound : forall assign rem trail prog kept_rev,
  trail_sound assign trail ->
  eval_cnf assign kept_rev = true ->
  eval_cnf assign rem = true ->
  match bcp_pass trail prog kept_rev rem with
  | BCP_PassConflict => False
  | BCP_PassOk trail' kept' _ =>
      trail_sound assign trail' /\ eval_cnf assign kept' = true
  end.
Proof.
  intros assign rem; induction rem as [| [cid cl] rest IH];
    intros trail prog kept_rev Htr Hkept Hrem.
  - cbn; split; [exact Htr | exact Hkept].
  - cbn [eval_cnf forallb] in Hrem; apply andb_true_iff in Hrem as [Hcl Hrest].
    cbn [bcp_pass].
    destruct (clause_has_true trail cl).
    + exact (IH trail prog kept_rev Htr Hkept Hrest).
    + destruct (scan_rup_clause trail None cl) as [| [| v | v] |] eqn:Hscan.
      * pose proof (scan_rup_clause_conflict assign trail None cl Htr I Hscan); congruence.
      * destruct (scan_rup_clause_unit assign trail None cl Z0 Htr Hcl Hscan)
          as [[] | Hz]; discriminate Hz.
      * destruct (scan_rup_clause_unit assign trail None cl (Z.pos v) Htr Hcl Hscan)
          as [[] | Hv]; cbn in Hv.
        exact (IH (pt_set v true trail) true kept_rev
                  (trail_sound_set assign trail v true Htr Hv) Hkept Hrest).
      * destruct (scan_rup_clause_unit assign trail None cl (Z.neg v) Htr Hcl Hscan)
          as [[] | Hv]; cbn in Hv; apply negb_true_iff in Hv.
        exact (IH (pt_set v false trail) true kept_rev
                  (trail_sound_set assign trail v false Htr Hv) Hkept Hrest).
      * apply IH; [exact Htr | unfold eval_cnf in Hkept |- *; cbn [forallb]; rewrite Hcl, Hkept; reflexivity | exact Hrest].
Qed.

Variant bcp_loop_res : Type :=
| BCP_LoopConflict
| BCP_LoopOpen (trail' : pos_trie bool) (active : cnf).

Fixpoint bcp_loop (passes : nat) (trail : pos_trie bool) (f : cnf)
  {struct passes} : bcp_loop_res :=
  match passes with
  | O => BCP_LoopOpen trail f
  | S p =>
      match bcp_pass trail false [] f with
      | BCP_PassConflict => BCP_LoopConflict
      | BCP_PassOk trail1 kept_rev true =>
          bcp_loop p trail1 (List.rev_append kept_rev [])
      | BCP_PassOk trail1 kept_rev false =>
          BCP_LoopOpen trail1 (List.rev_append kept_rev [])
      end
  end.

Lemma bcp_loop_sound : forall assign passes trail f,
  trail_sound assign trail ->
  eval_cnf assign f = true ->
  match bcp_loop passes trail f with
  | BCP_LoopConflict => False
  | BCP_LoopOpen trail' active =>
      trail_sound assign trail' /\ eval_cnf assign active = true
  end.
Proof.
  intros assign passes; induction passes as [| p IHp]; intros trail f Htr Hf; cbn [bcp_loop].
  - split; [exact Htr | exact Hf].
  - pose proof (bcp_pass_sound assign f trail false [] Htr eq_refl Hf) as Hbp.
    destruct (bcp_pass trail false [] f) as [| trail1 kept_rev [|]].
    + exact Hbp.
    + destruct Hbp as [Htr1 Hk].
      exact (IHp trail1 (List.rev_append kept_rev []) Htr1
               (eval_cnf_rev_append assign kept_rev [] Hk eq_refl)).
    + destruct Hbp as [Htr1 Hk].
      split; [exact Htr1 | exact (eval_cnf_rev_append assign kept_rev [] Hk eq_refl)].
Qed.

Fixpoint pick_unassigned_in_clause (trail : pos_trie bool) (cl : clause)
  {struct cl} : option positive :=
  match cl with
  | [] => None
  | Z0 :: rest => pick_unassigned_in_clause trail rest
  | Z.pos v :: rest =>
      match pt_get v trail with
      | None => Some v
      | Some _ => pick_unassigned_in_clause trail rest
      end
  | Z.neg v :: rest =>
      match pt_get v trail with
      | None => Some v
      | Some _ => pick_unassigned_in_clause trail rest
      end
  end.

Fixpoint unassigned_count_clause (trail : pos_trie bool) (cl : clause)
  {struct cl} : nat :=
  match cl with
  | [] => O
  | l :: rest =>
      match lit_status trail l with
      | None => S (unassigned_count_clause trail rest)
      | Some _ => unassigned_count_clause trail rest
      end
  end.

Fixpoint pick_branch_var (trail : pos_trie bool) (best : option (nat * positive)) (f : cnf)
  {struct f} : option positive :=
  match f with
  | [] => option_map snd best
  | (_, cl) :: rest =>
      match pick_unassigned_in_clause trail cl with
      | None => pick_branch_var trail best rest
      | Some v =>
          let cnt := unassigned_count_clause trail cl in
          if Nat.leb cnt 2%nat then Some v
          else
            match best with
            | None => pick_branch_var trail (Some (cnt, v)) rest
            | Some (bcnt, _) =>
                if Nat.ltb cnt bcnt
                then pick_branch_var trail (Some (cnt, v)) rest
                else pick_branch_var trail best rest
            end
      end
  end.

Fixpoint dpll_unsat (fuel : nat) (trail : pos_trie bool) (f : cnf)
  {struct fuel} : bool :=
  match bcp_loop (S (List.length f)) trail f with
  | BCP_LoopConflict => true
  | BCP_LoopOpen trail1 active =>
      match fuel with
      | O => false
      | S fuel' =>
          match pick_branch_var trail1 None active with
          | None => false
          | Some v =>
              dpll_unsat fuel' (pt_set v true trail1) active &&
              dpll_unsat fuel' (pt_set v false trail1) active
          end
      end
  end.

Lemma dpll_unsat_sound : forall fuel assign trail f,
  dpll_unsat fuel trail f = true ->
  trail_sound assign trail ->
  eval_cnf assign f = true ->
  False.
Proof.
  induction fuel as [| fuel' IH]; intros assign trail f Hdpll Htr Hf; cbn [dpll_unsat] in Hdpll.
  - pose proof (bcp_loop_sound assign (S (List.length f)) trail f Htr Hf) as Hbl.
    destruct (bcp_loop (S (List.length f)) trail f); [exact Hbl | discriminate Hdpll].
  - pose proof (bcp_loop_sound assign (S (List.length f)) trail f Htr Hf) as Hbl.
    destruct (bcp_loop (S (List.length f)) trail f) as [| trail1 active]; [exact Hbl |].
    destruct Hbl as [Htr1 Hact].
    destruct (pick_branch_var trail1 None active) as [v |]; [| discriminate Hdpll].
    apply andb_true_iff in Hdpll as [Ht Hf_br].
    destruct (assign v) eqn:Hv.
    + exact (IH assign (pt_set v true trail1) active Ht
               (trail_sound_set assign trail1 v true Htr1 Hv) Hact).
    + exact (IH assign (pt_set v false trail1) active Hf_br
               (trail_sound_set assign trail1 v false Htr1 Hv) Hact).
Qed.

Definition solve_cnf_unsat (fuel : nat) (f : cnf) : bool :=
  dpll_unsat fuel PT_Empty f.

Theorem solve_cnf_unsat_sound : forall (fuel : nat) (f : cnf) (assign : positive -> bool),
  solve_cnf_unsat fuel f = true ->
  eval_cnf assign f = false.
Proof.
  intros fuel f assign Hsol.
  destruct (eval_cnf assign f) eqn:Hev; [| reflexivity].
  exfalso.
  exact (dpll_unsat_sound fuel assign PT_Empty f Hsol (trail_sound_empty assign) Hev).
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
    + unfold eval_cnf in Hev |- *; cbn [forallb]; rewrite (Hsat c (or_introl eq_refl)), Hev; reflexivity.
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
  repeat split; cbn -[eval_cnf].
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
  induction ls as [| x [| y r] IH]; intros asg st out st' Hwf Hsat Hemit.
  - cbn in Hemit; inversion Hemit; subst; exists asg;
      split; [lia | split; [apply agree_below_refl | split; [exact Hsat |
      cbn; pose proof (proj1 (proj1 Hsat)); lia]]].
  - cbn in Hemit; inversion Hemit; subst; inversion Hwf as [| ? ? Hx _]; subst.
    exists asg;
      split; [lia | split; [apply agree_below_refl | split; [exact Hsat | exact Hx]]].
  - change ((let '(sub, st1) := emit_or_list (y :: r) st in emit_or2 x sub st1) = (out, st')) in Hemit.
    inversion Hwf as [| ? ? Hx Hwfr]; subst.
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

Fixpoint emit_or_list_opt (ls : list lit) (st : blast_state)
  {struct ls} : lit * blast_state :=
  match ls with
  | [] => (lit_false, st)
  | x :: rest =>
      let '(sub, st1) := emit_or_list_opt rest st in
      emit_or2_opt x sub st1
  end.

Lemma emit_or_list_opt_step : forall ls asg st out st',
  wf_lits_bound (bs_next_var st) ls ->
  sat_blast_st asg st ->
  emit_or_list_opt ls st = (out, st') ->
  exists asg',
    step_spec st st' asg asg' /\
    wf_lit_bound (bs_next_var st') out /\
    eval_lit asg' out = existsb (fun b : bool => b) (List.map (eval_lit asg) ls).
Proof.
  induction ls as [| x rest IH]; intros asg st out st' Hwf Hsat Hemit; cbn [emit_or_list_opt] in Hemit.
  - inversion Hemit; subst; exists asg; split;
      [exact (step_spec_refl _ asg Hsat) | split;
       [exact (wf_lit_bound_false _ (proj1 (proj1 Hsat))) | exact (sat_eval_lit_false asg _ Hsat)]].
  - inversion Hwf as [| ? ? Hx Hwfr]; subst.
    destruct (emit_or_list_opt rest st) as [sub st1] eqn:Hsub.
    destruct (IH asg st sub st1 Hwfr Hsat Hsub) as (asg1 & Hs1 & Hwf_sub & Hev_sub).
    destruct (emit_or2_opt_step asg1 x sub st1 out st' (proj2 (proj2 Hs1))
                (wf_lit_bound_mono _ _ x (proj1 Hs1) Hx) Hwf_sub Hemit)
      as (asg2 & Hs2 & Hwf_out & Hev_out).
    exists asg2; split; [exact (step_spec_trans st st1 st' asg asg1 asg2 Hs1 Hs2) | split; [exact Hwf_out |]].
    cbn; rewrite Hev_out, (step_spec_eval_lit st st1 asg asg1 x Hs1 Hx), Hev_sub; reflexivity.
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
  unfold add_clauses in Hqf; cbn [append_clauses bs_cnf] in Hqf.
  rewrite eval_cnf_app, (proj2 (proj2 (proj2 (proj2 Hs5)))) in Hqf; cbn in Hqf.
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

Lemma modulus_pow_sz : forall sz,
  @Integers.modulus sz = (2 ^ Z.pos sz)%Z.
Proof.
  intros sz; rewrite @Integers.modulus_def, two_power_pos_equiv; reflexivity.
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
  - assert (k_val = 0)%Z by (cbn in Hk; rewrite Z.pow_0_r in Hk; lia); subst k_val; reflexivity.
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
    destruct (fn_k k st) as [[bits_k psn_k] st1] eqn:Ef.
    destruct (emit_eq_const_bits (Z.of_nat k) b_bits st1) as [eq_k st2] eqn:Eeq.
    destruct (mux_shift_table sz fn_k b_bits r' st2) as [[rest_bits rest_psn] st3] eqn:Er.
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
      * subst ub; rewrite Nat2Z.id.
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
  unfold blast_shl_rail in Hbl.
  destruct (mux_shift_table sz (blast_shl_k nuw nsw sz (rbv_bits a))
                            (rbv_bits b) (Pos.to_nat sz) st)
    as [[bits sh_psn] st1] eqn:Hmux.
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
        cbn [andb]; rewrite Hev_nl, Hev_xhs, existsb_id_map_f.
        unfold hi; rewrite (step_spec_eval_lits st0 s01 asg0 asg01 _ Hs01 Hw_hi0),
                           map_skipn_eq, Hev_ba0.
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
  cbn zeta in Hspec_mux; rewrite Nat.sub_diag in Hspec_mux; cbn [Z.of_nat] in Hspec_mux.
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
      rewrite Z.gtb_ltb, <- (bools_to_Z_zero_iff hi).
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
      rewrite Hmsb_res, bools_to_Z_eq_repeat_iff, Bool.negb_involutive; reflexivity. }
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
  unfold blast_lshr_rail in Hbl.
  destruct (mux_shift_table sz (blast_lshr_k ex sz (rbv_bits a))
                            (rbv_bits b) (Pos.to_nat sz) st)
    as [[bits sh_psn] st1] eqn:Hmux.
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
  cbn zeta in Hspec_mux; rewrite Nat.sub_diag in Hspec_mux; cbn [Z.of_nat] in Hspec_mux.
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
  unfold blast_ashr_rail in Hbl.
  destruct (mux_shift_table sz (blast_ashr_k ex sz (rbv_bits a))
                            (rbv_bits b) (Pos.to_nat sz) st)
    as [[bits sh_psn] st1] eqn:Hmux.
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
  cbn zeta in Hspec_mux; rewrite Nat.sub_diag in Hspec_mux; cbn [Z.of_nat] in Hspec_mux.
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
    + unfold eval_rail_val; cbn [rbv_bits].
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
    unfold eval_rail_val; cbn [rbv_bits].
    rewrite map_app, map_repeat_eq, (eval_msb_lit fw asg a (conj Hwa Hla)),
            bools_to_Z_app, bools_to_Z_repeat_b, length_map, Hla, positive_nat_Z.
    set (va := eval_rail_val fw asg a).
    rewrite <- (unsigned_eval_rail_val fw asg a Hla).
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
      * f_equal; rewrite Hua_split, Hures, <- (bools_to_Z_zero_iff b_hi).
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
    + unfold eval_rail_val; cbn [rbv_bits].
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
      { unfold vr; rewrite (unsigned_eval_rail_val sz asg r Hlr); fold br.
        rewrite <- (firstn_skipn_eq (Pos.to_nat sz - 1) br) at 1, Hskip_one,
                bools_to_Z_app, Hlo_len, bools_to_Z_cons; cbn [bools_to_Z]; nia. }
      assert (Hhm_pow : (2 ^ Z.of_nat (Pos.to_nat sz - 1) = @Integers.half_modulus sz)%Z).
      { pose proof (@Integers.half_modulus_modulus sz) as Hhm.
        rewrite modulus_pow_sz, <- positive_nat_Z in Hhm.
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
    + unfold eval_rail_val, Integers.one, Integers.zero; cbn [rbv_bits List.map].
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
