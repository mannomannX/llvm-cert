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

From Vellvm Require Import
  Numeric.Zbits
  Numeric.Integers.

Unset Implicit Arguments.
Unset Strict Implicit.
Set Default Goal Selector "!".

Local Open Scope bool_scope.
Local Open Scope list_scope.

(** ** 1. Positive-Indexed Binary Trie ([O(log N)] Clause & Trail Maps) *)

Section PosTrie.
  Context {V : Type}.

  Inductive pos_trie : Type :=
  | PT_Empty
  | PT_Node (left_t : pos_trie) (val_opt : option V) (right_t : pos_trie).

  Fixpoint pt_get (p : positive) (t : pos_trie) : option V :=
    match t with
    | PT_Empty => None
    | PT_Node l ov r =>
        match p with
        | xH => ov
        | xO q => pt_get q l
        | xI q => pt_get q r
        end
    end.

  Fixpoint pt_set (p : positive) (v : V) (t : pos_trie) : pos_trie :=
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

  Fixpoint pt_rem (p : positive) (t : pos_trie) : pos_trie :=
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
  - subst u; rewrite pt_get_set_same in Hget; inversion Hget; subst; exact Hv.
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
  : option (pos_trie bool) :=
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
  : rup_clause_res :=
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
                             (hints : list positive) : bool :=
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

Fixpoint load_cnf_db (db : pos_trie clause) (f : cnf) : pos_trie clause :=
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

Fixpoint delete_cids_db (db : pos_trie clause) (cids : list positive) : pos_trie clause :=
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
  : bool :=
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
  intros sz x; unfold bit_int_to_bools; rewrite map_length, seq_length; reflexivity.
Qed.

Theorem bit_int_to_bools_repr : forall sz (x : @Integers.bit_int sz),
  @Integers.repr sz (bools_to_Z (bit_int_to_bools sz x)) = x.
Proof.
  intros sz x.
  apply @Integers.same_bits_eq; intros i Hi.
  rewrite @Integers.testbit_repr by exact Hi.
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by (rewrite Z2Nat.id; lia).
  rewrite bools_to_Z_testbit.
  unfold bit_int_to_bools.
  assert (Hlt : (Z.to_nat i < Pos.to_nat sz)%nat)
    by (unfold Integers.zwordsize in Hi; lia).
  rewrite (nth_indep _ false (@Integers.testbit sz x (Z.of_nat 0)))
    by (rewrite map_length, seq_length; exact Hlt).
  rewrite map_nth, seq_nth by exact Hlt.
  cbn [Nat.add]; rewrite Z2Nat.id by lia; reflexivity.
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

Fixpoint append_clauses (cid : positive) (cls : list clause) : positive * cnf :=
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
  revert st cid' new_cnf Happ Hnew; clear Hst.
  induction cls as [| c0 cr IH]; intros st cid' new_cnf Happ Hnew c Hin.
  - inversion Hin.
  - cbn in Happ.
    destruct (append_clauses (Pos.succ (bs_next_cid st)) cr) as [cid2 tail_cnf] eqn:Hcr.
    inversion Happ; subst; clear Happ.
    cbn in Hnew; apply andb_true_iff in Hnew as [Hc0 Htail].
    destruct Hin as [<- | Hrest].
    + exact Hc0.
    + exact (IH (mk_blast_state (bs_next_var st) (Pos.succ (bs_next_cid st)) (bs_cnf st))
                cid2 tail_cnf Hcr Htail c Hrest).
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
  unfold emit_and2 in Hemit; cbn in Hemit.
  destruct (append_clauses (bs_next_cid st)
              [[neg_lit (Z.pos (bs_next_var st)); a];
               [neg_lit (Z.pos (bs_next_var st)); b];
               [Z.pos (bs_next_var st); neg_lit a; neg_lit b]]) as [cid' new_cnf] eqn:Happ.
  inversion Hemit; subst; clear Hemit.
  split; [discriminate |].
  intros rem Hsat.
  rewrite <- app_assoc in Hsat; rewrite eval_cnf_app in Hsat.
  apply andb_true_iff in Hsat as [Hst Hnew_rem].
  rewrite eval_cnf_app in Hnew_rem; apply andb_true_iff in Hnew_rem as [Hnew _].
  assert (Hcls : eval_cnf assign (bs_cnf (add_clauses
                   [[neg_lit (Z.pos (bs_next_var st)); a];
                    [neg_lit (Z.pos (bs_next_var st)); b];
                    [Z.pos (bs_next_var st); neg_lit a; neg_lit b]]
                   (snd (alloc_var st)))) = true).
  { unfold add_clauses; cbn [alloc_var snd bs_next_cid bs_cnf].
    rewrite Happ; cbn [bs_cnf]; rewrite eval_cnf_app, Hst, Hnew; reflexivity. }
  destruct (add_clauses_sat_split assign _ _ Hcls) as [_ Hin].
  pose proof (Hin _ (or_introl eq_refl)) as C1.
  pose proof (Hin _ (or_intror (or_introl eq_refl))) as C2.
  pose proof (Hin _ (or_intror (or_intror (or_introl eq_refl)))) as C3.
  cbn [eval_clause existsb] in C1, C2, C3.
  rewrite (eval_neg_lit_nonzero assign a Ha), (eval_neg_lit_nonzero assign b Hb) in C3.
  cbn [neg_lit eval_lit] in C1, C2, C3.
  split; [exact Hst |].
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
  unfold emit_or2 in Hemit; cbn in Hemit.
  destruct (append_clauses (bs_next_cid st)
              [[Z.pos (bs_next_var st); neg_lit a];
               [Z.pos (bs_next_var st); neg_lit b];
               [neg_lit (Z.pos (bs_next_var st)); a; b]]) as [cid' new_cnf] eqn:Happ.
  inversion Hemit; subst; clear Hemit.
  split; [discriminate |].
  intros rem Hsat.
  rewrite <- app_assoc in Hsat; rewrite eval_cnf_app in Hsat.
  apply andb_true_iff in Hsat as [Hst Hnew_rem].
  rewrite eval_cnf_app in Hnew_rem; apply andb_true_iff in Hnew_rem as [Hnew _].
  assert (Hcls : eval_cnf assign (bs_cnf (add_clauses
                   [[Z.pos (bs_next_var st); neg_lit a];
                    [Z.pos (bs_next_var st); neg_lit b];
                    [neg_lit (Z.pos (bs_next_var st)); a; b]]
                   (snd (alloc_var st)))) = true).
  { unfold add_clauses; cbn [alloc_var snd bs_next_cid bs_cnf].
    rewrite Happ; cbn [bs_cnf]; rewrite eval_cnf_app, Hst, Hnew; reflexivity. }
  destruct (add_clauses_sat_split assign _ _ Hcls) as [_ Hin].
  pose proof (Hin _ (or_introl eq_refl)) as C1.
  pose proof (Hin _ (or_intror (or_introl eq_refl))) as C2.
  pose proof (Hin _ (or_intror (or_intror (or_introl eq_refl)))) as C3.
  cbn [eval_clause existsb] in C1, C2, C3.
  rewrite (eval_neg_lit_nonzero assign a Ha) in C1.
  rewrite (eval_neg_lit_nonzero assign b Hb) in C2.
  cbn [neg_lit eval_lit] in C1, C2, C3.
  split; [exact Hst |].
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
  unfold emit_xor2 in Hemit; cbn in Hemit.
  destruct (append_clauses (bs_next_cid st)
              [[neg_lit (Z.pos (bs_next_var st)); a; b];
               [neg_lit (Z.pos (bs_next_var st)); neg_lit a; neg_lit b];
               [Z.pos (bs_next_var st); neg_lit a; b];
               [Z.pos (bs_next_var st); a; neg_lit b]]) as [cid' new_cnf] eqn:Happ.
  inversion Hemit; subst; clear Hemit.
  split; [discriminate |].
  intros rem Hsat.
  rewrite <- app_assoc in Hsat; rewrite eval_cnf_app in Hsat.
  apply andb_true_iff in Hsat as [Hst Hnew_rem].
  rewrite eval_cnf_app in Hnew_rem; apply andb_true_iff in Hnew_rem as [Hnew _].
  assert (Hcls : eval_cnf assign (bs_cnf (add_clauses
                   [[neg_lit (Z.pos (bs_next_var st)); a; b];
                    [neg_lit (Z.pos (bs_next_var st)); neg_lit a; neg_lit b];
                    [Z.pos (bs_next_var st); neg_lit a; b];
                    [Z.pos (bs_next_var st); a; neg_lit b]]
                   (snd (alloc_var st)))) = true).
  { unfold add_clauses; cbn [alloc_var snd bs_next_cid bs_cnf].
    rewrite Happ; cbn [bs_cnf]; rewrite eval_cnf_app, Hst, Hnew; reflexivity. }
  destruct (add_clauses_sat_split assign _ _ Hcls) as [_ Hin].
  pose proof (Hin _ (or_introl eq_refl)) as C1.
  pose proof (Hin _ (or_intror (or_introl eq_refl))) as C2.
  pose proof (Hin _ (or_intror (or_intror (or_introl eq_refl)))) as C3.
  pose proof (Hin _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as C4.
  cbn [eval_clause existsb] in C1, C2, C3, C4.
  rewrite (eval_neg_lit_nonzero assign a Ha) in C2, C3.
  rewrite (eval_neg_lit_nonzero assign b Hb) in C2, C4.
  cbn [neg_lit eval_lit] in C1, C2, C3, C4.
  split; [exact Hst |].
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
  unfold emit_mux2 in Hemit; cbn in Hemit.
  destruct (append_clauses (bs_next_cid st)
              [[neg_lit sel; neg_lit (Z.pos (bs_next_var st)); tl];
               [neg_lit sel; Z.pos (bs_next_var st); neg_lit tl];
               [sel; neg_lit (Z.pos (bs_next_var st)); fl];
               [sel; Z.pos (bs_next_var st); neg_lit fl]]) as [cid' new_cnf] eqn:Happ.
  inversion Hemit; subst; clear Hemit.
  split; [discriminate |].
  intros rem Hsat.
  rewrite <- app_assoc in Hsat; rewrite eval_cnf_app in Hsat.
  apply andb_true_iff in Hsat as [Hst Hnew_rem].
  rewrite eval_cnf_app in Hnew_rem; apply andb_true_iff in Hnew_rem as [Hnew _].
  assert (Hcls : eval_cnf assign (bs_cnf (add_clauses
                   [[neg_lit sel; neg_lit (Z.pos (bs_next_var st)); tl];
                    [neg_lit sel; Z.pos (bs_next_var st); neg_lit tl];
                    [sel; neg_lit (Z.pos (bs_next_var st)); fl];
                    [sel; Z.pos (bs_next_var st); neg_lit fl]]
                   (snd (alloc_var st)))) = true).
  { unfold add_clauses; cbn [alloc_var snd bs_next_cid bs_cnf].
    rewrite Happ; cbn [bs_cnf]; rewrite eval_cnf_app, Hst, Hnew; reflexivity. }
  destruct (add_clauses_sat_split assign _ _ Hcls) as [_ Hin].
  pose proof (Hin _ (or_introl eq_refl)) as C1.
  pose proof (Hin _ (or_intror (or_introl eq_refl))) as C2.
  pose proof (Hin _ (or_intror (or_intror (or_introl eq_refl)))) as C3.
  pose proof (Hin _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as C4.
  cbn [eval_clause existsb] in C1, C2, C3, C4.
  rewrite (eval_neg_lit_nonzero assign sel Hsel) in C1, C2.
  rewrite (eval_neg_lit_nonzero assign tl Htl) in C2.
  rewrite (eval_neg_lit_nonzero assign fl Hfl) in C4.
  cbn [neg_lit eval_lit] in C1, C2, C3, C4.
  split; [exact Hst |].
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
  - unfold blast_const_rail; cbn; rewrite map_length, seq_length; reflexivity.
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
    rewrite (nth_indep _ false
               ((fun x => eval_lit assign (if Z.testbit (Z.of_N val) (Z.of_nat x)
                                           then lit_true else lit_false)) 0%nat))
      by (rewrite map_length, seq_length; exact Hlt).
    rewrite map_nth, seq_nth by exact Hlt.
    cbn [Nat.add]; rewrite Z2Nat.id by lia.
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
  (xs ys : list lit) (st : blast_state) : list lit * blast_state :=
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
  - inversion Hm; subst; exists []; apply app_nil_r.
  - inversion Hm; subst; exists []; apply app_nil_r.
  - inversion Hm; subst; exists []; apply app_nil_r.
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
      * apply Hzr_ev; [cbn in Hk; lia | exact Hsat].
Qed.

Lemma emit_and2_pref : forall x y st z st1,
  emit_and2 x y st = (z, st1) -> exists d, bs_cnf st1 = bs_cnf st ++ d.
Proof.
  intros x y st z st1 H; unfold emit_and2 in H; cbn in H.
  destruct (append_clauses _ _) as [cid' new_cnf]; inversion H; subst; cbn.
  exists new_cnf; reflexivity.
Qed.

Lemma emit_or2_pref : forall x y st z st1,
  emit_or2 x y st = (z, st1) -> exists d, bs_cnf st1 = bs_cnf st ++ d.
Proof.
  intros x y st z st1 H; unfold emit_or2 in H; cbn in H.
  destruct (append_clauses _ _) as [cid' new_cnf]; inversion H; subst; cbn.
  exists new_cnf; reflexivity.
Qed.

Lemma emit_xor2_pref : forall x y st z st1,
  emit_xor2 x y st = (z, st1) -> exists d, bs_cnf st1 = bs_cnf st ++ d.
Proof.
  intros x y st z st1 H; unfold emit_xor2 in H; cbn in H.
  destruct (append_clauses _ _) as [cid' new_cnf]; inversion H; subst; cbn.
  exists new_cnf; reflexivity.
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

Fixpoint emit_or_list (ls : list lit) (st : blast_state) : lit * blast_state :=
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
  induction ls as [| x [| y r] IH]; intros st out st' H; cbn in H.
  - inversion H; subst; exists []; apply app_nil_r.
  - inversion H; subst; exists []; apply app_nil_r.
  - destruct (emit_or_list (y :: r) st) as [sub st1] eqn:Hs.
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
  - cbn [emit_or_list] in Hemit.
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
  : list lit * blast_state :=
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

Fixpoint alloc_fresh_bits (n : nat) (st : blast_state) : list lit * blast_state :=
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
  induction ts as [| t rt IH]; intros [| f rf] st ms st' H; cbn in H.
  - inversion H; subst; exists []; apply app_nil_r.
  - inversion H; subst; exists []; apply app_nil_r.
  - inversion H; subst; exists []; apply app_nil_r.
  - destruct (emit_mux2 sel t f st) as [m st1] eqn:Hm.
    destruct (mux_bits_list sel rt rf st1) as [mr st2] eqn:Hmr.
    inversion H; subst; clear H.
    assert (Hd1 : exists d1, bs_cnf st1 = bs_cnf st ++ d1).
    { unfold emit_mux2 in Hm; cbn in Hm.
      destruct (append_clauses _ _) as [cid' new_cnf]; inversion Hm; subst; cbn.
      exists new_cnf; reflexivity. }
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
    try discriminate; cbn in Hm.
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
  induction n as [| n' IH]; intros st vs st' H; cbn in H.
  - inversion H; subst; repeat split; constructor.
  - destruct (alloc_fresh_bits n' (snd (alloc_var st))) as [vr st2] eqn:Hr.
    inversion H; subst; clear H.
    destruct (IH _ vr st' Hr) as (Hcnf & Hlen & Hwf).
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
      by (apply nth_In; rewrite map_length, Hlx; exact Hk).
    apply in_map_iff in Hin_map as [z [Hz_eq Hz_in]].
    rewrite <- Hz_eq; exact (Hall z Hz_in). }
  rewrite Hxor_k_false in Hxk; symmetry in Hxk.
  apply xorb_false_iff in Hxk; symmetry; exact Hxk.
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
  intros sz src_no_ub src_r tgt_r st pf assign Hnub
         ([Hws Hls] & Hwfs & Hps) ([Hwt Hlt] & Hwft & Hpt)
         Hunsat Hlf Hgates Hno_ub Hsrc_def.
  pose proof (check_lrat_unsat_sound _ _ Hunsat assign) as Hquery_false.
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
