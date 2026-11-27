(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Positive-Indexed Trie, [LRAT] Checker & Bounded DPLL ([CertValidator.LratCore])

    Purpose:
      Defines a self-contained, extraction-ready SAT core over [Z]-indexed CNF
      clauses: an $O(\log N)$ positive-index trie ([pos_trie]), a linear [LRAT]
      UNSAT checker ([check_lrat_unsat]), and bounded DPLL ([solve_cnf_unsat]).

    Trust Contract & Fail-Closed Boundary:
      Fail-closed boolean checkers ([check_lrat_unsat_sound],
      [solve_cnf_unsat_sound]); [true] guarantees [eval_cnf assign f = false] for
      all assignments, while invalid hints or exhausted fuel return [false].

    Assumptions:
      Stdlib-only ([ZArith], [NArith], [PArith], [List], [Bool], [Lia]); zero
      Vellvm dependencies and zero custom axioms.

    Section Outline:
      Prelude ([length_tr]); 1. Positive-Indexed Binary Trie ([PosTrie]); 2. CNF
      Syntax & Verified [LRAT] UNSAT Checker; 5. Verified Bounded DPLL Solver. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  List
  Bool
  Lia.
Import ListNotations.

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

Fixpoint length_tr_acc {A : Type} (acc : nat) (xs : list A) {struct xs} : nat :=
  match xs with
  | [] => acc
  | _ :: rest => length_tr_acc (S acc) rest
  end.

Definition length_tr {A : Type} (xs : list A) : nat :=
  length_tr_acc O xs.

Lemma length_tr_acc_eq : forall {A : Type} (acc : nat) (xs : list A),
  length_tr_acc acc xs = (acc + List.length xs)%nat.
Proof.
  intros A acc xs; revert acc; induction xs as [| x rest IH]; intro acc; cbn;
    [lia | rewrite IH; lia].
Qed.

Lemma length_tr_eq : forall {A : Type} (xs : list A),
  length_tr xs = List.length xs.
Proof.
  intros A xs; unfold length_tr; rewrite length_tr_acc_eq; reflexivity.
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

Fixpoint unassigned_count_clause_acc (trail : pos_trie bool) (acc : nat) (cl : clause)
  {struct cl} : nat :=
  match cl with
  | [] => acc
  | l :: rest =>
      match lit_status trail l with
      | None => unassigned_count_clause_acc trail (S acc) rest
      | Some _ => unassigned_count_clause_acc trail acc rest
      end
  end.

Definition unassigned_count_clause (trail : pos_trie bool) (cl : clause) : nat :=
  unassigned_count_clause_acc trail O cl.

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

Fixpoint dpll_worklist (fuel : nat) (stack : list (pos_trie bool * cnf))
  {struct fuel} : bool :=
  match stack with
  | [] => true
  | (trail, f) :: rest =>
      match fuel with
      | O => false
      | S fuel' =>
          match bcp_loop (S (length_tr f)) trail f with
          | BCP_LoopConflict => dpll_worklist fuel' rest
          | BCP_LoopOpen trail1 active =>
              match pick_branch_var trail1 None active with
              | None => false
              | Some v =>
                  dpll_worklist fuel'
                    ((pt_set v true trail1, active) ::
                     (pt_set v false trail1, active) :: rest)
              end
          end
      end
  end.

Lemma dpll_worklist_sound : forall fuel assign stack,
  dpll_worklist fuel stack = true ->
  (exists trail f, In (trail, f) stack /\ trail_sound assign trail /\ eval_cnf assign f = true) ->
  False.
Proof.
  induction fuel as [| fuel' IH]; intros assign stack Hdpll (trail & f & Hin & Htr & Hf).
  - destruct stack as [| [tr0 f0] rest]; [exact Hin | discriminate Hdpll].
  - destruct stack as [| [tr0 f0] rest]; [exact Hin |].
    cbn [dpll_worklist] in Hdpll.
    destruct Hin as [Heq | Hin_rest].
    + inversion Heq; subst tr0 f0; clear Heq.
      pose proof (bcp_loop_sound assign (S (length_tr f)) trail f Htr Hf) as Hbl.
      destruct (bcp_loop (S (length_tr f)) trail f) as [| trail1 active]; [exact Hbl |].
      destruct Hbl as [Htr1 Hact].
      destruct (pick_branch_var trail1 None active) as [v |]; [| discriminate Hdpll].
      destruct (assign v) eqn:Hv.
      * apply (IH assign _ Hdpll).
        exists (pt_set v true trail1), active.
        split; [left; reflexivity | split; [exact (trail_sound_set assign trail1 v true Htr1 Hv) | exact Hact]].
      * apply (IH assign _ Hdpll).
        exists (pt_set v false trail1), active.
        split; [right; left; reflexivity | split; [exact (trail_sound_set assign trail1 v false Htr1 Hv) | exact Hact]].
    + destruct (bcp_loop (S (length_tr f0)) tr0 f0) as [| trail1 active].
      * apply (IH assign rest Hdpll).
        exists trail, f; exact (conj Hin_rest (conj Htr Hf)).
      * destruct (pick_branch_var trail1 None active) as [v |]; [| discriminate Hdpll].
        apply (IH assign _ Hdpll).
        exists trail, f; split; [right; right; exact Hin_rest | exact (conj Htr Hf)].
Qed.

Definition dpll_unsat (fuel : nat) (trail : pos_trie bool) (f : cnf) : bool :=
  dpll_worklist fuel [(trail, f)].

Lemma dpll_unsat_sound : forall fuel assign trail f,
  dpll_unsat fuel trail f = true ->
  trail_sound assign trail ->
  eval_cnf assign f = true ->
  False.
Proof.
  intros fuel assign trail f Hdpll Htr Hf.
  apply (dpll_worklist_sound fuel assign [(trail, f)] Hdpll).
  exists trail, f; split; [left; reflexivity | exact (conj Htr Hf)].
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

