(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Shared Granular Diagnostic Combinators & Formatters ([CertValidator.common.Diag])

    Purpose:
      Provides standardized [[<gate-tag>]] diagnostic construction, lazy error
      combinators over [sum string _], stack-safe $O(\log n)$ decimal/hex
      numeric formatters, and unique-match lookup distinguishing missing vs.
      duplicate entries across [CertValidator].

    Trust Contract & Fail-Closed Boundary:
      Refines only error ([inl msg]) reporting. Success ([inr x]) results carry
      algebraic specs ([guard_err_inr], [opt_to_err_inr], [bind_err_inr],
      [find_unique_diag_spec]), while [unit -> string] thunks avoid allocation.

    Assumptions:
      Stdlib-only plus [CertValidator.common.Options]; zero Vellvm dependencies
      and zero custom axioms.

    Section Outline:
      1. Tagged Diagnostic Builders & Lazy Combinators; 2. Stack-Safe Numeric
      Formatters; 3. Unique-Match Lookup ([unique_match], [find_unique_diag]). *)

From CertValidator.common Require Import Options.

From Stdlib Require Import
  Ascii
  String
  List
  NArith
  ZArith
  PArith
  PeanoNat
  Bool.
Import ListNotations.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** 1. Tagged Diagnostic Builders & Lazy Combinators *)

Definition diag (tag msg : string) : string :=
  "[" ++ tag ++ "] " ++ msg.

#[global] Arguments diag _ _ : simpl never.

Definition guard_err (b : bool) (mk_msg : unit -> string) : string + unit :=
  if b then inr tt else inl (mk_msg tt).

Lemma guard_err_inr : forall b mk_msg,
  guard_err b mk_msg = inr tt -> b = true.
Proof.
  intros [] mk_msg H; [reflexivity | discriminate H].
Qed.

Definition opt_to_err {A : Type} (o : option A) (mk_msg : unit -> string) : string + A :=
  match o with
  | Some x => inr x
  | None => inl (mk_msg tt)
  end.

Lemma opt_to_err_inr : forall {A : Type} (o : option A) mk_msg x,
  opt_to_err o mk_msg = inr x -> o = Some x.
Proof.
  intros A [y |] mk_msg x H; [inversion H; reflexivity | discriminate H].
Qed.

Definition bind_err {A B : Type} (r : string + A) (k : A -> string + B) : string + B :=
  match r with
  | inl err => inl err
  | inr x => k x
  end.

Lemma bind_err_inr : forall {A B : Type} (r : string + A) (k : A -> string + B) y,
  bind_err r k = inr y ->
  exists x, r = inr x /\ k x = inr y.
Proof.
  intros A B [err | x] k y H; [discriminate H | exists x; exact (conj eq_refl H)].
Qed.

Definition sum_ok_b {A : Type} (r : string + A) : bool :=
  match r with
  | inr _ => true
  | inl _ => false
  end.

Lemma sum_ok_b_true : forall {A : Type} (r : string + A),
  sum_ok_b r = true -> exists x, r = inr x.
Proof.
  intros A [err | x] H; [discriminate H | exists x; reflexivity].
Qed.

(** ** 2. Stack-Safe $O(\log n)$ Numeric Diagnostic Formatters *)

Fixpoint diag_rev_chars_to_string (acc : list ascii) (s : string) {struct acc} : string :=
  match acc with
  | [] => s
  | c :: rest => diag_rev_chars_to_string rest (String c s)
  end.

Definition diag_chars_to_string (cs : list ascii) : string :=
  diag_rev_chars_to_string (List.rev_append cs []) EmptyString.

Definition diag_dec_digit (d : N) : ascii :=
  Ascii.ascii_of_N (48%N + d).

Definition diag_hex_digit (d : N) : ascii :=
  if N.ltb d 10%N then Ascii.ascii_of_N (48%N + d)
  else Ascii.ascii_of_N (87%N + d).

Fixpoint diag_N_dec_acc (fuel : nat) (n : N) (acc : list ascii) {struct fuel} : list ascii :=
  if N.eqb n 0%N then acc
  else
    match fuel with
    | O => acc
    | S fuel' =>
        diag_N_dec_acc fuel' (N.div n 10%N) (diag_dec_digit (N.modulo n 10%N) :: acc)
    end.

Definition diag_N_dec (n : N) : string :=
  if N.eqb n 0%N then "0"
  else diag_chars_to_string (diag_N_dec_acc (S (N.size_nat n)) n []).

Fixpoint diag_N_hex_acc (fuel : nat) (n : N) (acc : list ascii) {struct fuel} : list ascii :=
  if N.eqb n 0%N then acc
  else
    match fuel with
    | O => acc
    | S fuel' =>
        diag_N_hex_acc fuel' (N.div n 16%N) (diag_hex_digit (N.modulo n 16%N) :: acc)
    end.

Definition diag_N_hex (n : N) : string :=
  "0x" ++
  (if N.eqb n 0%N then "0"
   else diag_chars_to_string (diag_N_hex_acc (S (N.size_nat n)) n [])).

Definition diag_pos_dec (p : positive) : string :=
  diag_N_dec (N.pos p).

Definition diag_Z_dec (z : Z) : string :=
  match z with
  | Z0 => "0"
  | Zpos p => diag_pos_dec p
  | Zneg p => String "-"%char (diag_pos_dec p)
  end.

Definition diag_nat_dec (n : nat) : string :=
  diag_N_dec (N.of_nat n).

#[global] Arguments diag_N_dec _ : simpl never.
#[global] Arguments diag_N_hex _ : simpl never.
#[global] Arguments diag_pos_dec _ : simpl never.
#[global] Arguments diag_Z_dec _ : simpl never.
#[global] Arguments diag_nat_dec _ : simpl never.

(** ** 3. Unique-Match Lookup (Missing vs. Duplicate Diagnostics) *)

Variant unique_match (A : Type) : Type :=
| UM_Missing
| UM_Unique (x : A)
| UM_Duplicate (x1 x2 : A).

Arguments UM_Missing {A}.
Arguments UM_Unique {A} x.
Arguments UM_Duplicate {A} x1 x2.

Fixpoint find_unique_diag_acc {A : Type} (p : A -> bool) (found : option A) (xs : list A)
  {struct xs} : unique_match A :=
  match xs with
  | [] =>
      match found with
      | None => UM_Missing
      | Some x => UM_Unique x
      end
  | x :: rest =>
      if p x then
        match found with
        | None => find_unique_diag_acc p (Some x) rest
        | Some x1 => UM_Duplicate x1 x
        end
      else find_unique_diag_acc p found rest
  end.

Definition find_unique_diag {A : Type} (p : A -> bool) (xs : list A) : unique_match A :=
  find_unique_diag_acc p None xs.

Lemma find_unique_diag_acc_unique :
  forall {A : Type} (p : A -> bool) xs found res,
    find_unique_diag_acc p found xs = UM_Unique res ->
    (match found with Some f => f = res | None => In res xs /\ p res = true end) /\
    (forall y, In y xs -> p y = true -> y = res).
Proof.
  intros A p xs; induction xs as [| x rest IH]; intros [f |] res H;
    cbn [find_unique_diag_acc] in H.
  - inversion H; subst; split; [reflexivity | intros y []].
  - discriminate H.
  - destruct (p x) eqn:Epx; [discriminate H |].
    destruct (IH (Some f) res H) as [Hf Hrest].
    split; [exact Hf |].
    intros y [-> | Hy] Hpy; [rewrite Hpy in Epx; discriminate Epx | exact (Hrest y Hy Hpy)].
  - destruct (p x) eqn:Epx.
    + destruct (IH (Some x) res H) as [Hx Hrest].
      subst res; split; [split; [left; reflexivity | exact Epx] |].
      intros y [-> | Hy] Hpy; [reflexivity | exact (Hrest y Hy Hpy)].
    + destruct (IH None res H) as [[Hin Hpr] Hrest].
      split; [split; [right; exact Hin | exact Hpr] |].
      intros y [-> | Hy] Hpy; [rewrite Hpy in Epx; discriminate Epx | exact (Hrest y Hy Hpy)].
Qed.

Lemma find_unique_diag_spec :
  forall {A : Type} (p : A -> bool) xs res,
    find_unique_diag p xs = UM_Unique res ->
    In res xs /\ p res = true /\ (forall y, In y xs -> p y = true -> y = res).
Proof.
  intros A p xs res H; unfold find_unique_diag in H.
  destruct (find_unique_diag_acc_unique p xs None res H) as [[Hin Hpr] Huniq].
  exact (conj Hin (conj Hpr Huniq)).
Qed.
