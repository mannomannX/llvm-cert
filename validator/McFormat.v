(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Canonical [mc-cert-v1] Certificate AST & Total S-Expression Parser ([CertValidator.McFormat])

    Purpose:
      Defines the canonical [mc_certificate] AST, decidable and diagnostic well-formedness
      checkers ([wf_mc_cert]), stack-safe [mc_string_to_bytes], and total bounded-depth
      S-expression parser ([parse_mc_cert]) backed by [parse_mc_cert_wf].

    Trust Contract & Fail-Closed Boundary:
      [parse_mc_cert] fails closed ([inl err]) on malformed S-expressions, wrong schema tag,
      unsupported architectures/widths, duplicate bindings, or invalid loop/call specs; every
      [inr c] satisfies [wf_mc_cert c = true] by [parse_mc_cert_wf]. Extracted via [Extract.v].

    Assumptions:
      [Stdlib], [CertValidator.common.{Options,Diag}], and [CertValidator.{AigLrat,CertFormat,
      AlgRules,Elf64Spec,McFrameMem,McIsaCommon}]; zero custom axioms.

    Section Outline:
      1. Tail-recursive byte/map helpers; 2. [mc_certificate] AST & [wf_mc_cert]; 2b. Diagnostic
      well-formedness checkers & bridge proofs; 3. S-expression parser ([parse_mc_cert]). *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.Ascii
  Strings.String
  List
  Bool
  Lia.
Import ListNotations.

From CertValidator.common Require Import
  Options
  Diag.

From CertValidator Require Import
  AigLrat
  CertFormat
  AlgRules
  Elf64Spec
  McFrameMem
  McIsaCommon.

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
#[local] Arguments Nat.eqb _ _ : simpl nomatch.
#[local] Arguments Nat.leb _ _ : simpl nomatch.
#[local] Arguments String.eqb _ _ : simpl nomatch.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** 1. Stack-Safe Tail-Recursive String-to-Bytes Conversion *)

Fixpoint mc_string_to_bytes_acc (acc : list N) (s : string) {struct s} : list N :=
  match s with
  | EmptyString => List.rev_append acc []
  | String c rest => mc_string_to_bytes_acc (Ascii.N_of_ascii c :: acc) rest
  end.

Definition mc_string_to_bytes (s : string) : list N :=
  mc_string_to_bytes_acc [] s.

Lemma mc_string_to_bytes_acc_spec : forall s acc,
  mc_string_to_bytes_acc acc s = List.rev_append acc (string_to_bytes s).
Proof.
  induction s as [| c rest IH]; intros acc; cbn [mc_string_to_bytes_acc].
  - rewrite string_to_bytes_nil; reflexivity.
  - rewrite string_to_bytes_cons, (IH (Ascii.N_of_ascii c :: acc)); reflexivity.
Qed.

Lemma mc_string_to_bytes_eq : forall s,
  mc_string_to_bytes s = string_to_bytes s.
Proof.
  intros s; unfold mc_string_to_bytes; exact (mc_string_to_bytes_acc_spec s []).
Qed.

Fixpoint mc_map_tr_acc {A B : Type} (f : A -> B) (acc : list B) (xs : list A) {struct xs} : list B :=
  match xs with
  | [] => List.rev_append acc []
  | x :: rest => mc_map_tr_acc f (f x :: acc) rest
  end.

Definition mc_map_tr {A B : Type} (f : A -> B) (xs : list A) : list B :=
  mc_map_tr_acc f [] xs.

Lemma mc_map_tr_acc_eq : forall {A B : Type} (f : A -> B) (acc : list B) (xs : list A),
  mc_map_tr_acc f acc xs = List.rev_append acc (List.map f xs).
Proof.
  intros A B f acc xs; revert acc; induction xs as [| x rest IH]; intros acc;
    cbn [mc_map_tr_acc List.map]; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma mc_map_tr_eq : forall {A B : Type} (f : A -> B) (xs : list A),
  mc_map_tr f xs = List.map f xs.
Proof.
  intros A B f xs; unfold mc_map_tr; exact (mc_map_tr_acc_eq f [] xs).
Qed.

(** ** 2. Canonical [mc-cert-v1] AST & Well-Formedness *)

Record mc_loop_reg_bind : Set := mk_mc_loop_reg_bind {
  mlr_reg : N;
  mlr_width : positive;
  mlr_expr : cert_expr;
}.

Variant mc_loop_slot_bind : Set :=
| MLS_Expr (off : Z) (sz : mc_mem_size) (e : cert_expr)
| MLS_SavedReg (off : Z) (r : N).

Record mc_loop_spec : Set := mk_mc_loop_spec {
  ml_ir_header : string;
  ml_mc_pc : N;
  ml_sp_off : Z;
  ml_regs : list mc_loop_reg_bind;
  ml_slots : list mc_loop_slot_bind;
  ml_inv : option cert_expr;
}.

Record mc_callee_spec : Set := mk_mc_callee_spec {
  mcs_name : string;
  mcs_ret_width : positive;
  mcs_ret_ext : rv_arg_ext;
  mcs_args : list rv_arg_spec;
}.

Record mc_certificate : Set := mk_mc_certificate {
  mc_arch : elf_arch;
  mc_elf_kind : elf_kind;
  mc_fn_name : string;
  mc_rvc : bool;
  mc_ret_width : positive;
  mc_args : list rv_arg_spec;
  mc_calls : list mc_callee_spec;
  mc_loop : option mc_loop_spec;
  mc_lrat_proof : option (list lrat_step);
}.

Definition mc_strip_leading_at (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => if Ascii.eqb c "@"%char then rest else s
  end.

Definition mc_format_starts_with_bang (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c _ => Ascii.eqb c "!"%char
  end.

Definition mc_str_in_list (s : string) (xs : list string) : bool :=
  existsb (String.eqb s) xs.

Fixpoint mc_no_dup_strings (xs : list string) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (mc_str_in_list x rest) && mc_no_dup_strings rest
  end.

Definition n_in_list_bool (x : N) (xs : list N) : bool :=
  existsb (N.eqb x) xs.

Fixpoint no_dup_N (xs : list N) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (n_in_list_bool x rest) && no_dup_N rest
  end.

Definition mc_loop_reg_valid (arch : elf_arch) (r : N) : bool :=
  match arch with
  | EA_Riscv64 => (1 <=? r)%N && (r <=? 31)%N && negb (N.eqb r 2%N)
  | EA_AArch64 => (r <=? 30)%N
  end.

Definition mc_loop_saved_reg_valid (arch : elf_arch) (r : N) : bool :=
  match arch with
  | EA_Riscv64 => N.eqb r 1%N || ((8 <=? r)%N && (r <=? 9)%N) || ((18 <=? r)%N && (r <=? 27)%N)
  | EA_AArch64 => (19 <=? r)%N && (r <=? 30)%N
  end.

Definition wf_mc_loop_reg_bind (arch : elf_arch) (rb : mc_loop_reg_bind) : bool :=
  mc_loop_reg_valid arch (mlr_reg rb) &&
  (Pos.eqb (mlr_width rb) 32%positive || Pos.eqb (mlr_width rb) 64%positive) &&
  wt_cert_expr [] (mlr_expr rb) &&
  Pos.eqb (cert_expr_bit_width (mlr_expr rb)) (mlr_width rb) &&
  is_let_free_expr (mlr_expr rb) &&
  ub_free_expr (mlr_expr rb).

Definition wf_mc_loop_slot_bind (arch : elf_arch) (sp_off : Z) (sb : mc_loop_slot_bind) : bool :=
  match sb with
  | MLS_Expr off sz e =>
      mc_slot_in_frame sp_off off sz &&
      wt_cert_expr [] e &&
      Pos.eqb (cert_expr_bit_width e) (mc_mem_bits sz) &&
      is_let_free_expr e &&
      ub_free_expr e
  | MLS_SavedReg off r =>
      mc_slot_in_frame sp_off off MS_8 &&
      mc_loop_saved_reg_valid arch r
  end.

Definition mc_loop_slot_interval (sb : mc_loop_slot_bind) : Z * mc_mem_size :=
  match sb with
  | MLS_Expr off sz _ => (off, sz)
  | MLS_SavedReg off _ => (off, MS_8)
  end.

Definition mc_intervals_disjoint (p1 p2 : Z * mc_mem_size) : bool :=
  let '(o1, s1) := p1 in
  let '(o2, s2) := p2 in
  Z.leb (o1 + mc_mem_bytes_Z s1)%Z o2 || Z.leb (o2 + mc_mem_bytes_Z s2)%Z o1.

Fixpoint mc_intervals_pairwise_disjoint (ps : list (Z * mc_mem_size)) : bool :=
  match ps with
  | [] => true
  | p :: rest => forallb (mc_intervals_disjoint p) rest && mc_intervals_pairwise_disjoint rest
  end.

Definition wf_mc_loop_spec (arch : elf_arch) (ls : mc_loop_spec) : bool :=
  negb (String.eqb (ml_ir_header ls) "") &&
  mc_sp_aligned16 (ml_sp_off ls) &&
  match arch with
  | EA_Riscv64 => N.eqb (N.modulo (ml_mc_pc ls) 2%N) 0%N
  | EA_AArch64 => N.eqb (N.modulo (ml_mc_pc ls) 4%N) 0%N
  end &&
  no_dup_N (mc_map_tr mlr_reg (ml_regs ls)) &&
  forallb (wf_mc_loop_reg_bind arch) (ml_regs ls) &&
  forallb (wf_mc_loop_slot_bind arch (ml_sp_off ls)) (ml_slots ls) &&
  mc_intervals_pairwise_disjoint (mc_map_tr mc_loop_slot_interval (ml_slots ls)) &&
  match ml_inv ls with
  | None => true
  | Some inv =>
      wt_cert_expr [] inv &&
      Pos.eqb (cert_expr_bit_width inv) 1%positive &&
      is_let_free_expr inv &&
      ub_free_expr inv
  end.

Definition wf_mc_callee_spec (c : mc_callee_spec) : bool :=
  negb (String.eqb (mc_strip_leading_at (mcs_name c)) "") &&
  rv_supported_arg_width (mcs_ret_width c) &&
  Nat.leb (List.length (mcs_args c)) 8 &&
  forallb rv_valid_arg_spec (mcs_args c) &&
  forallb (fun sp => negb (mc_format_starts_with_bang (ras_name sp))) (mcs_args c) &&
  mc_no_dup_strings (mc_map_tr ras_name (mcs_args c)).

Definition wf_mc_calls (fn_name : string) (cs : list mc_callee_spec) : bool :=
  let fn_bare := mc_strip_leading_at fn_name in
  forallb wf_mc_callee_spec cs &&
  forallb (fun c => negb (String.eqb (mc_strip_leading_at (mcs_name c)) fn_bare)) cs &&
  mc_no_dup_strings (mc_map_tr (fun c => mc_strip_leading_at (mcs_name c)) cs).

Definition wf_mc_cert (c : mc_certificate) : bool :=
  negb (String.eqb (mc_fn_name c) "") &&
  rv_supported_arg_width (mc_ret_width c) &&
  Nat.leb (List.length (mc_args c)) 8 &&
  forallb rv_valid_arg_spec (mc_args c) &&
  wf_mc_calls (mc_fn_name c) (mc_calls c) &&
  match mc_loop c with
  | None => true
  | Some ls => wf_mc_loop_spec (mc_arch c) ls
  end &&
  match mc_lrat_proof c with
  | None => true
  | Some [] => false
  | Some (_ :: _) => true
  end.

(** ** 2b. Granular Well-Formedness Diagnostic Checkers & Bridge Proofs *)

Fixpoint check_forall_idx_diag_acc {A : Type}
  (chk : nat -> A -> string + unit) (idx : nat) (xs : list A) {struct xs} : string + unit :=
  match xs with
  | [] => inr tt
  | x :: rest =>
      match chk idx x with
      | inl err => inl err
      | inr tt => check_forall_idx_diag_acc chk (S idx) rest
      end
  end.

Lemma check_forall_idx_diag_acc_sound :
  forall {A : Type} (chk : nat -> A -> string + unit) (p : A -> bool) idx xs,
    (forall i x, chk i x = inr tt -> p x = true) ->
    check_forall_idx_diag_acc chk idx xs = inr tt ->
    forallb p xs = true.
Proof.
  intros A chk p idx xs Hchk; revert idx.
  induction xs as [| x rest IH]; intros idx H; cbn in *.
  - reflexivity.
  - destruct (chk idx x) as [err | []] eqn:Hx; [discriminate H |].
    apply Hchk in Hx.
    rewrite Hx; cbn.
    exact (IH (S idx) H).
Qed.

Fixpoint check_no_dup_by_diag {A : Type}
  (in_list : A -> list A -> bool) (fmt : A -> string)
  (tag msg_pfx : string) (xs : list A) {struct xs} : string + unit :=
  match xs with
  | [] => inr tt
  | x :: rest =>
      if in_list x rest then
        inl (diag tag (msg_pfx ++ " '" ++ fmt x ++ "'"))
      else check_no_dup_by_diag in_list fmt tag msg_pfx rest
  end.

Lemma check_no_dup_N_diag_sound : forall tag msg_pfx xs,
  check_no_dup_by_diag n_in_list_bool diag_N_dec tag msg_pfx xs = inr tt ->
  no_dup_N xs = true.
Proof.
  intros tag msg_pfx xs H.
  induction xs as [| x rest IH]; cbn in *; [reflexivity |].
  destruct (n_in_list_bool x rest) eqn:Hin; [discriminate H |].
  cbn; exact (IH H).
Qed.

Lemma check_mc_no_dup_strings_diag_sound : forall tag msg_pfx xs,
  check_no_dup_by_diag mc_str_in_list (fun s => s) tag msg_pfx xs = inr tt ->
  mc_no_dup_strings xs = true.
Proof.
  intros tag msg_pfx xs H.
  induction xs as [| x rest IH]; cbn in *; [reflexivity |].
  destruct (mc_str_in_list x rest) eqn:Hin; [discriminate H |].
  cbn; exact (IH H).
Qed.

Fixpoint check_interval_against_rest_diag
  (p : Z * mc_mem_size) (rest : list (Z * mc_mem_size)) {struct rest} : string + unit :=
  match rest with
  | [] => inr tt
  | q :: tl =>
      if mc_intervals_disjoint p q then
        check_interval_against_rest_diag p tl
      else
        let '(o1, s1) := p in
        let '(o2, s2) := q in
        inl (diag "mc-cert-loop"
          ("overlapping loop stack slots: [" ++ diag_Z_dec o1 ++ ", +" ++
           diag_Z_dec (mc_mem_bytes_Z s1) ++ ") and [" ++ diag_Z_dec o2 ++ ", +" ++
           diag_Z_dec (mc_mem_bytes_Z s2) ++ ")"))
  end.

Lemma check_interval_against_rest_diag_sound : forall p rest,
  check_interval_against_rest_diag p rest = inr tt ->
  forallb (mc_intervals_disjoint p) rest = true.
Proof.
  intros p rest; induction rest as [| q tl IH]; intro H; cbn in *; [reflexivity |].
  destruct (mc_intervals_disjoint p q) eqn:Hd;
    [cbn; exact (IH H) | destruct p as [o1 s1], q as [o2 s2]; discriminate H].
Qed.

Fixpoint check_intervals_disjoint_diag (ps : list (Z * mc_mem_size)) {struct ps} : string + unit :=
  match ps with
  | [] => inr tt
  | p :: rest =>
      bind_err (check_interval_against_rest_diag p rest) (fun _ =>
      check_intervals_disjoint_diag rest)
  end.

Lemma check_intervals_disjoint_diag_sound : forall ps,
  check_intervals_disjoint_diag ps = inr tt ->
  mc_intervals_pairwise_disjoint ps = true.
Proof.
  intro ps; induction ps as [| p rest IH]; intro H; cbn in *; [reflexivity |].
  destruct (check_interval_against_rest_diag p rest) as [err | []] eqn:Hp; [discriminate H |].
  cbn in H.
  rewrite (check_interval_against_rest_diag_sound _ _ Hp), (IH H); reflexivity.
Qed.

Definition check_mc_loop_reg_bind_diag
  (arch : elf_arch) (idx : nat) (rb : mc_loop_reg_bind) : string + unit :=
  let pfx : string :=
    ("loop reg #" ++ diag_nat_dec idx ++ " (x" ++ diag_N_dec (mlr_reg rb) ++ "): ")%string in
  bind_err
    (guard_err (mc_loop_reg_valid arch (mlr_reg rb))
      (fun _ => diag "mc-cert-loop"
        (pfx ++ "invalid register index for " ++ elf_arch_name arch)))
    (fun _ =>
  bind_err
    (guard_err (Pos.eqb (mlr_width rb) 32%positive || Pos.eqb (mlr_width rb) 64%positive)
      (fun _ => diag "mc-cert-loop"
        (pfx ++ "unsupported width " ++ diag_pos_dec (mlr_width rb) ++ " (expected 32 or 64)")))
    (fun _ =>
  bind_err
    (guard_err (wt_cert_expr [] (mlr_expr rb))
      (fun _ => diag "mc-cert-loop" (pfx ++ "expression failed well-typedness check")))
    (fun _ =>
  bind_err
    (guard_err (Pos.eqb (cert_expr_bit_width (mlr_expr rb)) (mlr_width rb))
      (fun _ => diag "mc-cert-loop"
        (pfx ++ "expression bit width " ++ diag_pos_dec (cert_expr_bit_width (mlr_expr rb)) ++
         " does not match declared width " ++ diag_pos_dec (mlr_width rb))))
    (fun _ =>
  bind_err
    (guard_err (is_let_free_expr (mlr_expr rb))
      (fun _ => diag "mc-cert-loop" (pfx ++ "expression contains disallowed let bindings")))
    (fun _ =>
  guard_err (ub_free_expr (mlr_expr rb))
    (fun _ => diag "mc-cert-loop" (pfx ++ "expression failed UB-freedom check"))))))).

Lemma check_mc_loop_reg_bind_diag_sound : forall arch idx rb,
  check_mc_loop_reg_bind_diag arch idx rb = inr tt ->
  wf_mc_loop_reg_bind arch rb = true.
Proof.
  intros arch idx rb H.
  unfold check_mc_loop_reg_bind_diag in H; unfold wf_mc_loop_reg_bind.
  repeat (match type of H with
          | bind_err (guard_err ?c _) _ = inr tt =>
              destruct c; cbn [guard_err bind_err] in H; [| discriminate H]
          | guard_err ?c _ = inr tt =>
              destruct c; cbn [guard_err] in H; [| discriminate H]
          end).
  reflexivity.
Qed.

Definition check_mc_loop_slot_bind_diag
  (arch : elf_arch) (sp_off : Z) (idx : nat) (sb : mc_loop_slot_bind) : string + unit :=
  match sb with
  | MLS_Expr off sz e =>
      let pfx : string :=
        ("loop slot #" ++ diag_nat_dec idx ++ " at offset " ++ diag_Z_dec off ++
         " (size " ++ diag_Z_dec (mc_mem_bytes_Z sz) ++ "): ")%string in
      bind_err
        (guard_err (mc_slot_in_frame sp_off off sz)
          (fun _ => diag "mc-cert-loop"
            (pfx ++ "out of frame bounds for sp-off " ++ diag_Z_dec sp_off)))
        (fun _ =>
      bind_err
        (guard_err (wt_cert_expr [] e)
          (fun _ => diag "mc-cert-loop" (pfx ++ "expression failed well-typedness check")))
        (fun _ =>
      bind_err
        (guard_err (Pos.eqb (cert_expr_bit_width e) (mc_mem_bits sz))
          (fun _ => diag "mc-cert-loop"
            (pfx ++ "expression bit width " ++ diag_pos_dec (cert_expr_bit_width e) ++
             " does not match slot width " ++ diag_pos_dec (mc_mem_bits sz))))
        (fun _ =>
      bind_err
        (guard_err (is_let_free_expr e)
          (fun _ => diag "mc-cert-loop" (pfx ++ "expression contains disallowed let bindings")))
        (fun _ =>
      guard_err (ub_free_expr e)
        (fun _ => diag "mc-cert-loop" (pfx ++ "expression failed UB-freedom check"))))))
  | MLS_SavedReg off r =>
      let pfx : string :=
        ("loop saved-reg #" ++ diag_nat_dec idx ++ " (x" ++ diag_N_dec r ++
         ") at offset " ++ diag_Z_dec off ++ ": ")%string in
      bind_err
        (guard_err (mc_slot_in_frame sp_off off MS_8)
          (fun _ => diag "mc-cert-loop"
            (pfx ++ "out of frame bounds for sp-off " ++ diag_Z_dec sp_off)))
        (fun _ =>
      guard_err (mc_loop_saved_reg_valid arch r)
        (fun _ => diag "mc-cert-loop"
          (pfx ++ "not a callee-saved register for " ++ elf_arch_name arch)))
  end.

Lemma check_mc_loop_slot_bind_diag_sound : forall arch sp_off idx sb,
  check_mc_loop_slot_bind_diag arch sp_off idx sb = inr tt ->
  wf_mc_loop_slot_bind arch sp_off sb = true.
Proof.
  intros arch sp_off idx [off sz e | off r] H;
    unfold check_mc_loop_slot_bind_diag in H; unfold wf_mc_loop_slot_bind;
    repeat (match type of H with
            | bind_err (guard_err ?c _) _ = inr tt =>
                destruct c; cbn [guard_err bind_err] in H; [| discriminate H]
            | guard_err ?c _ = inr tt =>
                destruct c; cbn [guard_err] in H; [| discriminate H]
            end);
    reflexivity.
Qed.

Definition check_mc_loop_inv_diag (opt_inv : option cert_expr) : string + unit :=
  match opt_inv with
  | None => inr tt
  | Some inv =>
      bind_err
        (guard_err (wt_cert_expr [] inv)
          (fun _ => diag "mc-cert-loop" "loop invariant failed well-typedness check"))
        (fun _ =>
      bind_err
        (guard_err (Pos.eqb (cert_expr_bit_width inv) 1%positive)
          (fun _ => diag "mc-cert-loop"
            ("loop invariant bit width is " ++ diag_pos_dec (cert_expr_bit_width inv) ++
             ", expected 1")))
        (fun _ =>
      bind_err
        (guard_err (is_let_free_expr inv)
          (fun _ => diag "mc-cert-loop" "loop invariant contains disallowed let bindings"))
        (fun _ =>
      guard_err (ub_free_expr inv)
        (fun _ => diag "mc-cert-loop" "loop invariant failed UB-freedom check"))))
  end.

Lemma check_mc_loop_inv_diag_sound : forall opt_inv,
  check_mc_loop_inv_diag opt_inv = inr tt ->
  (match opt_inv with
   | None => true
   | Some inv =>
       wt_cert_expr [] inv &&
       Pos.eqb (cert_expr_bit_width inv) 1%positive &&
       is_let_free_expr inv &&
       ub_free_expr inv
   end) = true.
Proof.
  intros [inv |] H; [| reflexivity].
  unfold check_mc_loop_inv_diag in H.
  repeat (match type of H with
          | bind_err (guard_err ?c _) _ = inr tt =>
              destruct c; cbn [guard_err bind_err] in H; [| discriminate H]
          | guard_err ?c _ = inr tt =>
              destruct c; cbn [guard_err] in H; [| discriminate H]
          end).
  reflexivity.
Qed.

Definition check_mc_loop_spec_diag (arch : elf_arch) (ls : mc_loop_spec) : string + unit :=
  let pc_align : N := match arch with EA_Riscv64 => 2%N | EA_AArch64 => 4%N end in
  bind_err
    (guard_err (negb (String.eqb (ml_ir_header ls) ""))
      (fun _ => diag "mc-cert-loop" "empty loop ir-header"))
    (fun _ =>
  bind_err
    (guard_err (mc_sp_aligned16 (ml_sp_off ls))
      (fun _ => diag "mc-cert-loop"
        ("loop sp-off is not 16-byte aligned: " ++ diag_Z_dec (ml_sp_off ls))))
    (fun _ =>
  bind_err
    (guard_err (N.eqb (N.modulo (ml_mc_pc ls) pc_align) 0%N)
      (fun _ => diag "mc-cert-loop"
        ("loop mc-pc " ++ diag_N_hex (ml_mc_pc ls) ++ " is not " ++
         diag_N_dec pc_align ++ "-byte aligned for " ++ elf_arch_name arch)))
    (fun _ =>
  bind_err
    (check_no_dup_by_diag n_in_list_bool diag_N_dec "mc-cert-loop"
      "duplicate loop binding for register x" (mc_map_tr mlr_reg (ml_regs ls)))
    (fun _ =>
  bind_err
    (check_forall_idx_diag_acc (check_mc_loop_reg_bind_diag arch) 0 (ml_regs ls))
    (fun _ =>
  bind_err
    (check_forall_idx_diag_acc (check_mc_loop_slot_bind_diag arch (ml_sp_off ls)) 0 (ml_slots ls))
    (fun _ =>
  bind_err
    (check_intervals_disjoint_diag (mc_map_tr mc_loop_slot_interval (ml_slots ls)))
    (fun _ => check_mc_loop_inv_diag (ml_inv ls)))))))).

Lemma check_mc_loop_spec_diag_sound : forall arch ls,
  check_mc_loop_spec_diag arch ls = inr tt ->
  wf_mc_loop_spec arch ls = true.
Proof.
  intros arch ls H.
  unfold check_mc_loop_spec_diag in H; unfold wf_mc_loop_spec.
  destruct (negb (String.eqb (ml_ir_header ls) "")) eqn:Hhdr;
    cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (mc_sp_aligned16 (ml_sp_off ls)) eqn:Hsp;
    cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (N.eqb (N.modulo (ml_mc_pc ls)
             match arch with EA_Riscv64 => 2%N | EA_AArch64 => 4%N end) 0%N) eqn:Hpc;
    cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (check_no_dup_by_diag n_in_list_bool diag_N_dec "mc-cert-loop"
             "duplicate loop binding for register x" (mc_map_tr mlr_reg (ml_regs ls)))
    as [err | []] eqn:Hnd; cbn [bind_err] in H; [discriminate H |].
  destruct (check_forall_idx_diag_acc (check_mc_loop_reg_bind_diag arch) 0 (ml_regs ls))
    as [err | []] eqn:Hregs; cbn [bind_err] in H; [discriminate H |].
  destruct (check_forall_idx_diag_acc (check_mc_loop_slot_bind_diag arch (ml_sp_off ls)) 0 (ml_slots ls))
    as [err | []] eqn:Hslots; cbn [bind_err] in H; [discriminate H |].
  destruct (check_intervals_disjoint_diag (mc_map_tr mc_loop_slot_interval (ml_slots ls)))
    as [err | []] eqn:Hdisj; cbn [bind_err] in H; [discriminate H |].
  rewrite (check_no_dup_N_diag_sound _ _ _ Hnd).
  rewrite (check_forall_idx_diag_acc_sound _ _ _ _ (check_mc_loop_reg_bind_diag_sound arch) Hregs).
  rewrite (check_forall_idx_diag_acc_sound _ _ _ _ (check_mc_loop_slot_bind_diag_sound arch (ml_sp_off ls)) Hslots).
  rewrite (check_intervals_disjoint_diag_sound _ Hdisj).
  rewrite (check_mc_loop_inv_diag_sound _ H).
  destruct arch; cbn in Hpc; cbn;
    rewrite Hpc, !Bool.andb_true_r; reflexivity.
Qed.

Definition check_mc_callee_arg_diag (cname : string) (idx : nat) (sp : rv_arg_spec) : string + unit :=
  bind_err
    (guard_err (rv_valid_arg_spec sp)
      (fun _ => diag "mc-cert-call"
        ("callee '" ++ cname ++ "' arg #" ++ diag_nat_dec idx ++ " ('" ++ ras_name sp ++
         "'): invalid width or disallowed '$' prefix")))
    (fun _ =>
  guard_err (negb (mc_format_starts_with_bang (ras_name sp)))
    (fun _ => diag "mc-cert-call"
      ("callee '" ++ cname ++ "' arg #" ++ diag_nat_dec idx ++ " ('" ++ ras_name sp ++
       "'): name cannot start with '!'"))).

Definition check_mc_callee_spec_diag (c : mc_callee_spec) : string + unit :=
  let cname := mc_strip_leading_at (mcs_name c) in
  bind_err
    (guard_err (negb (String.eqb cname ""))
      (fun _ => diag "mc-cert-call" "callee name cannot be empty"))
    (fun _ =>
  bind_err
    (guard_err (rv_supported_arg_width (mcs_ret_width c))
      (fun _ => diag "mc-cert-call"
        ("callee '" ++ cname ++ "': unsupported return width " ++
         diag_pos_dec (mcs_ret_width c))))
    (fun _ =>
  bind_err
    (guard_err (Nat.leb (List.length (mcs_args c)) 8)
      (fun _ => diag "mc-cert-call"
        ("callee '" ++ cname ++ "': too many arguments (" ++
         diag_nat_dec (List.length (mcs_args c)) ++ " > 8)")))
    (fun _ =>
  bind_err
    (check_forall_idx_diag_acc (check_mc_callee_arg_diag cname) 0 (mcs_args c))
    (fun _ =>
  check_no_dup_by_diag mc_str_in_list (fun s => s) "mc-cert-call"
    ("callee '" ++ cname ++ "': duplicate argument name") (mc_map_tr ras_name (mcs_args c)))))).

Lemma check_mc_callee_spec_diag_sound : forall c,
  check_mc_callee_spec_diag c = inr tt ->
  wf_mc_callee_spec c = true.
Proof.
  intros c H; unfold check_mc_callee_spec_diag in H; unfold wf_mc_callee_spec.
  destruct (negb (String.eqb (mc_strip_leading_at (mcs_name c)) "")) eqn:Hnm;
    cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (rv_supported_arg_width (mcs_ret_width c)) eqn:Hrw;
    cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (Nat.leb (List.length (mcs_args c)) 8) eqn:Hlen;
    cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (check_forall_idx_diag_acc (check_mc_callee_arg_diag (mc_strip_leading_at (mcs_name c))) 0 (mcs_args c))
    as [err | []] eqn:Hargs; cbn [bind_err] in H; [discriminate H |].
  assert (Hv : forallb rv_valid_arg_spec (mcs_args c) = true).
  { refine (check_forall_idx_diag_acc_sound _ _ _ _ _ Hargs).
    intros i sp Hsp; unfold check_mc_callee_arg_diag in Hsp.
    destruct (rv_valid_arg_spec sp); [reflexivity | discriminate Hsp]. }
  assert (Hb : forallb (fun sp => negb (mc_format_starts_with_bang (ras_name sp))) (mcs_args c) = true).
  { refine (check_forall_idx_diag_acc_sound _ _ _ _ _ Hargs).
    intros i sp Hsp; unfold check_mc_callee_arg_diag in Hsp.
    destruct (rv_valid_arg_spec sp); cbn [guard_err bind_err] in Hsp; [| discriminate Hsp].
    destruct (negb (mc_format_starts_with_bang (ras_name sp))); [reflexivity | discriminate Hsp]. }
  rewrite Hv, Hb, (check_mc_no_dup_strings_diag_sound _ _ _ H).
  reflexivity.
Qed.

Definition check_mc_calls_diag (fn_name : string) (cs : list mc_callee_spec) : string + unit :=
  let fn_bare := mc_strip_leading_at fn_name in
  bind_err
    (check_forall_idx_diag_acc (fun _ c => check_mc_callee_spec_diag c) 0 cs)
    (fun _ =>
  bind_err
    (check_forall_idx_diag_acc
      (fun idx c =>
        guard_err (negb (String.eqb (mc_strip_leading_at (mcs_name c)) fn_bare))
          (fun _ => diag "mc-cert-call"
            ("callee #" ++ diag_nat_dec idx ++ " ('" ++ mcs_name c ++
             "'): direct self-recursion into '" ++ fn_bare ++ "' is disallowed")))
      0 cs)
    (fun _ =>
  check_no_dup_by_diag mc_str_in_list (fun s => s) "mc-cert-call"
    "duplicate callee name" (mc_map_tr (fun c => mc_strip_leading_at (mcs_name c)) cs))).

Lemma check_mc_calls_diag_sound : forall fn_name cs,
  check_mc_calls_diag fn_name cs = inr tt ->
  wf_mc_calls fn_name cs = true.
Proof.
  intros fn_name cs H; unfold check_mc_calls_diag in H; unfold wf_mc_calls.
  destruct (check_forall_idx_diag_acc (fun _ c => check_mc_callee_spec_diag c) 0 cs)
    as [err | []] eqn:Hcs; cbn [bind_err] in H; [discriminate H |].
  destruct (check_forall_idx_diag_acc
             (fun idx c =>
               guard_err (negb (String.eqb (mc_strip_leading_at (mcs_name c))
                                           (mc_strip_leading_at fn_name)))
                 (fun _ => diag "mc-cert-call"
                   ("callee #" ++ diag_nat_dec idx ++ " ('" ++ mcs_name c ++
                    "'): direct self-recursion into '" ++ mc_strip_leading_at fn_name ++
                    "' is disallowed")))
             0 cs)
    as [err | []] eqn:Hself; cbn [bind_err] in H; [discriminate H |].
  assert (Hwf : forallb wf_mc_callee_spec cs = true).
  { refine (check_forall_idx_diag_acc_sound _ _ _ _ _ Hcs).
    intros _ c Hc; exact (check_mc_callee_spec_diag_sound _ Hc). }
  assert (Hnoself : forallb (fun c => negb (String.eqb (mc_strip_leading_at (mcs_name c))
                                                       (mc_strip_leading_at fn_name))) cs = true).
  { refine (check_forall_idx_diag_acc_sound _ _ _ _ _ Hself).
    intros i c Hc.
    destruct (negb (String.eqb (mc_strip_leading_at (mcs_name c)) (mc_strip_leading_at fn_name)));
      [reflexivity | discriminate Hc]. }
  rewrite Hwf, Hnoself, (check_mc_no_dup_strings_diag_sound _ _ _ H).
  reflexivity.
Qed.

(** ** 3. Total S-Expression Parser ([parse_mc_cert]) *)

Definition parse_mc_arch_sexp (sx : sexp) : string + elf_arch :=
  match sx with
  | SList [SAtom tag; SAtom a] =>
      if String.eqb tag "arch" then
        if String.eqb a "rv64" then inr EA_Riscv64
        else if String.eqb a "aarch64" then inr EA_AArch64
        else inl (diag "mc-cert-parse" ("unknown architecture '" ++ a ++ "' (expected 'rv64' or 'aarch64')"))
      else inl (diag "mc-cert-parse" ("expected 'arch' field in mc-cert-v1, got '" ++ tag ++ "'"))
  | _ => inl (diag "mc-cert-parse" "malformed 'arch' field in mc-cert-v1")
  end.

Definition parse_mc_elf_kind_sexp (sx : sexp) : string + elf_kind :=
  match sx with
  | SList [SAtom tag; SAtom k] =>
      if String.eqb tag "elf-kind" then
        if String.eqb k "rel" then inr EK_Rel
        else if String.eqb k "exec" then inr EK_Exec
        else if String.eqb k "dyn" then inr EK_Dyn
        else inl (diag "mc-cert-parse" ("unknown ELF kind '" ++ k ++ "' (expected 'rel', 'exec', or 'dyn')"))
      else inl (diag "mc-cert-parse" ("expected 'elf-kind' field in mc-cert-v1, got '" ++ tag ++ "'"))
  | _ => inl (diag "mc-cert-parse" "malformed 'elf-kind' field in mc-cert-v1")
  end.

Definition parse_mc_rvc_sexp (sx : sexp) : string + bool :=
  match sx with
  | SList [SAtom tag; flag_sx] =>
      if String.eqb tag "rvc" then parse_bool01 flag_sx
      else inl (diag "mc-cert-parse" ("expected 'rvc' field in mc-cert-v1, got '" ++ tag ++ "'"))
  | _ => inl (diag "mc-cert-parse" "malformed 'rvc' field in mc-cert-v1")
  end.

Definition parse_rv_width_sexp (sx : sexp) : string + positive :=
  match sx with
  | SAtom s =>
      if String.eqb s "1" then inr 1%positive
      else if String.eqb s "8" then inr 8%positive
      else if String.eqb s "16" then inr 16%positive
      else if String.eqb s "32" then inr 32%positive
      else if String.eqb s "64" then inr 64%positive
      else inl (diag "mc-cert-parse" ("unsupported bit width '" ++ s ++ "' (expected 1, 8, 16, 32, or 64)"))
  | _ => inl (diag "mc-cert-parse" "expected bit width atom (1, 8, 16, 32, or 64)")
  end.

Lemma parse_rv_width_supported : forall sx w,
  parse_rv_width_sexp sx = inr w -> rv_supported_arg_width w = true.
Proof.
  intros [s | s | es] w H; cbn in H; try discriminate.
  destruct (String.eqb s "1"); [inversion H; subst; reflexivity |].
  destruct (String.eqb s "8"); [inversion H; subst; reflexivity |].
  destruct (String.eqb s "16"); [inversion H; subst; reflexivity |].
  destruct (String.eqb s "32"); [inversion H; subst; reflexivity |].
  destruct (String.eqb s "64"); [inversion H; subst; reflexivity | discriminate].
Qed.

Definition parse_mc_ret_width_sexp (sx : sexp) : string + positive :=
  match sx with
  | SList [SAtom tag; w_sx] =>
      if String.eqb tag "ret-width" then parse_rv_width_sexp w_sx
      else inl (diag "mc-cert-parse" ("expected 'ret-width' field in mc-cert-v1, got '" ++ tag ++ "'"))
  | _ => inl (diag "mc-cert-parse" "malformed 'ret-width' field in mc-cert-v1")
  end.

Lemma parse_mc_ret_width_supported : forall sx w,
  parse_mc_ret_width_sexp sx = inr w -> rv_supported_arg_width w = true.
Proof.
  intros [| | [| [tag | |] [| w_sx [| ? ?]]]] w H; cbn in H; try discriminate.
  destruct (String.eqb tag "ret-width"); [| discriminate].
  exact (parse_rv_width_supported w_sx w H).
Qed.

Definition parse_rv_arg_ext_sexp (sx : sexp) : string + rv_arg_ext :=
  match sx with
  | SAtom s =>
      if String.eqb s "none" then inr RAE_None
      else if String.eqb s "signext" then inr RAE_SignExt
      else if String.eqb s "zeroext" then inr RAE_ZeroExt
      else inl (diag "mc-cert-parse"
        ("unknown argument extension mode '" ++ s ++ "' (expected 'none', 'signext', or 'zeroext')"))
  | _ => inl (diag "mc-cert-parse" "expected atom for argument extension mode")
  end.

Definition parse_rv_arg_spec_sexp (sx : sexp) : string + rv_arg_spec :=
  match sx with
  | SList [SAtom tag; nm_sx; w_sx; ext_sx] =>
      if String.eqb tag "arg" then
        match parse_nonempty_str nm_sx, parse_rv_width_sexp w_sx, parse_rv_arg_ext_sexp ext_sx with
        | inr nm, inr w, inr ext =>
            if negb (starts_with_dollar nm) then inr (mk_rv_arg_spec nm w ext)
            else inl (diag "mc-cert-parse" ("argument name cannot start with '$': '" ++ nm ++ "'"))
        | inl err, _, _ => inl err
        | _, inl err, _ => inl err
        | _, _, inl err => inl err
        end
      else inl (diag "mc-cert-parse" ("expected 'arg' tag in mc-cert-v1 args, got '" ++ tag ++ "'"))
  | _ => inl (diag "mc-cert-parse" "malformed 'arg' entry in mc-cert-v1")
  end.

Lemma parse_rv_arg_spec_wf : forall sx sp,
  parse_rv_arg_spec_sexp sx = inr sp -> rv_valid_arg_spec sp = true.
Proof.
  intros [| | [| [tag | |] [| nm_sx [| w_sx [| ext_sx [| ? ?]]]]]] sp H;
    cbn in H; try discriminate.
  destruct (String.eqb tag "arg"); [| discriminate].
  destruct (parse_nonempty_str nm_sx) as [| nm]; [discriminate |].
  destruct (parse_rv_width_sexp w_sx) as [| w] eqn:Hw; [discriminate |].
  destruct (parse_rv_arg_ext_sexp ext_sx) as [| ext]; [discriminate |].
  destruct (negb (starts_with_dollar nm)) eqn:Hnd; [| discriminate].
  inversion H; subst; clear H.
  unfold rv_valid_arg_spec; cbn [ras_width ras_name].
  rewrite (parse_rv_width_supported _ _ Hw), Hnd; reflexivity.
Qed.

Definition parse_mc_args_sexp (sx : sexp) : string + list rv_arg_spec :=
  match parse_tagged_section_list "args" parse_rv_arg_spec_sexp sx with
  | inl err => inl err
  | inr specs =>
      if Nat.leb (List.length specs) 8 then inr specs
      else inl (diag "mc-cert-parse"
        ("too many arguments in mc-cert-v1 (" ++ diag_nat_dec (List.length specs) ++ " > 8)"))
  end.

Lemma parse_mc_args_wf : forall sx specs,
  parse_mc_args_sexp sx = inr specs ->
  Nat.leb (List.length specs) 8 = true /\
  forallb rv_valid_arg_spec specs = true.
Proof.
  intros sx specs H; unfold parse_mc_args_sexp in H.
  destruct (parse_tagged_section_list "args" parse_rv_arg_spec_sexp sx) as [| xs] eqn:Hs;
    [discriminate H |].
  destruct (Nat.leb (List.length xs) 8) eqn:Hlen; [| discriminate H].
  inversion H; subst xs; clear H.
  split; [exact Hlen |].
  exact (parse_tagged_section_list_wf _ _ _ parse_rv_arg_spec_wf _ _ Hs).
Qed.

Definition parse_mc_N_sexp (ctx : string) (sx : sexp) : string + N :=
  match sx with
  | SAtom s =>
      match parse_canonical_N s with
      | Some n => inr n
      | None => inl (diag "mc-cert-parse" ("expected canonical unsigned integer for " ++ ctx ++ ", got '" ++ s ++ "'"))
      end
  | _ => inl (diag "mc-cert-parse" ("expected unsigned integer atom for " ++ ctx))
  end.

Definition parse_mc_Z_sexp (ctx : string) (sx : sexp) : string + Z :=
  match sx with
  | SAtom (String c rest as s) =>
      if Nat.eqb (Ascii.nat_of_ascii c) 45 then
        match parse_pos_str rest with
        | Some p => inr (Z.neg p)
        | None => inl (diag "mc-cert-parse"
            ("expected canonical negative integer for " ++ ctx ++ ", got '" ++ s ++ "'"))
        end
      else
        match parse_canonical_N s with
        | Some n => inr (Z.of_N n)
        | None => inl (diag "mc-cert-parse" ("expected canonical integer for " ++ ctx ++ ", got '" ++ s ++ "'"))
        end
  | _ => inl (diag "mc-cert-parse" ("expected integer atom for " ++ ctx))
  end.

Definition parse_mc_slot_size_sexp (sx : sexp) : string + mc_mem_size :=
  match sx with
  | SAtom s =>
      if String.eqb s "1" then inr MS_1
      else if String.eqb s "2" then inr MS_2
      else if String.eqb s "4" then inr MS_4
      else if String.eqb s "8" then inr MS_8
      else inl (diag "mc-cert-parse" ("invalid stack slot byte size '" ++ s ++ "' (expected 1, 2, 4, or 8)"))
  | _ => inl (diag "mc-cert-parse" "expected stack slot byte size atom (1, 2, 4, or 8)")
  end.

Definition parse_mc_reg_width_sexp (sx : sexp) : string + positive :=
  match sx with
  | SAtom s =>
      if String.eqb s "32" then inr 32%positive
      else if String.eqb s "64" then inr 64%positive
      else inl (diag "mc-cert-parse" ("invalid loop register width '" ++ s ++ "' (expected 32 or 64)"))
  | _ => inl (diag "mc-cert-parse" "expected loop register width atom (32 or 64)")
  end.

Definition parse_mc_loop_reg_sexp (sx : sexp) : string + mc_loop_reg_bind :=
  match sx with
  | SList [SAtom tag; r_sx; w_sx; e_sx] =>
      if String.eqb tag "reg" then
        match parse_mc_N_sexp "loop reg index" r_sx,
              parse_mc_reg_width_sexp w_sx,
              parse_cert_expr [] e_sx with
        | inr r, inr w, inr e => inr (mk_mc_loop_reg_bind r w e)
        | inl err, _, _ => inl err
        | _, inl err, _ => inl err
        | _, _, inl err => inl err
        end
      else inl (diag "mc-cert-parse" ("expected 'reg' entry in loop regs, got '" ++ tag ++ "'"))
  | _ => inl (diag "mc-cert-parse" "malformed 'reg' entry in loop regs")
  end.

Definition parse_mc_loop_slot_sexp (sx : sexp) : string + mc_loop_slot_bind :=
  match sx with
  | SList [SAtom tag; off_sx; sz_sx; e_sx] =>
      if String.eqb tag "slot" then
        match parse_mc_Z_sexp "loop slot offset" off_sx,
              parse_mc_slot_size_sexp sz_sx,
              parse_cert_expr [] e_sx with
        | inr off, inr sz, inr e => inr (MLS_Expr off sz e)
        | inl err, _, _ => inl err
        | _, inl err, _ => inl err
        | _, _, inl err => inl err
        end
      else inl (diag "mc-cert-parse" ("unexpected loop slot entry tag '" ++ tag ++ "' (expected 'slot')"))
  | SList [SAtom tag; off_sx; r_sx] =>
      if String.eqb tag "saved-reg" then
        match parse_mc_Z_sexp "loop saved-reg offset" off_sx,
              parse_mc_N_sexp "loop saved-reg index" r_sx with
        | inr off, inr r => inr (MLS_SavedReg off r)
        | inl err, _ => inl err
        | _, inl err => inl err
        end
      else inl (diag "mc-cert-parse" ("unexpected loop slot entry tag '" ++ tag ++ "' (expected 'saved-reg')"))
  | _ => inl (diag "mc-cert-parse" "malformed slot entry in loop slots")
  end.

Definition parse_mc_loop_inv_tail (inv_tail : list sexp) : string + option cert_expr :=
  match inv_tail with
  | [] => inr None
  | [SList [SAtom tag; inv_sx]] =>
      if String.eqb tag "inv" then
        match parse_cert_expr [] inv_sx with
        | inr inv => inr (Some inv)
        | inl err => inl err
        end
      else inl (diag "mc-cert-parse" ("expected optional 'inv' field in loop section, got '" ++ tag ++ "'"))
  | _ => inl (diag "mc-cert-parse" "malformed trailing fields in loop section")
  end.

Definition parse_mc_loop_sexp (arch : elf_arch) (sx : sexp) : string + mc_loop_spec :=
  match sx with
  | SList (SAtom tag :: hdr_sx :: pc_sx :: sp_sx :: regs_sx :: slots_sx :: inv_tail) =>
      if String.eqb tag "loop" then
        match parse_tagged_nonempty_str_sexp "ir-header" hdr_sx with
        | inl err => inl err
        | inr hdr =>
            match pc_sx with
            | SList [SAtom pc_t; pc_val_sx] =>
                if String.eqb pc_t "mc-pc" then
                  match sp_sx with
                  | SList [SAtom sp_t; sp_val_sx] =>
                      if String.eqb sp_t "sp-off" then
                        match parse_tagged_section_list "regs" parse_mc_loop_reg_sexp regs_sx,
                              parse_tagged_section_list "slots" parse_mc_loop_slot_sexp slots_sx,
                              parse_mc_loop_inv_tail inv_tail,
                              parse_mc_N_sexp "loop mc-pc" pc_val_sx,
                              parse_mc_Z_sexp "loop sp-off" sp_val_sx with
                        | inr regs, inr slots, inr opt_inv, inr pc, inr sp_off =>
                            let ls := mk_mc_loop_spec hdr pc sp_off regs slots opt_inv in
                            match check_mc_loop_spec_diag arch ls with
                            | inr tt => inr ls
                            | inl err => inl err
                            end
                        | inl err, _, _, _, _ => inl err
                        | _, inl err, _, _, _ => inl err
                        | _, _, inl err, _, _ => inl err
                        | _, _, _, inl err, _ => inl err
                        | _, _, _, _, inl err => inl err
                        end
                      else inl (diag "mc-cert-parse" ("expected 'sp-off' field in loop section, got '" ++ sp_t ++ "'"))
                  | _ => inl (diag "mc-cert-parse" "malformed 'sp-off' field in loop section")
                  end
                else inl (diag "mc-cert-parse" ("expected 'mc-pc' field in loop section, got '" ++ pc_t ++ "'"))
            | _ => inl (diag "mc-cert-parse" "malformed 'mc-pc' field in loop section")
            end
        end
      else inl (diag "mc-cert-parse" ("expected 'loop' section tag in mc-cert-v1, got '" ++ tag ++ "'"))
  | _ => inl (diag "mc-cert-parse" "malformed 'loop' section in mc-cert-v1")
  end.

Lemma parse_mc_loop_sexp_wf : forall arch sx ls,
  parse_mc_loop_sexp arch sx = inr ls -> wf_mc_loop_spec arch ls = true.
Proof.
  intros arch [| | [| [tag | |] [| hdr_sx [| pc_sx [| sp_sx [| regs_sx [| slots_sx inv_tail]]]]]]] ls H;
    cbn in H; try discriminate.
  destruct (String.eqb tag "loop"); [| discriminate].
  destruct (parse_tagged_nonempty_str_sexp "ir-header" hdr_sx) as [| hdr]; [discriminate |].
  destruct pc_sx as [| | [| [pc_t | |] [| pc_val_sx [| ? ?]]]]; try discriminate.
  destruct (String.eqb pc_t "mc-pc"); [| discriminate].
  destruct sp_sx as [| | [| [sp_t | |] [| sp_val_sx [| ? ?]]]]; try discriminate.
  destruct (String.eqb sp_t "sp-off"); [| discriminate].
  destruct (parse_tagged_section_list "regs" parse_mc_loop_reg_sexp regs_sx) as [| regs]; [discriminate |].
  destruct (parse_tagged_section_list "slots" parse_mc_loop_slot_sexp slots_sx) as [| slots]; [discriminate |].
  destruct (parse_mc_loop_inv_tail inv_tail) as [| opt_inv]; [discriminate |].
  destruct (parse_mc_N_sexp "loop mc-pc" pc_val_sx) as [| pc]; [discriminate |].
  destruct (parse_mc_Z_sexp "loop sp-off" sp_val_sx) as [| sp_off]; [discriminate |].
  destruct (check_mc_loop_spec_diag arch (mk_mc_loop_spec hdr pc sp_off regs slots opt_inv))
    as [err | []] eqn:Hwf; [discriminate |].
  inversion H; subst ls.
  exact (check_mc_loop_spec_diag_sound _ _ Hwf).
Qed.

Definition parse_mc_callee_ret_sexp (sx : sexp) : string + (positive * rv_arg_ext) :=
  match sx with
  | SList [SAtom tag; w_sx; ext_sx] =>
      if String.eqb tag "ret-width" then
        match parse_rv_width_sexp w_sx, parse_rv_arg_ext_sexp ext_sx with
        | inr w, inr ext => inr (w, ext)
        | inl err, _ => inl err
        | _, inl err => inl err
        end
      else inl (diag "mc-cert-parse" ("expected 'ret-width' field in callee, got '" ++ tag ++ "'"))
  | _ => inl (diag "mc-cert-parse" "malformed 'ret-width' field in callee")
  end.

Lemma parse_mc_callee_ret_supported : forall sx w ext,
  parse_mc_callee_ret_sexp sx = inr (w, ext) -> rv_supported_arg_width w = true.
Proof.
  intros [| | [| [tag | |] [| w_sx [| ext_sx [| ? ?]]]]] w ext H;
    cbn in H; try discriminate H.
  destruct (String.eqb tag "ret-width"); [| discriminate H].
  destruct (parse_rv_width_sexp w_sx) as [| w0] eqn:Hw; [discriminate H |].
  destruct (parse_rv_arg_ext_sexp ext_sx); [discriminate H |].
  inversion H; subst w0; exact (parse_rv_width_supported _ _ Hw).
Qed.

Definition parse_mc_callee_sexp (sx : sexp) : string + mc_callee_spec :=
  match sx with
  | SList [SAtom tag; nm_sx; ret_sx; args_sx] =>
      if String.eqb tag "callee" then
        match parse_nonempty_str nm_sx, parse_mc_callee_ret_sexp ret_sx, parse_mc_args_sexp args_sx with
        | inr nm, inr (rw, rext), inr cargs =>
            let c := mk_mc_callee_spec nm rw rext cargs in
            match check_mc_callee_spec_diag c with
            | inr tt => inr c
            | inl err => inl err
            end
        | inl err, _, _ => inl err
        | _, inl err, _ => inl err
        | _, _, inl err => inl err
        end
      else inl (diag "mc-cert-parse" ("expected 'callee' entry in mc-cert-v1 calls, got '" ++ tag ++ "'"))
  | _ => inl (diag "mc-cert-parse" "malformed 'callee' entry in mc-cert-v1 calls")
  end.

Lemma parse_mc_callee_sexp_wf : forall sx c,
  parse_mc_callee_sexp sx = inr c -> wf_mc_callee_spec c = true.
Proof.
  intros [| | [| [tag | |] [| nm_sx [| ret_sx [| args_sx [| ? ?]]]]]] c H;
    cbn in H; try discriminate H.
  destruct (String.eqb tag "callee"); [| discriminate H].
  destruct (parse_nonempty_str nm_sx) as [| nm]; [discriminate H |].
  destruct (parse_mc_callee_ret_sexp ret_sx) as [| [rw rext]]; [discriminate H |].
  destruct (parse_mc_args_sexp args_sx) as [| cargs]; [discriminate H |].
  destruct (check_mc_callee_spec_diag (mk_mc_callee_spec nm rw rext cargs)) as [err | []] eqn:Hwf;
    [discriminate H |].
  inversion H; subst; exact (check_mc_callee_spec_diag_sound _ Hwf).
Qed.

Definition parse_mc_loop_and_lrat (arch : elf_arch) (tail : list sexp)
  : string + (option mc_loop_spec * option (list lrat_step)) :=
  match tail with
  | [] => inr (None, None)
  | [sec_sx] =>
      match sec_sx with
      | SList (SAtom tag :: _) =>
          if String.eqb tag "lrat" then
            match parse_nonempty_tagged_section "lrat" parse_lrat_step_sexp sec_sx with
            | inr (s :: sr) => inr (None, Some (s :: sr))
            | inr [] => inl (diag "mc-cert-parse" "empty 'lrat' section in mc-cert-v1")
            | inl err => inl (diag "mc-cert-parse" err)
            end
          else if String.eqb tag "loop" then
            match parse_mc_loop_sexp arch sec_sx with
            | inr ls => inr (Some ls, None)
            | inl err => inl err
            end
          else inl (diag "mc-cert-parse" ("unexpected optional section tag '" ++ tag ++ "' in mc-cert-v1"))
      | _ => inl (diag "mc-cert-parse" "malformed optional section in mc-cert-v1")
      end
  | [loop_sx; lrat_sx] =>
      match parse_mc_loop_sexp arch loop_sx,
            parse_nonempty_tagged_section "lrat" parse_lrat_step_sexp lrat_sx with
      | inr ls, inr (s :: sr) => inr (Some ls, Some (s :: sr))
      | inr _, inr [] => inl (diag "mc-cert-parse" "empty 'lrat' section in mc-cert-v1")
      | inl err, _ => inl err
      | _, inl err => inl (diag "mc-cert-parse" err)
      end
  | _ => inl (diag "mc-cert-parse" "unexpected trailing section in mc-cert-v1")
  end.

Lemma parse_mc_loop_and_lrat_wf : forall arch tail opt_loop opt_pf,
  parse_mc_loop_and_lrat arch tail = inr (opt_loop, opt_pf) ->
  (match opt_loop with None => true | Some ls => wf_mc_loop_spec arch ls end) = true /\
  (match opt_pf with None => true | Some [] => false | Some (_ :: _) => true end) = true.
Proof.
  intros arch tail opt_loop opt_pf H.
  destruct tail as [| s1 [| s2 [| ? ?]]]; cbn in H; try discriminate.
  - inversion H; subst; split; reflexivity.
  - destruct s1 as [| | [| [tag | |] s1_rest]]; try discriminate.
    destruct (String.eqb tag "lrat").
    + destruct (parse_nonempty_tagged_section "lrat" parse_lrat_step_sexp (SList (SAtom tag :: s1_rest)))
        as [| [| s sr]]; try discriminate H.
      inversion H; subst; split; reflexivity.
    + destruct (String.eqb tag "loop"); [| discriminate H].
      destruct (parse_mc_loop_sexp arch (SList (SAtom tag :: s1_rest))) as [| ls] eqn:Hl;
        [discriminate H |].
      inversion H; subst; split; [exact (parse_mc_loop_sexp_wf _ _ _ Hl) | reflexivity].
  - destruct (parse_mc_loop_sexp arch s1) as [| ls] eqn:Hl; [discriminate H |].
    destruct (parse_nonempty_tagged_section "lrat" parse_lrat_step_sexp s2)
      as [| [| s sr]]; try discriminate H.
    inversion H; subst; split; [exact (parse_mc_loop_sexp_wf _ _ _ Hl) | reflexivity].
Qed.

Definition parse_mc_tail (arch : elf_arch) (fn_name : string) (tail : list sexp)
  : string + (list mc_callee_spec * option mc_loop_spec * option (list lrat_step)) :=
  match tail with
  | SList (SAtom tag :: cre) :: rest =>
      if String.eqb tag "calls" then
        match parse_nonempty_tagged_section "calls" parse_mc_callee_sexp (SList (SAtom "calls" :: cre)) with
        | inl err => inl (diag "mc-cert-parse" err)
        | inr cs =>
            match check_mc_calls_diag fn_name cs with
            | inl err => inl err
            | inr tt =>
                match parse_mc_loop_and_lrat arch rest with
                | inr (opt_loop, opt_pf) => inr (cs, opt_loop, opt_pf)
                | inl err => inl err
                end
            end
        end
      else
        match parse_mc_loop_and_lrat arch tail with
        | inr (opt_loop, opt_pf) => inr ([], opt_loop, opt_pf)
        | inl err => inl err
        end
  | _ =>
      match parse_mc_loop_and_lrat arch tail with
      | inr (opt_loop, opt_pf) => inr ([], opt_loop, opt_pf)
      | inl err => inl err
      end
  end.

Lemma parse_mc_tail_wf : forall arch fn_name tail calls opt_loop opt_pf,
  parse_mc_tail arch fn_name tail = inr (calls, opt_loop, opt_pf) ->
  wf_mc_calls fn_name calls = true /\
  (match opt_loop with None => true | Some ls => wf_mc_loop_spec arch ls end) = true /\
  (match opt_pf with None => true | Some [] => false | Some (_ :: _) => true end) = true.
Proof.
  intros arch fn_name tail calls opt_loop opt_pf H.
  destruct tail as [| [| | [| [tag | |] cre]] rest];
    try (unfold parse_mc_tail in H;
         destruct (parse_mc_loop_and_lrat arch _) as [| [ol op]] eqn:Hll; [discriminate H |];
         inversion H; subst; clear H;
         destruct (parse_mc_loop_and_lrat_wf _ _ _ _ Hll) as [Hl Hp];
         split; [reflexivity | exact (conj Hl Hp)]).
  unfold parse_mc_tail in H.
  destruct (String.eqb tag "calls") eqn:Etag.
  - destruct (parse_nonempty_tagged_section "calls" parse_mc_callee_sexp (SList (SAtom "calls" :: cre)))
      as [| cs]; [discriminate H |].
    destruct (check_mc_calls_diag fn_name cs) as [err | []] eqn:Hwc; [discriminate H |].
    destruct (parse_mc_loop_and_lrat arch rest) as [| [ol op]] eqn:Hll; [discriminate H |].
    inversion H; subst; clear H.
    destruct (parse_mc_loop_and_lrat_wf _ _ _ _ Hll) as [Hl Hp].
    split; [exact (check_mc_calls_diag_sound _ _ Hwc) | exact (conj Hl Hp)].
  - destruct (parse_mc_loop_and_lrat arch (SList (SAtom tag :: cre) :: rest)) as [| [ol op]] eqn:Hll;
      [discriminate H |].
    inversion H; subst; clear H.
    destruct (parse_mc_loop_and_lrat_wf _ _ _ _ Hll) as [Hl Hp].
    split; [reflexivity | exact (conj Hl Hp)].
Qed.

Definition parse_mc_cert_sexp (root : sexp) : string + mc_certificate :=
  match root with
  | SList (SAtom schema_tag :: arch_sx :: kind_sx :: fn_sx :: rvc_sx :: rw_sx :: args_sx :: tail) =>
      if String.eqb schema_tag "mc-cert-v1" then
        match parse_mc_arch_sexp arch_sx,
              parse_mc_elf_kind_sexp kind_sx,
              parse_tagged_nonempty_str_sexp "fn" fn_sx,
              parse_mc_rvc_sexp rvc_sx,
              parse_mc_ret_width_sexp rw_sx,
              parse_mc_args_sexp args_sx with
        | inr arch, inr kind, inr fn_nm, inr rvc, inr rw, inr args =>
            match parse_mc_tail arch fn_nm tail with
            | inr (calls, opt_loop, opt_pf) =>
                inr (mk_mc_certificate arch kind fn_nm rvc rw args calls opt_loop opt_pf)
            | inl err => inl err
            end
        | inl err, _, _, _, _, _ => inl err
        | _, inl err, _, _, _, _ => inl err
        | _, _, inl err, _, _, _ => inl (diag "mc-cert-parse" err)
        | _, _, _, inl err, _, _ => inl err
        | _, _, _, _, inl err, _ => inl err
        | _, _, _, _, _, inl err => inl err
        end
      else inl (diag "mc-cert-parse"
        ("unsupported MC certificate schema tag '" ++ schema_tag ++ "' (expected 'mc-cert-v1')"))
  | _ => inl (diag "mc-cert-parse" "malformed mc-cert-v1 root S-expression")
  end.

Definition parse_mc_cert (input : string) : string + mc_certificate :=
  match parse_sexp input with
  | inl err => inl (diag "mc-cert-parse" err)
  | inr root => parse_mc_cert_sexp root
  end.

Theorem parse_mc_cert_sexp_wf : forall root c,
  parse_mc_cert_sexp root = inr c -> wf_mc_cert c = true.
Proof.
  intros [| | [| [schema_tag | |] [| arch_sx [| kind_sx [| fn_sx [| rvc_sx [| rw_sx [| args_sx tail]]]]]]]]
         c H; cbn in H; try discriminate.
  destruct (String.eqb schema_tag "mc-cert-v1"); [| discriminate].
  destruct (parse_mc_arch_sexp arch_sx) as [| arch]; [discriminate |].
  destruct (parse_mc_elf_kind_sexp kind_sx) as [| kind]; [discriminate |].
  destruct (parse_tagged_nonempty_str_sexp "fn" fn_sx) as [| fn_nm] eqn:Hfn; [discriminate |].
  destruct (parse_mc_rvc_sexp rvc_sx) as [| rvc]; [discriminate |].
  destruct (parse_mc_ret_width_sexp rw_sx) as [| rw] eqn:Hrw; [discriminate |].
  destruct (parse_mc_args_sexp args_sx) as [| args] eqn:Hargs; [discriminate |].
  destruct (parse_mc_tail arch fn_nm tail) as [| [[calls opt_loop] opt_pf]] eqn:Htail; [discriminate |].
  inversion H; subst c; clear H.
  destruct (parse_mc_args_wf _ _ Hargs) as [Hlen Hspecs].
  destruct (parse_mc_tail_wf _ _ _ _ _ _ Htail) as (Hcalls & Hloop & Hpf).
  unfold wf_mc_cert; cbn [mc_arch mc_fn_name mc_ret_width mc_args mc_calls mc_loop mc_lrat_proof].
  rewrite (parse_tagged_nonempty_str_ok _ _ _ Hfn),
          (parse_mc_ret_width_supported _ _ Hrw),
          Hlen, Hspecs, Hcalls, Hloop, Hpf; reflexivity.
Qed.

Theorem parse_mc_cert_wf : forall input c,
  parse_mc_cert input = inr c -> wf_mc_cert c = true.
Proof.
  intros input c H; unfold parse_mc_cert in H.
  destruct (parse_sexp input) as [| root]; [discriminate |].
  exact (parse_mc_cert_sexp_wf root c H).
Qed.
