(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Canonical [mc-cert-v1] Certificate AST & Total S-Expression Parser ([CertValidator.McFormat])

    Implements for Milestone M1 of Phase [8.3a]:
    1. Canonical AST ([mc_certificate]) and decidable well-formedness predicate
       ([wf_mc_cert]) for machine-code refinement certificates.
    2. Stack-safe tail-recursive byte conversion ([mc_string_to_bytes]) using
       [List.rev_append] so multi-MiB ELF binaries never overflow the OCaml stack.
    3. Total bounded-depth S-expression parser ([parse_mc_cert]) reusing
       [CertFormat.parse_sexp] and [CertFormat.parse_lrat_step_sexp], backed
       by the axiom-free theorem [parse_mc_cert_wf]. *)

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

From CertValidator Require Import
  AigLrat
  CertFormat
  AlgRules
  Elf64Spec
  McFrameMem
  Rv64Sem.

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
  induction s as [| c rest IH]; intros acc; cbn [mc_string_to_bytes_acc string_to_bytes].
  - reflexivity.
  - rewrite (IH (Ascii.N_of_ascii c :: acc)); reflexivity.
Qed.

Lemma mc_string_to_bytes_eq : forall s,
  mc_string_to_bytes s = string_to_bytes s.
Proof.
  intros s; unfold mc_string_to_bytes; exact (mc_string_to_bytes_acc_spec s []).
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
  no_dup_N (List.map mlr_reg (ml_regs ls)) &&
  forallb (wf_mc_loop_reg_bind arch) (ml_regs ls) &&
  forallb (wf_mc_loop_slot_bind arch (ml_sp_off ls)) (ml_slots ls) &&
  mc_intervals_pairwise_disjoint (List.map mc_loop_slot_interval (ml_slots ls)) &&
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
  mc_no_dup_strings (List.map ras_name (mcs_args c)).

Definition wf_mc_calls (fn_name : string) (cs : list mc_callee_spec) : bool :=
  let fn_bare := mc_strip_leading_at fn_name in
  forallb wf_mc_callee_spec cs &&
  forallb (fun c => negb (String.eqb (mc_strip_leading_at (mcs_name c)) fn_bare)) cs &&
  mc_no_dup_strings (List.map (fun c => mc_strip_leading_at (mcs_name c)) cs).

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

(** ** 3. Total S-Expression Parser ([parse_mc_cert]) *)

Definition parse_mc_arch_sexp (sx : sexp) : string + elf_arch :=
  match sx with
  | SList [SAtom tag; SAtom a] =>
      if String.eqb tag "arch" then
        if String.eqb a "rv64" then inr EA_Riscv64
        else if String.eqb a "aarch64" then inr EA_AArch64
        else inl "unknown architecture in mc-cert-v1"
      else inl "expected arch field in mc-cert-v1"
  | _ => inl "malformed arch field in mc-cert-v1"
  end.

Definition parse_mc_elf_kind_sexp (sx : sexp) : string + elf_kind :=
  match sx with
  | SList [SAtom tag; SAtom k] =>
      if String.eqb tag "elf-kind" then
        if String.eqb k "rel" then inr EK_Rel
        else if String.eqb k "exec" then inr EK_Exec
        else if String.eqb k "dyn" then inr EK_Dyn
        else inl "unknown ELF kind in mc-cert-v1"
      else inl "expected elf-kind field in mc-cert-v1"
  | _ => inl "malformed elf-kind field in mc-cert-v1"
  end.

Definition parse_mc_rvc_sexp (sx : sexp) : string + bool :=
  match sx with
  | SList [SAtom tag; flag_sx] =>
      if String.eqb tag "rvc" then parse_bool01 flag_sx
      else inl "expected rvc field in mc-cert-v1"
  | _ => inl "malformed rvc field in mc-cert-v1"
  end.

Definition parse_rv_width_sexp (sx : sexp) : string + positive :=
  match sx with
  | SAtom s =>
      if String.eqb s "1" then inr 1%positive
      else if String.eqb s "8" then inr 8%positive
      else if String.eqb s "16" then inr 16%positive
      else if String.eqb s "32" then inr 32%positive
      else if String.eqb s "64" then inr 64%positive
      else inl "expected RV64 supported bit width (1, 8, 16, 32, or 64)"
  | _ => inl "expected RV64 supported bit width (1, 8, 16, 32, or 64)"
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
      else inl "expected ret-width field in mc-cert-v1"
  | _ => inl "malformed ret-width field in mc-cert-v1"
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
      else inl "unknown argument extension mode in mc-cert-v1"
  | _ => inl "expected atom for argument extension mode in mc-cert-v1"
  end.

Definition parse_rv_arg_spec_sexp (sx : sexp) : string + rv_arg_spec :=
  match sx with
  | SList [SAtom tag; nm_sx; w_sx; ext_sx] =>
      if String.eqb tag "arg" then
        match parse_nonempty_str nm_sx, parse_rv_width_sexp w_sx, parse_rv_arg_ext_sexp ext_sx with
        | inr nm, inr w, inr ext =>
            if negb (starts_with_dollar nm) then inr (mk_rv_arg_spec nm w ext)
            else inl "argument name cannot start with '$'"
        | inl err, _, _ => inl err
        | _, inl err, _ => inl err
        | _, _, inl err => inl err
        end
      else inl "expected arg tag in mc-cert-v1 args"
  | _ => inl "malformed arg entry in mc-cert-v1"
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
      else inl "too many arguments in mc-cert-v1 (maximum 8)"
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

Definition parse_mc_N_sexp (sx : sexp) : string + N :=
  match sx with
  | SAtom s =>
      match parse_canonical_N s with
      | Some n => inr n
      | None => inl "expected canonical unsigned integer in mc-cert-v1 loop section"
      end
  | _ => inl "expected unsigned integer atom in mc-cert-v1 loop section"
  end.

Definition parse_mc_Z_sexp (sx : sexp) : string + Z :=
  match sx with
  | SAtom (String c rest as s) =>
      if Nat.eqb (Ascii.nat_of_ascii c) 45 then
        match parse_pos_str rest with
        | Some p => inr (Z.neg p)
        | None => inl "expected canonical negative integer in mc-cert-v1 loop section"
        end
      else
        match parse_canonical_N s with
        | Some n => inr (Z.of_N n)
        | None => inl "expected canonical integer in mc-cert-v1 loop section"
        end
  | _ => inl "expected integer atom in mc-cert-v1 loop section"
  end.

Definition parse_mc_slot_size_sexp (sx : sexp) : string + mc_mem_size :=
  match sx with
  | SAtom s =>
      if String.eqb s "1" then inr MS_1
      else if String.eqb s "2" then inr MS_2
      else if String.eqb s "4" then inr MS_4
      else if String.eqb s "8" then inr MS_8
      else inl "expected stack slot byte size (1, 2, 4, or 8) in mc-cert-v1"
  | _ => inl "expected stack slot byte size atom in mc-cert-v1"
  end.

Definition parse_mc_reg_width_sexp (sx : sexp) : string + positive :=
  match sx with
  | SAtom s =>
      if String.eqb s "32" then inr 32%positive
      else if String.eqb s "64" then inr 64%positive
      else inl "expected loop register width (32 or 64) in mc-cert-v1"
  | _ => inl "expected loop register width atom in mc-cert-v1"
  end.

Definition parse_mc_loop_reg_sexp (sx : sexp) : string + mc_loop_reg_bind :=
  match sx with
  | SList [SAtom tag; r_sx; w_sx; e_sx] =>
      if String.eqb tag "reg" then
        match parse_mc_N_sexp r_sx, parse_mc_reg_width_sexp w_sx, parse_cert_expr [] e_sx with
        | inr r, inr w, inr e => inr (mk_mc_loop_reg_bind r w e)
        | inl err, _, _ => inl err
        | _, inl err, _ => inl err
        | _, _, inl err => inl err
        end
      else inl "expected reg entry in mc-cert-v1 loop regs"
  | _ => inl "malformed reg entry in mc-cert-v1 loop regs"
  end.

Definition parse_mc_loop_slot_sexp (sx : sexp) : string + mc_loop_slot_bind :=
  match sx with
  | SList [SAtom tag; off_sx; sz_sx; e_sx] =>
      if String.eqb tag "slot" then
        match parse_mc_Z_sexp off_sx, parse_mc_slot_size_sexp sz_sx, parse_cert_expr [] e_sx with
        | inr off, inr sz, inr e => inr (MLS_Expr off sz e)
        | inl err, _, _ => inl err
        | _, inl err, _ => inl err
        | _, _, inl err => inl err
        end
      else inl "unexpected slot entry tag in mc-cert-v1 loop slots"
  | SList [SAtom tag; off_sx; r_sx] =>
      if String.eqb tag "saved-reg" then
        match parse_mc_Z_sexp off_sx, parse_mc_N_sexp r_sx with
        | inr off, inr r => inr (MLS_SavedReg off r)
        | inl err, _ => inl err
        | _, inl err => inl err
        end
      else inl "unexpected slot entry tag in mc-cert-v1 loop slots"
  | _ => inl "malformed slot entry in mc-cert-v1 loop slots"
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
      else inl "expected optional inv field in mc-cert-v1 loop section"
  | _ => inl "malformed trailing fields in mc-cert-v1 loop section"
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
                              parse_mc_N_sexp pc_val_sx,
                              parse_mc_Z_sexp sp_val_sx with
                        | inr regs, inr slots, inr opt_inv, inr pc, inr sp_off =>
                            let ls := mk_mc_loop_spec hdr pc sp_off regs slots opt_inv in
                            if wf_mc_loop_spec arch ls then inr ls
                            else inl "loop cutpoint specification failed well-formedness check"
                        | inl err, _, _, _, _ => inl err
                        | _, inl err, _, _, _ => inl err
                        | _, _, inl err, _, _ => inl err
                        | _, _, _, inl err, _ => inl err
                        | _, _, _, _, inl err => inl err
                        end
                      else inl "expected sp-off field in mc-cert-v1 loop section"
                  | _ => inl "malformed sp-off field in mc-cert-v1 loop section"
                  end
                else inl "expected mc-pc field in mc-cert-v1 loop section"
            | _ => inl "malformed mc-pc field in mc-cert-v1 loop section"
            end
        end
      else inl "expected loop section tag in mc-cert-v1"
  | _ => inl "malformed loop section in mc-cert-v1"
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
  destruct (parse_mc_N_sexp pc_val_sx) as [| pc]; [discriminate |].
  destruct (parse_mc_Z_sexp sp_val_sx) as [| sp_off]; [discriminate |].
  destruct (wf_mc_loop_spec arch (mk_mc_loop_spec hdr pc sp_off regs slots opt_inv)) eqn:Hwf;
    [| discriminate].
  inversion H; subst ls; exact Hwf.
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
      else inl "expected ret-width field in mc-cert-v1 callee"
  | _ => inl "malformed ret-width field in mc-cert-v1 callee"
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
            if wf_mc_callee_spec c then inr c
            else inl "invalid callee specification in mc-cert-v1 calls"
        | inl err, _, _ => inl err
        | _, inl err, _ => inl err
        | _, _, inl err => inl err
        end
      else inl "expected callee entry in mc-cert-v1 calls"
  | _ => inl "malformed callee entry in mc-cert-v1 calls"
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
  destruct (wf_mc_callee_spec (mk_mc_callee_spec nm rw rext cargs)) eqn:Hwf;
    [inversion H; subst; exact Hwf | discriminate H].
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
            | inr [] => inl "empty lrat section in mc-cert-v1"
            | inl err => inl err
            end
          else if String.eqb tag "loop" then
            match parse_mc_loop_sexp arch sec_sx with
            | inr ls => inr (Some ls, None)
            | inl err => inl err
            end
          else inl "unexpected optional section tag in mc-cert-v1"
      | _ => inl "malformed optional section in mc-cert-v1"
      end
  | [loop_sx; lrat_sx] =>
      match parse_mc_loop_sexp arch loop_sx,
            parse_nonempty_tagged_section "lrat" parse_lrat_step_sexp lrat_sx with
      | inr ls, inr (s :: sr) => inr (Some ls, Some (s :: sr))
      | inr _, inr [] => inl "empty lrat section in mc-cert-v1"
      | inl err, _ => inl err
      | _, inl err => inl err
      end
  | _ => inl "unexpected trailing section in mc-cert-v1"
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
        | inl err => inl err
        | inr cs =>
            if wf_mc_calls fn_name cs then
              match parse_mc_loop_and_lrat arch rest with
              | inr (opt_loop, opt_pf) => inr (cs, opt_loop, opt_pf)
              | inl err => inl err
              end
            else inl "duplicate callee or direct self-recursion in mc-cert-v1 calls"
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
    destruct (wf_mc_calls fn_name cs) eqn:Hwc; [| discriminate H].
    destruct (parse_mc_loop_and_lrat arch rest) as [| [ol op]] eqn:Hll; [discriminate H |].
    inversion H; subst; clear H.
    destruct (parse_mc_loop_and_lrat_wf _ _ _ _ Hll) as [Hl Hp].
    split; [exact Hwc | exact (conj Hl Hp)].
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
        | _, _, inl err, _, _, _ => inl err
        | _, _, _, inl err, _, _ => inl err
        | _, _, _, _, inl err, _ => inl err
        | _, _, _, _, _, inl err => inl err
        end
      else inl "unsupported MC certificate schema tag (expected mc-cert-v1)"
  | _ => inl "malformed mc-cert-v1 root S-expression"
  end.

Definition parse_mc_cert (input : string) : string + mc_certificate :=
  match parse_sexp input with
  | inl err => inl err
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
