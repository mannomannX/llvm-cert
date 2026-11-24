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
  Elf64Spec
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

Record mc_certificate : Set := mk_mc_certificate {
  mc_arch : elf_arch;
  mc_elf_kind : elf_kind;
  mc_fn_name : string;
  mc_rvc : bool;
  mc_ret_width : positive;
  mc_args : list rv_arg_spec;
  mc_lrat_proof : option (list lrat_step);
}.

Definition wf_mc_cert (c : mc_certificate) : bool :=
  negb (String.eqb (mc_fn_name c) "") &&
  rv_supported_arg_width (mc_ret_width c) &&
  Nat.leb (List.length (mc_args c)) 8 &&
  forallb rv_valid_arg_spec (mc_args c) &&
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

Definition parse_mc_lrat_tail (tail : list sexp) : string + option (list lrat_step) :=
  match tail with
  | [] => inr None
  | [lrat_sx] =>
      match parse_nonempty_tagged_section "lrat" parse_lrat_step_sexp lrat_sx with
      | inr (s :: sr) => inr (Some (s :: sr))
      | inr [] => inl "empty lrat section in mc-cert-v1"
      | inl err => inl err
      end
  | _ => inl "unexpected trailing section in mc-cert-v1"
  end.

Definition parse_mc_cert_sexp (root : sexp) : string + mc_certificate :=
  match root with
  | SList (SAtom schema_tag :: arch_sx :: kind_sx :: fn_sx :: rvc_sx :: rw_sx :: args_sx :: tail) =>
      if String.eqb schema_tag "mc-cert-v1" then
        match parse_mc_arch_sexp arch_sx,
              parse_mc_elf_kind_sexp kind_sx,
              parse_tagged_nonempty_str_sexp "fn" fn_sx,
              parse_mc_rvc_sexp rvc_sx,
              parse_mc_ret_width_sexp rw_sx,
              parse_mc_args_sexp args_sx,
              parse_mc_lrat_tail tail with
        | inr arch, inr kind, inr fn_nm, inr rvc, inr rw, inr args, inr opt_pf =>
            inr (mk_mc_certificate arch kind fn_nm rvc rw args opt_pf)
        | inl err, _, _, _, _, _, _ => inl err
        | _, inl err, _, _, _, _, _ => inl err
        | _, _, inl err, _, _, _, _ => inl err
        | _, _, _, inl err, _, _, _ => inl err
        | _, _, _, _, inl err, _, _ => inl err
        | _, _, _, _, _, inl err, _ => inl err
        | _, _, _, _, _, _, inl err => inl err
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
  destruct (parse_mc_lrat_tail tail) as [| opt_pf] eqn:Hpf; [discriminate |].
  inversion H; subst c; clear H.
  destruct (parse_mc_args_wf _ _ Hargs) as [Hlen Hspecs].
  unfold wf_mc_cert; cbn [mc_fn_name mc_ret_width mc_args mc_lrat_proof].
  rewrite (parse_tagged_nonempty_str_ok _ _ _ Hfn),
          (parse_mc_ret_width_supported _ _ Hrw),
          Hlen, Hspecs.
  cbn [andb].
  destruct tail as [| lrat_sx [| ? ?]]; cbn [parse_mc_lrat_tail] in Hpf; try discriminate Hpf.
  - inversion Hpf; reflexivity.
  - destruct (parse_nonempty_tagged_section "lrat" parse_lrat_step_sexp lrat_sx)
      as [| [| s sr]]; try discriminate Hpf.
    inversion Hpf; reflexivity.
Qed.

Theorem parse_mc_cert_wf : forall input c,
  parse_mc_cert input = inr c -> wf_mc_cert c = true.
Proof.
  intros input c H; unfold parse_mc_cert in H.
  destruct (parse_sexp input) as [| root]; [discriminate |].
  exact (parse_mc_cert_sexp_wf root c H).
Qed.
