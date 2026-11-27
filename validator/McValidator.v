(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Verified ELF64-to-IR Backend Translation Validator ([CertValidator.McValidator])

    Purpose:
      Top-level ELF64-to-IR backend validator re-exporting [McExprRewrite], integrating
      certificate parsing, IR syntax/prototype/ABI gates, ELF slicing, straight-line/loop/call
      validation ([validate_mc_tle_with_cert_str]), and DIMACS emission ([emit_mc_dimacs_cnf_str]).

    Trust Contract & Fail-Closed Boundary:
      [validate_mc_tle_with_cert_str] fails closed ([inl err]) on parse, well-formedness,
      syntax/prototype/ABI gate, ELF relocation/slice, decode, symbolic lowering, or LRAT
      discharge failures; [inr tt] is backed by [validate_mc_tle_with_cert_str_sound].
      Extracted to OCaml via [Extract.v].

    Assumptions:
      [Stdlib], [Vellvm], [CertValidator.common.Diag], [CertValidator] MC/RV64/A64 modules,
      and exported [McExprRewrite]; zero [Admitted] and zero custom axioms.

    Section Outline:
      5. Prototype, ABI & syntax gates, [validate_mc_mcfg_with_cert],
      [validate_mc_tle_with_cert_str], and soundness proof; 6. DIMACS CNF emitter. *)

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

From Vellvm Require Import
  Utils
  Utils.ITreeUtil
  Utils.Assoc
  Utils.ListUtil
  Numeric.Zbits
  Numeric.Integers
  Syntax.LLVMAst
  Syntax.AstLib
  Syntax.CFG
  Syntax.ModuleRefs
  Syntax.DynamicTypes
  Syntax.TypToDtyp
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.Attributes
  Semantics.Denotation
  Semantics.Operations.Compare
  Semantics.Operations.Conversion
  Semantics.Operations.Select
  Semantics.Operations.Freeze
  Semantics.LLVMEvents.

From CertValidator.common Require Import
  Diag.

From CertValidator Require Import
  AigLrat
  CertFormat
  AlgRules
  CertValidator
  Elf64Spec
  McFrameMem
  McIsaCommon
  Rv64Decode
  Rv64ExecSym
  Rv64DagProof
  Rv64LoopSeg
  A64Decode
  A64ExecSym
  A64DagProof
  A64LoopSeg
  McFormat
  McOblDischarger
  McLoop
  McCall.

From CertValidator Require Export
  McExprRewrite.

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
#[local] Arguments Nat.eqb _ _ : simpl nomatch.
#[local] Arguments Nat.leb _ _ : simpl nomatch.
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
#[local] Arguments Integers.add : simpl never.
#[local] Arguments Integers.sub : simpl never.
#[local] Arguments Integers.mul : simpl never.
#[local] Arguments Integers.divs : simpl never.
#[local] Arguments Integers.shru : simpl never.
#[local] Arguments Integers.shr : simpl never.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** 5. IR Prototype, ABI Extension, Syntax Gates & End-to-End Validator *)

Definition attr_is_signext (a : param_attr) : bool :=
  match a with
  | PARAMATTR_Signext => true
  | _ => false
  end.

Definition attr_is_zeroext (a : param_attr) : bool :=
  match a with
  | PARAMATTR_Zeroext => true
  | _ => false
  end.

Definition check_mc_arg_ext
  (arch : elf_arch) (w : positive) (attrs : list param_attr) (ext : rv_arg_ext) : bool :=
  match arch with
  | EA_Riscv64 =>
      if Pos.eqb w 64%positive then
        match ext with RAE_None => true | _ => false end
      else
        match ext with
        | RAE_SignExt => existsb attr_is_signext attrs
        | RAE_ZeroExt => existsb attr_is_zeroext attrs
        | RAE_None => false
        end
  | EA_AArch64 =>
      if Pos.eqb w 64%positive || Pos.eqb w 32%positive then
        match ext with RAE_None => true | _ => false end
      else
        match ext with
        | RAE_SignExt => existsb attr_is_signext attrs
        | RAE_ZeroExt => existsb attr_is_zeroext attrs
        | RAE_None => true
        end
  end.

Definition check_one_mc_arg
  (arch : elf_arch) (pnm : string) (dt : dtyp) (attrs : list param_attr) (sp : rv_arg_spec) : bool :=
  String.eqb (ras_name sp) pnm &&
  rv_valid_arg_spec sp &&
  dtyp_eqb dt (DTYPE_Base (DTYPE_I (ras_width sp))) &&
  check_mc_arg_ext arch (ras_width sp) attrs (ras_ext sp).

Fixpoint check_mc_arg_specs
  (arch : elf_arch) (pnms : list string) (dts : list dtyp) (pattrs : list (list param_attr))
  (specs : list rv_arg_spec) {struct pnms} : bool :=
  match pnms, dts, pattrs, specs with
  | [], [], [], [] => true
  | p :: rp, d :: rd, a :: ra, s :: rs =>
      check_one_mc_arg arch p d a s && check_mc_arg_specs arch rp rd ra rs
  | _, _, _, _ => false
  end.

Definition check_one_mc_arg_diag
  (arch : elf_arch) (idx : nat) (pnm : string) (dt : dtyp)
  (attrs : list param_attr) (sp : rv_arg_spec) : string + unit :=
  bind_err
    (guard_err (String.eqb (ras_name sp) pnm)
      (fun _ => diag "mc-ir-abi"
        ("arg #" ++ diag_nat_dec idx ++ ": mc-cert-v1 name '" ++ ras_name sp ++
         "' does not match IR param '" ++ pnm ++ "'")))
    (fun _ =>
  bind_err
    (guard_err (rv_valid_arg_spec sp)
      (fun _ => diag "mc-ir-abi"
        ("arg #" ++ diag_nat_dec idx ++ " ('" ++ pnm ++
         "'): invalid mc-cert-v1 arg spec width " ++ diag_pos_dec (ras_width sp))))
    (fun _ =>
  bind_err
    (guard_err (dtyp_eqb dt (DTYPE_Base (DTYPE_I (ras_width sp))))
      (fun _ => diag "mc-ir-abi"
        ("arg #" ++ diag_nat_dec idx ++ " ('" ++ pnm ++
         "'): IR parameter type disagrees with mc-cert-v1 i" ++ diag_pos_dec (ras_width sp))))
    (fun _ =>
  guard_err (check_mc_arg_ext arch (ras_width sp) attrs (ras_ext sp))
    (fun _ => diag "mc-ir-abi"
      ("arg #" ++ diag_nat_dec idx ++ " ('" ++ pnm ++ "', i" ++ diag_pos_dec (ras_width sp) ++
       "): signext/zeroext ABI extension mismatch for " ++ elf_arch_name arch))))).

Lemma check_one_mc_arg_diag_sound :
  forall arch idx pnm dt attrs sp,
    check_one_mc_arg_diag arch idx pnm dt attrs sp = inr tt ->
    check_one_mc_arg arch pnm dt attrs sp = true.
Proof.
  intros arch idx pnm dt attrs sp H.
  unfold check_one_mc_arg_diag in H; unfold check_one_mc_arg.
  destruct (String.eqb (ras_name sp) pnm); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (rv_valid_arg_spec sp); cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (dtyp_eqb dt (DTYPE_Base (DTYPE_I (ras_width sp))));
    cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (check_mc_arg_ext arch (ras_width sp) attrs (ras_ext sp));
    cbn [guard_err] in H; [reflexivity | discriminate H].
Qed.

Fixpoint check_mc_arg_specs_idx_diag
  (arch : elf_arch) (idx : nat) (pnms : list string) (dts : list dtyp)
  (pattrs : list (list param_attr)) (specs : list rv_arg_spec)
  {struct pnms} : string + unit :=
  match pnms, dts, pattrs, specs with
  | [], [], [], [] => inr tt
  | p :: rp, d :: rd, a :: ra, s :: rs =>
      bind_err (check_one_mc_arg_diag arch idx p d a s)
        (fun _ => check_mc_arg_specs_idx_diag arch (S idx) rp rd ra rs)
  | _, _, _, _ =>
      inl (diag "mc-ir-abi"
        ("argument count mismatch (at index " ++ diag_nat_dec idx ++
         "): mc-cert-v1 args must match IR parameter count"))
  end.

Lemma check_mc_arg_specs_idx_diag_sound :
  forall arch idx pnms dts pattrs specs,
    check_mc_arg_specs_idx_diag arch idx pnms dts pattrs specs = inr tt ->
    check_mc_arg_specs arch pnms dts pattrs specs = true.
Proof.
  intros arch idx pnms; revert idx;
    induction pnms as [| p rp IH];
    intros idx [| d rd] [| a ra] [| s rs] H;
    cbn [check_mc_arg_specs_idx_diag check_mc_arg_specs] in *;
    try discriminate H; [reflexivity |].
  destruct (check_one_mc_arg_diag arch idx p d a s) as [| []] eqn:E1;
    cbn [bind_err] in H; [discriminate H |].
  rewrite (check_one_mc_arg_diag_sound _ _ _ _ _ _ E1), (IH _ _ _ _ H); reflexivity.
Qed.

Lemma check_mc_arg_specs_len : forall arch pnms dts pattrs specs,
  check_mc_arg_specs arch pnms dts pattrs specs = true ->
  List.length pnms = List.length dts /\
  List.length dts = List.length pattrs /\
  List.length pattrs = List.length specs.
Proof.
  intros arch; induction pnms as [| p rp IH]; intros [| d rd] [| a ra] [| s rs] H;
    cbn in H; try discriminate H; [repeat split |].
  apply andb_true_iff in H as [_ Hr].
  destruct (IH _ _ _ Hr) as (H1 & H2 & H3); repeat split; cbn; lia.
Qed.

Lemma check_mc_arg_specs_nth : forall arch pnms dts pattrs specs idx p d a s,
  check_mc_arg_specs arch pnms dts pattrs specs = true ->
  nth_error pnms idx = Some p ->
  nth_error dts idx = Some d ->
  nth_error pattrs idx = Some a ->
  nth_error specs idx = Some s ->
  check_one_mc_arg arch p d a s = true.
Proof.
  intros arch; induction pnms as [| p0 rp IH]; intros [| d0 rd] [| a0 ra] [| s0 rs] [| idx'] p d a s H Hp Hd Ha Hs;
    cbn in H, Hp, Hd, Ha, Hs; try discriminate;
    apply andb_true_iff in H as [H1 Hr].
  - inversion Hp; inversion Hd; inversion Ha; inversion Hs; subst; exact H1.
  - exact (IH _ _ _ _ _ _ _ _ Hr Hp Hd Ha Hs).
Qed.

Lemma check_one_mc_arg_inv : forall arch pnm dt attrs sp,
  check_one_mc_arg arch pnm dt attrs sp = true ->
  ras_name sp = pnm /\
  rv_valid_arg_spec sp = true /\
  dt = DTYPE_Base (DTYPE_I (ras_width sp)).
Proof.
  intros arch pnm dt attrs sp H; unfold check_one_mc_arg in H.
  rewrite !andb_true_iff in H; destruct H as (((Hn & Hv) & Hdt) & _).
  apply String.eqb_eq in Hn.
  unfold dtyp_eqb in Hdt; destruct (dtyp_eq_dec dt (DTYPE_Base (DTYPE_I (ras_width sp))));
    [| discriminate Hdt].
  repeat split; assumption.
Qed.

Lemma check_mc_arg_specs_names : forall arch pnms dts pattrs specs,
  check_mc_arg_specs arch pnms dts pattrs specs = true ->
  List.map ras_name specs = pnms.
Proof.
  intros arch; induction pnms as [| p rp IH]; intros [| d rd] [| a ra] [| s rs] H;
    cbn in H; try discriminate H; [reflexivity |].
  apply andb_true_iff in H as [H1 Hr].
  destruct (check_one_mc_arg_inv _ _ _ _ _ H1) as [Hnm _].
  cbn; rewrite Hnm, (IH _ _ _ Hr); reflexivity.
Qed.

Lemma check_mc_arg_specs_compat : forall arch pnms dts pattrs specs idx sp,
  check_mc_arg_specs arch pnms dts pattrs specs = true ->
  nth_error specs idx = Some sp ->
  nth_error dts idx = Some (DTYPE_Base (DTYPE_I (ras_width sp))) /\
  nth_error pnms idx = Some (ras_name sp).
Proof.
  intros arch; induction pnms as [| p rp IH]; intros [| d rd] [| a ra] [| s rs] [| idx'] sp H Hs;
    cbn in H, Hs; try discriminate;
    apply andb_true_iff in H as [H1 Hr].
  - inversion Hs; subst s; destruct (check_one_mc_arg_inv _ _ _ _ _ H1) as [Hnm [_ Hdt]]; subst; split; reflexivity.
  - exact (IH _ _ _ _ _ Hr Hs).
Qed.

Definition check_mc_ir_syntax_gates (G : CFG.cfg dtyp) : bool :=
  cfg_no_fast_math G &&
  cfg_no_concurrency G &&
  cfg_supported_abi G &&
  cfg_intrinsics_allowlisted G &&
  cfg_no_vaarg G &&
  cfg_no_exceptions G &&
  list_empty_b (cfg_alloca_slot_names G) &&
  bmap_varargs_irrel (ocfg_map (blks G)).

Definition check_mc_ir_syntax_gates_diag (G : CFG.cfg dtyp) : string + unit :=
  bind_err
    (guard_err (cfg_no_fast_math G)
      (fun _ => diag "mc-ir-syntax" "unsupported fast-math flags in IR CFG"))
    (fun _ =>
  bind_err
    (guard_err (cfg_no_concurrency G)
      (fun _ => diag "mc-ir-syntax" "unsupported volatile/atomic/fence operation in IR CFG"))
    (fun _ =>
  bind_err
    (guard_err (cfg_supported_abi G)
      (fun _ => diag "mc-ir-syntax" "unsupported calling convention or ABI feature in IR CFG"))
    (fun _ =>
  bind_err
    (guard_err (cfg_intrinsics_allowlisted G)
      (fun _ => diag "mc-ir-syntax" "unsupported LLVM intrinsic call in IR CFG"))
    (fun _ =>
  bind_err
    (guard_err (cfg_no_vaarg G)
      (fun _ => diag "mc-ir-syntax" "unsupported varargs/va_arg operation in IR CFG"))
    (fun _ =>
  bind_err
    (guard_err (cfg_no_exceptions G)
      (fun _ => diag "mc-ir-syntax" "unsupported exception-handling instruction in IR CFG"))
    (fun _ =>
  bind_err
    (guard_err (list_empty_b (cfg_alloca_slot_names G))
      (fun _ => diag "mc-ir-syntax" "stack alloca instructions are not supported in MC mode"))
    (fun _ =>
  guard_err (bmap_varargs_irrel (ocfg_map (blks G)))
    (fun _ => diag "mc-ir-syntax" "unsupported bmap/varargs metadata in IR CFG")))))))).

Lemma check_mc_ir_syntax_gates_diag_sound :
  forall G,
    check_mc_ir_syntax_gates_diag G = inr tt ->
    check_mc_ir_syntax_gates G = true.
Proof.
  intros G H; unfold check_mc_ir_syntax_gates_diag in H; unfold check_mc_ir_syntax_gates.
  repeat (match type of H with
          | bind_err (guard_err ?c _) _ = inr tt =>
              destruct c; cbn [guard_err bind_err] in H; [| discriminate H]
          | guard_err ?c _ = inr tt =>
              destruct c; cbn [guard_err] in H; [| discriminate H]
          end).
  reflexivity.
Qed.

Definition check_mc_ir_proto_contract
  (tenv : list (ident * typ)) (defn : definition typ (CFG.cfg typ)) (mcert : mc_certificate)
  : bool :=
  let proto := df_prototype defn in
  let ir_cfg := convert_typ tenv (df_instrs defn) in
  let ir_pnames := List.map cert_reg_name (args ir_cfg) in
  let '(s_rattrs, s_pattrs) := dc_param_attrs proto in
  cert_fn_matches_raw_id (mc_fn_name mcert) (dc_name proto) &&
  match dc_type proto with
  | TYPE_Function ret_ty arg_tys false =>
      let arg_dtys := List.map (typ_to_dtyp tenv) arg_tys in
      dtyp_eqb (typ_to_dtyp tenv ret_ty) (DTYPE_Base (DTYPE_I (mc_ret_width mcert))) &&
      rv_supported_arg_width (mc_ret_width mcert) &&
      forallb decl_ann_supported (dc_annotations proto) &&
      forallb (fun a => negb (is_unmodeled_fn_attr a))
              (dc_attrs proto ++ ann_fun_attributes (dc_annotations proto)) &&
      forallb (fun a => negb (is_unmodeled_param_attr a)) s_rattrs &&
      forallb (forallb (fun a => negb (is_unmodeled_param_attr a))) s_pattrs &&
      forallb2 attr_preserves_dtyp_b arg_dtys s_pattrs &&
      forallb2 raw_id_eqb (df_args defn) (args ir_cfg) &&
      no_dup_raw_ids (args ir_cfg) &&
      no_dup_strings ir_pnames &&
      check_mc_arg_specs (mc_arch mcert) ir_pnames arg_dtys s_pattrs (mc_args mcert) &&
      match mc_arch mcert with
      | EA_Riscv64 => true
      | EA_AArch64 =>
          forallb (fun sp => negb (existsb (String.eqb (a64_hi_var_name (ras_name sp))) ir_pnames))
                  (mc_args mcert)
      end &&
      cfg_param_dtyp_compatible ir_cfg arg_dtys &&
      check_mc_ir_syntax_gates ir_cfg
  | _ => false
  end.

Definition check_mc_ir_proto_contract_diag
  (tenv : list (ident * typ)) (defn : definition typ (CFG.cfg typ)) (mcert : mc_certificate)
  : string + unit :=
  let proto := df_prototype defn in
  let fnm := mc_fn_name mcert in
  let ir_cfg := convert_typ tenv (df_instrs defn) in
  let ir_pnames := List.map cert_reg_name (args ir_cfg) in
  let '(s_rattrs, s_pattrs) := dc_param_attrs proto in
  bind_err
    (guard_err (cert_fn_matches_raw_id fnm (dc_name proto))
      (fun _ => diag "mc-ir-proto" ("IR prototype name mismatch for '" ++ fnm ++ "'")))
    (fun _ =>
  match dc_type proto with
  | TYPE_Function ret_ty arg_tys false =>
      let arg_dtys := List.map (typ_to_dtyp tenv) arg_tys in
      bind_err
        (guard_err (dtyp_eqb (typ_to_dtyp tenv ret_ty) (DTYPE_Base (DTYPE_I (mc_ret_width mcert))))
          (fun _ => diag "mc-ir-proto"
            ("function '" ++ fnm ++ "': IR return type does not match mc-cert-v1 ret-width " ++
             diag_pos_dec (mc_ret_width mcert))))
        (fun _ =>
      bind_err
        (guard_err (rv_supported_arg_width (mc_ret_width mcert))
          (fun _ => diag "mc-ir-proto"
            ("function '" ++ fnm ++ "': unsupported return width " ++ diag_pos_dec (mc_ret_width mcert))))
        (fun _ =>
      bind_err
        (guard_err (forallb decl_ann_supported (dc_annotations proto))
          (fun _ => diag "mc-ir-proto"
            ("function '" ++ fnm ++ "': unsupported declaration annotation on IR function")))
        (fun _ =>
      bind_err
        (guard_err
          (forallb (fun a => negb (is_unmodeled_fn_attr a))
            (dc_attrs proto ++ ann_fun_attributes (dc_annotations proto)))
          (fun _ => diag "mc-ir-proto"
            ("function '" ++ fnm ++ "': unmodeled function attribute on IR function")))
        (fun _ =>
      bind_err
        (guard_err (forallb (fun a => negb (is_unmodeled_param_attr a)) s_rattrs)
          (fun _ => diag "mc-ir-proto"
            ("function '" ++ fnm ++ "': unmodeled return attribute on IR function")))
        (fun _ =>
      bind_err
        (guard_err (forallb (forallb (fun a => negb (is_unmodeled_param_attr a))) s_pattrs)
          (fun _ => diag "mc-ir-proto"
            ("function '" ++ fnm ++ "': unmodeled parameter attribute on IR function")))
        (fun _ =>
      bind_err
        (guard_err (forallb2 attr_preserves_dtyp_b arg_dtys s_pattrs)
          (fun _ => diag "mc-ir-proto"
            ("function '" ++ fnm ++ "': parameter count or attribute/dtyp preservation mismatch")))
        (fun _ =>
      bind_err
        (guard_err (forallb2 raw_id_eqb (df_args defn) (args ir_cfg))
          (fun _ => diag "mc-ir-proto"
            ("function '" ++ fnm ++ "': definition vs CFG parameter ID list mismatch")))
        (fun _ =>
      bind_err
        (guard_err (no_dup_raw_ids (args ir_cfg))
          (fun _ => diag "mc-ir-proto"
            ("function '" ++ fnm ++ "': duplicate raw parameter IDs in IR CFG")))
        (fun _ =>
      bind_err
        (guard_err (no_dup_strings ir_pnames)
          (fun _ => diag "mc-ir-proto"
            ("function '" ++ fnm ++ "': duplicate formatted parameter names in IR CFG")))
        (fun _ =>
      bind_err
        (check_mc_arg_specs_idx_diag (mc_arch mcert) 0 ir_pnames arg_dtys s_pattrs (mc_args mcert))
        (fun _ =>
      bind_err
        (guard_err
          (match mc_arch mcert with
           | EA_Riscv64 => true
           | EA_AArch64 =>
               forallb (fun sp => negb (existsb (String.eqb (a64_hi_var_name (ras_name sp))) ir_pnames))
                 (mc_args mcert)
           end)
          (fun _ => diag "mc-ir-abi"
            ("function '" ++ fnm ++ "': AArch64 parameter name collides with reserved __a64_hi_* symbol")))
        (fun _ =>
      bind_err
        (guard_err (cfg_param_dtyp_compatible ir_cfg arg_dtys)
          (fun _ => diag "mc-ir-proto"
            ("function '" ++ fnm ++ "': IR CFG parameter uses disagree with prototype types")))
        (fun _ => check_mc_ir_syntax_gates_diag ir_cfg)))))))))))))
  | _ => inl (diag "mc-ir-proto" ("function '" ++ fnm ++ "': varargs or non-function prototype unsupported"))
  end).

Lemma check_mc_ir_proto_contract_diag_sound :
  forall tenv defn mcert,
    check_mc_ir_proto_contract_diag tenv defn mcert = inr tt ->
    check_mc_ir_proto_contract tenv defn mcert = true.
Proof.
  intros tenv defn mcert H.
  unfold check_mc_ir_proto_contract_diag in H; unfold check_mc_ir_proto_contract.
  destruct (dc_param_attrs (df_prototype defn)) as [s_rattrs s_pattrs].
  destruct (cert_fn_matches_raw_id (mc_fn_name mcert) (dc_name (df_prototype defn))) eqn:Hfn;
    cbn [guard_err bind_err] in H; [| discriminate H].
  destruct (dc_type (df_prototype defn)) as [| | | | | | | | | | | ret_ty arg_tys [|] | | | | |] eqn:Edct;
    try discriminate H.
  repeat match type of H with
  | bind_err (guard_err ?c _) _ = inr tt =>
      destruct c; cbn [guard_err bind_err] in H; [| discriminate H]
  | bind_err (check_mc_arg_specs_idx_diag _ _ _ _ _ _) _ = inr tt =>
      let E := fresh "Eargs" in
      destruct (check_mc_arg_specs_idx_diag _ _ _ _ _ _) as [| []] eqn:E;
        cbn [bind_err] in H; [discriminate H | rewrite (check_mc_arg_specs_idx_diag_sound _ _ _ _ _ _ E)]
  end.
  rewrite (check_mc_ir_syntax_gates_diag_sound _ H); reflexivity.
Qed.

Definition mc_build_init_ctx
  (arch : elf_arch) (ir_pnames : list string) (arg_dtys : list dtyp)
  (s_pattrs : list (list param_attr)) (specs : list rv_arg_spec)
  : list (string * positive) * ub_ctx :=
  let '(proto_vars, proto_ctx) := seed_proto_param_ctx ir_pnames arg_dtys s_pattrs in
  let arg_vars := List.map (fun sp => (ras_name sp, ras_width sp)) specs in
  let extra_vars :=
    match arch with
    | EA_Riscv64 => []
    | EA_AArch64 => a64_hi_vars specs
    end in
  let mc_ctx := List.map (fun sp => UBA_ParamNoUndef (ras_name sp) (ras_width sp)) specs in
  let extra_ctx :=
    match arch with
    | EA_Riscv64 => []
    | EA_AArch64 => List.map (fun nv => UBA_ParamNoUndef (fst nv) (snd nv)) (a64_hi_vars specs)
    end in
  (proto_vars ++ arg_vars ++ extra_vars, proto_ctx ++ mc_ctx ++ extra_ctx).

Definition check_mc_cert_wf_diag (c : mc_certificate) : string + unit :=
  bind_err
    (guard_err (negb (String.eqb (mc_fn_name c) ""))
      (fun _ => diag "mc-cert-wf" "empty mc-cert-v1 function name"))
    (fun _ =>
  bind_err
    (guard_err (rv_supported_arg_width (mc_ret_width c))
      (fun _ => diag "mc-cert-wf"
        ("unsupported mc-cert-v1 ret-width " ++ diag_pos_dec (mc_ret_width c))))
    (fun _ =>
  bind_err
    (guard_err (Nat.leb (List.length (mc_args c)) 8)
      (fun _ => diag "mc-cert-wf"
        ("too many mc-cert-v1 arguments (" ++ diag_nat_dec (List.length (mc_args c)) ++ " > 8)")))
    (fun _ =>
  bind_err
    (check_forall_idx_diag_acc
      (fun idx sp =>
        guard_err (rv_valid_arg_spec sp)
          (fun _ => diag "mc-cert-wf"
            ("mc-cert-v1 arg #" ++ diag_nat_dec idx ++ " ('" ++ ras_name sp ++
             "'): invalid width " ++ diag_pos_dec (ras_width sp) ++ " or disallowed '$' prefix")))
      0 (mc_args c))
    (fun _ =>
  bind_err
    (check_mc_calls_diag (mc_fn_name c) (mc_calls c))
    (fun _ =>
  bind_err
    (match mc_loop c with
     | None => inr tt
     | Some ls => check_mc_loop_spec_diag (mc_arch c) ls
     end)
    (fun _ =>
  match mc_lrat_proof c with
  | Some [] => inl (diag "mc-cert-wf" "empty LRAT proof in mc-cert-v1 certificate")
  | _ => inr tt
  end)))))).

Definition find_unique_mc_defn_diag
  (fn_name : string) (ds : list (definition typ (CFG.cfg typ)))
  : string + definition typ (CFG.cfg typ) :=
  match find_unique_diag (fun d => cert_fn_matches_raw_id fn_name (dc_name (df_prototype d))) ds with
  | UM_Missing =>
      inl (diag "ir-fn-lookup" ("function '" ++ fn_name ++ "' not found in IR module"))
  | UM_Duplicate _ _ =>
      inl (diag "ir-fn-lookup" ("function '" ++ fn_name ++ "' is defined multiple times in IR module"))
  | UM_Unique d => inr d
  end.

Lemma find_unique_mc_defn_diag_in :
  forall fn_name ds d,
    find_unique_mc_defn_diag fn_name ds = inr d ->
    In d ds /\ cert_fn_matches_raw_id fn_name (dc_name (df_prototype d)) = true.
Proof.
  intros fn_name ds d H; unfold find_unique_mc_defn_diag in H.
  destruct (find_unique_diag (fun d0 => cert_fn_matches_raw_id fn_name (dc_name (df_prototype d0))) ds)
    as [| d0 | d1 d2] eqn:Eu; try discriminate H.
  inversion H; subst d0.
  destruct (find_unique_diag_spec _ _ _ Eu) as [Hin [Hm _]].
  exact (conj Hin Hm).
Qed.

Definition mc_decode_and_summarize
  (arch : elf_arch) (rvc : bool) (bytes : list N)
  (arg_specs : list rv_arg_spec) (ret_w : positive) : string + cfg_dag :=
  match arch with
  | EA_Riscv64 =>
      match decode_rv64_bytes rvc bytes with
      | inl err => inl err
      | inr insts =>
          let rv_fuel := S (2 * length_tr insts) in
          summarize_rv64_dag rv_fuel insts arg_specs ret_w
      end
  | EA_AArch64 =>
      if rvc then inl (diag "mc-rvc" "compressed mode (rvc 1) is not supported for AArch64")
      else
        match decode_a64_bytes bytes with
        | inl err => inl err
        | inr insts =>
            let a64_fuel := S (2 * length_tr insts) in
            summarize_a64_dag a64_fuel insts arg_specs ret_w
        end
  end.

Definition validate_mc_mcfg_with_cert
  (ir_m : CFG.mcfg typ) (raw_elf : list N) (mcert : mc_certificate) : string + unit :=
  match check_mc_cert_wf_diag mcert with
  | inl err => inl err
  | inr tt =>
      if negb (mcfg_identified_typs_defined ir_m) then
        inl (diag "ir-type" "undefined identified type in IR module")
      else
        match find_unique_mc_defn_diag (mc_fn_name mcert) (m_definitions ir_m) with
        | inl err => inl err
        | inr ir_defn =>
            match check_mc_ir_proto_contract_diag (m_type_defs ir_m) ir_defn mcert with
            | inl err => inl err
            | inr tt =>
                let fn_bare := strip_leading_at (mc_fn_name mcert) in
                match mc_calls mcert with
                | [] =>
                    match elf64_extract_func raw_elf (mc_arch mcert) (mc_elf_kind mcert) fn_bare with
                    | inl err => inl err
                    | inr sl =>
                        if negb (Bool.eqb (mc_rvc mcert) (efs_rvc sl)) then
                          inl (diag "mc-rvc"
                            ("ELF64 RVC flag disagrees with mc-cert-v1 rvc mode for '" ++ fn_bare ++ "'"))
                        else
                          let tenv := m_type_defs ir_m in
                          let ir_cfg := convert_typ tenv (df_instrs ir_defn) in
                          let ir_pnames := List.map cert_reg_name (args ir_cfg) in
                          let arg_dtys := defn_arg_dtys tenv ir_defn in
                          let s_pattrs := snd (dc_param_attrs (df_prototype ir_defn)) in
                          let '(seed_vars, mc_init_ctx) :=
                              mc_build_init_ctx (mc_arch mcert) ir_pnames arg_dtys s_pattrs (mc_args mcert) in
                          let allowed := used_src_param_vars ir_cfg ++ seed_vars in
                          match mc_loop mcert with
                          | None =>
                              match mc_decode_and_summarize (mc_arch mcert) (mc_rvc mcert) (efs_bytes sl) (mc_args mcert) (mc_ret_width mcert) with
                              | inl err => inl err
                              | inr d_mc =>
                                  match flatten_mc_dag_to_expr (mc_ret_width mcert) d_mc with
                                  | inl err => inl err
                                  | inr e_mc =>
                                      match summarize_cfg_dag_with_uas (fun _ => []) false ir_cfg ir_pnames with
                                      | None =>
                                          inl (diag "mc-ir-reify" ("IR CFG symbolic summarization failed for '" ++ fn_bare ++ "'"))
                                      | Some d_ir =>
                                          match src_dag_to_expr (mc_ret_width mcert) d_ir with
                                          | Some e_ir =>
                                              check_mc_expr_refines_diag mc_init_ctx allowed e_ir e_mc (mc_lrat_proof mcert)
                                          | None =>
                                              let dag_fuel := S (dag_node_count d_ir + 1) in
                                              let ro :=
                                                RO_ScalarRefines (mc_ret_width mcert)
                                                  (CE_BvConst (mc_ret_width mcert) 0%N)
                                                  (CE_BvConst (mc_ret_width mcert) 0%N) false in
                                              if check_dag_refines_cert dag_fuel allowed mc_init_ctx ro
                                                   (mc_lrat_proof mcert)
                                                   (spine_src_evals d_ir) (spine_branch_conds d_ir)
                                                   d_ir (CD_RetScalar (mc_ret_width mcert) e_mc)
                                              then inr tt
                                              else
                                                match mc_lrat_proof mcert with
                                                | Some pf =>
                                                    inl (diag "lrat-check"
                                                      ("LRAT proof (" ++ diag_nat_dec (length_tr pf) ++
                                                       " step(s)) failed to discharge MC-to-IR DAG refinement obligation for '" ++ fn_bare ++ "'"))
                                                | None =>
                                                    inl (diag "mc-refine"
                                                      ("MC-to-IR DAG refinement obligation failed for '" ++ fn_bare ++ "'"))
                                                end
                                          end
                                      end
                                  end
                              end
                          | Some ls =>
                              match mc_arch mcert with
                              | EA_Riscv64 =>
                                  match decode_rv64_bytes (mc_rvc mcert) (efs_bytes sl) with
                                  | inl err => inl err
                                  | inr insts =>
                                      validate_mc_loop_rv64 ir_cfg allowed mc_init_ctx insts (mc_args mcert) (mc_ret_width mcert) ls (mc_lrat_proof mcert)
                                  end
                              | EA_AArch64 =>
                                  if mc_rvc mcert then inl (diag "mc-rvc" "compressed mode (rvc 1) is not supported for AArch64")
                                  else
                                    match decode_a64_bytes (efs_bytes sl) with
                                    | inl err => inl err
                                    | inr insts =>
                                        validate_mc_loop_a64 ir_cfg allowed mc_init_ctx insts (mc_args mcert) (mc_ret_width mcert) ls (mc_lrat_proof mcert)
                                    end
                              end
                          end
                    end
                | callees =>
                    match mc_loop mcert with
                    | Some _ => inl (diag "mc-mode" "combining (calls ...) and (loop ...) in one certificate is not supported")
                    | None =>
                        match check_mc_callee_contracts_diag (m_type_defs ir_m) ir_m (mc_arch mcert) callees with
                        | inl err => inl err
                        | inr tt =>
                          match elf64_extract_func_with_calls raw_elf (mc_arch mcert) (mc_elf_kind mcert) fn_bare
                                  (List.map (fun c => mc_strip_leading_at (mcs_name c)) callees) with
                          | inl err => inl err
                          | inr (sl, ci) =>
                              if negb (Bool.eqb (mc_rvc mcert) (efs_rvc sl)) then
                                inl (diag "mc-rvc"
                                  ("ELF64 RVC flag disagrees with mc-cert-v1 rvc mode for '" ++ fn_bare ++ "'"))
                              else
                                let tenv := m_type_defs ir_m in
                                let ir_cfg := convert_typ tenv (df_instrs ir_defn) in
                                let ir_pnames := List.map cert_reg_name (args ir_cfg) in
                                let arg_dtys := defn_arg_dtys tenv ir_defn in
                                let s_pattrs := snd (dc_param_attrs (df_prototype ir_defn)) in
                                let '(seed_vars, mc_init_ctx) :=
                                    mc_build_init_ctx (mc_arch mcert) ir_pnames arg_dtys s_pattrs (mc_args mcert) in
                                let allowed := used_src_param_vars ir_cfg ++ seed_vars in
                                match mc_arch mcert with
                                | EA_Riscv64 =>
                                    match decode_rv64_bytes_with_calls (mc_rvc mcert) (mc_elf_kind mcert) (efs_range_lo sl) ci (efs_bytes sl) with
                                    | inl err => inl err
                                    | inr insts =>
                                        validate_mc_call_rv64 ir_cfg allowed mc_init_ctx insts (mc_args mcert) (mc_ret_width mcert) callees (mc_lrat_proof mcert)
                                    end
                                | EA_AArch64 =>
                                    if mc_rvc mcert then inl (diag "mc-rvc" "compressed mode (rvc 1) is not supported for AArch64")
                                    else
                                      match decode_a64_bytes_with_calls (mc_elf_kind mcert) (efs_range_lo sl) ci (efs_bytes sl) with
                                      | inl err => inl err
                                      | inr insts =>
                                          validate_mc_call_a64 ir_cfg allowed mc_init_ctx insts (mc_args mcert) (mc_ret_width mcert) callees (mc_lrat_proof mcert)
                                      end
                                end
                          end
                        end
                    end
                end
            end
        end
  end.

Definition validate_mc_tle_with_cert_str
  (ir_tle : toplevel_entities typ (block typ * list (block typ)))
  (elf_str cert_str : string) : string + unit :=
  match parse_mc_cert cert_str with
  | inl err => inl err
  | inr mcert =>
      validate_mc_mcfg_with_cert
        (mcfg_of_tle (resolve_module_refs ir_tle))
        (mc_string_to_bytes elf_str)
        mcert
  end.

Lemma mc_args_noundef_ctx_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle specs rf0,
    rv_rf_matches_args penv specs rf0 ->
    ub_ctx_holds penv foracle (List.map (fun sp => UBA_ParamNoUndef (ras_name sp) (ras_width sp)) specs).
Proof.
  intros penv foracle specs rf0 Hm.
  apply Forall_forall; intros ua Hin.
  apply in_map_iff in Hin as [sp [Heq Hsp]]; subst ua.
  destruct (In_nth_error specs sp Hsp) as [k Hnth].
  destruct (nth_error_Some specs k) as [Hs1 _].
  assert (Hlt : (k < List.length specs)%nat) by (apply Hs1; congruence).
  destruct (Hm k sp Hlt Hnth) as [v [Hp _]].
  cbn [ub_assumption_holds]; intros dv Hdv; rewrite Hp in Hdv; injection Hdv as <-; discriminate.
Qed.

Lemma a64_args_noundef_ctx_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle specs rf0,
    a64_rf_matches_args penv specs rf0 ->
    ub_ctx_holds penv foracle (List.map (fun sp => UBA_ParamNoUndef (ras_name sp) (ras_width sp)) specs).
Proof.
  intros penv foracle specs rf0 Hm.
  apply Forall_forall; intros ua Hin.
  apply in_map_iff in Hin as [sp [Heq Hsp]]; subst ua.
  destruct (In_nth_error specs sp Hsp) as [k Hnth].
  destruct (nth_error_Some specs k) as [Hs1 _].
  assert (Hlt : (k < List.length specs)%nat) by (apply Hs1; congruence).
  destruct (Hm k sp Hlt Hnth) as [v [Hp _]].
  cbn [ub_assumption_holds]; intros dv Hdv; rewrite Hp in Hdv; injection Hdv as <-; discriminate.
Qed.

Lemma a64_hi_vars_wf_and_ctx {Pa : Params} :
  forall (penv : param_env Pa) foracle specs rf0,
    NoDup (List.map ras_name specs) ->
    let penv' := a64_extend_penv_with_hi penv specs rf0 in
    wf_param_env_for (a64_hi_vars specs) penv' /\
    ub_ctx_holds penv' foracle (List.map (fun nv => UBA_ParamNoUndef (fst nv) (snd nv)) (a64_hi_vars specs)).
Proof.
  intros penv foracle specs rf0 Hnd penv'.
  assert (Hlookup : forall nm w, In (nm, w) (a64_hi_vars specs) ->
    exists k sp, nth_error specs k = Some sp /\
      nm = a64_hi_var_name (ras_name sp) /\ w = 64%positive /\ (ras_width sp =? 64)%positive = false).
  { intros nm w Hin; unfold a64_hi_vars in Hin; apply in_flat_map in Hin as [sp [Hsp Hhere]].
    destruct (Pos.eqb (ras_width sp) 64%positive) eqn:E64; [contradiction Hhere |].
    destruct Hhere as [Heq | []]; inversion Heq; subst nm w.
    destruct (In_nth_error specs sp Hsp) as [k Hnth].
    exists k, sp; repeat split; assumption. }
  split.
  - intros nm w Hin; destruct (Hlookup nm w Hin) as (k & sp & Hnth & -> & -> & Hw64).
    pose proof (a64_extend_penv_at_hi 0%nat k specs sp rf0 penv Hnd Hnth Hw64) as Hp.
    change (a64_extend_penv_with_hi_at 0%nat specs rf0 penv) with penv' in Hp.
    exists (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (N.of_nat (0 + k)) rf0))).
    split; [exact Hp | right; eexists; reflexivity].
  - apply Forall_forall; intros ua Hin; apply in_map_iff in Hin as [[nm w] [<- Hnv]]; cbn [fst snd].
    destruct (Hlookup nm w Hnv) as (k & sp & Hnth & -> & -> & Hw64).
    pose proof (a64_extend_penv_at_hi 0%nat k specs sp rf0 penv Hnd Hnth Hw64) as Hp.
    change (a64_extend_penv_with_hi_at 0%nat specs rf0 penv) with penv' in Hp.
    cbn [ub_assumption_holds]; intros dv Hdv; rewrite Hp in Hdv; injection Hdv as <-; discriminate.
Qed.

Lemma wf_cfg_dag_mono : forall vars1 vars2 d,
  incl vars1 vars2 ->
  wf_cfg_dag vars1 d = true ->
  wf_cfg_dag vars2 d = true.
Proof.
  intros vars1 vars2 d Hinc; induction d as [| | w ret_e | w step_e next IH | uas next IH | cond on_t IHt on_f IHf];
    intro Hwf; cbn [wf_cfg_dag] in *; try exact Hwf.
  - rewrite !andb_true_iff in *; destruct Hwf as (((? & ?) & ?) & Hsub); repeat split; try assumption.
    apply incl_vars_subset_b; eapply incl_tran; [exact (vars_subset_b_incl _ _ Hsub) | exact Hinc].
  - rewrite !andb_true_iff in *; destruct Hwf as ((((? & ?) & ?) & Hsub) & Hn); repeat split; try assumption;
      [apply incl_vars_subset_b; eapply incl_tran; [exact (vars_subset_b_incl _ _ Hsub) | exact Hinc] | exact (IH Hn)].
  - exact (IH Hwf).
  - rewrite !andb_true_iff in *; destruct Hwf as (((((? & ?) & ?) & Hsub) & Ht) & Hf); repeat split; try assumption;
      [apply incl_vars_subset_b; eapply incl_tran; [exact (vars_subset_b_incl _ _ Hsub) | exact Hinc] | exact (IHt Ht) | exact (IHf Hf)].
Qed.

Lemma eval_cert_expr_penv_agree {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) foracle e,
    is_let_free_expr e = true ->
    (forall nm w, In (nm, w) (collect_free_vars [] e) -> penv1 nm = penv2 nm) ->
    eval_cert_expr penv1 [] foracle e = eval_cert_expr penv2 [] foracle e.
Proof.
  intros penv1 penv2 foracle e.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hlf Hag; cbn [is_let_free_expr collect_free_vars eval_cert_expr lookup_let_val] in *.
  - reflexivity.
  - reflexivity.
  - rewrite (Hag nm w ltac:(left; reflexivity)); reflexivity.
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    rewrite (IHl Hlfl (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_introl Hx)))),
            (IHr Hlfr (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror Hx)))); reflexivity.
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    rewrite (IHl Hlfl (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_introl Hx)))),
            (IHr Hlfr (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror Hx)))); reflexivity.
  - rewrite (IHo Hlf Hag); reflexivity.
  - rewrite !andb_true_iff in Hlf; destruct Hlf as [[Hlfc Hlft] Hlff].
    rewrite (IHc Hlfc (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_introl Hx)))),
            (IHt Hlft (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hx)))))),
            (IHf Hlff (fun x wx Hx => Hag x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hx)))))); reflexivity.
  - rewrite (IHo Hlf Hag); reflexivity.
  - discriminate Hlf.
Qed.

Lemma eval_cfg_dag_penv_agree {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) foracle allowed d,
    wf_cfg_dag allowed d = true ->
    (forall nm w, In (nm, w) allowed -> penv1 nm = penv2 nm) ->
    eval_cfg_dag penv1 foracle d = eval_cfg_dag penv2 foracle d.
Proof.
  intros penv1 penv2 foracle allowed d;
    induction d as [| | w ret_e | w step_e next IH | uas next IH | cond on_t IHt on_f IHf];
    intros Hwf Hag; cbn [wf_cfg_dag eval_cfg_dag] in *; try reflexivity.
  - rewrite !andb_true_iff in Hwf; destruct Hwf as (((_ & _) & Hlf) & Hsub).
    unfold eval_closed_cert_expr.
    erewrite eval_cert_expr_penv_agree; [reflexivity | exact Hlf |].
    intros nm w0 Hin; apply (Hag nm w0 ((vars_subset_b_incl _ _ Hsub) _ Hin)).
  - rewrite !andb_true_iff in Hwf; destruct Hwf as ((((_ & _) & Hlf) & Hsub) & Hn).
    unfold eval_closed_cert_expr.
    erewrite (eval_cert_expr_penv_agree penv1 penv2);
      [| exact Hlf | intros nm w0 Hin; apply (Hag nm w0 ((vars_subset_b_incl _ _ Hsub) _ Hin))].
    destruct (eval_cert_expr penv2 [] foracle step_e); try reflexivity; exact (IH Hn Hag).
  - exact (IH Hwf Hag).
  - rewrite !andb_true_iff in Hwf; destruct Hwf as (((((_ & _) & Hlf) & Hsub) & Ht) & Hf).
    unfold eval_closed_cert_expr.
    erewrite (eval_cert_expr_penv_agree penv1 penv2);
      [| exact Hlf | intros nm w0 Hin; apply (Hag nm w0 ((vars_subset_b_incl _ _ Hsub) _ Hin))].
    destruct (eval_cert_expr penv2 [] foracle cond) as [| | | dvc]; try reflexivity.
    destruct dvc as [dbc | |]; try reflexivity.
    destruct dbc as [| wc cbit | | | | | |]; try reflexivity.
    destruct wc as [| |]; try reflexivity.
    destruct (@Integers.unsigned 1 cbit =? 1)%Z; [exact (IHt Ht Hag) | exact (IHf Hf Hag)].
Qed.

Lemma validate_mc_core_refine_sound {Pa : Params} :
  forall allowed mc_init_ctx ret_w lrat_pf d_ir d_mc e_mc penv dv_ir dv_mc,
    flatten_mc_dag_to_expr ret_w d_mc = inr e_mc ->
    (match src_dag_to_expr ret_w d_ir with
     | Some e_ir => check_mc_expr_refines mc_init_ctx allowed e_ir e_mc lrat_pf
     | None =>
         check_dag_refines_cert (S (dag_node_count d_ir + 1)) allowed mc_init_ctx
           (RO_ScalarRefines ret_w (CE_BvConst ret_w 0%N) (CE_BvConst ret_w 0%N) false)
           lrat_pf (spine_src_evals d_ir) (spine_branch_conds d_ir) d_ir (CD_RetScalar ret_w e_mc)
     end) = true ->
    wf_cfg_dag allowed d_ir = true ->
    wf_cfg_dag allowed d_mc = true ->
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv dummy_freeze_oracle mc_init_ctx ->
    eval_cfg_dag penv dummy_freeze_oracle d_mc = DO_Ret dv_mc ->
    eval_cfg_dag penv dummy_freeze_oracle d_ir = DO_Ret dv_ir ->
    dvalue_refines dv_ir dv_mc.
Proof.
  intros allowed mc_init_ctx ret_w lrat_pf d_ir d_mc e_mc penv dv_ir dv_mc
         Eflat Hchk Hwfd_ir Hwfd_mc Hpenv_all Hctx_all Hevd_mc Hevd_ir.
  destruct (flatten_mc_dag_to_expr_typing allowed ret_w d_mc e_mc Hwfd_mc Eflat)
    as (Hwt_mc & Hbw_mc & Hlf_mc & Hub_mc & Hfv_mc).
  assert (Hp_mc : wf_param_env_for (collect_free_vars [] e_mc) penv)
    by (intros x wx Hx; exact (Hpenv_all x wx (Hfv_mc (x, wx) Hx))).
  pose proof (flatten_mc_dag_to_expr_sound allowed ret_w d_mc e_mc
                penv dummy_freeze_oracle dv_mc Hwfd_mc Hpenv_all Eflat Hevd_mc) as Heve_mc.
  destruct (src_dag_to_expr ret_w d_ir) as [e_ir |] eqn:Esd.
  - destruct (src_dag_to_expr_typing allowed ret_w d_ir e_ir Hwfd_ir Esd)
      as (Hwt_ir & _ & Hlf_ir & Hfv_ir).
    assert (Hp_ir : wf_param_env_for (collect_free_vars [] e_ir) penv)
      by (intros x wx Hx; exact (Hpenv_all x wx (Hfv_ir (x, wx) Hx))).
    pose proof (src_dag_to_expr_sound allowed ret_w d_ir e_ir
                  penv dummy_freeze_oracle dv_ir Hwfd_ir Hpenv_all Esd Hevd_ir) as Heve_ir.
    pose proof (prepare_mc_expr_pair_sound _ allowed e_ir e_mc lrat_pf
                  penv dummy_freeze_oracle Hwt_ir Hlf_ir Hp_ir Hp_mc Hctx_all Hchk) as Href_e.
    rewrite Heve_ir, Heve_mc in Href_e; exact Href_e.
  - assert (Hwfd_flat : wf_cfg_dag allowed (CD_RetScalar ret_w e_mc) = true).
    { cbn [wf_cfg_dag]; rewrite Hwt_mc, Hbw_mc, Pos.eqb_refl, Hlf_mc, (incl_vars_subset_b _ _ Hfv_mc); reflexivity. }
    destruct (check_dag_refines_cert_sound
                (S (dag_node_count d_ir + 1)) allowed mc_init_ctx
                (RO_ScalarRefines ret_w (CE_BvConst ret_w 0%N) (CE_BvConst ret_w 0%N) false)
                lrat_pf (spine_src_evals d_ir) (spine_branch_conds d_ir)
                d_ir (CD_RetScalar ret_w e_mc) penv dummy_freeze_oracle dv_ir
                Hwfd_ir Hwfd_flat Hpenv_all Hctx_all
                (fun big H => spine_src_evals_wf allowed d_ir big Hwfd_ir H)
                (fun big H => spine_src_evals_ret penv dummy_freeze_oracle d_ir dv_ir big Hevd_ir H)
                (fun c H => spine_branch_conds_ret penv dummy_freeze_oracle d_ir dv_ir c Hevd_ir H)
                Hchk Hevd_ir) as (dv_tgt & Hevt_flat & Href_dv).
    cbn [eval_cfg_dag] in Hevt_flat; rewrite Heve_mc in Hevt_flat; inversion Hevt_flat; subst dv_tgt; exact Href_dv.
Qed.

Lemma cert_reg_name_not_bang : forall id, mc_starts_with_bang (cert_reg_name id) = false.
Proof. intro id; unfold cert_reg_name; reflexivity. Qed.

Lemma a64_hi_var_name_not_bang : forall nm, mc_starts_with_bang (a64_hi_var_name nm) = false.
Proof. intro nm; unfold a64_hi_var_name; reflexivity. Qed.

Theorem validate_mc_tle_with_cert_str_sound :
  forall {Pa : Params}
         (ir_tle : toplevel_entities typ (block typ * list (block typ)))
         (elf_str cert_str : string),
    validate_mc_tle_with_cert_str ir_tle elf_str cert_str = inr tt ->
    let ir_m := mcfg_of_tle (resolve_module_refs ir_tle) in
    let raw_elf := mc_string_to_bytes elf_str in
    exists mcert ir_defn,
      parse_mc_cert cert_str = inr mcert /\
      wf_mc_cert mcert = true /\
      In ir_defn (m_definitions ir_m) /\
      cert_fn_matches_raw_id (mc_fn_name mcert) (dc_name (df_prototype ir_defn)) = true /\
      let tenv := m_type_defs ir_m in
      let ir_cfg := convert_typ tenv (df_instrs ir_defn) in
      let ir_pnames := List.map cert_reg_name (args ir_cfg) in
      let arg_dtys := defn_arg_dtys tenv ir_defn in
      let s_pattrs := snd (dc_param_attrs (df_prototype ir_defn)) in
      match mc_calls mcert with
      | [] =>
          exists sl,
            elf64_extract_func raw_elf (mc_arch mcert) (mc_elf_kind mcert) (strip_leading_at (mc_fn_name mcert)) = inr sl /\
            efs_rvc sl = mc_rvc mcert /\
            match mc_arch mcert with
            | EA_Riscv64 =>
                exists insts,
                  decode_rv64_bytes (mc_rvc mcert) (efs_bytes sl) = inr insts /\
                  match mc_loop mcert with
                  | None =>
                      let rv_fuel := S (2 * List.length insts) in
                      forall (vs : list (@dvalue Pa)) rf0 mstk0,
                        Forall2 dvalue_has_dtyp vs arg_dtys ->
                        Forall2 (fun attrs v => existsb attr_is_noundef attrs = true -> dvalue_well_defined v = true)
                                s_pattrs vs ->
                        mc_valid_sp0 (rv_read_reg 2%N rf0) ->
                        rv_rf_matches_args (build_param_env ir_pnames vs) (mc_args mcert) rf0 ->
                        exists sigma_ir rf_end mstk_end,
                          wf_draw_strat sigma_ir /\
                          rv_exec_mem rv_fuel insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 = Some (rf_end, mstk_end) /\
                          rv_callee_saved_preserved rf0 rf_end /\
                          rf_end 1%N = rf0 1%N /\
                          (cfg_steps_to_ub sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
                           exists sigma_ir' env_out dv_ir,
                             cfg_steps_to_ret sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)
                               sigma_ir' env_out dv_ir /\
                             dvalue_refines dv_ir
                               (DVALUE_Base (@DVALUE_I Pa (mc_ret_width mcert)
                                  (rv_trunc_ret_val (mc_ret_width mcert) (rv_read_reg 10%N rf_end)))))
                  | Some ls =>
                      forall (vs : list (@dvalue Pa)) rf0 mstk0,
                        Forall2 dvalue_has_dtyp vs arg_dtys ->
                        Forall2 (fun attrs v => existsb attr_is_noundef attrs = true -> dvalue_well_defined v = true)
                                s_pattrs vs ->
                        mc_valid_sp0 (rv_read_reg 2%N rf0) ->
                        rv_rf_matches_args (build_param_env ir_pnames vs) (mc_args mcert) rf0 ->
                        rv_loop_sound_spec ir_cfg insts (mc_ret_width mcert) ls vs rf0 mstk0
                  end
            | EA_AArch64 =>
                mc_rvc mcert = false /\
                exists insts,
                  decode_a64_bytes (efs_bytes sl) = inr insts /\
                  match mc_loop mcert with
                  | None =>
                      let a64_fuel := S (2 * List.length insts) in
                      forall (vs : list (@dvalue Pa)) rf0 sp0 fl0 mstk0,
                        Forall2 dvalue_has_dtyp vs arg_dtys ->
                        Forall2 (fun attrs v => existsb attr_is_noundef attrs = true -> dvalue_well_defined v = true)
                                s_pattrs vs ->
                        mc_valid_sp0 sp0 ->
                        a64_rf_matches_args (build_param_env ir_pnames vs) (mc_args mcert) rf0 ->
                        exists sigma_ir rf_end fl_end mstk_end,
                          wf_draw_strat sigma_ir /\
                          a64_exec_mem a64_fuel insts 0%N sp0 rf0 sp0 fl0 mstk0 = Some (rf_end, sp0, fl_end, mstk_end) /\
                          a64_callee_saved_preserved rf0 rf_end /\
                          (cfg_steps_to_ub sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None) \/
                           exists sigma_ir' env_out dv_ir,
                             cfg_steps_to_ret sigma_ir (init_cfg_locals (args ir_cfg) vs) (denote_cfg ir_cfg None)
                               sigma_ir' env_out dv_ir /\
                             dvalue_refines dv_ir
                               (DVALUE_Base (@DVALUE_I Pa (mc_ret_width mcert)
                                  (rv_trunc_ret_val (mc_ret_width mcert) (a64_read_reg 0%N rf_end)))))
                  | Some ls =>
                      forall (vs : list (@dvalue Pa)) rf0 sp0 fl0 mstk0,
                        Forall2 dvalue_has_dtyp vs arg_dtys ->
                        Forall2 (fun attrs v => existsb attr_is_noundef attrs = true -> dvalue_well_defined v = true)
                                s_pattrs vs ->
                        mc_valid_sp0 sp0 ->
                        a64_rf_matches_args (build_param_env ir_pnames vs) (mc_args mcert) rf0 ->
                        a64_loop_sound_spec ir_cfg insts (mc_ret_width mcert) ls vs rf0 sp0 fl0 mstk0
                  end
            end
      | callees =>
          mc_loop mcert = None /\
          check_mc_callee_contracts tenv ir_m (mc_arch mcert) callees = true /\
          exists sl ci,
            elf64_extract_func_with_calls raw_elf (mc_arch mcert) (mc_elf_kind mcert)
              (strip_leading_at (mc_fn_name mcert))
              (List.map (fun c => mc_strip_leading_at (mcs_name c)) callees) = inr (sl, ci) /\
            efs_rvc sl = mc_rvc mcert /\
            match mc_arch mcert with
            | EA_Riscv64 =>
                exists insts,
                  decode_rv64_bytes_with_calls (mc_rvc mcert) (mc_elf_kind mcert) (efs_range_lo sl) ci (efs_bytes sl) = inr insts /\
                  forall (vs : list (@dvalue Pa)) rf0 mstk0,
                    Forall2 dvalue_has_dtyp vs arg_dtys ->
                    Forall2 (fun attrs v => existsb attr_is_noundef attrs = true -> dvalue_well_defined v = true)
                            s_pattrs vs ->
                    mc_valid_sp0_depth 2%nat (rv_read_reg 2%N rf0) ->
                    rv_rf_matches_args (build_param_env ir_pnames vs) (mc_args mcert) rf0 ->
                    rv_call_sound_spec ir_cfg insts (mc_ret_width mcert) callees vs rf0 mstk0
            | EA_AArch64 =>
                mc_rvc mcert = false /\
                exists insts,
                  decode_a64_bytes_with_calls (mc_elf_kind mcert) (efs_range_lo sl) ci (efs_bytes sl) = inr insts /\
                  forall (vs : list (@dvalue Pa)) rf0 sp0 fl0 mstk0,
                    Forall2 dvalue_has_dtyp vs arg_dtys ->
                    Forall2 (fun attrs v => existsb attr_is_noundef attrs = true -> dvalue_well_defined v = true)
                            s_pattrs vs ->
                    mc_valid_sp0_depth 2%nat sp0 ->
                    a64_rf_matches_args (build_param_env ir_pnames vs) (mc_args mcert) rf0 ->
                    a64_call_sound_spec ir_cfg insts (mc_ret_width mcert) callees vs rf0 sp0 fl0 mstk0
            end
      end.
Proof.
  intros Pa ir_tle elf_str cert_str Hval ir_m raw_elf.
  unfold validate_mc_tle_with_cert_str in Hval; fold ir_m raw_elf in Hval.
  destruct (parse_mc_cert cert_str) as [| mcert] eqn:Ecert; [discriminate Hval |].
  pose proof (parse_mc_cert_wf cert_str mcert Ecert) as Hwf_cert.
  unfold validate_mc_mcfg_with_cert in Hval.
  destruct (check_mc_cert_wf_diag mcert) as [| []]; [discriminate Hval |].
  destruct (mcfg_identified_typs_defined ir_m); cbn [negb] in Hval; [| discriminate Hval].
  destruct (find_unique_mc_defn_diag (mc_fn_name mcert) (m_definitions ir_m)) as [| ir_defn] eqn:Efnd;
    [discriminate Hval |].
  destruct (find_unique_mc_defn_diag_in _ _ _ Efnd) as [Hin_defn _].
  destruct (check_mc_ir_proto_contract_diag (m_type_defs ir_m) ir_defn mcert) as [| []] eqn:Hproto_d;
    [discriminate Hval |].
  pose proof (check_mc_ir_proto_contract_diag_sound _ _ _ Hproto_d) as Hproto.
  set (tenv := m_type_defs ir_m) in *.
  set (ir_cfg := convert_typ tenv (df_instrs ir_defn)) in *.
  set (ir_pnames := List.map cert_reg_name (args ir_cfg)) in *.
  set (arg_dtys := defn_arg_dtys tenv ir_defn) in *.
  set (s_pattrs := snd (dc_param_attrs (df_prototype ir_defn))) in *.
  assert (Hfn_m : cert_fn_matches_raw_id (mc_fn_name mcert) (dc_name (df_prototype ir_defn)) = true).
  { unfold check_mc_ir_proto_contract in Hproto; cbn zeta in Hproto.
    destruct (dc_param_attrs (df_prototype ir_defn)).
    apply andb_true_iff in Hproto as [Hfn _]; exact Hfn. }
  exists mcert, ir_defn.
  repeat split; try assumption.
  (* Unpack prototype invariants *)
  unfold check_mc_ir_proto_contract in Hproto; cbn zeta in Hproto; fold tenv ir_cfg ir_pnames in Hproto.
  destruct (dc_param_attrs (df_prototype ir_defn)) as [s_rattrs s_pattrs0] eqn:Edcpa.
  apply andb_true_iff in Hproto as [_ Hbody].
  destruct (dc_type (df_prototype ir_defn)) as [| | | | | | | | | | | ret_ty arg_tys [|] | | | | |] eqn:Edct;
    try discriminate Hbody.
  rewrite !andb_true_iff in Hbody.
  destruct Hbody as (((((((((((((_ & _) & _) & _) & _) & _) & _) & _) & Hnd_raw) & Hnd_sp) & Hmc_args) & Hhi_dis) & Hcomp) & _).
  apply no_dup_raw_ids_spec in Hnd_raw.
  apply no_dup_strings_spec in Hnd_sp.
  assert (Hlen_sp_s : List.length ir_pnames = List.length (args ir_cfg))
    by (unfold ir_pnames; apply List.length_map).
  assert (Hlen_ad : List.length arg_dtys = List.length (args ir_cfg)).
  { unfold arg_dtys, defn_arg_dtys; rewrite Edct; cbn match.
    destruct (check_mc_arg_specs_len _ _ _ _ _ Hmc_args) as [Hlp _].
    rewrite <- Hlp, Hlen_sp_s; reflexivity. }
  assert (Harg_dtys_eq : arg_dtys = List.map (typ_to_dtyp tenv) arg_tys)
    by (unfold arg_dtys, defn_arg_dtys; rewrite Edct; reflexivity).
  rewrite <- Harg_dtys_eq in Hcomp.
  assert (Hpu_ir : forall idx w0 pnm,
    In (idx, DTYPE_Base (DTYPE_I w0)) (param_idx_uses_cfg ir_cfg) ->
    nth_error ir_pnames idx = Some pnm ->
    In (pnm, w0) (used_src_param_vars ir_cfg)).
  { intros idx w0 pnm Hin Hpnm; unfold used_src_param_vars; apply in_flat_map.
    exists (idx, DTYPE_Base (DTYPE_I w0)); split; [exact Hin | fold ir_pnames; rewrite Hpnm; left; reflexivity]. }
  assert (Hnames_eq : List.map ras_name (mc_args mcert) = ir_pnames)
    by exact (check_mc_arg_specs_names _ _ _ _ _ Hmc_args).
  assert (Hcompat_args : forall idx sp,
    nth_error (mc_args mcert) idx = Some sp ->
    nth_error arg_dtys idx = Some (DTYPE_Base (DTYPE_I (ras_width sp))) /\
    nth_error ir_pnames idx = Some (ras_name sp)).
  { intros idx sp Hnth; rewrite Harg_dtys_eq; exact (check_mc_arg_specs_compat _ _ _ _ _ idx sp Hmc_args Hnth). }
  assert (Hnd_mc : NoDup (List.map ras_name (mc_args mcert)))
    by (rewrite Hnames_eq; exact Hnd_sp).
  assert (Hnb_ir : forall nm, In nm ir_pnames -> mc_starts_with_bang nm = false).
  { intros nm Hin; unfold ir_pnames in Hin; apply in_map_iff in Hin as [id [<- _]].
    exact (cert_reg_name_not_bang id). }
  destruct (mc_calls mcert) as [| c0 c_rest] eqn:Ecalls.
  {
  destruct (elf64_extract_func raw_elf (mc_arch mcert) (mc_elf_kind mcert) (strip_leading_at (mc_fn_name mcert)))
    as [| sl] eqn:Eelf; [discriminate Hval |].
  destruct (Bool.eqb (mc_rvc mcert) (efs_rvc sl)) eqn:Ervc; cbn [negb] in Hval; [| discriminate Hval].
  apply Bool.eqb_prop in Ervc.
  destruct (mc_build_init_ctx (mc_arch mcert) ir_pnames arg_dtys s_pattrs (mc_args mcert))
    as [seed_vars mc_init_ctx] eqn:Ectx_b.
  set (allowed := used_src_param_vars ir_cfg ++ seed_vars) in *.
  exists sl; split; [solve [exact Eelf | reflexivity] | split; [symmetry; exact Ervc |]].
  destruct (mc_loop mcert) as [ls |] eqn:Eloop.
  - (* Some ls: verified structured loop *)
    destruct (mc_arch mcert) eqn:Earch.
    + (* EA_Riscv64 loop *)
      destruct (decode_rv64_bytes (mc_rvc mcert) (efs_bytes sl)) as [| insts] eqn:Edec;
        [discriminate Hval |].
      exists insts; split; [reflexivity |].
      intros vs rf0 mstk0 Hty Hnu Hsp0 Hm.
      change (m_type_defs ir_m) with tenv in Hty, Hnu, Hm.
      change (convert_typ tenv (df_instrs ir_defn)) with ir_cfg in Hty, Hnu, Hm.
      change (List.map cert_reg_name (args ir_cfg)) with ir_pnames in Hty, Hnu, Hm.
      change (defn_arg_dtys tenv ir_defn) with arg_dtys in Hty, Hnu, Hm.
      change (snd (dc_param_attrs (df_prototype ir_defn))) with s_pattrs in Hty, Hnu, Hm.
      set (penv := build_param_env ir_pnames vs) in *.
      pose proof (used_src_param_vars_wf ir_cfg arg_dtys vs Hnd_sp Hlen_ad Hcomp Hty) as Hpenv_used.
      fold ir_pnames penv in Hpenv_used.
      assert (Hlen_sp_vs : List.length ir_pnames = List.length vs)
        by (pose proof (Forall2_length Hty); lia).
      unfold s_pattrs in *; cbn [snd] in *.
      unfold mc_build_init_ctx in Ectx_b.
      destruct (seed_proto_param_ctx ir_pnames arg_dtys s_pattrs0) as [proto_vars proto_ctx] eqn:Eseed.
      inversion Ectx_b; subst seed_vars mc_init_ctx; clear Ectx_b.
      pose proof (seed_proto_param_ctx_sound ir_pnames arg_dtys s_pattrs0 vs dummy_freeze_oracle
                    Hnd_sp Hlen_sp_vs Hty Hnu) as [Hpenv_proto Hctx_proto].
      rewrite Eseed in Hpenv_proto, Hctx_proto; cbn [fst snd] in Hpenv_proto, Hctx_proto.
      assert (Hmc_vars_all : forall sp, In sp (mc_args mcert) -> In (ras_name sp, ras_width sp) allowed).
      { intros sp Hsp; unfold allowed; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left.
        apply in_map_iff; exists sp; split; [reflexivity | exact Hsp]. }
      assert (Hmc_vars_wf :
        wf_param_env_for (List.map (fun sp => (ras_name sp, ras_width sp)) (mc_args mcert) ++ []) penv).
      { intros nm w Hin; rewrite app_nil_r in Hin; apply in_map_iff in Hin as [sp [Heq Hsp]]; inversion Heq; subst nm w.
        destruct (In_nth_error (mc_args mcert) sp Hsp) as [k Hnth].
        destruct (nth_error_Some (mc_args mcert) k) as [Hs1 _].
        destruct (Hm k sp ltac:(apply Hs1; congruence) Hnth) as [v [Hp _]].
        exists (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)); split; [exact Hp | right; exists v; reflexivity]. }
      assert (Hpenv_all : wf_param_env_for allowed penv).
      { intros nm w Hin; unfold allowed in Hin; apply in_app_iff in Hin as [Hu | Hs].
        - exact (Hpenv_used nm w Hu).
        - apply in_app_iff in Hs as [Hp | Hm_v]; [exact (Hpenv_proto nm w Hp) | exact (Hmc_vars_wf nm w Hm_v)]. }
      assert (Hctx0 : forall penv' : param_env Pa,
        (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv nm) ->
        ub_ctx_holds penv' dummy_freeze_oracle (proto_ctx ++ List.map (fun sp => UBA_ParamNoUndef (ras_name sp) (ras_width sp)) (mc_args mcert) ++ [])).
      { intros penv' Hag; rewrite app_nil_r; apply Forall_app; split.
        - assert (Hlk' : forall idx pnm v, nth_error ir_pnames idx = Some pnm -> nth_error vs idx = Some v -> penv' pnm = Some v).
          { intros idx pnm v Hnp Hnv.
            rewrite (Hag pnm (Hnb_ir pnm (nth_error_In _ _ Hnp))).
            destruct (build_param_env_nth ir_pnames vs idx pnm Hnd_sp Hlen_sp_vs Hnp) as [dv [Hdv Hbp]].
            rewrite Hnv in Hdv; inversion Hdv; subst dv; exact Hbp. }
          destruct (seed_proto_param_ctx_sound_aux ir_pnames arg_dtys s_pattrs0 vs penv' dummy_freeze_oracle Hty Hnu Hlk') as [_ Hcp].
          rewrite Eseed in Hcp; exact Hcp.
        - apply mc_args_noundef_ctx_sound with (rf0 := rf0).
          intros k sp Hlt Hnth; destruct (Hm k sp Hlt Hnth) as [v [Hp Hmt]].
          assert (Hinnm : In (ras_name sp) ir_pnames)
            by (rewrite <- Hnames_eq; apply in_map_iff; exists sp; split; [reflexivity | exact (nth_error_In _ _ Hnth)]).
          exists v; split; [rewrite (Hag _ (Hnb_ir _ Hinnm)); exact Hp | exact Hmt]. }
      exact (validate_mc_loop_rv64_sound ir_cfg allowed _ insts (mc_args mcert) (mc_ret_width mcert) ls (mc_lrat_proof mcert)
               arg_dtys vs penv rf0 mstk0 Hval (decode_rv64_bytes_no_word_mulh _ _ _ Edec) Hnd_raw Hnd_sp Hlen_sp_s Hlen_ad
               Hcomp Hty (fun idx w pnm Hin Hpnm => in_or_app _ _ _ (or_introl (Hpu_ir idx w pnm Hin Hpnm)))
               (fun _ _ => eq_refl) Hpenv_all Hctx0 Hmc_vars_all Hsp0 Hm).
    + (* EA_AArch64 loop *)
      destruct (mc_rvc mcert) eqn:Emrvc; [discriminate Hval |].
      split; [reflexivity |].
      destruct (decode_a64_bytes (efs_bytes sl)) as [| insts] eqn:Edec;
        [discriminate Hval |].
      exists insts; split; [reflexivity |].
      intros vs rf0 sp0 fl0 mstk0 Hty Hnu Hsp0 Hm.
      change (m_type_defs ir_m) with tenv in Hty, Hnu, Hm.
      change (convert_typ tenv (df_instrs ir_defn)) with ir_cfg in Hty, Hnu, Hm.
      change (List.map cert_reg_name (args ir_cfg)) with ir_pnames in Hty, Hnu, Hm.
      change (defn_arg_dtys tenv ir_defn) with arg_dtys in Hty, Hnu, Hm.
      change (snd (dc_param_attrs (df_prototype ir_defn))) with s_pattrs in Hty, Hnu, Hm.
      set (penv := build_param_env ir_pnames vs) in *.
      set (penv' := a64_extend_penv_with_hi penv (mc_args mcert) rf0) in *.
      assert (Hdis_orig : forall nm, In nm ir_pnames -> penv' nm = penv nm).
      { intros nm Hinnm; unfold penv', a64_extend_penv_with_hi; apply a64_extend_penv_at_orig.
        intros sp Hsp Heq; rewrite forallb_forall in Hhi_dis.
        pose proof (Hhi_dis sp Hsp) as Hneg; apply negb_true_iff in Hneg.
        assert (Hex : existsb (String.eqb (a64_hi_var_name (ras_name sp))) ir_pnames = true)
          by (apply existsb_exists; exists nm; split; [exact Hinnm | rewrite <- Heq; apply String.eqb_refl]).
        rewrite Hex in Hneg; discriminate Hneg. }
      assert (Hdis_args : forall sp, In sp (mc_args mcert) -> ~ In (a64_hi_var_name (ras_name sp)) (List.map ras_name (mc_args mcert))).
      { intros sp Hsp Hin; rewrite Hnames_eq in Hin; rewrite forallb_forall in Hhi_dis.
        pose proof (Hhi_dis sp Hsp) as Hneg; apply negb_true_iff in Hneg.
        assert (Hex : existsb (String.eqb (a64_hi_var_name (ras_name sp))) ir_pnames = true)
          by (apply existsb_exists; exists (a64_hi_var_name (ras_name sp)); split; [exact Hin | apply String.eqb_refl]).
        rewrite Hex in Hneg; discriminate Hneg. }
      pose proof (used_src_param_vars_wf ir_cfg arg_dtys vs Hnd_sp Hlen_ad Hcomp Hty) as Hpenv_used0.
      fold ir_pnames penv in Hpenv_used0.
      assert (Hpenv_used : wf_param_env_for (used_src_param_vars ir_cfg) penv').
      { intros nm w Hin; destruct (Hpenv_used0 nm w Hin) as [dv [Hp Hwf_dv]].
        assert (Hinnm : In nm ir_pnames).
        { unfold used_src_param_vars in Hin; apply in_flat_map in Hin as [[idx dt] [_ Hhere]].
          destruct dt as [[w0 | | | | | | | | | |] | |]; try contradiction Hhere.
          destruct (nth_error (List.map cert_reg_name (args ir_cfg)) idx) as [nm0 |] eqn:Hnth; [| contradiction Hhere].
          destruct Hhere as [Heq | []]; inversion Heq; subst nm0; fold ir_pnames in Hnth; exact (nth_error_In _ _ Hnth). }
        rewrite (Hdis_orig nm Hinnm); exists dv; split; assumption. }
      assert (Hlen_sp_vs : List.length ir_pnames = List.length vs)
        by (pose proof (Forall2_length Hty); lia).
      unfold s_pattrs in *; cbn [snd] in *.
      unfold mc_build_init_ctx in Ectx_b.
      destruct (seed_proto_param_ctx ir_pnames arg_dtys s_pattrs0) as [proto_vars proto_ctx] eqn:Eseed.
      inversion Ectx_b; subst seed_vars mc_init_ctx; clear Ectx_b.
      assert (Hlookup' : forall idx pnm v,
        nth_error ir_pnames idx = Some pnm -> nth_error vs idx = Some v -> penv' pnm = Some v).
      { intros idx pnm v Hnp Hnv.
        rewrite (Hdis_orig pnm (nth_error_In _ _ Hnp)).
        destruct (build_param_env_nth ir_pnames vs idx pnm Hnd_sp Hlen_sp_vs Hnp) as [dv [Hdv Hbp]].
        rewrite Hnv in Hdv; inversion Hdv; subst dv; exact Hbp. }
      pose proof (seed_proto_param_ctx_sound_aux ir_pnames arg_dtys s_pattrs0 vs penv' dummy_freeze_oracle Hty Hnu Hlookup')
        as [Hpenv_proto Hctx_proto].
      rewrite Eseed in Hpenv_proto, Hctx_proto; cbn [fst snd] in Hpenv_proto, Hctx_proto.
      assert (Hm' : a64_rf_matches_args penv' (mc_args mcert) rf0).
      { intros k sp Hlt Hnth; destruct (Hm k sp Hlt Hnth) as [v [Hp Hmt]].
        assert (Hinnm : In (ras_name sp) ir_pnames)
          by (rewrite <- Hnames_eq; apply in_map_iff; exists sp; split; [reflexivity | exact (nth_error_In _ _ Hnth)]).
        exists v; split; [rewrite (Hdis_orig _ Hinnm); exact Hp | exact Hmt]. }
      destruct (a64_hi_vars_wf_and_ctx penv dummy_freeze_oracle (mc_args mcert) rf0 Hnd_mc) as [Hpenv_hi Hctx_hi].
      fold penv' in Hpenv_hi, Hctx_hi.
      assert (Hmc_vars_all : forall sp, In sp (mc_args mcert) -> In (ras_name sp, ras_width sp) allowed).
      { intros sp Hsp; unfold allowed; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left.
        apply in_map_iff; exists sp; split; [reflexivity | exact Hsp]. }
      assert (Hhi_vars_all : forall nv, In nv (a64_hi_vars (mc_args mcert)) -> In nv allowed).
      { intros nv Hnv; unfold allowed; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; exact Hnv. }
      assert (Hmc_vars_wf : wf_param_env_for (List.map (fun sp => (ras_name sp, ras_width sp)) (mc_args mcert)) penv').
      { intros nm w Hin; apply in_map_iff in Hin as [sp [Heq Hsp]]; inversion Heq; subst nm w.
        destruct (In_nth_error (mc_args mcert) sp Hsp) as [k Hnth].
        destruct (nth_error_Some (mc_args mcert) k) as [Hs1 _].
        destruct (Hm' k sp ltac:(apply Hs1; congruence) Hnth) as [v [Hp _]].
        exists (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)); split; [exact Hp | right; exists v; reflexivity]. }
      assert (Hpenv_all : wf_param_env_for allowed penv').
      { intros nm w Hin; unfold allowed in Hin; apply in_app_iff in Hin as [Hu | Hs].
        - exact (Hpenv_used nm w Hu).
        - apply in_app_iff in Hs as [Hp | Hrest]; [exact (Hpenv_proto nm w Hp) |].
          apply in_app_iff in Hrest as [Hmv | Hhi]; [exact (Hmc_vars_wf nm w Hmv) | exact (Hpenv_hi nm w Hhi)]. }
      assert (Hctx0 : forall penv'' : param_env Pa,
        (forall nm, mc_starts_with_bang nm = false -> penv'' nm = penv' nm) ->
        ub_ctx_holds penv'' dummy_freeze_oracle
          (proto_ctx ++ List.map (fun sp => UBA_ParamNoUndef (ras_name sp) (ras_width sp)) (mc_args mcert)
                     ++ List.map (fun nv => UBA_ParamNoUndef (fst nv) (snd nv)) (a64_hi_vars (mc_args mcert)))).
      { intros penv'' Hag; apply Forall_app; split.
        - assert (Hlk'' : forall idx pnm v, nth_error ir_pnames idx = Some pnm -> nth_error vs idx = Some v -> penv'' pnm = Some v).
          { intros idx pnm v Hnp Hnv; rewrite (Hag pnm (Hnb_ir pnm (nth_error_In _ _ Hnp))); exact (Hlookup' idx pnm v Hnp Hnv). }
          destruct (seed_proto_param_ctx_sound_aux ir_pnames arg_dtys s_pattrs0 vs penv'' dummy_freeze_oracle Hty Hnu Hlk'') as [_ Hcp].
          rewrite Eseed in Hcp; exact Hcp.
        - apply Forall_app; split.
          + apply a64_args_noundef_ctx_sound with (rf0 := rf0).
            intros k sp Hlt Hnth; destruct (Hm' k sp Hlt Hnth) as [v [Hp Hmt]].
            assert (Hinnm : In (ras_name sp) ir_pnames)
              by (rewrite <- Hnames_eq; apply in_map_iff; exists sp; split; [reflexivity | exact (nth_error_In _ _ Hnth)]).
            exists v; split; [rewrite (Hag _ (Hnb_ir _ Hinnm)); exact Hp | exact Hmt].
          + unfold ub_ctx_holds in Hctx_hi |- *; rewrite Forall_forall in Hctx_hi |- *; intros ua Hin; pose proof (Hctx_hi ua Hin) as Hha.
            apply in_map_iff in Hin as [[nm w] [<- Hnv]]; unfold a64_hi_vars in Hnv; apply in_flat_map in Hnv as [sp [_ Hhere]].
            destruct (Pos.eqb (ras_width sp) 64%positive); [contradiction Hhere |].
            destruct Hhere as [Heq | []]; inversion Heq; subst nm w; cbn [fst snd] in *.
            intros dv Hdv; rewrite (Hag _ (a64_hi_var_name_not_bang (ras_name sp))) in Hdv; exact (Hha dv Hdv). }
      assert (Hnames_p : forall sp, In sp (mc_args mcert) -> penv' (ras_name sp) = penv (ras_name sp))
        by (intros sp Hsp; apply Hdis_orig; rewrite <- Hnames_eq; apply in_map_iff; exists sp; split; [reflexivity | exact Hsp]).
      exact (validate_mc_loop_a64_sound ir_cfg allowed _ insts (mc_args mcert) (mc_ret_width mcert) ls (mc_lrat_proof mcert)
               arg_dtys vs penv' rf0 sp0 fl0 mstk0 Hval (decode_a64_bytes_valid _ _ Edec) Hnd_raw Hnd_sp Hlen_sp_s Hlen_ad
               Hcomp Hty (fun idx w pnm Hin Hpnm => in_or_app _ _ _ (or_introl (Hpu_ir idx w pnm Hin Hpnm)))
               Hdis_orig (fun _ _ => eq_refl) Hpenv_all Hctx0 Hmc_vars_all Hhi_vars_all Hnd_mc Hdis_args Hnames_p Hsp0 Hm).
  - (* None: existing DAG pipeline *)
    destruct (mc_decode_and_summarize (mc_arch mcert) (mc_rvc mcert) (efs_bytes sl) (mc_args mcert) (mc_ret_width mcert))
      as [| d_mc] eqn:Edec_s; [discriminate Hval |].
    destruct (flatten_mc_dag_to_expr (mc_ret_width mcert) d_mc) as [| e_mc] eqn:Eflat;
      [discriminate Hval |].
    destruct (summarize_cfg_dag_with_uas (fun _ => []) false ir_cfg ir_pnames)
      as [d_ir |] eqn:Esum_ir; [| discriminate Hval].
    pose proof (summarize_cfg_dag_with_uas_wf (fun _ => []) false ir_cfg ir_pnames (used_src_param_vars ir_cfg) d_ir Hpu_ir Esum_ir)
      as Hwfd_ir0.
    assert (Hwfd_ir : wf_cfg_dag allowed d_ir = true)
      by (eapply wf_cfg_dag_mono; [intros u Hu; unfold allowed; apply in_app_iff; left; exact Hu | exact Hwfd_ir0]).
    assert (Hchk :
      (match src_dag_to_expr (mc_ret_width mcert) d_ir with
       | Some e_ir => check_mc_expr_refines mc_init_ctx allowed e_ir e_mc (mc_lrat_proof mcert)
       | None =>
           check_dag_refines_cert (S (dag_node_count d_ir + 1)) allowed mc_init_ctx
             (RO_ScalarRefines (mc_ret_width mcert) (CE_BvConst (mc_ret_width mcert) 0%N) (CE_BvConst (mc_ret_width mcert) 0%N) false)
             (mc_lrat_proof mcert) (spine_src_evals d_ir) (spine_branch_conds d_ir) d_ir (CD_RetScalar (mc_ret_width mcert) e_mc)
       end) = true).
    { destruct (src_dag_to_expr (mc_ret_width mcert) d_ir) as [e_ir |].
      - destruct (check_mc_expr_refines_diag mc_init_ctx allowed e_ir e_mc (mc_lrat_proof mcert))
          as [| []] eqn:Hchk_d; [discriminate Hval | exact (check_mc_expr_refines_diag_sound _ _ _ _ _ Hchk_d)].
      - destruct (check_dag_refines_cert (S (dag_node_count d_ir + 1)) allowed mc_init_ctx
                    (RO_ScalarRefines (mc_ret_width mcert) (CE_BvConst (mc_ret_width mcert) 0%N) (CE_BvConst (mc_ret_width mcert) 0%N) false)
                    (mc_lrat_proof mcert) (spine_src_evals d_ir) (spine_branch_conds d_ir) d_ir (CD_RetScalar (mc_ret_width mcert) e_mc));
          [reflexivity | destruct (mc_lrat_proof mcert); discriminate Hval]. }
    cbn zeta.
    destruct (mc_arch mcert) eqn:Earch; unfold mc_decode_and_summarize in Edec_s.
    + (* EA_Riscv64 *)
    destruct (decode_rv64_bytes (mc_rvc mcert) (efs_bytes sl)) as [| insts] eqn:Edec;
      [discriminate Edec_s |].
    rewrite length_tr_eq in Edec_s.
    set (rv_fuel := S (2 * List.length insts)) in *.
    destruct (summarize_rv64_dag rv_fuel insts (mc_args mcert) (mc_ret_width mcert))
      as [| d_mc0] eqn:Esum_mc; [discriminate Edec_s |].
    inversion Edec_s; subst d_mc0; clear Edec_s.
    exists insts; split; [reflexivity |].
    intros vs rf0 mstk0 Hty Hnu Hsp0 Hm.
    change (m_type_defs ir_m) with tenv in Hty, Hnu, Hm.
    change (convert_typ tenv (df_instrs ir_defn)) with ir_cfg in Hty, Hnu, Hm.
    change (List.map cert_reg_name (args ir_cfg)) with ir_pnames in Hty, Hnu, Hm.
    change (defn_arg_dtys tenv ir_defn) with arg_dtys in Hty, Hnu, Hm.
    change (snd (dc_param_attrs (df_prototype ir_defn))) with s_pattrs in Hty, Hnu, Hm.
    set (penv := build_param_env ir_pnames vs) in *.
    pose proof (used_src_param_vars_wf ir_cfg arg_dtys vs Hnd_sp Hlen_ad Hcomp Hty) as Hpenv_used.
    fold ir_pnames penv in Hpenv_used.
    assert (Hlen_sp_vs : List.length ir_pnames = List.length vs)
      by (pose proof (Forall2_length Hty); lia).
    unfold s_pattrs in *; cbn [snd] in *.
    unfold mc_build_init_ctx in Ectx_b.
    destruct (seed_proto_param_ctx ir_pnames arg_dtys s_pattrs0) as [proto_vars proto_ctx] eqn:Eseed.
    inversion Ectx_b; subst seed_vars mc_init_ctx; clear Ectx_b.
    pose proof (seed_proto_param_ctx_sound ir_pnames arg_dtys s_pattrs0 vs dummy_freeze_oracle
                  Hnd_sp Hlen_sp_vs Hty Hnu) as [Hpenv_proto Hctx_proto].
    rewrite Eseed in Hpenv_proto, Hctx_proto; cbn [fst snd] in Hpenv_proto, Hctx_proto.
    pose proof (mc_args_noundef_ctx_sound penv dummy_freeze_oracle (mc_args mcert) rf0 Hm) as Hctx_mc.
    assert (Hctx_all : ub_ctx_holds penv dummy_freeze_oracle
                         (proto_ctx ++ List.map (fun sp => UBA_ParamNoUndef (ras_name sp) (ras_width sp)) (mc_args mcert) ++ []))
      by (rewrite app_nil_r; apply Forall_app; split; assumption).
    assert (Hmc_vars_all :
      forall sp, In sp (mc_args mcert) -> In (ras_name sp, ras_width sp) allowed).
    { intros sp Hsp; unfold allowed; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left.
      apply in_map_iff; exists sp; split; [reflexivity | exact Hsp]. }
    assert (Hmc_vars_wf :
      wf_param_env_for (List.map (fun sp => (ras_name sp, ras_width sp)) (mc_args mcert) ++ []) penv).
    { intros nm w Hin; rewrite app_nil_r in Hin; apply in_map_iff in Hin as [sp [Heq Hsp]]; inversion Heq; subst nm w.
      destruct (In_nth_error (mc_args mcert) sp Hsp) as [k Hnth].
      destruct (nth_error_Some (mc_args mcert) k) as [Hs1 _].
      destruct (Hm k sp ltac:(apply Hs1; congruence) Hnth) as [v [Hp _]].
      exists (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)); split; [exact Hp | right; exists v; reflexivity]. }
    assert (Hpenv_all : wf_param_env_for allowed penv).
    { intros nm w Hin; unfold allowed in Hin; apply in_app_iff in Hin as [Hu | Hs].
      - exact (Hpenv_used nm w Hu).
      - apply in_app_iff in Hs as [Hp | Hm_v]; [exact (Hpenv_proto nm w Hp) | exact (Hmc_vars_wf nm w Hm_v)]. }
    pose proof (decode_rv64_bytes_no_word_mulh (mc_rvc mcert) (efs_bytes sl) insts Edec) as Hnmul.
    pose proof (summarize_rv64_dag_wf rv_fuel insts (mc_args mcert) (mc_ret_width mcert) d_mc Hnmul Esum_mc)
      as Hwfd_mc0.
    assert (Hwfd_mc : wf_cfg_dag allowed d_mc = true).
    { eapply wf_cfg_dag_mono; [| exact Hwfd_mc0].
      intros u Hu; apply in_map_iff in Hu as [sp [<- Hsp]]; exact (Hmc_vars_all sp Hsp). }
    destruct (summarize_rv64_dag_sound rv_fuel (mc_rvc mcert) (efs_bytes sl) insts
                (mc_args mcert) (mc_ret_width mcert) d_mc penv dummy_freeze_oracle rf0 mstk0
                Edec Esum_mc Hsp0 Hm)
      as (rf_end & mstk_end & Hexec & Hcs & Hra & Hevd_mc).
    destruct (summarize_src_dag_with_uas_sound (fun _ => []) ir_cfg ir_pnames arg_dtys vs
                dummy_freeze_oracle d_ir Hnd_raw Hnd_sp Hlen_sp_s Hlen_ad Hcomp Hty Esum_ir)
      as (sigma_ir & Hwfsig & Hsrc_out).
    exists sigma_ir, rf_end, mstk_end;
      split; [exact Hwfsig | split; [exact Hexec | split; [exact Hcs | split; [exact Hra |]]]].
    destruct Hsrc_out as [[Hub_s _] | (sigma_ir' & env_out & dv_ir & Hevd_ir & Hst_ret)].
    * left; exact Hub_s.
    * right; exists sigma_ir', env_out, dv_ir; split; [exact Hst_ret |].
      eapply validate_mc_core_refine_sound;
        [exact Eflat | exact Hchk | exact Hwfd_ir | exact Hwfd_mc | exact Hpenv_all | exact Hctx_all | exact Hevd_mc | exact Hevd_ir].
    + (* EA_AArch64 *)
    destruct (mc_rvc mcert) eqn:Emrvc; [discriminate Edec_s |].
    split; [reflexivity |].
    destruct (decode_a64_bytes (efs_bytes sl)) as [| insts] eqn:Edec;
      [discriminate Edec_s |].
    rewrite length_tr_eq in Edec_s.
    set (a64_fuel := S (2 * List.length insts)) in *.
    destruct (summarize_a64_dag a64_fuel insts (mc_args mcert) (mc_ret_width mcert))
      as [| d_mc0] eqn:Esum_mc; [discriminate Edec_s |].
    inversion Edec_s; subst d_mc0; clear Edec_s.
    exists insts; split; [reflexivity |].
    intros vs rf0 sp0 fl0 mstk0 Hty Hnu Hsp0 Hm.
    change (m_type_defs ir_m) with tenv in Hty, Hnu, Hm.
    change (convert_typ tenv (df_instrs ir_defn)) with ir_cfg in Hty, Hnu, Hm.
    change (List.map cert_reg_name (args ir_cfg)) with ir_pnames in Hty, Hnu, Hm.
    change (defn_arg_dtys tenv ir_defn) with arg_dtys in Hty, Hnu, Hm.
    change (snd (dc_param_attrs (df_prototype ir_defn))) with s_pattrs in Hty, Hnu, Hm.
    set (penv := build_param_env ir_pnames vs) in *.
    set (penv' := a64_extend_penv_with_hi penv (mc_args mcert) rf0) in *.
    assert (Hdis_orig : forall nm, In nm ir_pnames -> penv' nm = penv nm).
    { intros nm Hinnm; unfold penv', a64_extend_penv_with_hi; apply a64_extend_penv_at_orig.
      intros sp Hsp Heq; rewrite forallb_forall in Hhi_dis.
      pose proof (Hhi_dis sp Hsp) as Hneg; apply negb_true_iff in Hneg.
      assert (Hex : existsb (String.eqb (a64_hi_var_name (ras_name sp))) ir_pnames = true)
        by (apply existsb_exists; exists nm; split; [exact Hinnm | rewrite <- Heq; apply String.eqb_refl]).
      rewrite Hex in Hneg; discriminate Hneg. }
    assert (Hdis_args : forall sp, In sp (mc_args mcert) -> ~ In (a64_hi_var_name (ras_name sp)) (List.map ras_name (mc_args mcert))).
    { intros sp Hsp Hin; rewrite Hnames_eq in Hin; rewrite forallb_forall in Hhi_dis.
      pose proof (Hhi_dis sp Hsp) as Hneg; apply negb_true_iff in Hneg.
      assert (Hex : existsb (String.eqb (a64_hi_var_name (ras_name sp))) ir_pnames = true)
        by (apply existsb_exists; exists (a64_hi_var_name (ras_name sp)); split; [exact Hin | apply String.eqb_refl]).
      rewrite Hex in Hneg; discriminate Hneg. }
    pose proof (used_src_param_vars_wf ir_cfg arg_dtys vs Hnd_sp Hlen_ad Hcomp Hty) as Hpenv_used0.
    fold ir_pnames penv in Hpenv_used0.
    assert (Hpenv_used : wf_param_env_for (used_src_param_vars ir_cfg) penv').
    { intros nm w Hin; destruct (Hpenv_used0 nm w Hin) as [dv [Hp Hwf_dv]].
      assert (Hinnm : In nm ir_pnames).
      { unfold used_src_param_vars in Hin; apply in_flat_map in Hin as [[idx dt] [_ Hhere]].
        destruct dt as [[w0 | | | | | | | | | |] | |]; try contradiction Hhere.
        destruct (nth_error (List.map cert_reg_name (args ir_cfg)) idx) as [nm0 |] eqn:Hnth; [| contradiction Hhere].
        destruct Hhere as [Heq | []]; inversion Heq; subst nm0; fold ir_pnames in Hnth; exact (nth_error_In _ _ Hnth). }
      rewrite (Hdis_orig nm Hinnm); exists dv; split; assumption. }
    assert (Hlen_sp_vs : List.length ir_pnames = List.length vs)
      by (pose proof (Forall2_length Hty); lia).
    unfold s_pattrs in *; cbn [snd] in *.
    unfold mc_build_init_ctx in Ectx_b.
    destruct (seed_proto_param_ctx ir_pnames arg_dtys s_pattrs0) as [proto_vars proto_ctx] eqn:Eseed.
    inversion Ectx_b; subst seed_vars mc_init_ctx; clear Ectx_b.
    assert (Hlookup' : forall idx pnm v,
      nth_error ir_pnames idx = Some pnm -> nth_error vs idx = Some v -> penv' pnm = Some v).
    { intros idx pnm v Hnp Hnv.
      rewrite (Hdis_orig pnm (nth_error_In _ _ Hnp)).
      destruct (build_param_env_nth ir_pnames vs idx pnm Hnd_sp Hlen_sp_vs Hnp) as [dv [Hdv Hbp]].
      rewrite Hnv in Hdv; inversion Hdv; subst dv; exact Hbp. }
    pose proof (seed_proto_param_ctx_sound_aux ir_pnames arg_dtys s_pattrs0 vs penv' dummy_freeze_oracle Hty Hnu Hlookup')
      as [Hpenv_proto Hctx_proto].
    rewrite Eseed in Hpenv_proto, Hctx_proto; cbn [fst snd] in Hpenv_proto, Hctx_proto.
    assert (Hm' : a64_rf_matches_args penv' (mc_args mcert) rf0).
    { intros k sp Hlt Hnth; destruct (Hm k sp Hlt Hnth) as [v [Hp Hmt]].
      assert (Hinnm : In (ras_name sp) ir_pnames)
        by (rewrite <- Hnames_eq; apply in_map_iff; exists sp; split; [reflexivity | exact (nth_error_In _ _ Hnth)]).
      exists v; split; [rewrite (Hdis_orig _ Hinnm); exact Hp | exact Hmt]. }
    pose proof (a64_args_noundef_ctx_sound penv' dummy_freeze_oracle (mc_args mcert) rf0 Hm') as Hctx_mc.
    destruct (a64_hi_vars_wf_and_ctx penv dummy_freeze_oracle (mc_args mcert) rf0 Hnd_mc) as [Hpenv_hi Hctx_hi].
    fold penv' in Hpenv_hi, Hctx_hi.
    assert (Hctx_all : ub_ctx_holds penv' dummy_freeze_oracle
                         (proto_ctx ++ List.map (fun sp => UBA_ParamNoUndef (ras_name sp) (ras_width sp)) (mc_args mcert)
                                    ++ List.map (fun nv => UBA_ParamNoUndef (fst nv) (snd nv)) (a64_hi_vars (mc_args mcert))))
      by (apply Forall_app; split; [exact Hctx_proto | apply Forall_app; split; assumption]).
    assert (Hmc_vars_wf :
      wf_param_env_for (List.map (fun sp => (ras_name sp, ras_width sp)) (mc_args mcert)) penv').
    { intros nm w Hin; apply in_map_iff in Hin as [sp [Heq Hsp]]; inversion Heq; subst nm w.
      destruct (In_nth_error (mc_args mcert) sp Hsp) as [k Hnth].
      destruct (nth_error_Some (mc_args mcert) k) as [Hs1 _].
      destruct (Hm' k sp ltac:(apply Hs1; congruence) Hnth) as [v [Hp _]].
      exists (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)); split; [exact Hp | right; exists v; reflexivity]. }
    assert (Hpenv_all : wf_param_env_for allowed penv').
    { intros nm w Hin; unfold allowed in Hin; apply in_app_iff in Hin as [Hu | Hs].
      - exact (Hpenv_used nm w Hu).
      - apply in_app_iff in Hs as [Hp | Hrest]; [exact (Hpenv_proto nm w Hp) |].
        apply in_app_iff in Hrest as [Hmv | Hhi]; [exact (Hmc_vars_wf nm w Hmv) | exact (Hpenv_hi nm w Hhi)]. }
    pose proof (decode_a64_bytes_valid (efs_bytes sl) insts Edec) as Hval_a64.
    pose proof (summarize_a64_dag_wf a64_fuel insts (mc_args mcert) (mc_ret_width mcert) d_mc Hval_a64 Esum_mc)
      as Hwfd_mc0.
    assert (Hwfd_mc : wf_cfg_dag allowed d_mc = true).
    { eapply wf_cfg_dag_mono; [| exact Hwfd_mc0].
      intros u Hu; apply in_app_iff in Hu as [Hu1 | Hu2];
        unfold allowed; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff;
        [left; exact Hu1 | right; exact Hu2]. }
    destruct (summarize_a64_dag_sound a64_fuel (efs_bytes sl) insts (mc_args mcert) (mc_ret_width mcert)
                d_mc penv dummy_freeze_oracle rf0 sp0 fl0 mstk0 Edec Hnd_mc Hdis_args Esum_mc Hsp0 Hm)
      as (rf_end & fl_end & mstk_end & Hexec & Hcs & Hevd_mc).
    fold penv' in Hevd_mc.
    destruct (summarize_src_dag_with_uas_sound (fun _ => []) ir_cfg ir_pnames arg_dtys vs
                dummy_freeze_oracle d_ir Hnd_raw Hnd_sp Hlen_sp_s Hlen_ad Hcomp Hty Esum_ir)
      as (sigma_ir & Hwfsig & Hsrc_out).
    exists sigma_ir, rf_end, fl_end, mstk_end;
      split; [exact Hwfsig | split; [exact Hexec | split; [exact Hcs |]]].
    destruct Hsrc_out as [[Hub_s _] | (sigma_ir' & env_out & dv_ir & Hevd_ir & Hst_ret)].
    * left; exact Hub_s.
    * right; exists sigma_ir', env_out, dv_ir; split; [exact Hst_ret |].
      assert (Hevd_ir' : eval_cfg_dag penv' dummy_freeze_oracle d_ir = DO_Ret dv_ir).
      { rewrite <- Hevd_ir; eapply eval_cfg_dag_penv_agree; [exact Hwfd_ir0 |].
        intros nm w Hin; unfold used_src_param_vars in Hin; apply in_flat_map in Hin as [[idx dt] [_ Hhere]].
        destruct dt as [[w0 | | | | | | | | | |] | |]; try contradiction Hhere.
        destruct (nth_error (List.map cert_reg_name (args ir_cfg)) idx) as [nm0 |] eqn:Hnth; [| contradiction Hhere].
        destruct Hhere as [Heq | []]; inversion Heq; subst nm0; fold ir_pnames in Hnth.
        exact (Hdis_orig nm (nth_error_In _ _ Hnth)). }
      eapply validate_mc_core_refine_sound;
        [exact Eflat | exact Hchk | exact Hwfd_ir | exact Hwfd_mc | exact Hpenv_all | exact Hctx_all | exact Hevd_mc | exact Hevd_ir'].
  }
  {
    cbn iota in Hval.
    destruct (mc_loop mcert) eqn:Eloop; [discriminate Hval |].
    cbn iota in Hval.
    destruct (check_mc_callee_contracts_diag tenv ir_m (mc_arch mcert) (c0 :: c_rest)) as [| []] eqn:Hcal_d;
      [discriminate Hval |].
    pose proof (check_mc_callee_contracts_diag_sound _ _ _ _ Hcal_d) as Hcal.
    destruct (elf64_extract_func_with_calls raw_elf (mc_arch mcert) (mc_elf_kind mcert)
                (strip_leading_at (mc_fn_name mcert))
                (List.map (fun c => mc_strip_leading_at (mcs_name c)) (c0 :: c_rest)))
      as [| [sl ci]] eqn:Eelf; [discriminate Hval |].
    destruct (Bool.eqb (mc_rvc mcert) (efs_rvc sl)) eqn:Ervc; cbn [negb] in Hval; [| discriminate Hval].
    apply Bool.eqb_prop in Ervc.
    destruct (mc_build_init_ctx (mc_arch mcert) ir_pnames arg_dtys s_pattrs (mc_args mcert))
      as [seed_vars mc_init_ctx] eqn:Ectx_b.
    set (allowed := used_src_param_vars ir_cfg ++ seed_vars) in *.
    split; [reflexivity | split; [solve [exact Hcal | reflexivity] | exists sl, ci; split; [solve [exact Eelf | reflexivity] | split; [symmetry; exact Ervc |]]]].
    destruct (mc_arch mcert) eqn:Earch.
    - (* EA_Riscv64 calls *)
      destruct (decode_rv64_bytes_with_calls (mc_rvc mcert) (mc_elf_kind mcert) (efs_range_lo sl) ci (efs_bytes sl))
        as [| insts] eqn:Edec; [discriminate Hval |].
      exists insts; split; [reflexivity |].
      intros vs rf0 mstk0 Hty Hnu Hsp0 Hm.
      change (m_type_defs ir_m) with tenv in Hty, Hnu, Hm.
      change (convert_typ tenv (df_instrs ir_defn)) with ir_cfg in Hty, Hnu, Hm.
      change (List.map cert_reg_name (args ir_cfg)) with ir_pnames in Hty, Hnu, Hm.
      change (defn_arg_dtys tenv ir_defn) with arg_dtys in Hty, Hnu, Hm.
      change (snd (dc_param_attrs (df_prototype ir_defn))) with s_pattrs in Hty, Hnu, Hm.
      set (penv := build_param_env ir_pnames vs) in *.
      pose proof (used_src_param_vars_wf ir_cfg arg_dtys vs Hnd_sp Hlen_ad Hcomp Hty) as Hpenv_used.
      fold ir_pnames penv in Hpenv_used.
      assert (Hlen_sp_vs : List.length ir_pnames = List.length vs)
        by (pose proof (Forall2_length Hty); lia).
      unfold s_pattrs in *; cbn [snd] in *.
      unfold mc_build_init_ctx in Ectx_b.
      destruct (seed_proto_param_ctx ir_pnames arg_dtys s_pattrs0) as [proto_vars proto_ctx] eqn:Eseed.
      inversion Ectx_b; subst seed_vars mc_init_ctx; clear Ectx_b.
      pose proof (seed_proto_param_ctx_sound ir_pnames arg_dtys s_pattrs0 vs dummy_freeze_oracle
                    Hnd_sp Hlen_sp_vs Hty Hnu) as [Hpenv_proto Hctx_proto].
      rewrite Eseed in Hpenv_proto, Hctx_proto; cbn [fst snd] in Hpenv_proto, Hctx_proto.
      assert (Hmc_vars_all : forall sp, In sp (mc_args mcert) -> In (ras_name sp, ras_width sp) allowed).
      { intros sp Hsp; unfold allowed; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left.
        apply in_map_iff; exists sp; split; [reflexivity | exact Hsp]. }
      assert (Hmc_vars_wf :
        wf_param_env_for (List.map (fun sp => (ras_name sp, ras_width sp)) (mc_args mcert) ++ []) penv).
      { intros nm w Hin; rewrite app_nil_r in Hin; apply in_map_iff in Hin as [sp [Heq Hsp]]; inversion Heq; subst nm w.
        destruct (In_nth_error (mc_args mcert) sp Hsp) as [k Hnth].
        destruct (nth_error_Some (mc_args mcert) k) as [Hs1 _].
        destruct (Hm k sp ltac:(apply Hs1; congruence) Hnth) as [v [Hp _]].
        exists (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)); split; [exact Hp | right; exists v; reflexivity]. }
      assert (Hpenv_all : wf_param_env_for allowed penv).
      { intros nm w Hin; unfold allowed in Hin; apply in_app_iff in Hin as [Hu | Hs].
        - exact (Hpenv_used nm w Hu).
        - apply in_app_iff in Hs as [Hp | Hm_v]; [exact (Hpenv_proto nm w Hp) | exact (Hmc_vars_wf nm w Hm_v)]. }
      assert (Hctx0 : forall penv' : param_env Pa,
        (forall nm, mc_starts_with_bang nm = false -> penv' nm = penv nm) ->
        ub_ctx_holds penv' dummy_freeze_oracle (proto_ctx ++ List.map (fun sp => UBA_ParamNoUndef (ras_name sp) (ras_width sp)) (mc_args mcert) ++ [])).
      { intros penv' Hag; rewrite app_nil_r; apply Forall_app; split.
        - assert (Hlk' : forall idx pnm v, nth_error ir_pnames idx = Some pnm -> nth_error vs idx = Some v -> penv' pnm = Some v).
          { intros idx pnm v Hnp Hnv.
            rewrite (Hag pnm (Hnb_ir pnm (nth_error_In _ _ Hnp))).
            destruct (build_param_env_nth ir_pnames vs idx pnm Hnd_sp Hlen_sp_vs Hnp) as [dv [Hdv Hbp]].
            rewrite Hnv in Hdv; inversion Hdv; subst dv; exact Hbp. }
          destruct (seed_proto_param_ctx_sound_aux ir_pnames arg_dtys s_pattrs0 vs penv' dummy_freeze_oracle Hty Hnu Hlk') as [_ Hcp].
          rewrite Eseed in Hcp; exact Hcp.
        - apply mc_args_noundef_ctx_sound with (rf0 := rf0).
          intros k sp Hlt Hnth; destruct (Hm k sp Hlt Hnth) as [v [Hp Hmt]].
          assert (Hinnm : In (ras_name sp) ir_pnames)
            by (rewrite <- Hnames_eq; apply in_map_iff; exists sp; split; [reflexivity | exact (nth_error_In _ _ Hnth)]).
          exists v; split; [rewrite (Hag _ (Hnb_ir _ Hinnm)); exact Hp | exact Hmt]. }
      exact (validate_mc_call_rv64_sound ir_cfg allowed _ insts (mc_args mcert) (mc_ret_width mcert) (c0 :: c_rest) (mc_lrat_proof mcert)
               arg_dtys vs penv rf0 mstk0 Hval Hnd_raw Hnd_sp Hlen_sp_s Hlen_ad
               Hcomp Hty Hcompat_args
               (fun idx w pnm Hin Hpnm => in_or_app _ _ _ (or_introl (Hpu_ir idx w pnm Hin Hpnm)))
               (fun _ _ => eq_refl) Hpenv_all Hctx0 Hmc_vars_all Hsp0 Hm).
    - (* EA_AArch64 calls *)
      destruct (mc_rvc mcert) eqn:Emrvc; [discriminate Hval |].
      split; [reflexivity |].
      destruct (decode_a64_bytes_with_calls (mc_elf_kind mcert) (efs_range_lo sl) ci (efs_bytes sl))
        as [| insts] eqn:Edec; [discriminate Hval |].
      exists insts; split; [reflexivity |].
      intros vs rf0 sp0 fl0 mstk0 Hty Hnu Hsp0 Hm.
      change (m_type_defs ir_m) with tenv in Hty, Hnu, Hm.
      change (convert_typ tenv (df_instrs ir_defn)) with ir_cfg in Hty, Hnu, Hm.
      change (List.map cert_reg_name (args ir_cfg)) with ir_pnames in Hty, Hnu, Hm.
      change (defn_arg_dtys tenv ir_defn) with arg_dtys in Hty, Hnu, Hm.
      change (snd (dc_param_attrs (df_prototype ir_defn))) with s_pattrs in Hty, Hnu, Hm.
      set (penv := build_param_env ir_pnames vs) in *.
      set (penv' := a64_extend_penv_with_hi penv (mc_args mcert) rf0) in *.
      assert (Hdis_orig : forall nm, In nm ir_pnames -> penv' nm = penv nm).
      { intros nm Hinnm; unfold penv', a64_extend_penv_with_hi; apply a64_extend_penv_at_orig.
        intros sp Hsp Heq; rewrite forallb_forall in Hhi_dis.
        pose proof (Hhi_dis sp Hsp) as Hneg; apply negb_true_iff in Hneg.
        assert (Hex : existsb (String.eqb (a64_hi_var_name (ras_name sp))) ir_pnames = true)
          by (apply existsb_exists; exists nm; split; [exact Hinnm | rewrite <- Heq; apply String.eqb_refl]).
        rewrite Hex in Hneg; discriminate Hneg. }
      assert (Hdis_args : forall sp, In sp (mc_args mcert) -> ~ In (a64_hi_var_name (ras_name sp)) (List.map ras_name (mc_args mcert))).
      { intros sp Hsp Hin; rewrite Hnames_eq in Hin; rewrite forallb_forall in Hhi_dis.
        pose proof (Hhi_dis sp Hsp) as Hneg; apply negb_true_iff in Hneg.
        assert (Hex : existsb (String.eqb (a64_hi_var_name (ras_name sp))) ir_pnames = true)
          by (apply existsb_exists; exists (a64_hi_var_name (ras_name sp)); split; [exact Hin | apply String.eqb_refl]).
        rewrite Hex in Hneg; discriminate Hneg. }
      pose proof (used_src_param_vars_wf ir_cfg arg_dtys vs Hnd_sp Hlen_ad Hcomp Hty) as Hpenv_used0.
      fold ir_pnames penv in Hpenv_used0.
      assert (Hpenv_used : wf_param_env_for (used_src_param_vars ir_cfg) penv').
      { intros nm w Hin; destruct (Hpenv_used0 nm w Hin) as [dv [Hp Hwf_dv]].
        assert (Hinnm : In nm ir_pnames).
        { unfold used_src_param_vars in Hin; apply in_flat_map in Hin as [[idx dt] [_ Hhere]].
          destruct dt as [[w0 | | | | | | | | | |] | |]; try contradiction Hhere.
          destruct (nth_error (List.map cert_reg_name (args ir_cfg)) idx) as [nm0 |] eqn:Hnth; [| contradiction Hhere].
          destruct Hhere as [Heq | []]; inversion Heq; subst nm0; fold ir_pnames in Hnth; exact (nth_error_In _ _ Hnth). }
        rewrite (Hdis_orig nm Hinnm); exists dv; split; assumption. }
      assert (Hlen_sp_vs : List.length ir_pnames = List.length vs)
        by (pose proof (Forall2_length Hty); lia).
      unfold s_pattrs in *; cbn [snd] in *.
      unfold mc_build_init_ctx in Ectx_b.
      destruct (seed_proto_param_ctx ir_pnames arg_dtys s_pattrs0) as [proto_vars proto_ctx] eqn:Eseed.
      inversion Ectx_b; subst seed_vars mc_init_ctx; clear Ectx_b.
      assert (Hlookup' : forall idx pnm v,
        nth_error ir_pnames idx = Some pnm -> nth_error vs idx = Some v -> penv' pnm = Some v).
      { intros idx pnm v Hnp Hnv.
        rewrite (Hdis_orig pnm (nth_error_In _ _ Hnp)).
        destruct (build_param_env_nth ir_pnames vs idx pnm Hnd_sp Hlen_sp_vs Hnp) as [dv [Hdv Hbp]].
        rewrite Hnv in Hdv; inversion Hdv; subst dv; exact Hbp. }
      pose proof (seed_proto_param_ctx_sound_aux ir_pnames arg_dtys s_pattrs0 vs penv' dummy_freeze_oracle Hty Hnu Hlookup')
        as [Hpenv_proto Hctx_proto].
      rewrite Eseed in Hpenv_proto, Hctx_proto; cbn [fst snd] in Hpenv_proto, Hctx_proto.
      assert (Hm' : a64_rf_matches_args penv' (mc_args mcert) rf0).
      { intros k sp Hlt Hnth; destruct (Hm k sp Hlt Hnth) as [v [Hp Hmt]].
        assert (Hinnm : In (ras_name sp) ir_pnames)
          by (rewrite <- Hnames_eq; apply in_map_iff; exists sp; split; [reflexivity | exact (nth_error_In _ _ Hnth)]).
        exists v; split; [rewrite (Hdis_orig _ Hinnm); exact Hp | exact Hmt]. }
      destruct (a64_hi_vars_wf_and_ctx penv dummy_freeze_oracle (mc_args mcert) rf0 Hnd_mc) as [Hpenv_hi Hctx_hi].
      fold penv' in Hpenv_hi, Hctx_hi.
      assert (Hmc_vars_all : forall sp, In sp (mc_args mcert) -> In (ras_name sp, ras_width sp) allowed).
      { intros sp Hsp; unfold allowed; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left.
        apply in_map_iff; exists sp; split; [reflexivity | exact Hsp]. }
      assert (Hhi_vars_all : forall nv, In nv (a64_hi_vars (mc_args mcert)) -> In nv allowed).
      { intros nv Hnv; unfold allowed; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; exact Hnv. }
      assert (Hmc_vars_wf : wf_param_env_for (List.map (fun sp => (ras_name sp, ras_width sp)) (mc_args mcert)) penv').
      { intros nm w Hin; apply in_map_iff in Hin as [sp [Heq Hsp]]; inversion Heq; subst nm w.
        destruct (In_nth_error (mc_args mcert) sp Hsp) as [k Hnth].
        destruct (nth_error_Some (mc_args mcert) k) as [Hs1 _].
        destruct (Hm' k sp ltac:(apply Hs1; congruence) Hnth) as [v [Hp _]].
        exists (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)); split; [exact Hp | right; exists v; reflexivity]. }
      assert (Hpenv_all : wf_param_env_for allowed penv').
      { intros nm w Hin; unfold allowed in Hin; apply in_app_iff in Hin as [Hu | Hs].
        - exact (Hpenv_used nm w Hu).
        - apply in_app_iff in Hs as [Hp | Hrest]; [exact (Hpenv_proto nm w Hp) |].
          apply in_app_iff in Hrest as [Hmv | Hhi]; [exact (Hmc_vars_wf nm w Hmv) | exact (Hpenv_hi nm w Hhi)]. }
      assert (Hctx0 : forall penv'' : param_env Pa,
        (forall nm, mc_starts_with_bang nm = false -> penv'' nm = penv' nm) ->
        ub_ctx_holds penv'' dummy_freeze_oracle
          (proto_ctx ++ List.map (fun sp => UBA_ParamNoUndef (ras_name sp) (ras_width sp)) (mc_args mcert)
                     ++ List.map (fun nv => UBA_ParamNoUndef (fst nv) (snd nv)) (a64_hi_vars (mc_args mcert)))).
      { intros penv'' Hag; apply Forall_app; split.
        - assert (Hlk'' : forall idx pnm v, nth_error ir_pnames idx = Some pnm -> nth_error vs idx = Some v -> penv'' pnm = Some v).
          { intros idx pnm v Hnp Hnv; rewrite (Hag pnm (Hnb_ir pnm (nth_error_In _ _ Hnp))); exact (Hlookup' idx pnm v Hnp Hnv). }
          destruct (seed_proto_param_ctx_sound_aux ir_pnames arg_dtys s_pattrs0 vs penv'' dummy_freeze_oracle Hty Hnu Hlk'') as [_ Hcp].
          rewrite Eseed in Hcp; exact Hcp.
        - apply Forall_app; split.
          + apply a64_args_noundef_ctx_sound with (rf0 := rf0).
            intros k sp Hlt Hnth; destruct (Hm' k sp Hlt Hnth) as [v [Hp Hmt]].
            assert (Hinnm : In (ras_name sp) ir_pnames)
              by (rewrite <- Hnames_eq; apply in_map_iff; exists sp; split; [reflexivity | exact (nth_error_In _ _ Hnth)]).
            exists v; split; [rewrite (Hag _ (Hnb_ir _ Hinnm)); exact Hp | exact Hmt].
          + unfold ub_ctx_holds in Hctx_hi |- *; rewrite Forall_forall in Hctx_hi |- *; intros ua Hin; pose proof (Hctx_hi ua Hin) as Hha.
            apply in_map_iff in Hin as [[nm w] [<- Hnv]]; unfold a64_hi_vars in Hnv; apply in_flat_map in Hnv as [sp [_ Hhere]].
            destruct (Pos.eqb (ras_width sp) 64%positive); [contradiction Hhere |].
            destruct Hhere as [Heq | []]; inversion Heq; subst nm w; cbn [fst snd] in *.
            intros dv Hdv; rewrite (Hag _ (a64_hi_var_name_not_bang (ras_name sp))) in Hdv; exact (Hha dv Hdv). }
      assert (Hnames_p : forall sp, In sp (mc_args mcert) -> penv' (ras_name sp) = penv (ras_name sp))
        by (intros sp Hsp; apply Hdis_orig; rewrite <- Hnames_eq; apply in_map_iff; exists sp; split; [reflexivity | exact Hsp]).
      exact (validate_mc_call_a64_sound ir_cfg allowed _ insts (mc_args mcert) (mc_ret_width mcert) (c0 :: c_rest) (mc_lrat_proof mcert)
               arg_dtys vs penv' rf0 sp0 fl0 mstk0 Hval Hnd_raw Hnd_sp Hlen_sp_s Hlen_ad
               Hcomp Hty Hcompat_args
               (fun idx w pnm Hin Hpnm => in_or_app _ _ _ (or_introl (Hpu_ir idx w pnm Hin Hpnm)))
               Hdis_orig (fun _ _ => eq_refl) Hpenv_all Hctx0 Hmc_vars_all Hhi_vars_all Hnd_mc Hdis_args Hnames_p Hsp0 Hm).
  }
Qed.

(** ** 6. Diagnostic Tail-Recursive DIMACS CNF Emitter *)

Definition push_str_rev_chars (acc : list ascii) (s : string) : list ascii :=
  str_to_chars_rev_acc acc s.

Fixpoint format_cnf_clauses_rev (acc : list ascii) (f : cnf) {struct f} : list ascii :=
  match f with
  | [] => acc
  | (_, cl) :: rest =>
      let acc1 :=
        match cl with
        | [] => ascii_of_nat 10 :: ascii_of_nat 48 :: acc
        | _ :: _ =>
            let fix go (a : list ascii) (ls : list lit) {struct ls} : list ascii :=
                match ls with
                | [] => ascii_of_nat 10 :: ascii_of_nat 48 :: a
                | l :: rs => go (ascii_of_nat 32 :: push_str_rev_chars a (show_Z_dec l)) rs
                end in
            go acc cl
        end in
      format_cnf_clauses_rev acc1 rest
  end.

Definition format_dimacs_cnf (num_vars : positive) (f : cnf) : string :=
  let f_asc := List.rev_append f [] in
  let nclauses := length_tr f_asc in
  let hdr := ("p cnf " ++ show_Z_dec (Z.pos num_vars) ++ " " ++ show_Z_dec (Z.of_nat nclauses) ++ String (ascii_of_nat 10) "")%string in
  let rev_all := format_cnf_clauses_rev (push_str_rev_chars [] hdr) f_asc in
  rev_chars_to_str_acc EmptyString rev_all.

Definition emit_mc_dimacs_cnf_str
  (ir_tle : toplevel_entities typ (block typ * list (block typ)))
  (elf_str cert_str : string) : string + string :=
  match parse_mc_cert cert_str with
  | inl err => inl err
  | inr mcert =>
      let ir_m := mcfg_of_tle (resolve_module_refs ir_tle) in
      let raw_elf := mc_string_to_bytes elf_str in
      match check_mc_cert_wf_diag mcert with
      | inl err => inl err
      | inr tt =>
          if negb (mcfg_identified_typs_defined ir_m) then
            inl (diag "ir-type" "undefined identified type in IR module")
          else
            match find_unique_mc_defn_diag (mc_fn_name mcert) (m_definitions ir_m) with
            | inl err => inl err
            | inr ir_defn =>
                match check_mc_ir_proto_contract_diag (m_type_defs ir_m) ir_defn mcert with
                | inl err => inl err
                | inr tt =>
                    let fn_bare := strip_leading_at (mc_fn_name mcert) in
                    match mc_calls mcert with
                    | [] =>
                        match elf64_extract_func raw_elf (mc_arch mcert) (mc_elf_kind mcert) fn_bare with
                        | inl err => inl err
                        | inr sl =>
                            if negb (Bool.eqb (mc_rvc mcert) (efs_rvc sl)) then
                              inl (diag "mc-rvc"
                                ("ELF64 RVC flag disagrees with mc-cert-v1 rvc mode for '" ++ fn_bare ++ "'"))
                            else
                              let tenv := m_type_defs ir_m in
                              let ir_cfg := convert_typ tenv (df_instrs ir_defn) in
                              let ir_pnames := List.map cert_reg_name (args ir_cfg) in
                              let arg_dtys := defn_arg_dtys tenv ir_defn in
                              let s_pattrs := snd (dc_param_attrs (df_prototype ir_defn)) in
                              let '(seed_vars, mc_init_ctx) :=
                                  mc_build_init_ctx (mc_arch mcert) ir_pnames arg_dtys s_pattrs (mc_args mcert) in
                              let allowed := used_src_param_vars ir_cfg ++ seed_vars in
                              match mc_loop mcert with
                              | None =>
                                  match mc_decode_and_summarize (mc_arch mcert) (mc_rvc mcert) (efs_bytes sl) (mc_args mcert) (mc_ret_width mcert) with
                                  | inl err => inl err
                                  | inr d_mc =>
                                      match flatten_mc_dag_to_expr (mc_ret_width mcert) d_mc with
                                      | inl err => inl err
                                      | inr e_mc =>
                                          match summarize_cfg_dag_with_uas (fun _ => []) false ir_cfg ir_pnames with
                                          | None =>
                                              inl (diag "mc-ir-reify" ("IR CFG symbolic summarization failed for '" ++ fn_bare ++ "'"))
                                          | Some d_ir =>
                                              match src_dag_to_expr (mc_ret_width mcert) d_ir with
                                              | None =>
                                                  inl (diag "mc-ir-reify" ("IR DAG could not be flattened to scalar select tree for CNF emission ('" ++ fn_bare ++ "')"))
                                              | Some e_ir =>
                                                  let '(es', et') := prepare_mc_expr_pair mc_init_ctx allowed e_ir e_mc in
                                                  if check_expr_refines mc_init_ctx es' et' then
                                                    inr ("c ALGEBRAIC_OK" ++ String (ascii_of_nat 10) "")%string
                                                  else
                                                    let sz := cert_expr_bit_width es' in
                                                    let known_vars := collect_free_vars [] es' ++ collect_free_vars [] et' in
                                                    let env0 := blast_ub_ctx mc_init_ctx known_vars mc_init_ctx
                                                                  (mk_blast_env (init_blast_state 2%positive) [] []) in
                                                    let ms_s := if expr_has_freeze es' then Some ([], default_let_expand_budget) else None in
                                                    let ms_t := if expr_has_freeze et' then Some ([], default_let_expand_budget) else None in
                                                    match blast_cert_expr mc_init_ctx [] ms_s es' env0 with
                                                    | None => inl (diag "mc-refine" ("failed to bit-blast source IR expression for '" ++ fn_bare ++ "'"))
                                                    | Some (src_r, env1) =>
                                                        match blast_cert_expr mc_init_ctx [] ms_t et' env1 with
                                                        | None => inl (diag "mc-refine" ("failed to bit-blast target MC expression for '" ++ fn_bare ++ "'"))
                                                        | Some (tgt_r, env2) =>
                                                            let '(cex_lit, st5) := blast_refinement_cex_opt_gates sz lit_true src_r tgt_r (be_st env2) in
                                                            let st_final := add_clauses [[cex_lit]] st5 in
                                                            inr (format_dimacs_cnf (Pos.pred (bs_next_var st_final)) (bs_cnf st_final))
                                                        end
                                                    end
                                              end
                                          end
                                      end
                                  end
                              | Some ls =>
                                  match mc_arch mcert with
                                  | EA_Riscv64 =>
                                      match decode_rv64_bytes (mc_rvc mcert) (efs_bytes sl) with
                                      | inl err => inl err
                                      | inr insts =>
                                          match emit_mc_loop_cnf_rv64 ir_cfg allowed mc_init_ctx insts (mc_args mcert) (mc_ret_width mcert) ls with
                                          | inl err => inl err
                                          | inr None => inr ("c ALGEBRAIC_OK" ++ String (ascii_of_nat 10) "")%string
                                          | inr (Some (nv, f)) => inr (format_dimacs_cnf nv f)
                                          end
                                      end
                                  | EA_AArch64 =>
                                      if mc_rvc mcert then inl (diag "mc-rvc" "compressed mode (rvc 1) is not supported for AArch64")
                                      else
                                        match decode_a64_bytes (efs_bytes sl) with
                                        | inl err => inl err
                                        | inr insts =>
                                            match emit_mc_loop_cnf_a64 ir_cfg allowed mc_init_ctx insts (mc_args mcert) (mc_ret_width mcert) ls with
                                            | inl err => inl err
                                            | inr None => inr ("c ALGEBRAIC_OK" ++ String (ascii_of_nat 10) "")%string
                                            | inr (Some (nv, f)) => inr (format_dimacs_cnf nv f)
                                            end
                                        end
                                  end
                              end
                        end
                    | callees =>
                        match mc_loop mcert with
                        | Some _ => inl (diag "mc-mode" "combining (calls ...) and (loop ...) in one certificate is not supported")
                        | None =>
                            match check_mc_callee_contracts_diag (m_type_defs ir_m) ir_m (mc_arch mcert) callees with
                            | inl err => inl err
                            | inr tt =>
                              let callee_names := List.map (fun c => mc_strip_leading_at (mcs_name c)) callees in
                              match elf64_extract_func_with_calls raw_elf (mc_arch mcert) (mc_elf_kind mcert) fn_bare callee_names with
                              | inl err => inl err
                              | inr (sl, ci) =>
                                  if negb (Bool.eqb (mc_rvc mcert) (efs_rvc sl)) then
                                    inl (diag "mc-rvc"
                                      ("ELF64 RVC flag disagrees with mc-cert-v1 rvc mode for '" ++ fn_bare ++ "'"))
                                  else
                                    let tenv := m_type_defs ir_m in
                                    let ir_cfg := convert_typ tenv (df_instrs ir_defn) in
                                    let ir_pnames := List.map cert_reg_name (args ir_cfg) in
                                    let arg_dtys := defn_arg_dtys tenv ir_defn in
                                    let s_pattrs := snd (dc_param_attrs (df_prototype ir_defn)) in
                                    let '(seed_vars, mc_init_ctx) :=
                                        mc_build_init_ctx (mc_arch mcert) ir_pnames arg_dtys s_pattrs (mc_args mcert) in
                                    let allowed := used_src_param_vars ir_cfg ++ seed_vars in
                                    match mc_arch mcert with
                                    | EA_Riscv64 =>
                                        match decode_rv64_bytes_with_calls (mc_rvc mcert) (mc_elf_kind mcert) (efs_range_lo sl) ci (efs_bytes sl) with
                                        | inl err => inl err
                                        | inr insts =>
                                            match emit_mc_call_cnf_rv64 ir_cfg allowed mc_init_ctx insts (mc_args mcert) (mc_ret_width mcert) callees with
                                            | inl err => inl err
                                            | inr None => inr ("c ALGEBRAIC_OK" ++ String (ascii_of_nat 10) "")%string
                                            | inr (Some (nv, f)) => inr (format_dimacs_cnf nv f)
                                            end
                                        end
                                    | EA_AArch64 =>
                                        if mc_rvc mcert then inl (diag "mc-rvc" "compressed mode (rvc 1) is not supported for AArch64")
                                        else
                                          match decode_a64_bytes_with_calls (mc_elf_kind mcert) (efs_range_lo sl) ci (efs_bytes sl) with
                                          | inl err => inl err
                                          | inr insts =>
                                              match emit_mc_call_cnf_a64 ir_cfg allowed mc_init_ctx insts (mc_args mcert) (mc_ret_width mcert) callees with
                                              | inl err => inl err
                                              | inr None => inr ("c ALGEBRAIC_OK" ++ String (ascii_of_nat 10) "")%string
                                              | inr (Some (nv, f)) => inr (format_dimacs_cnf nv f)
                                              end
                                          end
                                    end
                              end
                            end
                        end
                    end
                end
            end
      end
  end.

