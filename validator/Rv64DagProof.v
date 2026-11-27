(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Bitvector & Soundness Proofs for RV64 DAG Lowering ([CertValidator.Rv64DagProof])

    Purpose:
      Proves bitvector arithmetic soundness, symbolic well-formedness ([summarize_rv64_dag_wf]),
      and semantic equivalence ([summarize_rv64_dag_sound]) between concrete [rv_exec] and
      [eval_cfg_dag].

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml. Establishes that any DAG accepted by
      [summarize_rv64_dag] is well-formed and preserves concrete RV64 semantics and LP64
      callee-saved registers.

    Assumptions:
      [Stdlib], [Vellvm], [CertValidator.common.Diag], and [CertValidator.{CertFormat,AigLrat,
      AlgRules,CfgDag,Elf64Spec,McFrameMem,McIsaCommon,Rv64Decode,Rv64ExecSym}]; zero custom axioms.

    Section Outline:
      5. Bitvector arithmetic lemmas, [summarize_rv64_dag_at_sound], [summarize_rv64_dag_at_wf],
      [inst_no_word_mulh] invariants, and [summarize_rv64_dag_wf] / [summarize_rv64_dag_sound]. *)

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
  Numeric.Zbits
  Numeric.Integers
  Syntax.LLVMAst
  Syntax.DynamicTypes
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.Operations.Compare
  Semantics.Operations.Conversion
  Semantics.Operations.Select.

From CertValidator.common Require Import
  Diag.

From CertValidator Require Import
  CertFormat
  AigLrat
  AlgRules
  CfgDag
  Elf64Spec
  McFrameMem
  McIsaCommon
  Rv64Decode
  Rv64ExecSym.

Unset Implicit Arguments.
Unset Strict Implicit.
Set Default Goal Selector "!".

#[local] Arguments Pos.eqb _ _ : simpl nomatch.
#[local] Arguments Pos.ltb _ _ : simpl nomatch.
#[local] Arguments Pos.leb _ _ : simpl nomatch.
#[local] Arguments N.eqb _ _ : simpl nomatch.
#[local] Arguments N.ltb _ _ : simpl nomatch.
#[local] Arguments N.leb _ _ : simpl nomatch.
#[local] Arguments N.div _ _ : simpl nomatch.
#[local] Arguments N.modulo _ _ : simpl nomatch.
#[local] Arguments Z.eqb _ _ : simpl nomatch.
#[local] Arguments Z.ltb _ _ : simpl nomatch.
#[local] Arguments Z.leb _ _ : simpl nomatch.
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
#[local] Arguments Integers.shl : simpl never.
#[local] Arguments Integers.shru : simpl never.
#[local] Arguments Integers.shr : simpl never.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** 5. Bitvector Arithmetic & Semantic Equivalence Proofs ([0 Admitted], [0] Custom Axioms) *)

Lemma eval_sym_alu_imm_raw_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle op w a va imm,
    (w = 32%positive \/ w = 64%positive) ->
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa w va)) ->
    eval_closed_cert_expr penv foracle (sym_alu_imm_raw op w a imm) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (rv_eval_alu_imm_raw op w va imm))).
Proof.
  intros Pa penv foracle op w a va imm Hw Ha.
  destruct op; cbn [sym_alu_imm_raw rv_eval_alu_imm_raw].
  - (* RAI_Addi *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    rewrite Ha. pose proof (eval_ce_bv_z penv foracle w imm) as Hz.
    unfold eval_closed_cert_expr in Hz; rewrite Hz; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAI_Slti *)
    assert (H1w : (1 <? w)%positive = true) by (destruct Hw as [-> | ->]; reflexivity).
    rewrite (eval_ce_zext _ _ _ _ _ _ H1w
               (eval_ce_icmp_eq_bool penv foracle CIP_Slt w a (ce_bv_z w imm) va (@Integers.repr w imm) Ha (eval_ce_bv_z _ _ _ _))).
    destruct (@Integers.lt w va (@Integers.repr w imm));
      [rewrite (@Integers.unsigned_one 1%positive) | rewrite (@Integers.unsigned_zero 1%positive)]; reflexivity.
  - (* RAI_Sltiu *)
    assert (H1w : (1 <? w)%positive = true) by (destruct Hw as [-> | ->]; reflexivity).
    rewrite (eval_ce_zext _ _ _ _ _ _ H1w
               (eval_ce_icmp_eq_bool penv foracle CIP_Ult w a (ce_bv_z w imm) va (@Integers.repr w imm) Ha (eval_ce_bv_z _ _ _ _))).
    destruct (@Integers.ltu w va (@Integers.repr w imm));
      [rewrite (@Integers.unsigned_one 1%positive) | rewrite (@Integers.unsigned_zero 1%positive)]; reflexivity.
  - (* RAI_Xori *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    rewrite Ha. pose proof (eval_ce_bv_z penv foracle w imm) as Hz.
    unfold eval_closed_cert_expr in Hz; rewrite Hz; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAI_Ori *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    rewrite Ha. pose proof (eval_ce_bv_z penv foracle w imm) as Hz.
    unfold eval_closed_cert_expr in Hz; rewrite Hz; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAI_Andi *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    rewrite Ha. pose proof (eval_ce_bv_z penv foracle w imm) as Hz.
    unfold eval_closed_cert_expr in Hz; rewrite Hz; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAI_Slli *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha; cbn [eou_bind].
    pose proof (Z.mod_pos_bound imm (Z.pos w) ltac:(lia)) as Hbd.
    rewrite (Z2N.id _ (proj1 Hbd)).
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct (z_mod_pos_lt_modulus w imm (mod_lt_32_64 w Hw)) as [Hlt Heq].
    cbn - [Integers.unsigned Integers.repr Integers.shl Z.geb Z.of_N Z.modulo].
    rewrite Hlt, Heq; reflexivity.
  - (* RAI_Srli *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha; cbn [eou_bind].
    pose proof (Z.mod_pos_bound imm (Z.pos w) ltac:(lia)) as Hbd.
    rewrite (Z2N.id _ (proj1 Hbd)).
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct (z_mod_pos_lt_modulus w imm (mod_lt_32_64 w Hw)) as [Hlt Heq].
    cbn - [Integers.unsigned Integers.repr Integers.shru Z.geb Z.of_N Z.modulo].
    rewrite Hlt, Heq; reflexivity.
  - (* RAI_Srai *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha; cbn [eou_bind].
    pose proof (Z.mod_pos_bound imm (Z.pos w) ltac:(lia)) as Hbd.
    rewrite (Z2N.id _ (proj1 Hbd)).
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct (z_mod_pos_lt_modulus w imm (mod_lt_32_64 w Hw)) as [Hlt Heq].
    cbn - [Integers.unsigned Integers.repr Integers.shr Z.geb Z.of_N Z.modulo].
    rewrite Hlt, Heq; reflexivity.
Qed.

Lemma eval_sym_alu_imm_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle op is_word a va imm,
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive va)) ->
    eval_closed_cert_expr penv foracle (sym_alu_imm op is_word a imm) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_eval_alu_imm op is_word va imm))).
Proof.
  intros Pa penv foracle op [|] a va imm Ha; cbn [sym_alu_imm rv_eval_alu_imm].
  - eapply eval_ce_sext; [reflexivity |].
    apply eval_sym_alu_imm_raw_sound; [left; reflexivity |].
    apply eval_ce_trunc; [reflexivity | exact Ha].
  - apply eval_sym_alu_imm_raw_sound; [right; reflexivity | exact Ha].
Qed.

Lemma eval_sym_div_rem_guarded_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle op w a b va vb,
    (w = 32%positive \/ w = 64%positive) ->
    (op = CB_UDiv \/ op = CB_URem \/ op = CB_SDiv \/ op = CB_SRem) ->
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa w va)) ->
    eval_closed_cert_expr penv foracle b = raise_ret (DVALUE_Base (@DVALUE_I Pa w vb)) ->
    eval_closed_cert_expr penv foracle (sym_div_rem_guarded op w a b) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w
      (match op with
       | CB_UDiv => rv_divu_total w va vb
       | CB_URem => rv_modu_total w va vb
       | CB_SDiv => rv_divs_total w va vb
       | _ => rv_mods_total w va vb
       end))).
Proof.
  intros Pa penv foracle op w a b va vb Hw Hop Ha Hb.
  assert (Hzw : (@Integers.zwordsize w > 1)%Z)
    by (destruct Hw as [-> | ->];
        [replace (@Integers.zwordsize 32%positive) with 32%Z by reflexivity
        | replace (@Integers.zwordsize 64%positive) with 64%Z by reflexivity]; lia).
  destruct Hop as [-> | [-> | [-> | ->]]]; cbn [sym_div_rem_guarded].
  - (* CB_UDiv *)
    set (is_z := CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N)).
    assert (Hisz : eval_closed_cert_expr penv foracle is_z =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if @Integers.eq w vb (@Integers.zero w) then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { unfold is_z; apply (eval_ce_icmp_eq_bool _ _ CIP_Eq); [exact Hb | rewrite eval_ce_const, repr_zero_N; reflexivity]. }
    assert (Hsb : eval_closed_cert_expr penv foracle (CE_Select w is_z (CE_BvConst w 1%N) b) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if @Integers.eq w vb (@Integers.zero w) then @Integers.one w else vb)))).
    { eapply eval_ce_select_int; [exact Hisz | rewrite eval_ce_const, repr_one_N; reflexivity | exact Hb]. }
    unfold rv_divu_total.
    destruct (@Integers.eq w vb (@Integers.zero w)) eqn:Ez.
    + pose proof Ez as Ez'; apply integers_eq_zero_iff in Ez'; rewrite Ez'; cbn [Z.eqb].
      eapply (eval_ce_select_int _ _ _ _ _ _ true); [rewrite Hisz; reflexivity | exact (eval_ce_all_ones _ _ _) |].
      rewrite eval_ce_binop, Ha, Hsb; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.divu Integers.unsigned].
      rewrite (@Integers.unsigned_one w); reflexivity.
    + assert (Hnz : (@Integers.unsigned w vb =? 0)%Z = false).
      { destruct (Z.eqb (@Integers.unsigned w vb) 0%Z) eqn:Ezb; [| reflexivity].
        apply Z.eqb_eq in Ezb; apply integers_eq_zero_iff in Ezb; congruence. }
      rewrite Hnz.
      eapply (eval_ce_select_int _ _ _ _ _ _ false); [rewrite Hisz; reflexivity | exact (eval_ce_all_ones _ _ _) |].
      rewrite eval_ce_binop, Ha, Hsb; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.divu Integers.unsigned].
      rewrite Hnz; reflexivity.
  - (* CB_URem *)
    set (is_z := CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N)).
    assert (Hisz : eval_closed_cert_expr penv foracle is_z =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if @Integers.eq w vb (@Integers.zero w) then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { unfold is_z; apply (eval_ce_icmp_eq_bool _ _ CIP_Eq); [exact Hb | rewrite eval_ce_const, repr_zero_N; reflexivity]. }
    assert (Hsb : eval_closed_cert_expr penv foracle (CE_Select w is_z (CE_BvConst w 1%N) b) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if @Integers.eq w vb (@Integers.zero w) then @Integers.one w else vb)))).
    { eapply eval_ce_select_int; [exact Hisz | rewrite eval_ce_const, repr_one_N; reflexivity | exact Hb]. }
    unfold rv_modu_total.
    destruct (@Integers.eq w vb (@Integers.zero w)) eqn:Ez.
    + pose proof Ez as Ez'; apply integers_eq_zero_iff in Ez'; rewrite Ez'; cbn [Z.eqb].
      eapply (eval_ce_select_int _ _ _ _ _ _ true); [rewrite Hisz; reflexivity | exact Ha |].
      rewrite eval_ce_binop, Ha, Hsb; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.modu Integers.unsigned].
      rewrite (@Integers.unsigned_one w); reflexivity.
    + assert (Hnz : (@Integers.unsigned w vb =? 0)%Z = false).
      { destruct (Z.eqb (@Integers.unsigned w vb) 0%Z) eqn:Ezb; [| reflexivity].
        apply Z.eqb_eq in Ezb; apply integers_eq_zero_iff in Ezb; congruence. }
      rewrite Hnz.
      eapply (eval_ce_select_int _ _ _ _ _ _ false); [rewrite Hisz; reflexivity | exact Ha |].
      rewrite eval_ce_binop, Ha, Hsb; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.modu Integers.unsigned].
      rewrite Hnz; reflexivity.
  - (* CB_SDiv *)
    set (is_z := CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N)).
    set (imin := ce_int_min w).
    set (is_ovf := CE_BinOp CB_And 1%positive no_binop_flags (CE_ICmp CIP_Eq false w a imin) (CE_ICmp CIP_Eq false w b (ce_all_ones w))).
    assert (Hisz : eval_closed_cert_expr penv foracle is_z =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if Z.eqb (@Integers.signed w vb) 0%Z then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { assert (Hz0 : eval_closed_cert_expr penv foracle (CE_BvConst w 0%N) = raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))))
        by (rewrite eval_ce_const, repr_zero_N; reflexivity).
      unfold is_z; rewrite (eval_ce_icmp_eq_bool _ _ CIP_Eq w b (CE_BvConst w 0%N) vb (@Integers.zero w) Hb Hz0).
      destruct (Z.eqb (@Integers.signed w vb) 0%Z) eqn:Esz, (@Integers.eq w vb (@Integers.zero w)) eqn:Euz;
        try reflexivity; [exfalso; apply Z.eqb_eq, integers_signed_zero_iff, integers_eq_zero_iff in Esz; congruence
                       | exfalso; apply integers_eq_zero_iff, integers_signed_zero_iff, Z.eqb_eq in Euz; congruence]. }
    assert (Hovf : eval_closed_cert_expr penv foracle is_ovf =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
        (if Z.eqb (@Integers.signed w va) (@Integers.min_signed w) && Z.eqb (@Integers.signed w vb) (-1)%Z
         then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { unfold is_ovf; rewrite eval_ce_binop.
      rewrite (eval_ce_icmp_eq_bool penv foracle CIP_Eq w a imin va (@Integers.repr w (@Integers.min_signed w)) Ha (eval_ce_int_min _ _ _)).
      rewrite (eval_ce_icmp_eq_bool penv foracle CIP_Eq w b (ce_all_ones w) vb (@Integers.mone w) Hb (eval_ce_all_ones _ _ _)).
      cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op].
      destruct (@Integers.eq w va (@Integers.repr w (@Integers.min_signed w))) eqn:Ea,
               (@Integers.eq w vb (@Integers.mone w)) eqn:Eb;
        destruct (Z.eqb (@Integers.signed w va) (@Integers.min_signed w)) eqn:Esa,
                 (Z.eqb (@Integers.signed w vb) (-1)%Z) eqn:Esb;
        cbn [andb];
        try (exfalso; apply integers_eq_min_signed_iff in Ea; apply Z.eqb_neq in Esa; congruence);
        try (exfalso; apply Z.eqb_eq in Esa; apply integers_eq_min_signed_iff in Esa; congruence);
        try (exfalso; apply integers_eq_mone_iff in Eb; apply Z.eqb_neq in Esb; congruence);
        try (exfalso; apply Z.eqb_eq in Esb; apply integers_eq_mone_iff in Esb; congruence);
        reflexivity. }
    set (cz := Z.eqb (@Integers.signed w vb) 0%Z) in *.
    set (co := (Z.eqb (@Integers.signed w va) (@Integers.min_signed w) && Z.eqb (@Integers.signed w vb) (-1)%Z)%bool) in *.
    assert (Hbad : eval_closed_cert_expr penv foracle (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if (cz || co)%bool then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { rewrite eval_ce_binop, Hisz, Hovf; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op].
      destruct cz, co; reflexivity. }
    assert (Hsa : eval_closed_cert_expr penv foracle (CE_Select w is_ovf (CE_BvConst w 0%N) a) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if co then @Integers.zero w else va)))).
    { eapply eval_ce_select_int; [exact Hovf | rewrite eval_ce_const, repr_zero_N; reflexivity | exact Ha]. }
    assert (Hsb : eval_closed_cert_expr penv foracle (CE_Select w (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) (CE_BvConst w 1%N) b) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if (cz || co)%bool then @Integers.one w else vb)))).
    { eapply eval_ce_select_int; [exact Hbad | rewrite eval_ce_const, repr_one_N; reflexivity | exact Hb]. }
    assert (Hsdiv : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_SDiv w no_binop_flags (CE_Select w is_ovf (CE_BvConst w 0%N) a)
        (CE_Select w (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) (CE_BvConst w 1%N) b)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w
        (@Integers.divs w (if co then @Integers.zero w else va) (if (cz || co)%bool then @Integers.one w else vb))))).
    { rewrite eval_ce_binop, Hsa, Hsb; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [Integers.signed Integers.min_signed Integers.divs Z.eqb].
      destruct (cz || co)%bool eqn:Ebc.
      - rewrite (@Integers.signed_one w) by exact Hzw; cbn [Z.eqb].
        rewrite andb_false_r; reflexivity.
      - apply orb_false_iff in Ebc as [Hcz Hco].
        unfold cz in Hcz; rewrite Hcz, Hco.
        rewrite (Z.eqb_sym (@Integers.min_signed w) (@Integers.signed w va)).
        unfold co in Hco; rewrite Hco; reflexivity. }
    unfold rv_divs_total; fold cz co.
    destruct cz eqn:Ecz.
    { eapply (eval_ce_select_int _ _ _ _ _ _ true); [exact Hisz | exact (eval_ce_all_ones _ _ _) |].
      eapply eval_ce_select_int; [exact Hovf | exact (eval_ce_int_min _ _ _) | exact Hsdiv]. }
    { destruct co eqn:Eco.
      - eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hisz | exact (eval_ce_all_ones _ _ _) |].
        eapply (eval_ce_select_int _ _ _ _ _ _ true); [exact Hovf | exact (eval_ce_int_min _ _ _) | exact Hsdiv].
      - eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hisz | exact (eval_ce_all_ones _ _ _) |].
        eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hovf | exact (eval_ce_int_min _ _ _) | exact Hsdiv]. }
  - (* CB_SRem *)
    set (is_z := CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N)).
    set (imin := ce_int_min w).
    set (is_ovf := CE_BinOp CB_And 1%positive no_binop_flags (CE_ICmp CIP_Eq false w a imin) (CE_ICmp CIP_Eq false w b (ce_all_ones w))).
    assert (Hisz : eval_closed_cert_expr penv foracle is_z =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if Z.eqb (@Integers.signed w vb) 0%Z then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { assert (Hz0 : eval_closed_cert_expr penv foracle (CE_BvConst w 0%N) = raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))))
        by (rewrite eval_ce_const, repr_zero_N; reflexivity).
      unfold is_z; rewrite (eval_ce_icmp_eq_bool _ _ CIP_Eq w b (CE_BvConst w 0%N) vb (@Integers.zero w) Hb Hz0).
      destruct (Z.eqb (@Integers.signed w vb) 0%Z) eqn:Esz, (@Integers.eq w vb (@Integers.zero w)) eqn:Euz;
        try reflexivity; [exfalso; apply Z.eqb_eq, integers_signed_zero_iff, integers_eq_zero_iff in Esz; congruence
                       | exfalso; apply integers_eq_zero_iff, integers_signed_zero_iff, Z.eqb_eq in Euz; congruence]. }
    assert (Hovf : eval_closed_cert_expr penv foracle is_ovf =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
        (if Z.eqb (@Integers.signed w va) (@Integers.min_signed w) && Z.eqb (@Integers.signed w vb) (-1)%Z
         then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { unfold is_ovf; rewrite eval_ce_binop.
      rewrite (eval_ce_icmp_eq_bool penv foracle CIP_Eq w a imin va (@Integers.repr w (@Integers.min_signed w)) Ha (eval_ce_int_min _ _ _)).
      rewrite (eval_ce_icmp_eq_bool penv foracle CIP_Eq w b (ce_all_ones w) vb (@Integers.mone w) Hb (eval_ce_all_ones _ _ _)).
      cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op].
      destruct (@Integers.eq w va (@Integers.repr w (@Integers.min_signed w))) eqn:Ea,
               (@Integers.eq w vb (@Integers.mone w)) eqn:Eb;
        destruct (Z.eqb (@Integers.signed w va) (@Integers.min_signed w)) eqn:Esa,
                 (Z.eqb (@Integers.signed w vb) (-1)%Z) eqn:Esb;
        cbn [andb];
        try (exfalso; apply integers_eq_min_signed_iff in Ea; apply Z.eqb_neq in Esa; congruence);
        try (exfalso; apply Z.eqb_eq in Esa; apply integers_eq_min_signed_iff in Esa; congruence);
        try (exfalso; apply integers_eq_mone_iff in Eb; apply Z.eqb_neq in Esb; congruence);
        try (exfalso; apply Z.eqb_eq in Esb; apply integers_eq_mone_iff in Esb; congruence);
        reflexivity. }
    set (cz := Z.eqb (@Integers.signed w vb) 0%Z) in *.
    set (co := (Z.eqb (@Integers.signed w va) (@Integers.min_signed w) && Z.eqb (@Integers.signed w vb) (-1)%Z)%bool) in *.
    assert (Hbad : eval_closed_cert_expr penv foracle (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if (cz || co)%bool then @Integers.one 1%positive else @Integers.zero 1%positive)))).
    { rewrite eval_ce_binop, Hisz, Hovf; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op].
      destruct cz, co; reflexivity. }
    assert (Hsa : eval_closed_cert_expr penv foracle (CE_Select w is_ovf (CE_BvConst w 0%N) a) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if co then @Integers.zero w else va)))).
    { eapply eval_ce_select_int; [exact Hovf | rewrite eval_ce_const, repr_zero_N; reflexivity | exact Ha]. }
    assert (Hsb : eval_closed_cert_expr penv foracle (CE_Select w (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) (CE_BvConst w 1%N) b) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if (cz || co)%bool then @Integers.one w else vb)))).
    { eapply eval_ce_select_int; [exact Hbad | rewrite eval_ce_const, repr_one_N; reflexivity | exact Hb]. }
    assert (Hsrem : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_SRem w no_binop_flags (CE_Select w is_ovf (CE_BvConst w 0%N) a)
        (CE_Select w (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) (CE_BvConst w 1%N) b)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w
        (@Integers.mods w (if co then @Integers.zero w else va) (if (cz || co)%bool then @Integers.one w else vb))))).
    { rewrite eval_ce_binop, Hsa, Hsb; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [Integers.signed Integers.min_signed Integers.mods Z.eqb].
      destruct (cz || co)%bool eqn:Ebc.
      - rewrite (@Integers.signed_one w) by exact Hzw; cbn [Z.eqb].
        rewrite andb_false_r; reflexivity.
      - apply orb_false_iff in Ebc as [Hcz Hco].
        unfold cz in Hcz; rewrite Hcz, Hco.
        rewrite (Z.eqb_sym (@Integers.min_signed w) (@Integers.signed w va)).
        unfold co in Hco; rewrite Hco; reflexivity. }
    unfold rv_mods_total; fold cz co.
    destruct cz eqn:Ecz.
    { eapply (eval_ce_select_int _ _ _ _ _ _ true); [exact Hisz | exact Ha |].
      eapply eval_ce_select_int; [exact Hovf | rewrite eval_ce_const, repr_zero_N; reflexivity | exact Hsrem]. }
    { destruct co eqn:Eco.
      - eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hisz | exact Ha |].
        eapply (eval_ce_select_int _ _ _ _ _ _ true); [exact Hovf | rewrite eval_ce_const, repr_zero_N; reflexivity | exact Hsrem].
      - eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hisz | exact Ha |].
        eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hovf | rewrite eval_ce_const, repr_zero_N; reflexivity | exact Hsrem]. }
Qed.

Lemma eval_sym_mulhi64_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle sa sb a b va vb,
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive va)) ->
    eval_closed_cert_expr penv foracle b = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive vb)) ->
    eval_closed_cert_expr penv foracle (sym_mulhi64 sa sb a b) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive
      (@Integers.repr 64%positive
         (Z.shiftr ((if sa then @Integers.signed 64%positive va else @Integers.unsigned 64%positive va) *
                    (if sb then @Integers.signed 64%positive vb else @Integers.unsigned 64%positive vb)) 64%Z)))).
Proof.
  intros Pa penv foracle sa sb a b va vb Ha Hb.
  unfold sym_mulhi64.
  assert (Ha128 : eval_closed_cert_expr penv foracle (if sa then ce_sext64_128 a else ce_zext64_128 a) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 128%positive
      (@Integers.repr 128%positive (if sa then @Integers.signed 64%positive va else @Integers.unsigned 64%positive va))))).
  { destruct sa; [apply eval_ce_sext | apply eval_ce_zext]; try reflexivity; assumption. }
  assert (Hb128 : eval_closed_cert_expr penv foracle (if sb then ce_sext64_128 b else ce_zext64_128 b) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 128%positive
      (@Integers.repr 128%positive (if sb then @Integers.signed 64%positive vb else @Integers.unsigned 64%positive vb))))).
  { destruct sb; [apply eval_ce_sext | apply eval_ce_zext]; try reflexivity; assumption. }
  assert (Hprod : eval_closed_cert_expr penv foracle
    (CE_BinOp CB_Mul 128%positive no_binop_flags
      (if sa then ce_sext64_128 a else ce_zext64_128 a)
      (if sb then ce_sext64_128 b else ce_zext64_128 b)) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 128%positive
      (@Integers.repr 128%positive
        ((if sa then @Integers.signed 64%positive va else @Integers.unsigned 64%positive va) *
         (if sb then @Integers.signed 64%positive vb else @Integers.unsigned 64%positive vb)))))).
  { rewrite eval_ce_binop, Ha128, Hb128; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    cbn - [Integers.mul Integers.repr Integers.signed Integers.unsigned Z.mul].
    unfold Integers.mul; do 3 f_equal.
    apply Integers.eqm_samerepr, Integers.eqm_mult;
      apply Integers.eqm_sym, Integers.eqm_unsigned_repr. }
  rewrite <- (mul_hi64_eq _).
  eapply eval_ce_trunc; [reflexivity |].
  rewrite eval_ce_binop, Hprod, eval_ce_const; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  cbn - [Integers.shru Integers.repr Integers.unsigned Z.geb].
  rewrite (@Integers.unsigned_repr 128%positive 64%Z) by (compute; split; discriminate).
  replace (64 >=? Z.pos 128)%Z with false by reflexivity.
  reflexivity.
Qed.

Lemma eval_sym_alu_reg_raw_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle op w a b va vb,
    (w = 32%positive \/ w = 64%positive) ->
    (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu \/ w = 64%positive) ->
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa w va)) ->
    eval_closed_cert_expr penv foracle b = raise_ret (DVALUE_Base (@DVALUE_I Pa w vb)) ->
    eval_closed_cert_expr penv foracle (sym_alu_reg_raw op w a b) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (rv_eval_alu_reg_raw op w va vb))).
Proof.
  intros Pa penv foracle op w a b va vb Hw Hmul Ha Hb.
  destruct op; cbn [sym_alu_reg_raw rv_eval_alu_reg_raw];
    try (exfalso; destruct Hmul as [[H0 [H1 H2]] | ->]; [contradiction | discriminate H0 || discriminate H1 || discriminate H2]).
  - (* RAR_Add *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha, Hb; cbn [eou_bind eval_iop].
    rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAR_Sub *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha, Hb; cbn [eou_bind eval_iop].
    rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAR_Sll *)
    assert (Hmask : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_And w no_binop_flags b (CE_BvConst w (Z.to_N (Z.pos w - 1)))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.land (@Integers.unsigned w vb) (Z.pos w - 1)))))).
    { rewrite eval_ce_binop, Hb, eval_ce_const; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      destruct Hw as [-> | ->];
        cbn - [Integers.and Integers.unsigned Integers.repr Z.land];
        unfold Integers.and;
        [rewrite (@Integers.unsigned_repr 32%positive 31%Z) by (compute; split; discriminate)
        | rewrite (@Integers.unsigned_repr 64%positive 63%Z) by (compute; split; discriminate)];
        reflexivity. }
    rewrite eval_ce_binop, Ha, Hmask; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    cbn - [Integers.shl Integers.unsigned Integers.repr Z.geb Z.gtb Z.shiftl Z.land Z.sub].
    destruct (land_mask_w_mod w vb Hw) as [Heq Hlt].
    rewrite Hlt, Heq; reflexivity.
  - (* RAR_Slt *)
    assert (H1w : (1 <? w)%positive = true) by (destruct Hw as [-> | ->]; reflexivity).
    rewrite (eval_ce_zext _ _ _ _ _ _ H1w (eval_ce_icmp_eq_bool penv foracle CIP_Slt w a b va vb Ha Hb)).
    destruct (@Integers.lt w va vb);
      [rewrite (@Integers.unsigned_one 1%positive) | rewrite (@Integers.unsigned_zero 1%positive)]; reflexivity.
  - (* RAR_Sltu *)
    assert (H1w : (1 <? w)%positive = true) by (destruct Hw as [-> | ->]; reflexivity).
    rewrite (eval_ce_zext _ _ _ _ _ _ H1w (eval_ce_icmp_eq_bool penv foracle CIP_Ult w a b va vb Ha Hb)).
    destruct (@Integers.ltu w va vb);
      [rewrite (@Integers.unsigned_one 1%positive) | rewrite (@Integers.unsigned_zero 1%positive)]; reflexivity.
  - (* RAR_Xor *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha, Hb; cbn [eou_bind eval_iop].
    rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAR_Srl *)
    assert (Hmask : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_And w no_binop_flags b (CE_BvConst w (Z.to_N (Z.pos w - 1)))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.land (@Integers.unsigned w vb) (Z.pos w - 1)))))).
    { rewrite eval_ce_binop, Hb, eval_ce_const; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      destruct Hw as [-> | ->];
        cbn - [Integers.and Integers.unsigned Integers.repr Z.land];
        unfold Integers.and;
        [rewrite (@Integers.unsigned_repr 32%positive 31%Z) by (compute; split; discriminate)
        | rewrite (@Integers.unsigned_repr 64%positive 63%Z) by (compute; split; discriminate)];
        reflexivity. }
    rewrite eval_ce_binop, Ha, Hmask; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    cbn - [Integers.shru Integers.unsigned Integers.repr Z.geb Z.land Z.sub].
    destruct (land_mask_w_mod w vb Hw) as [Heq Hlt].
    rewrite Hlt, Heq; reflexivity.
  - (* RAR_Sra *)
    assert (Hmask : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_And w no_binop_flags b (CE_BvConst w (Z.to_N (Z.pos w - 1)))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.land (@Integers.unsigned w vb) (Z.pos w - 1)))))).
    { rewrite eval_ce_binop, Hb, eval_ce_const; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      destruct Hw as [-> | ->];
        cbn - [Integers.and Integers.unsigned Integers.repr Z.land];
        unfold Integers.and;
        [rewrite (@Integers.unsigned_repr 32%positive 31%Z) by (compute; split; discriminate)
        | rewrite (@Integers.unsigned_repr 64%positive 63%Z) by (compute; split; discriminate)];
        reflexivity. }
    rewrite eval_ce_binop, Ha, Hmask; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    cbn - [Integers.shr Integers.unsigned Integers.repr Z.geb Z.land Z.sub].
    destruct (land_mask_w_mod w vb Hw) as [Heq Hlt].
    rewrite Hlt, Heq; reflexivity.
  - (* RAR_Or *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha, Hb; cbn [eou_bind eval_iop].
    rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAR_And *)
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Ha, Hb; cbn [eou_bind eval_iop].
    rewrite eval_iop_integer_base_same_width; cbn [eval_int_op]; reflexivity.
  - (* RAR_Mul *)
    rewrite eval_ce_binop, Ha, Hb; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct Hw as [-> | ->];
      cbn - [Integers.mul Integers.unsigned Integers.signed Integers.min_signed Integers.max_signed Z.mul Z.gtb];
      reflexivity.
  - (* RAR_Mulh *)
    destruct Hmul as [[H0 _] | ->]; [exfalso; apply H0; reflexivity |].
    exact (eval_sym_mulhi64_sound penv foracle true true a b va vb Ha Hb).
  - (* RAR_Mulhsu *)
    destruct Hmul as [[_ [H1 _]] | ->]; [exfalso; apply H1; reflexivity |].
    exact (eval_sym_mulhi64_sound penv foracle true false a b va vb Ha Hb).
  - (* RAR_Mulhu *)
    destruct Hmul as [[_ [_ H2]] | ->]; [exfalso; apply H2; reflexivity |].
    exact (eval_sym_mulhi64_sound penv foracle false false a b va vb Ha Hb).
  - (* RAR_Div *)
    exact (eval_sym_div_rem_guarded_sound penv foracle CB_SDiv w a b va vb Hw
             (or_intror (or_intror (or_introl eq_refl))) Ha Hb).
  - (* RAR_Divu *)
    exact (eval_sym_div_rem_guarded_sound penv foracle CB_UDiv w a b va vb Hw
             (or_introl eq_refl) Ha Hb).
  - (* RAR_Rem *)
    exact (eval_sym_div_rem_guarded_sound penv foracle CB_SRem w a b va vb Hw
             (or_intror (or_intror (or_intror eq_refl))) Ha Hb).
  - (* RAR_Remu *)
    exact (eval_sym_div_rem_guarded_sound penv foracle CB_URem w a b va vb Hw
             (or_intror (or_introl eq_refl)) Ha Hb).
Qed.

Lemma eval_sym_alu_reg_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle op is_word a b va vb,
    (is_word = false \/ (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu)) ->
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive va)) ->
    eval_closed_cert_expr penv foracle b = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive vb)) ->
    eval_closed_cert_expr penv foracle (sym_alu_reg op is_word a b) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_eval_alu_reg op is_word va vb))).
Proof.
  intros Pa penv foracle op [|] a b va vb Hmul Ha Hb; cbn [sym_alu_reg rv_eval_alu_reg].
  - destruct Hmul as [Hdis | Hno]; [discriminate Hdis |].
    eapply eval_ce_sext; [reflexivity |].
    apply eval_sym_alu_reg_raw_sound; [left; reflexivity | left; exact Hno | |].
    + apply eval_ce_trunc; [reflexivity | exact Ha].
    + apply eval_ce_trunc; [reflexivity | exact Hb].
  - apply eval_sym_alu_reg_raw_sound; [right; reflexivity | right; reflexivity | exact Ha | exact Hb].
Qed.

Lemma eval_sym_br_cond_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle c a b va vb,
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive va)) ->
    eval_closed_cert_expr penv foracle b = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive vb)) ->
    eval_closed_cert_expr penv foracle (sym_br_cond c a b) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
      (if rv_eval_br_cond c va vb then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle c a b va vb Ha Hb.
  destruct c; unfold sym_br_cond, rv_eval_br_cond;
    [rewrite (eval_ce_icmp_eq_bool _ _ CIP_Eq 64%positive a b va vb Ha Hb)
    | rewrite (eval_ce_icmp_eq_bool _ _ CIP_Ne 64%positive a b va vb Ha Hb)
    | rewrite (eval_ce_icmp_eq_bool _ _ CIP_Slt 64%positive a b va vb Ha Hb)
    | rewrite (eval_ce_icmp_eq_bool _ _ CIP_Sge 64%positive a b va vb Ha Hb)
    | rewrite (eval_ce_icmp_eq_bool _ _ CIP_Ult 64%positive a b va vb Ha Hb)
    | rewrite (eval_ce_icmp_eq_bool _ _ CIP_Uge 64%positive a b va vb Ha Hb)]; reflexivity.
Qed.

Definition rv_val_regs_agrees {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (rf0 : rv_regfile) (sp0 : @Integers.bit_int 64%positive)
  (vrf : rv_val_regs) (rf : rv_regfile) : Prop :=
  forall r,
    mc_sym_val_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) sp0
      (rv_val_read r vrf) (rv_read_reg r rf).

Lemma rv_val_regs_agrees_write {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 vrf rf rd sv v,
    rv_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_val_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) sp0 sv v ->
    rv_val_regs_agrees penv foracle rf0 sp0 (rv_val_write rd sv vrf) (rv_write_reg rd v rf).
Proof.
  intros penv foracle rf0 sp0 vrf rf rd sv v Hag Hv r.
  unfold rv_val_read, rv_val_write, rv_read_reg, rv_write_reg.
  destruct (N.eqb r 0%N) eqn:Er0.
  - cbn [mc_sym_val_agrees]; rewrite eval_ce_const, repr_zero_N; reflexivity.
  - destruct (N.eqb rd 0%N) eqn:Erd0.
    + pose proof (Hag r) as Hr; unfold rv_val_read, rv_read_reg in Hr; rewrite Er0 in Hr; exact Hr.
    + destruct (N.eqb r rd) eqn:Erd.
      * exact Hv.
      * pose proof (Hag r) as Hr; unfold rv_val_read, rv_read_reg in Hr; rewrite Er0 in Hr; exact Hr.
Qed.

Lemma rv_sym_step_write_sp : forall rd sv sp_off vrf astk sp_off' vrf' astk',
  (- mc_frame_cap <= sp_off <= 0)%Z ->
  rv_val_read 2%N vrf = MSV_StackPtr sp_off ->
  rv_sym_step_write rd sv sp_off vrf astk = Some (sp_off', vrf', astk') ->
  (- mc_frame_cap <= sp_off' <= 0)%Z /\
  rv_val_read 2%N vrf' = MSV_StackPtr sp_off'.
Proof.
  intros rd sv sp_off vrf astk sp_off' vrf' astk' Hrng Hsp Hst.
  unfold rv_sym_step_write in Hst.
  destruct (N.eqb rd 2%N) eqn:Erd2.
  - apply N.eqb_eq in Erd2; subst rd.
    destruct sv as [| | | off']; try discriminate Hst.
    destruct (Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z) eqn:Eb; [| discriminate Hst].
    apply andb_true_iff in Eb as [Eb1 Eb2]; apply Z.leb_le in Eb1; apply Z.leb_le in Eb2.
    inversion Hst; subst; split; [lia | reflexivity].
  - inversion Hst; subst; split; [exact Hrng |].
    unfold rv_val_read, rv_val_write in Hsp |- *; cbn [N.eqb] in Hsp |- *.
    destruct (N.eqb rd 0%N); [exact Hsp | rewrite N.eqb_sym, Erd2; exact Hsp].
Qed.

Lemma rv_sym_step_write_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 rd sv v sp_off vrf astk rf mstk sp_off' vrf' astk',
    rv_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) sp0 astk mstk ->
    mc_sym_val_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) sp0 sv v ->
    rv_sym_step_write rd sv sp_off vrf astk = Some (sp_off', vrf', astk') ->
    rv_val_regs_agrees penv foracle rf0 sp0 vrf' (rv_write_reg rd v rf) /\
    mc_sym_stack_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) sp0 astk' mstk.
Proof.
  intros penv foracle rf0 sp0 rd sv v sp_off vrf astk rf mstk sp_off' vrf' astk' Hag Hastk Hv Hst.
  unfold rv_sym_step_write in Hst.
  destruct (N.eqb rd 2%N) eqn:Erd2.
  - apply N.eqb_eq in Erd2; subst rd.
    destruct sv as [| | | off']; try discriminate Hst.
    destruct (Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z); [| discriminate Hst].
    inversion Hst; subst; split.
    + apply rv_val_regs_agrees_write; assumption.
    + apply mc_sym_stk_prune_agrees; exact Hastk.
  - inversion Hst; subst; split; [apply rv_val_regs_agrees_write; assumption | exact Hastk].
Qed.

Definition inst_no_word_mulh (d : decoded_rv_inst) : bool :=
  match dri_inst d with
  | RV_AluReg RAR_Mulh true _ _ _
  | RV_AluReg RAR_Mulhsu true _ _ _
  | RV_AluReg RAR_Mulhu true _ _ _ => false
  | _ => true
  end.

Lemma rv_sym_epilogue_ok_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp_off vrf rf,
    rv_val_regs_agrees penv foracle rf0 (rv_read_reg 2%N rf0) vrf rf ->
    rv_sym_epilogue_ok sp_off vrf = true ->
    rv_callee_saved_preserved rf0 rf /\ rf 1%N = rf0 1%N.
Proof.
  intros penv foracle rf0 sp_off vrf rf Hag Hep.
  unfold rv_sym_epilogue_ok in Hep; rewrite !andb_true_iff in Hep.
  destruct Hep as [[_ Hsp2] Hforall].
  destruct (rv_val_read 2%N vrf) as [| | | zsp] eqn:Ev2; try discriminate Hsp2.
  destruct zsp; try discriminate Hsp2.
  assert (Hreg_saved : forall r, In r rv_preserved_non_sp_regs -> rf r = rf0 r).
  { intros r Hin; rewrite forallb_forall in Hforall; pose proof (Hforall r Hin) as Hmatch.
    destruct (rv_val_read r vrf) as [| | r0 |] eqn:Erv; try discriminate Hmatch.
    apply N.eqb_eq in Hmatch; subst r0.
    pose proof (Hag r) as Hagr; rewrite Erv in Hagr; cbn [mc_sym_val_agrees] in Hagr.
    assert (Hrnz : r <> 0%N).
    { cbn [rv_preserved_non_sp_regs In] in Hin.
      repeat destruct Hin as [<- | Hin]; try discriminate; contradiction. }
    unfold rv_read_reg in Hagr; apply N.eqb_neq in Hrnz; rewrite Hrnz in Hagr; exact Hagr. }
  split.
  - intros r Hcs; unfold rv_is_callee_saved in Hcs; rewrite !orb_true_iff in Hcs.
    destruct Hcs as [[Hr2 | Hr89] | Hr18].
    + apply N.eqb_eq in Hr2; subst r.
      pose proof (Hag 2%N) as Hag2; rewrite Ev2 in Hag2; cbn [mc_sym_val_agrees] in Hag2.
      destruct Hag2 as [_ Heq2]; rewrite mc_add_ptr_zero in Heq2; exact Heq2.
    + apply andb_true_iff in Hr89 as [Hge Hle]; apply N.leb_le in Hge; apply N.leb_le in Hle.
      apply Hreg_saved; cbn [rv_preserved_non_sp_regs In].
      assert (r = 8%N \/ r = 9%N) by lia; destruct H as [-> | ->]; auto.
    + apply andb_true_iff in Hr18 as [Hge Hle]; apply N.leb_le in Hge; apply N.leb_le in Hle.
      apply Hreg_saved; cbn [rv_preserved_non_sp_regs In].
      assert (r = 18%N \/ r = 19%N \/ r = 20%N \/ r = 21%N \/ r = 22%N \/
              r = 23%N \/ r = 24%N \/ r = 25%N \/ r = 26%N \/ r = 27%N) by lia.
      repeat destruct H as [-> | H]; auto 20.
  - apply Hreg_saved; left; reflexivity.
Qed.

Theorem summarize_rv64_dag_at_sound :
  forall {Pa : Params} fuel insts im visited pc sp_off vrf astk ret_w d_mc penv foracle rf0 rf mstk,
    (forall q, pt_get (N.succ_pos q) im = lookup_rv_inst insts q) ->
    rv_supported_arg_width ret_w = true ->
    forallb inst_no_word_mulh insts = true ->
    mc_valid_sp0 (rv_read_reg 2%N rf0) ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    rv_val_read 2%N vrf = MSV_StackPtr sp_off ->
    rv_val_regs_agrees penv foracle rf0 (rv_read_reg 2%N rf0) vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0) astk mstk ->
    summarize_rv64_dag_at fuel im visited pc sp_off vrf astk ret_w = inr d_mc ->
    exists rf_end mstk_end,
      rv_exec_mem fuel insts pc (rv_read_reg 2%N rf0) rf mstk = Some (rf_end, mstk_end) /\
      rv_callee_saved_preserved rf0 rf_end /\
      rf_end 1%N = rf0 1%N /\
      eval_cfg_dag penv foracle d_mc =
      DO_Ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end)))).
Proof.
  intros Pa fuel insts im visited pc sp_off vrf astk ret_w d_mc penv foracle rf0 rf mstk Him.
  revert visited pc sp_off vrf astk ret_w d_mc penv foracle rf0 rf mstk.
  induction fuel as [| fuel' IH];
    intros visited pc sp_off vrf astk ret_w d_mc penv foracle rf0 rf mstk
           Hrw Hnmul Hsp0 Hrng Hsp2 Hag Hastk Hsum;
    cbn [summarize_rv64_dag_at rv_exec_mem] in *.
  - destruct (pt_has_n pc visited); discriminate Hsum.
  - destruct (pt_has_n pc visited); [discriminate Hsum |].
    destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Elook; [| discriminate Hsum].
    rewrite Him in Elook; rewrite Elook.
    assert (Hdec_mulh : inst_no_word_mulh dec = true).
    { clear -Elook Hnmul. induction insts as [| d rest IHl]; cbn in *; [discriminate |].
      apply andb_true_iff in Hnmul as [Hd Hr].
      destruct (N.eqb (dri_off d) pc); [inversion Elook; subst; exact Hd | exact (IHl Hr Elook)]. }
    destruct (dri_inst dec) as
      [| rd imm
       | op is_word rd rs1 imm
       | op is_word rd rs1 rs2
       | sz is_signed rd rs1 imm
       | sz rs1 rs2 imm
       | cond rs1 rs2 rel
       | rel
       | ] eqn:Ed.
    + (* RV_Nop *)
      exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N sp_off vrf astk ret_w d_mc penv foracle rf0 rf mstk
                Hrw Hnmul Hsp0 Hrng Hsp2 Hag Hastk Hsum).
    + (* RV_Lui *)
      destruct (rv_sym_step_write rd (MSV_Expr (ce_bv_z 64%positive imm)) sp_off vrf astk)
        as [[[sp_off' vrf'] astk'] |] eqn:Est; [| discriminate Hsum].
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      destruct (rv_sym_step_write_sound penv foracle rf0 (rv_read_reg 2%N rf0)
                  rd (MSV_Expr (ce_bv_z 64%positive imm)) (@Integers.repr 64%positive imm)
                  sp_off vrf astk rf mstk sp_off' vrf' astk' Hag Hastk (eval_ce_bv_z penv foracle 64%positive imm) Est)
        as [Hag' Hastk'].
      exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N sp_off' vrf' astk' ret_w d_mc
                penv foracle rf0 (rv_write_reg rd (@Integers.repr 64%positive imm) rf) mstk
                Hrw Hnmul Hsp0 Hrng' Hsp2' Hag' Hastk' Hsum).
    + (* RV_AluImm *)
      set (sv_opt :=
        match op, is_word, rv_val_read rs1 vrf with
        | RAI_Addi, false, MSV_StackPtr base_off =>
            let off' := (base_off + imm)%Z in
            if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z then Some (MSV_StackPtr off') else None
        | RAI_Addi, false, MSV_SavedReg r0 =>
            if Z.eqb imm 0%Z then Some (MSV_SavedReg r0) else None
        | _, _, MSV_Expr e => Some (MSV_Expr (sym_alu_imm op is_word e imm))
        | _, _, _ => None
        end) in *.
      destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hsum].
      destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
        [| discriminate Hsum].
      assert (Hval_sv : mc_sym_val_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                          sv (rv_eval_alu_imm op is_word (rv_read_reg rs1 rf) imm)).
      { subst sv_opt; destruct (rv_val_read rs1 vrf) as [| e1 | r0 | base_off] eqn:Er1.
        - destruct op, is_word; discriminate Esv.
        - assert (He_eq : sv = MSV_Expr (sym_alu_imm op is_word e1 imm))
            by (destruct op, is_word; inversion Esv; reflexivity).
          rewrite He_eq; cbn [mc_sym_val_agrees]; apply eval_sym_alu_imm_sound.
          pose proof (Hag rs1) as H1; rewrite Er1 in H1; exact H1.
        - destruct op; destruct is_word; try discriminate Esv.
          destruct (Z.eqb imm 0%Z) eqn:Ez0; [| discriminate Esv].
          apply Z.eqb_eq in Ez0; subst imm; inversion Esv; subst sv; clear Esv.
          pose proof (Hag rs1) as H1; rewrite Er1 in H1; cbn [mc_sym_val_agrees] in H1 |- *.
          cbn [rv_eval_alu_imm rv_eval_alu_imm_raw]; rewrite H1, mc_add_ptr_zero; reflexivity.
        - destruct op; destruct is_word; try discriminate Esv.
          cbv zeta in Esv.
          destruct (Z.leb (- mc_frame_cap) (base_off + imm) && Z.leb (base_off + imm) 0%Z) eqn:Erng;
            [| discriminate Esv].
          apply andb_true_iff in Erng as [Erng1 Erng2]; apply Z.leb_le in Erng1; apply Z.leb_le in Erng2.
          inversion Esv; subst sv; clear Esv.
          pose proof (Hag rs1) as H1; rewrite Er1 in H1; cbn [mc_sym_val_agrees] in H1 |- *.
          destruct H1 as [_ Hptr]; split; [lia |].
          cbn [rv_eval_alu_imm rv_eval_alu_imm_raw]; rewrite Hptr, mc_add_ptr_off; reflexivity. }
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      destruct (rv_sym_step_write_sound penv foracle rf0 (rv_read_reg 2%N rf0)
                  rd sv (rv_eval_alu_imm op is_word (rv_read_reg rs1 rf) imm)
                  sp_off vrf astk rf mstk sp_off' vrf' astk' Hag Hastk Hval_sv Est)
        as [Hag' Hastk'].
      exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N sp_off' vrf' astk' ret_w d_mc
                penv foracle rf0 (rv_write_reg rd (rv_eval_alu_imm op is_word (rv_read_reg rs1 rf) imm) rf) mstk
                Hrw Hnmul Hsp0 Hrng' Hsp2' Hag' Hastk' Hsum).
    + (* RV_AluReg *)
      set (is_mv := ((match op with RAR_Add => negb is_word | _ => false end) &&
                     (N.eqb rs1 0%N || N.eqb rs2 0%N))%bool) in *.
      set (sv_opt :=
        if is_mv then
          let sv := if N.eqb rs1 0%N then rv_val_read rs2 vrf else rv_val_read rs1 vrf in
          match sv with MSV_Undef => None | _ => Some sv end
        else
          match rv_val_read rs1 vrf, rv_val_read rs2 vrf with
          | MSV_Expr e1, MSV_Expr e2 => Some (MSV_Expr (sym_alu_reg op is_word e1 e2))
          | _, _ => None
          end) in *.
      destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hsum].
      destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
        [| discriminate Hsum].
      assert (Hval_sv : mc_sym_val_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0)
                          sv (rv_eval_alu_reg op is_word (rv_read_reg rs1 rf) (rv_read_reg rs2 rf))).
      { destruct is_mv eqn:Emv.
        - subst is_mv; apply andb_true_iff in Emv as [Hopm Hz].
          destruct op; try discriminate Hopm; destruct is_word; try discriminate Hopm.
          cbn [rv_eval_alu_reg rv_eval_alu_reg_raw].
          destruct (N.eqb rs1 0%N) eqn:Ez1.
          + apply N.eqb_eq in Ez1; subst rs1.
            replace (rv_read_reg 0%N rf) with (@Integers.zero 64%positive) by reflexivity.
            rewrite (@Integers.add_zero_l 64%positive).
            destruct (rv_val_read rs2 vrf) eqn:Er2; try discriminate Esv;
              inversion Esv; subst sv; pose proof (Hag rs2) as H2; rewrite Er2 in H2; exact H2.
          + cbn [orb] in Hz; apply N.eqb_eq in Hz; subst rs2.
            replace (rv_read_reg 0%N rf) with (@Integers.zero 64%positive) by reflexivity.
            rewrite (@Integers.add_zero 64%positive).
            destruct (rv_val_read rs1 vrf) eqn:Er1; try discriminate Esv;
              inversion Esv; subst sv; pose proof (Hag rs1) as H1; rewrite Er1 in H1; exact H1.
        - subst sv_opt; cbn [fst snd] in Esv.
          destruct (rv_val_read rs1 vrf) as [| e1 | |] eqn:Er1; try discriminate Esv.
          destruct (rv_val_read rs2 vrf) as [| e2 | |] eqn:Er2; try discriminate Esv.
          inversion Esv; subst sv; clear Esv.
          pose proof (Hag rs1) as H1; rewrite Er1 in H1;
            pose proof (Hag rs2) as H2; rewrite Er2 in H2; cbn [mc_sym_val_agrees] in H1, H2 |- *.
          assert (Hok_m : is_word = false \/ (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu)).
          { destruct is_word; [| left; reflexivity].
            right; unfold inst_no_word_mulh in Hdec_mulh; rewrite Ed in Hdec_mulh.
            destruct op; repeat split; intro C; discriminate C || discriminate Hdec_mulh. }
          apply eval_sym_alu_reg_sound; assumption. }
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      destruct (rv_sym_step_write_sound penv foracle rf0 (rv_read_reg 2%N rf0)
                  rd sv (rv_eval_alu_reg op is_word (rv_read_reg rs1 rf) (rv_read_reg rs2 rf))
                  sp_off vrf astk rf mstk sp_off' vrf' astk' Hag Hastk Hval_sv Est)
        as [Hag' Hastk'].
      exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N sp_off' vrf' astk' ret_w d_mc
                penv foracle rf0 (rv_write_reg rd (rv_eval_alu_reg op is_word (rv_read_reg rs1 rf) (rv_read_reg rs2 rf)) rf) mstk
                Hrw Hnmul Hsp0 Hrng' Hsp2' Hag' Hastk' Hsum).
    + (* RV_Load *)
      destruct (rv_val_read rs1 vrf) as [| | | base_off] eqn:Er1; try discriminate Hsum.
      destruct (mc_slot_in_frame sp_off (base_off + imm) sz) eqn:Eslot; [| discriminate Hsum].
      destruct (mc_sym_stk_load (base_off + imm) sz is_signed astk) as [sv |] eqn:Eload;
        [| discriminate Hsum].
      destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
        [| discriminate Hsum].
      pose proof (mc_slot_in_frame_bounds _ _ _ Eslot) as (Hb1 & Hb2 & Hb3 & _).
      assert (Hsz_pos : (1 <= mc_mem_bytes_Z sz)%Z) by (destruct sz; cbn; lia).
      pose proof (Hag rs1) as H1; rewrite Er1 in H1; cbn [mc_sym_val_agrees] in H1; destruct H1 as [_ Hptr1].
      pose proof (Hag 2%N) as H2; rewrite Hsp2 in H2; cbn [mc_sym_val_agrees] in H2; destruct H2 as [_ Hptr2].
      destruct Hsp0 as [Hsp0_cap Hsp0_al].
      assert (Hoff_eq : mc_addr_to_off (rv_read_reg 2%N rf0)
                          (@Integers.add 64%positive (rv_read_reg rs1 rf) (@Integers.repr 64%positive imm)) =
                        (base_off + imm)%Z).
      { rewrite Hptr1, mc_add_ptr_off; apply mc_addr_to_off_add; [exact Hsp0_cap | lia]. }
      assert (Hsp_eq : mc_addr_to_off (rv_read_reg 2%N rf0) (rv_read_reg 2%N rf) = sp_off).
      { rewrite Hptr2; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hrng]. }
      rewrite Hoff_eq, Hsp_eq, Eslot.
      pose proof (mc_sym_stk_load_sound penv foracle (fun r0 => rv_read_reg r0 rf0)
                    (rv_read_reg 2%N rf0) (base_off + imm) sz is_signed astk mstk sv Hastk Eload) as Hval_sv.
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      destruct (rv_sym_step_write_sound penv foracle rf0 (rv_read_reg 2%N rf0)
                  rd sv (mc_stk_load mstk (base_off + imm) sz is_signed)
                  sp_off vrf astk rf mstk sp_off' vrf' astk' Hag Hastk Hval_sv Est)
        as [Hag' Hastk'].
      exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N sp_off' vrf' astk' ret_w d_mc
                penv foracle rf0 (rv_write_reg rd (mc_stk_load mstk (base_off + imm) sz is_signed) rf) mstk
                Hrw Hnmul (conj Hsp0_cap Hsp0_al) Hrng' Hsp2' Hag' Hastk' Hsum).
    + (* RV_Store *)
      destruct (rv_val_read rs1 vrf) as [| | | base_off] eqn:Er1; try discriminate Hsum.
      destruct (mc_slot_in_frame sp_off (base_off + imm) sz) eqn:Eslot; [| discriminate Hsum].
      destruct (match rv_val_read rs2 vrf with
                | MSV_Undef => false
                | MSV_Expr _ => true
                | MSV_SavedReg _ | MSV_StackPtr _ => mc_mem_size_eqb sz MS_8
                end) eqn:Esvok; [| discriminate Hsum].
      pose proof (mc_slot_in_frame_bounds _ _ _ Eslot) as (Hb1 & Hb2 & Hb3 & _).
      assert (Hsz_pos : (1 <= mc_mem_bytes_Z sz)%Z) by (destruct sz; cbn; lia).
      pose proof (Hag rs1) as H1; rewrite Er1 in H1; cbn [mc_sym_val_agrees] in H1; destruct H1 as [_ Hptr1].
      pose proof (Hag 2%N) as H2; rewrite Hsp2 in H2; cbn [mc_sym_val_agrees] in H2; destruct H2 as [_ Hptr2].
      destruct Hsp0 as [Hsp0_cap Hsp0_al].
      assert (Hoff_eq : mc_addr_to_off (rv_read_reg 2%N rf0)
                          (@Integers.add 64%positive (rv_read_reg rs1 rf) (@Integers.repr 64%positive imm)) =
                        (base_off + imm)%Z).
      { rewrite Hptr1, mc_add_ptr_off; apply mc_addr_to_off_add; [exact Hsp0_cap | lia]. }
      assert (Hsp_eq : mc_addr_to_off (rv_read_reg 2%N rf0) (rv_read_reg 2%N rf) = sp_off).
      { rewrite Hptr2; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hrng]. }
      rewrite Hoff_eq, Hsp_eq, Eslot.
      assert (Hsz_match : match rv_val_read rs2 vrf with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end).
      { destruct (rv_val_read rs2 vrf); try exact I; apply mc_mem_size_eqb_eq; exact Esvok. }
      pose proof (mc_sym_stk_store_agrees penv foracle (fun r0 => rv_read_reg r0 rf0)
                    (rv_read_reg 2%N rf0) (base_off + imm) sz (rv_val_read rs2 vrf) (rv_read_reg rs2 rf)
                    astk mstk Hsz_match (Hag rs2) Hastk) as Hastk'.
      exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N sp_off vrf
                (mc_sym_stk_store (base_off + imm) sz (rv_val_read rs2 vrf) astk)
                ret_w d_mc penv foracle rf0 rf (mc_stk_store mstk (base_off + imm) sz (rv_read_reg rs2 rf))
                Hrw Hnmul (conj Hsp0_cap Hsp0_al) Hrng Hsp2 Hag Hastk' Hsum).
    + (* RV_Branch *)
      destruct (rv_val_read rs1 vrf) as [| e1 | |] eqn:Er1; try discriminate Hsum.
      destruct (rv_val_read rs2 vrf) as [| e2 | |] eqn:Er2; try discriminate Hsum.
      destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hsum].
      destruct (summarize_rv64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk ret_w) as [| dt] eqn:Edt;
        [discriminate Hsum |].
      destruct (summarize_rv64_dag_at fuel' im (pt_add_n pc visited) (pc + dri_len dec)%N sp_off vrf astk ret_w) as [| df] eqn:Edf;
        [discriminate Hsum |].
      inversion Hsum; subst d_mc; clear Hsum.
      pose proof (Hag rs1) as H1; rewrite Er1 in H1; cbn [mc_sym_val_agrees] in H1.
      pose proof (Hag rs2) as H2; rewrite Er2 in H2; cbn [mc_sym_val_agrees] in H2.
      pose proof (eval_sym_br_cond_sound penv foracle cond e1 e2 (rv_read_reg rs1 rf) (rv_read_reg rs2 rf) H1 H2) as Hbr.
      cbn [eval_cfg_dag]; rewrite Hbr.
      destruct (rv_eval_br_cond cond (rv_read_reg rs1 rf) (rv_read_reg rs2 rf)).
      * rewrite (@Integers.unsigned_one 1%positive); cbn [Z.eqb].
        exact (IH (pt_add_n pc visited) tgt_pc sp_off vrf astk ret_w dt penv foracle rf0 rf mstk
                  Hrw Hnmul Hsp0 Hrng Hsp2 Hag Hastk Edt).
      * rewrite (@Integers.unsigned_zero 1%positive); cbn [Z.eqb].
        exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N sp_off vrf astk ret_w df penv foracle rf0 rf mstk
                  Hrw Hnmul Hsp0 Hrng Hsp2 Hag Hastk Edf).
    + (* RV_Jal0 *)
      destruct (add_rel_off pc rel) as [tgt_pc |] eqn:Erel; [| discriminate Hsum].
      exact (IH (pt_add_n pc visited) tgt_pc sp_off vrf astk ret_w d_mc penv foracle rf0 rf mstk
                Hrw Hnmul Hsp0 Hrng Hsp2 Hag Hastk Hsum).
    + (* RV_Ret *)
      destruct (rv_sym_epilogue_ok sp_off vrf) eqn:Eep; [| discriminate Hsum].
      destruct (rv_val_read 10%N vrf) as [| e_ret | |] eqn:Er10; try discriminate Hsum.
      inversion Hsum; subst d_mc; clear Hsum.
      destruct (rv_sym_epilogue_ok_sound penv foracle rf0 sp_off vrf rf Hag Eep) as [Hcs Hra].
      exists rf, mstk; split; [reflexivity | split; [exact Hcs | split; [exact Hra |]]].
      cbn [eval_cfg_dag]; unfold rv_trunc_ret_expr, rv_trunc_ret_val.
      pose proof (Hag 10%N) as Ha10; rewrite Er10 in Ha10; cbn [mc_sym_val_agrees] in Ha10.
      destruct (Pos.eqb ret_w 64%positive) eqn:Ew64.
      * apply Pos.eqb_eq in Ew64; subst ret_w.
        rewrite Ha10, (@Integers.repr_unsigned 64%positive); reflexivity.
      * assert (Hlt64 : (ret_w <? 64)%positive = true) by (exact (rv_supported_arg_width_lt64 _ Hrw Ew64)).
        rewrite (eval_ce_trunc penv foracle 64%positive ret_w e_ret _ Hlt64 Ha10); reflexivity.
Qed.

Definition wf_sym_regs (allowed : list (string * positive)) (srf : rv_sym_regs) (def : rv_def_mask) : Prop :=
  forall r, rv_def_read r def = true -> wf_sym_expr allowed 64%positive (rv_sym_read r srf).

Lemma wf_sym_alu_imm_raw : forall allowed op w a imm,
  (w = 32%positive \/ w = 64%positive) ->
  wf_sym_expr allowed w a ->
  wf_sym_expr allowed w (sym_alu_imm_raw op w a imm).
Proof.
  intros allowed op w a imm Hw Ha.
  destruct op; cbn [sym_alu_imm_raw].
  - apply wf_sym_binop; [destruct Hw as [-> | ->]; left; discriminate | exact Ha | apply wf_sym_bv_z].
  - apply wf_sym_cast; [destruct Hw as [-> | ->]; reflexivity |].
    apply wf_sym_icmp; [exact Ha | apply wf_sym_bv_z].
  - apply wf_sym_cast; [destruct Hw as [-> | ->]; reflexivity |].
    apply wf_sym_icmp; [exact Ha | apply wf_sym_bv_z].
  - apply wf_sym_binop; [destruct Hw as [-> | ->]; left; discriminate | exact Ha | apply wf_sym_bv_z].
  - apply wf_sym_binop; [destruct Hw as [-> | ->]; left; discriminate | exact Ha | apply wf_sym_bv_z].
  - apply wf_sym_binop; [destruct Hw as [-> | ->]; left; discriminate | exact Ha | apply wf_sym_bv_z].
  - apply wf_sym_binop; [destruct Hw as [-> | ->]; left; discriminate | exact Ha | apply wf_sym_bv_const].
  - apply wf_sym_binop; [destruct Hw as [-> | ->]; left; discriminate | exact Ha | apply wf_sym_bv_const].
  - apply wf_sym_binop; [destruct Hw as [-> | ->]; left; discriminate | exact Ha | apply wf_sym_bv_const].
Qed.

Lemma wf_sym_alu_imm : forall allowed op is_word a imm,
  wf_sym_expr allowed 64%positive a ->
  wf_sym_expr allowed 64%positive (sym_alu_imm op is_word a imm).
Proof.
  intros allowed op [|] a imm Ha; cbn [sym_alu_imm].
  - apply wf_sym_cast; [reflexivity |].
    apply wf_sym_alu_imm_raw; [left; reflexivity |].
    apply wf_sym_cast; [reflexivity | exact Ha].
  - apply wf_sym_alu_imm_raw; [right; reflexivity | exact Ha].
Qed.

Lemma wf_sym_div_rem_guarded : forall allowed op w a b,
  (w = 32%positive \/ w = 64%positive) ->
  wf_sym_expr allowed w a ->
  wf_sym_expr allowed w b ->
  wf_sym_expr allowed w (sym_div_rem_guarded op w a b).
Proof.
  intros allowed op w a b Hw Ha Hb.
  assert (Hnz : w <> 1%positive) by (destruct Hw as [-> | ->]; discriminate).
  assert (Hiz : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N)))
    by (apply wf_sym_icmp; [exact Hb | apply wf_sym_bv_const]).
  destruct op; cbn [sym_div_rem_guarded];
    try (
      assert (Hovf : wf_sym_expr allowed 1%positive
        (CE_BinOp CB_And 1%positive no_binop_flags
          (CE_ICmp CIP_Eq false w a (ce_int_min w))
          (CE_ICmp CIP_Eq false w b (ce_all_ones w))))
      by (apply wf_sym_binop; [right; left; reflexivity | apply wf_sym_icmp; [exact Ha | apply wf_sym_bv_const] | apply wf_sym_icmp; [exact Hb | apply wf_sym_bv_const]]);
      assert (Hbad : wf_sym_expr allowed 1%positive
        (CE_BinOp CB_Or 1%positive no_binop_flags
          (CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N))
          (CE_BinOp CB_And 1%positive no_binop_flags
            (CE_ICmp CIP_Eq false w a (ce_int_min w))
            (CE_ICmp CIP_Eq false w b (ce_all_ones w)))))
      by (apply wf_sym_binop; [right; right; reflexivity | exact Hiz | exact Hovf]);
      apply wf_sym_select; [exact Hiz | try apply wf_sym_bv_const; try exact Ha |
        apply wf_sym_select; [exact Hovf | apply wf_sym_bv_const |
          apply wf_sym_binop; [left; exact Hnz | apply wf_sym_select; [exact Hovf | apply wf_sym_bv_const | exact Ha] | apply wf_sym_select; [exact Hbad | apply wf_sym_bv_const | exact Hb]]]]).
  - (* CB_UDiv *)
    apply wf_sym_select; [exact Hiz | apply wf_sym_bv_const |].
    apply wf_sym_binop; [left; exact Hnz | exact Ha | apply wf_sym_select; [exact Hiz | apply wf_sym_bv_const | exact Hb]].
  - (* CB_URem *)
    apply wf_sym_select; [exact Hiz | exact Ha |].
    apply wf_sym_binop; [left; exact Hnz | exact Ha | apply wf_sym_select; [exact Hiz | apply wf_sym_bv_const | exact Hb]].
Qed.

Lemma wf_sym_mulhi64 : forall allowed sa sb a b,
  wf_sym_expr allowed 64%positive a ->
  wf_sym_expr allowed 64%positive b ->
  wf_sym_expr allowed 64%positive (sym_mulhi64 sa sb a b).
Proof.
  intros allowed sa sb a b Ha Hb; unfold sym_mulhi64.
  apply wf_sym_cast; [reflexivity |].
  apply wf_sym_binop; [left; discriminate | | apply wf_sym_bv_const].
  apply wf_sym_binop; [left; discriminate | |].
  - destruct sa; apply wf_sym_cast; [reflexivity | exact Ha | reflexivity | exact Ha].
  - destruct sb; apply wf_sym_cast; [reflexivity | exact Hb | reflexivity | exact Hb].
Qed.

Lemma wf_sym_alu_reg_raw : forall allowed op w a b,
  (w = 32%positive \/ w = 64%positive) ->
  (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu \/ w = 64%positive) ->
  wf_sym_expr allowed w a ->
  wf_sym_expr allowed w b ->
  wf_sym_expr allowed w (sym_alu_reg_raw op w a b).
Proof.
  intros allowed op w a b Hw Hmul Ha Hb.
  assert (Hnz : w <> 1%positive) by (destruct Hw as [-> | ->]; discriminate).
  destruct op; cbn [sym_alu_reg_raw];
    try (exfalso; destruct Hmul as [[H0 [H1 H2]] | ->]; [contradiction | discriminate H0 || discriminate H1 || discriminate H2]).
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | exact Hb].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | exact Hb].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | apply wf_sym_binop; [left; exact Hnz | exact Hb | apply wf_sym_bv_const]].
  - apply wf_sym_cast; [destruct Hw as [-> | ->]; reflexivity | apply wf_sym_icmp; assumption].
  - apply wf_sym_cast; [destruct Hw as [-> | ->]; reflexivity | apply wf_sym_icmp; assumption].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | exact Hb].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | apply wf_sym_binop; [left; exact Hnz | exact Hb | apply wf_sym_bv_const]].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | apply wf_sym_binop; [left; exact Hnz | exact Hb | apply wf_sym_bv_const]].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | exact Hb].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | exact Hb].
  - apply wf_sym_binop; [left; exact Hnz | exact Ha | exact Hb].
  - destruct Hmul as [[H0 _] | ->]; [exfalso; apply H0; reflexivity | apply wf_sym_mulhi64; assumption].
  - destruct Hmul as [[_ [H1 _]] | ->]; [exfalso; apply H1; reflexivity | apply wf_sym_mulhi64; assumption].
  - destruct Hmul as [[_ [_ H2]] | ->]; [exfalso; apply H2; reflexivity | apply wf_sym_mulhi64; assumption].
  - apply wf_sym_div_rem_guarded; assumption.
  - apply wf_sym_div_rem_guarded; assumption.
  - apply wf_sym_div_rem_guarded; assumption.
  - apply wf_sym_div_rem_guarded; assumption.
Qed.

Lemma wf_sym_alu_reg : forall allowed op is_word a b,
  (is_word = false \/ (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu)) ->
  wf_sym_expr allowed 64%positive a ->
  wf_sym_expr allowed 64%positive b ->
  wf_sym_expr allowed 64%positive (sym_alu_reg op is_word a b).
Proof.
  intros allowed op [|] a b Hmul Ha Hb; cbn [sym_alu_reg].
  - destruct Hmul as [Hdis | Hno]; [discriminate Hdis |].
    apply wf_sym_cast; [reflexivity |].
    apply wf_sym_alu_reg_raw;
      [left; reflexivity | left; exact Hno
      | apply wf_sym_cast; [reflexivity | exact Ha]
      | apply wf_sym_cast; [reflexivity | exact Hb]].
  - apply wf_sym_alu_reg_raw; [right; reflexivity | right; reflexivity | exact Ha | exact Hb].
Qed.

Definition rv_val_regs_wf (allowed : list (string * positive)) (vrf : rv_val_regs) : Prop :=
  forall r, mc_sym_val_wf allowed (rv_val_read r vrf).

Lemma rv_val_regs_wf_write : forall allowed vrf rd sv,
  rv_val_regs_wf allowed vrf ->
  mc_sym_val_wf allowed sv ->
  rv_val_regs_wf allowed (rv_val_write rd sv vrf).
Proof.
  intros allowed vrf rd sv Hw Hsv r.
  unfold rv_val_read, rv_val_write.
  destruct (N.eqb r 0%N) eqn:Er0; [apply wf_sym_bv_const |].
  destruct (N.eqb rd 0%N) eqn:Erd0.
  { pose proof (Hw r) as Hr'; unfold rv_val_read in Hr'; rewrite Er0 in Hr'; exact Hr'. }
  destruct (N.eqb r rd); [exact Hsv |].
  pose proof (Hw r) as Hr'; unfold rv_val_read in Hr'; rewrite Er0 in Hr'; exact Hr'.
Qed.

Theorem summarize_rv64_dag_at_wf :
  forall fuel insts im visited pc allowed sp_off vrf astk ret_w d_mc,
    (forall q, pt_get (N.succ_pos q) im = lookup_rv_inst insts q) ->
    rv_supported_arg_width ret_w = true ->
    forallb inst_no_word_mulh insts = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    rv_val_read 2%N vrf = MSV_StackPtr sp_off ->
    rv_val_regs_wf allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    summarize_rv64_dag_at fuel im visited pc sp_off vrf astk ret_w = inr d_mc ->
    wf_cfg_dag allowed d_mc = true.
Proof.
  intros fuel insts im visited pc allowed sp_off vrf astk ret_w d_mc Him.
  revert visited pc allowed sp_off vrf astk ret_w d_mc.
  induction fuel as [| fuel' IH];
    intros visited pc allowed sp_off vrf astk ret_w d_mc
           Hrw Hnmul Hrng Hsp2 Hwf Hstk Hsum;
    cbn [summarize_rv64_dag_at] in Hsum.
  - destruct (pt_has_n pc visited); discriminate Hsum.
  - destruct (pt_has_n pc visited); [discriminate Hsum |].
    destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Elook; [| discriminate Hsum].
    rewrite Him in Elook.
    assert (Hdec_mulh : inst_no_word_mulh dec = true).
    { clear -Elook Hnmul. induction insts as [| d rest IHl]; cbn in *; [discriminate |].
      apply andb_true_iff in Hnmul as [Hd Hr].
      destruct (N.eqb (dri_off d) pc); [inversion Elook; subst; exact Hd | exact (IHl Hr Elook)]. }
    destruct (dri_inst dec) as
      [| rd imm
       | op is_word rd rs1 imm
       | op is_word rd rs1 rs2
       | sz is_signed rd rs1 imm
       | sz rs1 rs2 imm
       | cond rs1 rs2 rel
       | rel
       | ] eqn:Ed.
    + exact (IH (pt_add_n pc visited) (pc + dri_len dec)%N allowed sp_off vrf astk ret_w d_mc
                Hrw Hnmul Hrng Hsp2 Hwf Hstk Hsum).
    + destruct (rv_sym_step_write rd (MSV_Expr (ce_bv_z 64%positive imm)) sp_off vrf astk)
        as [[[sp_off' vrf'] astk'] |] eqn:Est; [| discriminate Hsum].
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      assert (Hwf' : rv_val_regs_wf allowed vrf').
      { unfold rv_sym_step_write in Est; destruct (N.eqb rd 2%N); [discriminate Est |].
        inversion Est; subst; apply rv_val_regs_wf_write; [exact Hwf | apply wf_sym_bv_z]. }
      assert (Hstk' : mc_sym_stack_wf allowed sp_off' astk').
      { unfold rv_sym_step_write in Est; destruct (N.eqb rd 2%N); [discriminate Est | inversion Est; subst; exact Hstk]. }
      exact (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hrng' Hsp2' Hwf' Hstk' Hsum).
    + set (sv_opt :=
        match op, is_word, rv_val_read rs1 vrf with
        | RAI_Addi, false, MSV_StackPtr base_off =>
            let off' := (base_off + imm)%Z in
            if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z then Some (MSV_StackPtr off') else None
        | RAI_Addi, false, MSV_SavedReg r0 =>
            if Z.eqb imm 0%Z then Some (MSV_SavedReg r0) else None
        | _, _, MSV_Expr e => Some (MSV_Expr (sym_alu_imm op is_word e imm))
        | _, _, _ => None
        end) in *.
      destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hsum].
      destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
        [| discriminate Hsum].
      assert (Hsv_wf : mc_sym_val_wf allowed sv).
      { subst sv_opt; destruct (rv_val_read rs1 vrf) as [| e1 | r0 | base_off] eqn:Er1.
        - destruct op, is_word; discriminate Esv.
        - assert (He_eq : sv = MSV_Expr (sym_alu_imm op is_word e1 imm))
            by (destruct op, is_word; inversion Esv; reflexivity).
          rewrite He_eq; apply wf_sym_alu_imm; pose proof (Hwf rs1) as H1; rewrite Er1 in H1; exact H1.
        - destruct op, is_word; try discriminate Esv; destruct (Z.eqb imm 0%Z); try discriminate Esv;
            inversion Esv; exact I.
        - destruct op, is_word; try discriminate Esv.
          cbv zeta in Esv.
          destruct (Z.leb (- mc_frame_cap) (base_off + imm) && Z.leb (base_off + imm) 0%Z) eqn:Eb; try discriminate Esv.
          apply andb_true_iff in Eb as [Eb1 Eb2]; apply Z.leb_le in Eb1; apply Z.leb_le in Eb2.
          inversion Esv; cbn [mc_sym_val_wf]; lia. }
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      assert (Hwf' : rv_val_regs_wf allowed vrf' /\ mc_sym_stack_wf allowed sp_off' astk').
      { unfold rv_sym_step_write in Est; destruct (N.eqb rd 2%N).
        - destruct sv; try discriminate Est; destruct (Z.leb (- mc_frame_cap) off && Z.leb off 0%Z) eqn:Eb; try discriminate Est.
          apply andb_true_iff in Eb as [Eb1 Eb2]; apply Z.leb_le in Eb1; apply Z.leb_le in Eb2.
          inversion Est; subst; split;
            [apply rv_val_regs_wf_write; assumption | eapply mc_sym_stk_prune_wf; [lia | exact Hstk]].
        - inversion Est; subst; split; [apply rv_val_regs_wf_write; assumption | exact Hstk]. }
      exact (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hrng' Hsp2' (proj1 Hwf') (proj2 Hwf') Hsum).
    + set (is_mv := ((match op with RAR_Add => negb is_word | _ => false end) &&
                     (N.eqb rs1 0%N || N.eqb rs2 0%N))%bool) in *.
      set (sv_opt :=
        if is_mv then
          let sv := if N.eqb rs1 0%N then rv_val_read rs2 vrf else rv_val_read rs1 vrf in
          match sv with MSV_Undef => None | _ => Some sv end
        else
          match rv_val_read rs1 vrf, rv_val_read rs2 vrf with
          | MSV_Expr e1, MSV_Expr e2 => Some (MSV_Expr (sym_alu_reg op is_word e1 e2))
          | _, _ => None
          end) in *.
      destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hsum].
      destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
        [| discriminate Hsum].
      assert (Hsv_wf : mc_sym_val_wf allowed sv).
      { destruct is_mv eqn:Emv.
        - subst sv_opt; cbn [fst snd] in Esv.
          destruct (N.eqb rs1 0%N).
          + destruct (rv_val_read rs2 vrf) eqn:Er2; try discriminate Esv; inversion Esv; subst sv;
              pose proof (Hwf rs2) as H2; rewrite Er2 in H2; exact H2.
          + destruct (rv_val_read rs1 vrf) eqn:Er1; try discriminate Esv; inversion Esv; subst sv;
              pose proof (Hwf rs1) as H1; rewrite Er1 in H1; exact H1.
        - subst sv_opt; destruct (rv_val_read rs1 vrf) as [| e1 | |] eqn:Er1; try discriminate Esv.
          destruct (rv_val_read rs2 vrf) as [| e2 | |] eqn:Er2; try discriminate Esv.
          inversion Esv; subst sv; clear Esv.
          assert (Hok_m : is_word = false \/ (op <> RAR_Mulh /\ op <> RAR_Mulhsu /\ op <> RAR_Mulhu)).
          { destruct is_word; [| left; reflexivity].
            right; unfold inst_no_word_mulh in Hdec_mulh; rewrite Ed in Hdec_mulh.
            destruct op; repeat split; intro C; discriminate C || discriminate Hdec_mulh. }
          apply wf_sym_alu_reg;
            [exact Hok_m
            | pose proof (Hwf rs1) as H1; rewrite Er1 in H1; exact H1
            | pose proof (Hwf rs2) as H2; rewrite Er2 in H2; exact H2]. }
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      assert (Hwf' : rv_val_regs_wf allowed vrf' /\ mc_sym_stack_wf allowed sp_off' astk').
      { unfold rv_sym_step_write in Est; destruct (N.eqb rd 2%N).
        - destruct sv; try discriminate Est; destruct (Z.leb (- mc_frame_cap) off && Z.leb off 0%Z); try discriminate Est.
          inversion Est; subst; split;
            [apply rv_val_regs_wf_write; assumption | eapply mc_sym_stk_prune_wf; [lia | exact Hstk]].
        - inversion Est; subst; split; [apply rv_val_regs_wf_write; assumption | exact Hstk]. }
      exact (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hrng' Hsp2' (proj1 Hwf') (proj2 Hwf') Hsum).
    + destruct (rv_val_read rs1 vrf) as [| | | base_off]; try discriminate Hsum.
      destruct (mc_slot_in_frame sp_off (base_off + imm) sz); [| discriminate Hsum].
      destruct (mc_sym_stk_load (base_off + imm) sz is_signed astk) as [sv |] eqn:Eload;
        [| discriminate Hsum].
      destruct (rv_sym_step_write rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
        [| discriminate Hsum].
      pose proof (mc_sym_stk_load_wf _ _ _ _ _ _ _ Hstk Eload) as Hsv_wf.
      destruct (rv_sym_step_write_sp _ _ _ _ _ _ _ _ Hrng Hsp2 Est) as [Hrng' Hsp2'].
      assert (Hwf' : rv_val_regs_wf allowed vrf' /\ mc_sym_stack_wf allowed sp_off' astk').
      { unfold rv_sym_step_write in Est; destruct (N.eqb rd 2%N).
        - destruct sv; try discriminate Est; destruct (Z.leb (- mc_frame_cap) off && Z.leb off 0%Z); try discriminate Est.
          inversion Est; subst; split;
            [apply rv_val_regs_wf_write; assumption | eapply mc_sym_stk_prune_wf; [lia | exact Hstk]].
        - inversion Est; subst; split; [apply rv_val_regs_wf_write; assumption | exact Hstk]. }
      exact (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hrng' Hsp2' (proj1 Hwf') (proj2 Hwf') Hsum).
    + destruct (rv_val_read rs1 vrf) as [| | | base_off]; try discriminate Hsum.
      destruct (mc_slot_in_frame sp_off (base_off + imm) sz) eqn:Eslot; [| discriminate Hsum].
      destruct (match rv_val_read rs2 vrf with
                | MSV_Undef => false
                | MSV_Expr _ => true
                | MSV_SavedReg _ | MSV_StackPtr _ => mc_mem_size_eqb sz MS_8
                end); [| discriminate Hsum].
      exact (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hrng Hsp2 Hwf
                (mc_sym_stk_store_wf _ _ _ _ _ _ Eslot (Hwf rs2) Hstk) Hsum).
    + destruct (rv_val_read rs1 vrf) as [| e1 | |] eqn:Er1; try discriminate Hsum.
      destruct (rv_val_read rs2 vrf) as [| e2 | |] eqn:Er2; try discriminate Hsum.
      destruct (add_rel_off pc rel) as [tgt_pc |]; [| discriminate Hsum].
      destruct (summarize_rv64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk ret_w) as [| dt] eqn:Edt;
        [discriminate Hsum |].
      destruct (summarize_rv64_dag_at fuel' im (pt_add_n pc visited) (pc + dri_len dec)%N sp_off vrf astk ret_w) as [| df] eqn:Edf;
        [discriminate Hsum |].
      inversion Hsum; subst d_mc; clear Hsum.
      pose proof (Hwf rs1) as H1; rewrite Er1 in H1; pose proof (Hwf rs2) as H2; rewrite Er2 in H2.
      assert (Hbc : wf_sym_expr allowed 1%positive (sym_br_cond cond e1 e2))
        by (destruct cond; apply wf_sym_icmp; assumption).
      destruct Hbc as (Htc & Hwc & Hlfc & Hvc).
      cbn [wf_cfg_dag]; rewrite Htc, Hwc, Hlfc, Hvc; cbn [Pos.eqb andb].
      rewrite (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hrng Hsp2 Hwf Hstk Edt),
              (IH _ _ _ _ _ _ _ _ Hrw Hnmul Hrng Hsp2 Hwf Hstk Edf); reflexivity.
    + destruct (add_rel_off pc rel); [| discriminate Hsum].
      exact (IH (pt_add_n pc visited) _ allowed sp_off vrf astk ret_w d_mc Hrw Hnmul Hrng Hsp2 Hwf Hstk Hsum).
    + destruct (rv_sym_epilogue_ok sp_off vrf); [| discriminate Hsum].
      destruct (rv_val_read 10%N vrf) as [| e_ret | |] eqn:Er10; try discriminate Hsum.
      inversion Hsum; subst d_mc; clear Hsum.
      pose proof (Hwf 10%N) as Ha10; rewrite Er10 in Ha10.
      assert (Hrte : wf_sym_expr allowed ret_w (rv_trunc_ret_expr ret_w e_ret)).
      { unfold rv_trunc_ret_expr; destruct (Pos.eqb ret_w 64%positive) eqn:Ew64.
        - apply Pos.eqb_eq in Ew64; subst ret_w; exact Ha10.
        - assert (Hlt64 : (ret_w <? 64)%positive = true) by (exact (rv_supported_arg_width_lt64 _ Hrw Ew64)).
          apply wf_sym_cast; [exact Hlt64 | exact Ha10]. }
      destruct Hrte as (Hte & Hwe & Hlfe & Hve).
      cbn [wf_cfg_dag]; rewrite Hte, Hwe, Hlfe, Hve, Pos.eqb_refl; reflexivity.
Qed.

Lemma decode_rvc_hw_no_word_mulh : forall hw inst,
  decode_rvc_hw hw = Some inst ->
  (match inst with
   | RV_AluReg RAR_Mulh true _ _ _
   | RV_AluReg RAR_Mulhsu true _ _ _
   | RV_AluReg RAR_Mulhu true _ _ _ => False
   | _ => True
   end).
Proof.
  intros hw inst H.
  unfold decode_rvc_hw in H.
  destruct (N.eqb hw 0%N); [discriminate |].
  cbv zeta in H;
  repeat match type of H with
  | Some _ = Some _ => inversion H; subst; exact I
  | None = Some _ => discriminate H
  | (if true then _ else _) = _ => cbv iota in H
  | (if false then _ else _) = _ => cbv iota in H
  | (if ?b then _ else _) = _ => destruct b
  end.
Qed.

Lemma decode_rv32_word_no_word_mulh : forall w inst,
  decode_rv32_word w = Some inst ->
  (match inst with
   | RV_AluReg RAR_Mulh true _ _ _
   | RV_AluReg RAR_Mulhsu true _ _ _
   | RV_AluReg RAR_Mulhu true _ _ _ => False
   | _ => True
   end).
Proof.
  intros w inst H.
  unfold decode_rv32_word in H.
  destruct (N.eqb (bit_slice w 0%N 7%N) 55%N); [inversion H; subst; exact I |].
  destruct (N.eqb (bit_slice w 0%N 7%N) 19%N).
  { cbv zeta in H;
    repeat match type of H with
    | Some _ = Some _ => inversion H; subst; exact I
    | None = Some _ => discriminate H
    | (if true then _ else _) = _ => cbv iota in H
    | (if false then _ else _) = _ => cbv iota in H
    | (if ?b then _ else _) = _ => destruct b
    end. }
  destruct (N.eqb (bit_slice w 0%N 7%N) 27%N).
  { cbv zeta in H;
    repeat match type of H with
    | Some _ = Some _ => inversion H; subst; exact I
    | None = Some _ => discriminate H
    | (if true then _ else _) = _ => cbv iota in H
    | (if false then _ else _) = _ => cbv iota in H
    | (if ?b then _ else _) = _ => destruct b
    end. }
  destruct (N.eqb (bit_slice w 0%N 7%N) 51%N).
  { cbn [Datatypes.option_map] in H.
    destruct (if N.eqb _ 0%N then _ else _) as [r |]; [inversion H; subst; destruct r; exact I | discriminate H]. }
  destruct (N.eqb (bit_slice w 0%N 7%N) 59%N).
  { destruct (N.eqb (bit_slice w 25%N 7%N) 0%N);
      [destruct (N.eqb (bit_slice w 12%N 3%N) 0%N); [| destruct (N.eqb (bit_slice w 12%N 3%N) 1%N); [| destruct (N.eqb (bit_slice w 12%N 3%N) 5%N)]];
       try (inversion H; subst; exact I); discriminate H |].
    destruct (N.eqb (bit_slice w 25%N 7%N) 32%N);
      [destruct (N.eqb (bit_slice w 12%N 3%N) 0%N); [| destruct (N.eqb (bit_slice w 12%N 3%N) 5%N)];
       try (inversion H; subst; exact I); discriminate H |].
    destruct (N.eqb (bit_slice w 25%N 7%N) 1%N);
      [destruct (N.eqb (bit_slice w 12%N 3%N) 0%N); [| destruct (N.eqb (bit_slice w 12%N 3%N) 4%N); [| destruct (N.eqb (bit_slice w 12%N 3%N) 5%N); [| destruct (N.eqb (bit_slice w 12%N 3%N) 6%N); [| destruct (N.eqb (bit_slice w 12%N 3%N) 7%N)]]]];
       try (inversion H; subst; exact I); discriminate H | discriminate H]. }
  cbv zeta in H;
  repeat match type of H with
  | Some _ = Some _ => inversion H; subst; exact I
  | None = Some _ => discriminate H
  | (if true then _ else _) = _ => cbv iota in H
  | (if false then _ else _) = _ => cbv iota in H
  | (if ?b then _ else _) = _ => destruct b
  | Datatypes.option_map _ ?x = _ => destruct x; cbn [Datatypes.option_map] in H
  end.
Qed.

Lemma decode_rv64_stream_acc_no_word_mulh : forall fuel rvc cur cur_off acc insts,
  forallb inst_no_word_mulh acc = true ->
  decode_rv64_stream_acc fuel rvc cur cur_off acc = inr insts ->
  forallb inst_no_word_mulh insts = true.
Proof.
  induction fuel as [| fuel' IH]; intros rvc [| b0 r0] cur_off acc insts Hacc H;
    cbn [decode_rv64_stream_acc] in H.
  - inversion H; subst insts; rewrite elf_rev_tr_eq, forallb_forall in *;
      intros x Hx; apply Hacc; rewrite in_rev; exact Hx.
  - discriminate H.
  - inversion H; subst insts; rewrite elf_rev_tr_eq, forallb_forall in *;
      intros x Hx; apply Hacc; rewrite in_rev; exact Hx.
  - destruct (take_u16_le (b0 :: r0)) as [[hw rest2] |] eqn:Ehw; [| discriminate H].
    destruct (negb (N.eqb (N.modulo hw 4%N) 3%N)).
    + destruct (negb rvc); [discriminate H |].
      destruct (decode_rvc_hw hw) as [inst |] eqn:Edec; [| discriminate H].
      eapply IH; [| exact H].
      cbn [forallb]; rewrite Hacc, andb_true_r.
      pose proof (decode_rvc_hw_no_word_mulh hw inst Edec) as Hnm.
      unfold inst_no_word_mulh; cbn [dri_inst].
      destruct inst as [| | | op [|] | | | | |]; try reflexivity; destruct op; try reflexivity; contradiction.
    + destruct (take_u32_le (b0 :: r0)) as [[w rest4] |] eqn:Ew; [| discriminate H].
      destruct (decode_rv32_word w) as [inst |] eqn:Edec; [| discriminate H].
      eapply IH; [| exact H].
      cbn [forallb]; rewrite Hacc, andb_true_r.
      pose proof (decode_rv32_word_no_word_mulh w inst Edec) as Hnm.
      unfold inst_no_word_mulh; cbn [dri_inst].
      destruct inst as [| | | op [|] | | | | |]; try reflexivity; destruct op; try reflexivity; contradiction.
Qed.

Lemma decode_rv64_bytes_no_word_mulh : forall rvc code insts,
  decode_rv64_bytes rvc code = inr insts ->
  forallb inst_no_word_mulh insts = true.
Proof.
  intros rvc code insts H; unfold decode_rv64_bytes in H.
  destruct (Nat.eqb (elf_length_tr code) 0 || negb (Nat.eqb (Nat.modulo (elf_length_tr code) 2) 0));
    [discriminate H |].
  destruct (negb rvc && negb (Nat.eqb (Nat.modulo (elf_length_tr code) 4) 0));
    [discriminate H |].
  eapply decode_rv64_stream_acc_no_word_mulh; [| exact H]; reflexivity.
Qed.

Definition rv_rf_matches_args {Pa : Params}
  (penv : param_env Pa) (arg_specs : list rv_arg_spec) (rf : rv_regfile) : Prop :=
  forall (k : nat) sp,
    (k < List.length arg_specs)%nat ->
    nth_error arg_specs k = Some sp ->
    exists v : @Integers.bit_int (ras_width sp),
      penv (ras_name sp) = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
      rv_read_reg (10%N + N.of_nat k) rf =
        (if Pos.eqb (ras_width sp) 64%positive then
           @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
         else
           match ras_ext sp with
           | RAE_ZeroExt => @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
           | RAE_SignExt | RAE_None => @Integers.repr 64%positive (@Integers.signed (ras_width sp) v)
           end).

Lemma rv_build_init_val_regs_other : forall specs base r,
  (r < base \/ base + N.of_nat (List.length specs) <= r)%N ->
  rv_build_init_val_regs base specs r = rv_empty_val_regs r.
Proof.
  induction specs as [| sp rest IH]; intros base r Hrng; cbn [rv_build_init_val_regs List.length] in *.
  - reflexivity.
  - destruct (N.eqb r base) eqn:Erb.
    + apply N.eqb_eq in Erb; lia.
    + apply IH; lia.
Qed.

Lemma rv_init_val_regs_agrees :
  forall {Pa : Params} (penv : param_env Pa) foracle arg_specs rf,
    forallb rv_valid_arg_spec arg_specs = true ->
    rv_rf_matches_args penv arg_specs rf ->
    rv_val_regs_agrees penv foracle rf (rv_read_reg 2%N rf)
      (rv_build_init_val_regs 10%N arg_specs) rf.
Proof.
  intros Pa penv foracle arg_specs rf Hws Hm r.
  assert (Hgen : forall base specs,
    (1 <= base)%N ->
    forallb rv_valid_arg_spec specs = true ->
    (forall (k : nat) sp, (k < List.length specs)%nat -> nth_error specs k = Some sp ->
      exists v : @Integers.bit_int (ras_width sp),
        penv (ras_name sp) = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
        rv_read_reg (base + N.of_nat k) rf =
          (if Pos.eqb (ras_width sp) 64%positive then
             @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
           else
             match ras_ext sp with
             | RAE_ZeroExt => @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
             | RAE_SignExt | RAE_None => @Integers.repr 64%positive (@Integers.signed (ras_width sp) v)
             end)) ->
    forall r0,
      mc_sym_val_agrees penv foracle (fun r1 => rv_read_reg r1 rf) (rv_read_reg 2%N rf)
        (rv_val_read r0 (rv_build_init_val_regs base specs)) (rv_read_reg r0 rf)).
  { clear Hws Hm r.
    intros base specs; revert base; induction specs as [| sp rest IH]; intros base Hge1 Hws' Hm' r0;
      cbn [rv_build_init_val_regs] in *.
    - unfold rv_val_read, rv_empty_val_regs.
      destruct (N.eqb r0 0%N) eqn:Er0.
      + apply N.eqb_eq in Er0; subst r0; unfold rv_read_reg; cbn [N.eqb mc_sym_val_agrees];
          rewrite eval_ce_const, repr_zero_N; reflexivity.
      + destruct (N.eqb r0 2%N) eqn:Er2.
        * apply N.eqb_eq in Er2; subst r0; cbn [mc_sym_val_agrees]; split;
            [unfold mc_frame_cap; lia | rewrite mc_add_ptr_zero; reflexivity].
        * destruct (n_in_list r0 rv_preserved_non_sp_regs); [reflexivity | exact I].
    - apply andb_true_iff in Hws' as [Hwsp Hwrest].
      unfold rv_valid_arg_spec in Hwsp; apply andb_true_iff in Hwsp as [Hwsp Hnd].
      unfold rv_val_read in *.
      destruct (N.eqb r0 0%N) eqn:Er0.
      { unfold rv_read_reg; rewrite Er0; cbn [mc_sym_val_agrees]; rewrite eval_ce_const, repr_zero_N; reflexivity. }
      destruct (N.eqb r0 base) eqn:Erb.
      + apply N.eqb_eq in Erb; subst base.
        destruct (Hm' 0%nat sp ltac:(cbn; lia) eq_refl) as [v [Hp Hrv]].
        rewrite N.add_0_r in Hrv; rewrite Hrv.
        cbn [mc_sym_val_agrees]; unfold rv_init_arg_expr.
        destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
        * apply Pos.eqb_eq in Ew64; destruct sp as [nm w ext]; cbn in *; subst w.
          unfold eval_closed_cert_expr; cbn [eval_cert_expr].
          rewrite Hp; cbn [eou_bind lookup_let_val check_scalar_width]; rewrite Pos.eqb_refl.
          rewrite (@Integers.repr_unsigned 64%positive); reflexivity.
        * destruct (ras_ext sp) eqn:Eext.
          -- rewrite (eval_ce_sext penv foracle (ras_width sp) 64%positive (CE_Var (ras_name sp) (ras_width sp)) v).
             ++ reflexivity.
             ++ exact (rv_supported_arg_width_lt64 _ Hwsp Ew64).
             ++ unfold eval_closed_cert_expr; cbn [eval_cert_expr]; rewrite Hp; cbn [lookup_let_val check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
          -- rewrite (eval_ce_sext penv foracle (ras_width sp) 64%positive (CE_Var (ras_name sp) (ras_width sp)) v).
             ++ reflexivity.
             ++ exact (rv_supported_arg_width_lt64 _ Hwsp Ew64).
             ++ unfold eval_closed_cert_expr; cbn [eval_cert_expr]; rewrite Hp; cbn [lookup_let_val check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
          -- rewrite (eval_ce_zext penv foracle (ras_width sp) 64%positive (CE_Var (ras_name sp) (ras_width sp)) v).
             ++ reflexivity.
             ++ exact (rv_supported_arg_width_lt64 _ Hwsp Ew64).
             ++ unfold eval_closed_cert_expr; cbn [eval_cert_expr]; rewrite Hp; cbn [lookup_let_val check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
      + assert (Hargs : forall (k : nat) sp0, (k < List.length rest)%nat -> nth_error rest k = Some sp0 ->
          exists v : @Integers.bit_int (ras_width sp0),
            penv (ras_name sp0) = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp0) v)) /\
            rv_read_reg (N.succ base + N.of_nat k) rf =
              (if Pos.eqb (ras_width sp0) 64%positive then
                 @Integers.repr 64%positive (@Integers.unsigned (ras_width sp0) v)
               else
                 match ras_ext sp0 with
                 | RAE_ZeroExt => @Integers.repr 64%positive (@Integers.unsigned (ras_width sp0) v)
                 | RAE_SignExt | RAE_None => @Integers.repr 64%positive (@Integers.signed (ras_width sp0) v)
                 end)).
        { intros k sp0 Hk Hnth.
          destruct (Hm' (S k) sp0 ltac:(cbn; lia) Hnth) as [v [Hp0 Hrv0]].
          exists v; split; [exact Hp0 |].
          replace (N.succ base + N.of_nat k)%N with (base + N.of_nat (S k))%N by lia; exact Hrv0. }
        pose proof (IH (N.succ base) ltac:(lia) Hwrest Hargs r0) as Hrec.
        unfold rv_val_read in Hrec; rewrite Er0 in Hrec; exact Hrec. }
  exact (Hgen 10%N arg_specs ltac:(lia) Hws Hm r).
Qed.

Lemma rv_init_val_regs_wf :
  forall allowed_all arg_specs,
    (forall sp, In sp arg_specs -> In (ras_name sp, ras_width sp) allowed_all) ->
    forallb rv_valid_arg_spec arg_specs = true ->
    rv_val_regs_wf allowed_all (rv_build_init_val_regs 10%N arg_specs).
Proof.
  intros allowed_all arg_specs Hall Hws.
  assert (Hgen : forall base specs,
    (forall sp, In sp specs -> In (ras_name sp, ras_width sp) allowed_all) ->
    forallb rv_valid_arg_spec specs = true ->
    rv_val_regs_wf allowed_all (rv_build_init_val_regs base specs)).
  { intros base specs; revert base; induction specs as [| sp rest IH]; intros base Hin Hws' r;
      cbn [rv_build_init_val_regs] in *.
    - unfold rv_val_read, rv_empty_val_regs.
      destruct (N.eqb r 0%N); [apply wf_sym_bv_const |].
      destruct (N.eqb r 2%N); [cbn [mc_sym_val_wf]; unfold mc_frame_cap; lia |].
      destruct (n_in_list r rv_preserved_non_sp_regs); exact I.
    - apply andb_true_iff in Hws' as [Hwsp Hwrest].
      unfold rv_valid_arg_spec in Hwsp; apply andb_true_iff in Hwsp as [Hwsp Hnd].
      unfold rv_val_read in *.
      destruct (N.eqb r 0%N) eqn:Er0; [apply wf_sym_bv_const |].
      destruct (N.eqb r base) eqn:Erb.
      + unfold rv_init_arg_expr.
        assert (Hvar : wf_sym_expr allowed_all (ras_width sp) (CE_Var (ras_name sp) (ras_width sp))).
        { split; [| split; [| split]].
          - cbn [wt_cert_expr lookup_let_width]; exact Hnd.
          - reflexivity.
          - reflexivity.
          - apply incl_vars_subset_b; intros [nm0 w0] H0; cbn in H0; destruct H0 as [H0 | []].
            inversion H0; subst; apply Hin; left; reflexivity. }
        destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
        * apply Pos.eqb_eq in Ew64; rewrite Ew64 in Hvar |- *; exact Hvar.
        * assert (Hlt : (ras_width sp <? 64)%positive = true) by (exact (rv_supported_arg_width_lt64 _ Hwsp Ew64)).
          destruct (ras_ext sp); apply wf_sym_cast; assumption.
      + pose proof (IH (N.succ base) (fun s Hs => Hin s (or_intror Hs)) Hwrest r) as Hrec.
        unfold rv_val_read in Hrec; rewrite Er0 in Hrec; exact Hrec. }
  exact (Hgen 10%N arg_specs Hall Hws).
Qed.

Theorem summarize_rv64_dag_wf :
  forall fuel insts arg_specs ret_w d_mc,
    forallb inst_no_word_mulh insts = true ->
    summarize_rv64_dag fuel insts arg_specs ret_w = inr d_mc ->
    wf_cfg_dag (List.map (fun sp => (ras_name sp, ras_width sp)) arg_specs) d_mc = true.
Proof.
  intros fuel insts arg_specs ret_w d_mc Hnmul Hsum.
  unfold summarize_rv64_dag in Hsum.
  destruct (Nat.leb (List.length arg_specs) 8); [| discriminate Hsum].
  destruct (forallb rv_valid_arg_spec arg_specs) eqn:Hws;
    cbn [negb] in Hsum; [| discriminate Hsum].
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hsum; [| discriminate Hsum].
  set (vrf0 := rv_build_init_val_regs 10%N arg_specs) in *.
  assert (Hsp2 : rv_val_read 2%N vrf0 = MSV_StackPtr 0%Z).
  { unfold rv_val_read, vrf0; cbn [N.eqb]; rewrite rv_build_init_val_regs_other by lia; reflexivity. }
  eapply summarize_rv64_dag_at_wf with (insts := insts) (sp_off := 0%Z);
    [exact (pt_of_list_first_lookup_rv insts)
    | exact Hrw | exact Hnmul | unfold mc_frame_cap; lia | exact Hsp2
    | | apply mc_sym_stack_wf_empty | exact Hsum].
  apply rv_init_val_regs_wf; [| exact Hws].
  intros sp Hsp; apply in_map_iff; exists sp; split; [reflexivity | exact Hsp].
Qed.

Theorem summarize_rv64_dag_sound :
  forall {Pa : Params} fuel rvc code insts arg_specs ret_w d_mc penv foracle rf0 mstk0,
    decode_rv64_bytes rvc code = inr insts ->
    summarize_rv64_dag fuel insts arg_specs ret_w = inr d_mc ->
    mc_valid_sp0 (rv_read_reg 2%N rf0) ->
    rv_rf_matches_args penv arg_specs rf0 ->
    exists rf_end mstk_end,
      rv_exec_mem fuel insts 0%N (rv_read_reg 2%N rf0) rf0 mstk0 = Some (rf_end, mstk_end) /\
      rv_callee_saved_preserved rf0 rf_end /\
      rf_end 1%N = rf0 1%N /\
      eval_cfg_dag penv foracle d_mc =
      DO_Ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end)))).
Proof.
  intros Pa fuel rvc code insts arg_specs ret_w d_mc penv foracle rf0 mstk0 Hdec Hsum Hsp0 Hm.
  pose proof (decode_rv64_bytes_no_word_mulh rvc code insts Hdec) as Hnmul.
  unfold summarize_rv64_dag in Hsum.
  destruct (Nat.leb (List.length arg_specs) 8); [| discriminate Hsum].
  destruct (forallb rv_valid_arg_spec arg_specs) eqn:Hws;
    cbn [negb] in Hsum; [| discriminate Hsum].
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hsum; [| discriminate Hsum].
  set (vrf0 := rv_build_init_val_regs 10%N arg_specs) in *.
  assert (Hsp2 : rv_val_read 2%N vrf0 = MSV_StackPtr 0%Z).
  { unfold rv_val_read, vrf0; cbn [N.eqb]; rewrite rv_build_init_val_regs_other by lia; reflexivity. }
  eapply summarize_rv64_dag_at_sound with (insts := insts) (sp_off := 0%Z);
    [exact (pt_of_list_first_lookup_rv insts)
    | exact Hrw | exact Hnmul | exact Hsp0 | unfold mc_frame_cap; lia | exact Hsp2
    | exact (rv_init_val_regs_agrees penv foracle arg_specs rf0 Hws Hm)
    | apply mc_sym_stack_agrees_empty | exact Hsum].
Qed.

