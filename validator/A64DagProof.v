(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * AArch64 (A64) DAG Well-Formedness & Soundness Proofs ([CertValidator.A64DagProof])

    Purpose:
      Proves bitvector and [NZCV] flag arithmetic equivalence, zero-axiom symbolic
      well-formedness ([summarize_a64_dag_wf]), and AAPCS64 upper-bits semantic soundness
      ([summarize_a64_dag_sound]) linking [a64_exec] to [eval_cfg_dag].

    Trust Contract & Fail-Closed Boundary:
      Proof-only module; not extracted to OCaml. Establishes that any DAG accepted by
      [summarize_a64_dag] is well-formed and preserves concrete [a64_exec] semantics and
      callee-saved registers.

    Assumptions:
      [Stdlib], [Vellvm], [CertValidator.common.Diag], and [CertValidator.{CertFormat,AigLrat,
      AlgRules,CfgDag,Elf64Spec,McFrameMem,McIsaCommon,A64Decode,A64ExecSym}]; zero custom axioms.

    Section Outline:
      5. Flag/bitvector soundness proofs; 5.2 Symbolic well-formedness ([summarize_a64_dag_at_wf]);
      5.3 AAPCS64 upper-bits extension & [summarize_a64_dag_wf] / [summarize_a64_dag_sound]. *)

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
  A64Decode
  A64ExecSym.

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
#[local] Arguments Integers.not : simpl never.
#[local] Arguments Integers.shl : simpl never.
#[local] Arguments Integers.shru : simpl never.
#[local] Arguments Integers.shr : simpl never.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** 5. Bitvector Arithmetic & Semantic Equivalence Proofs ([0 Admitted], [0] Custom Axioms) *)

Lemma a64_supported_arg_width_pos : forall w,
  rv_supported_arg_width w = true ->
  (w = 1%positive \/ w = 8%positive \/ w = 16%positive \/ w = 32%positive \/ w = 64%positive).
Proof.
  intros w Hw.
  do 7 (destruct w as [w|w|]; cbn in Hw; try discriminate Hw; auto 10).
Qed.

Lemma a64_supported_lt32 : forall w,
  rv_supported_arg_width w = true ->
  (w =? 64)%positive = false ->
  (w =? 32)%positive = false ->
  (w <? 32)%positive = true.
Proof.
  intros w Hw H64 H32.
  destruct (a64_supported_arg_width_pos w Hw) as [-> | [-> | [-> | [-> | ->]]]];
    try reflexivity; [rewrite Pos.eqb_refl in H32; discriminate H32
                   | rewrite Pos.eqb_refl in H64; discriminate H64].
Qed.

Lemma a64_w_32_64 : forall sf, (a64_w sf = 32%positive \/ a64_w sf = 64%positive).
Proof.
  intros [|]; [right | left]; reflexivity.
Qed.

Lemma eval_ce_not :
  forall {Pa : Params} (penv : param_env Pa) foracle w e v,
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa w v)) ->
    eval_closed_cert_expr penv foracle (a64_sym_not w e) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.not w v))).
Proof.
  intros Pa penv foracle w e v He; unfold a64_sym_not.
  rewrite eval_ce_binop, He, eval_ce_all_ones; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op].
  reflexivity.
Qed.

Lemma eval_ce_neg :
  forall {Pa : Params} (penv : param_env Pa) foracle w e v,
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa w v)) ->
    eval_closed_cert_expr penv foracle (a64_sym_neg w e) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.neg w v))).
Proof.
  intros Pa penv foracle w e v He; unfold a64_sym_neg.
  rewrite eval_ce_binop, eval_ce_const, He, repr_zero_N; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.sub Integers.zero Integers.neg].
  pose proof (@Integers.modulus_pos w); unfold Integers.sub, Integers.neg, Integers.zero.
  rewrite (@Integers.unsigned_repr w 0%Z) by (unfold Integers.max_unsigned; lia).
  rewrite Z.sub_0_l; reflexivity.
Qed.

Lemma eval_iop_or_poison_contrad :
  forall {Pa : Params} fl (dvr : @dvalue Pa) v64,
    eval_iop (Or (cbf_disjoint fl)) (DVALUE_Base DVALUE_Poison) dvr =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) ->
    False.
Proof.
  intros Pa fl dvr v64 He; cbn [eval_iop] in He.
  destruct dvr as [db | ? ? | vec el2]; try discriminate He.
  - destruct db; cbn in He; discriminate He.
  - destruct vec; cbn in He; try discriminate He.
    destruct (map_monad dvalue_to_dvalue_base el2) as [| | | xs]; unfold bind, ret in He; cbn in He; try discriminate He.
    destruct (vec_loop (eval_iop_integer_base (Or (cbf_disjoint fl)))
               (combine (repeat DVALUE_Poison (Datatypes.length xs)) xs)) as [| | | ans];
      cbn in He; try discriminate He.
    unfold canonicalize_vector in He; destruct (forallb dvalue_is_poison _); discriminate He.
Qed.

Lemma eval_a64_sym_trunc32_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle e v64,
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) ->
    eval_closed_cert_expr penv foracle (a64_sym_trunc32 e) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 32%positive (@Integers.repr 32%positive (@Integers.unsigned 64%positive v64)))).
Proof.
  intros Pa penv foracle e v64 He.
  assert (Hfall : eval_closed_cert_expr penv foracle (ce_trunc64_32 e) =
                  raise_ret (DVALUE_Base (@DVALUE_I Pa 32%positive (@Integers.repr 32%positive (@Integers.unsigned 64%positive v64)))))
    by (eapply eval_ce_trunc; [reflexivity | exact He]).
  unfold a64_sym_trunc32.
  destruct (a64_sym_trunc32_match e) as [inner |] eqn:Em; [| exact Hfall].
  destruct e as [| | | op w1 fl l r | | k fw tw fl o | | |];
    cbn [a64_sym_trunc32_match] in Em; try discriminate Em.
  - destruct op; try discriminate Em.
    destruct l as [| | | | | kl fw tw fll ol | | |]; try discriminate Em.
    destruct kl; try discriminate Em.
    destruct r as [| | | opr w2 flr lr rr | | | | |]; try discriminate Em.
    destruct opr; try discriminate Em.
    destruct rr as [w3 mask | | | | | | | |]; try discriminate Em.
    destruct (Pos.eqb w1 64%positive && Pos.eqb fw 32%positive && Pos.eqb tw 64%positive &&
              Pos.eqb w2 64%positive && Pos.eqb w3 64%positive &&
              N.eqb (N.land mask 4294967295%N) 0%N) eqn:Eok; [| discriminate Em].
    inversion Em; subst inner; clear Em.
    rewrite !andb_true_iff in Eok; destruct Eok as (((((Ew1 & Efw) & Etw) & Ew2) & Ew3) & Emask).
    apply Pos.eqb_eq in Ew1; apply Pos.eqb_eq in Efw; apply Pos.eqb_eq in Etw;
      apply Pos.eqb_eq in Ew2; apply Pos.eqb_eq in Ew3; apply N.eqb_eq in Emask; subst w1 fw tw w2 w3.
    unfold eval_closed_cert_expr in He |- *; cbn [eval_cert_expr] in He.
    destruct (eval_cert_expr penv [] foracle ol) as [| | | dvol] eqn:Eol; cbn [eou_bind] in He;
      try discriminate He.
    destruct (convert_pure (cert_to_pure_conv CCK_ZExt fll) (DTYPE_I 32) dvol (DTYPE_I 64))
      as [| | | dv_ext] eqn:Ecp; cbn [eou_bind] in He; try discriminate He.
    destruct (eval_cert_expr penv [] foracle lr) as [| | | dvlr] eqn:Elr; cbn [eou_bind] in He;
      try discriminate He.
    destruct (eval_iop (cert_to_ibinop CB_And flr) dvlr (DVALUE_Base (@DVALUE_I Pa 64%positive (@Integers.repr 64%positive (Z.of_N mask)))))
      as [| | | dvr] eqn:Eand; cbn [eou_bind] in He; try discriminate He.
    destruct dvol as [[| wol iol | | | | | |] | [|] elts |];
      cbn [convert_pure cert_to_pure_conv get_base_conversion_type convert_pure_base get_vector_conversion_type] in Ecp;
      try discriminate Ecp.
    -- destruct (Pos.eqb 32%positive wol) eqn:Ewol; [| unfold fmap in Ecp; cbn in Ecp; discriminate Ecp].
       apply Pos.eqb_eq in Ewol; subst wol.
       destruct (ccf_nneg fll && (Integers.signed iol <? 0)%Z); unfold fmap, ret in Ecp; cbn in Ecp;
         [inversion Ecp; subst dv_ext; cbn [cert_to_ibinop] in He; exfalso; eapply eval_iop_or_poison_contrad; exact He |].
       inversion Ecp; subst dv_ext; clear Ecp.
       destruct dvlr as [[p | wlr ilr | ? | ? | ? | | | ? ?] | ? ? | vec_lr elr_lr];
         cbn [eval_iop cert_to_ibinop] in Eand; unfold fmap, ret in Eand; cbn [eou_bind] in Eand; try discriminate Eand;
         try (unfold eval_iop_integer_base in Eand; cbn in Eand;
              inversion Eand as [Heqv]; rewrite <- Heqv in He;
              cbn [eval_iop cert_to_ibinop] in He; unfold fmap, ret in He; cbn in He; discriminate He).
       all: try (destruct vec_lr; cbn in Eand; try discriminate Eand;
                 destruct (map_monad dvalue_to_dvalue_base elr_lr) as [| | | xslr]; cbn in Eand; try discriminate Eand;
                 destruct (vec_loop And (combine xslr (repeat (DVALUE_I 64 (Integers.repr (Z.of_N mask))) (Datatypes.length xslr)))) as [| | | anslr]; cbn in Eand; try discriminate Eand;
                 inversion Eand as [Heqv]; rewrite <- Heqv in He; unfold canonicalize_vector in He;
                 destruct (forallb dvalue_is_poison (map DVALUE_Base anslr));
                 cbn [eval_iop cert_to_ibinop] in He; unfold fmap, ret in He; cbn in He; discriminate He).
       destruct (Pos.eq_dec wlr 64%positive) as [-> | Hne];
         [| unfold eval_iop_integer_base in Eand; destruct (Pos.eq_dec wlr 64%positive); [contradiction | cbn in Eand; discriminate Eand]].
       rewrite eval_iop_integer_base_same_width in Eand; unfold fmap, ret in Eand; cbn [eou_bind eval_int_op] in Eand.
       inversion Eand; subst dvr; clear Eand.
       cbn [eval_iop cert_to_ibinop] in He; unfold fmap, ret in He; cbn [eou_bind] in He.
       rewrite eval_iop_integer_base_same_width in He.
       cbn - [Integers.or Integers.and Integers.xor Integers.eq Integers.repr Integers.unsigned] in He.
       assert (Hinv : v64 = @Integers.or 64%positive
                              (@Integers.repr 64%positive (@Integers.unsigned 32%positive iol))
                              (@Integers.and 64%positive ilr (@Integers.repr 64%positive (Z.of_N mask)))).
       { destruct (cbf_disjoint fl) eqn:Edisj;
           [destruct (Integers.eq (Integers.or (Integers.repr (Integers.unsigned iol)) (Integers.and ilr (Integers.repr (Z.of_N mask))))
                                  (Integers.xor (Integers.repr (Integers.unsigned iol)) (Integers.and ilr (Integers.repr (Z.of_N mask)))));
            cbn in He; [| discriminate He] |];
           apply alg_ret_dvalue_I_inj in He; symmetry; exact He. }
       subst v64; clear He.
       do 3 f_equal.
       apply Integers.same_bits_eq; intros i Hi.
       assert (Hi32 : (0 <= i < 32)%Z) by (replace 32%Z with (@Integers.zwordsize 32%positive) by reflexivity; exact Hi).
       assert (Hi64 : (0 <= i < @Integers.zwordsize 64%positive)%Z) by (change (@Integers.zwordsize 64%positive) with 64%Z; lia).
       rewrite (@Integers.testbit_repr 32%positive _ i Hi).
       change (Z.testbit (@Integers.unsigned 64%positive
                 (@Integers.or 64%positive (@Integers.repr 64%positive (@Integers.unsigned 32%positive iol))
                   (@Integers.and 64%positive ilr (@Integers.repr 64%positive (Z.of_N mask))))) i)
         with (@Integers.testbit 64%positive
                 (@Integers.or 64%positive (@Integers.repr 64%positive (@Integers.unsigned 32%positive iol))
                   (@Integers.and 64%positive ilr (@Integers.repr 64%positive (Z.of_N mask)))) i).
       rewrite (@Integers.bits_or 64%positive _ _ i Hi64), (@Integers.bits_and 64%positive _ _ i Hi64).
       rewrite (@Integers.testbit_repr 64%positive _ i Hi64), (@Integers.testbit_repr 64%positive _ i Hi64).
       change (Z.testbit (@Integers.unsigned 32%positive iol) i) with (@Integers.testbit 32%positive iol i).
       assert (Hmk : Z.testbit (Z.of_N mask) i = false).
       { replace 4294967295%N with (N.ones 32%N) in Emask by reflexivity.
         pose proof (N.land_spec mask (N.ones 32%N) (Z.to_N i)) as Hls.
         rewrite Emask, N.bits_0, N.ones_spec_low in Hls by lia.
         destruct (N.testbit mask (Z.to_N i)) eqn:Et; [rewrite andb_true_r in Hls; discriminate |].
         rewrite <- N2Z.inj_testbit, Z2N.id in Et by lia; exact Et. }
       rewrite Hmk, andb_false_r, orb_false_r; reflexivity.
    -- unfold fmap, ret in Ecp; cbn in Ecp; inversion Ecp; subst dv_ext; cbn [cert_to_ibinop] in He;
         exfalso; eapply eval_iop_or_poison_contrad; exact He.
    -- unfold fmap, ret in Ecp; cbn in Ecp; destruct vector; discriminate Ecp.
  - destruct k; try discriminate Em.
    destruct (Pos.eqb fw 32%positive && Pos.eqb tw 64%positive) eqn:Eok; [| discriminate Em].
    inversion Em; subst inner; clear Em.
    apply andb_true_iff in Eok as [Efw Etw]; apply Pos.eqb_eq in Efw; apply Pos.eqb_eq in Etw; subst fw tw.
    unfold eval_closed_cert_expr in He |- *; cbn [eval_cert_expr] in He.
    destruct (eval_cert_expr penv [] foracle o) as [| | | dvo] eqn:Eo; cbn [eou_bind] in He;
      try discriminate He.
    destruct dvo as [[| wo io | | | | | |] | ? ? | vec_o ?];
      cbn [convert_pure cert_to_pure_conv get_base_conversion_type convert_pure_base get_vector_conversion_type] in He;
      unfold fmap, ret in He; cbn in He; try discriminate He;
      [| destruct vec_o; discriminate He].
    destruct (Pos.eqb 32%positive wo) eqn:Ewo; [| cbn in He; discriminate He].
    apply Pos.eqb_eq in Ewo; subst wo.
    destruct (ccf_nneg fl && (Integers.signed io <? 0)%Z); cbn in He; [discriminate He |].
    apply alg_ret_dvalue_I_inj in He; subst v64.
    do 3 f_equal.
    apply Integers.same_bits_eq; intros i Hi.
    assert (Hi32 : (0 <= i < 32)%Z) by (replace 32%Z with (@Integers.zwordsize 32%positive) by reflexivity; exact Hi).
    assert (Hi64 : (0 <= i < @Integers.zwordsize 64%positive)%Z) by (change (@Integers.zwordsize 64%positive) with 64%Z; lia).
    rewrite (@Integers.testbit_repr 32%positive _ i Hi).
    change (Z.testbit (@Integers.unsigned 64%positive (@Integers.repr 64%positive (@Integers.unsigned 32%positive io))) i)
      with (@Integers.testbit 64%positive (@Integers.repr 64%positive (@Integers.unsigned 32%positive io)) i).
    rewrite (@Integers.testbit_repr 64%positive _ i Hi64).
    change (Z.testbit (@Integers.unsigned 32%positive io) i) with (@Integers.testbit 32%positive io i); reflexivity.
Qed.

Lemma bool_to_bv1_eqb : forall (b1 b2 : bool),
  @Integers.eq 1%positive (if b1 then @Integers.one 1%positive else @Integers.zero 1%positive)
                          (if b2 then @Integers.one 1%positive else @Integers.zero 1%positive) = Bool.eqb b1 b2.
Proof.
  intros [|] [|]; compute; reflexivity.
Qed.

Lemma bool_to_bv1_xor : forall (b1 b2 : bool),
  @Integers.xor 1%positive (if b1 then @Integers.one 1%positive else @Integers.zero 1%positive)
                           (if b2 then @Integers.one 1%positive else @Integers.zero 1%positive) =
  (if xorb b1 b2 then @Integers.one 1%positive else @Integers.zero 1%positive).
Proof.
  intros [|] [|]; compute; reflexivity.
Qed.

Lemma subs_z_eq_iff : forall w (lhs rhs : @Integers.bit_int w),
  @Integers.eq w (@Integers.sub w lhs rhs) (@Integers.zero w) = @Integers.eq w lhs rhs.
Proof.
  intros w lhs rhs.
  destruct (@Integers.eq w (@Integers.sub w lhs rhs) (@Integers.zero w)) eqn:Es,
           (@Integers.eq w lhs rhs) eqn:Ee; try reflexivity.
  - pose proof (@Integers.eq_spec w (@Integers.sub w lhs rhs) (@Integers.zero w)) as Hs; rewrite Es in Hs.
    assert (Hu : @Integers.unsigned w lhs = @Integers.unsigned w rhs).
    { pose proof (@Integers.unsigned_range w lhs) as Hrl.
      pose proof (@Integers.unsigned_range w rhs) as Hrr.
      assert (Hm : ((@Integers.unsigned w lhs - @Integers.unsigned w rhs) mod @Integers.modulus w = 0)%Z).
      { unfold Integers.sub in Hs; apply (f_equal (@Integers.unsigned w)) in Hs.
        rewrite Integers.unsigned_repr_eq, Integers.unsigned_zero in Hs; exact Hs. }
      rewrite Z.mod_divide in Hm by (pose proof (@Integers.modulus_pos w); lia).
      destruct Hm as [q Hq]; destruct (Z.eq_dec q 0) as [-> | Hnz]; [lia |].
      exfalso; pose proof (@Integers.modulus_pos w); nia. }
    assert (Heq : lhs = rhs) by (rewrite <- (@Integers.repr_unsigned w lhs), <- (@Integers.repr_unsigned w rhs), Hu; reflexivity).
    subst rhs; rewrite Integers.eq_true in Ee; discriminate Ee.
  - pose proof (@Integers.eq_spec w lhs rhs) as He; rewrite Ee in He; subst rhs.
    rewrite Integers.sub_idem, Integers.eq_true in Es; discriminate Es.
Qed.

Lemma subs_n_xor_v_slt_iff : forall w (lhs rhs : @Integers.bit_int w),
  let res := @Integers.sub w lhs rhs in
  let sl := @Integers.lt w lhs (@Integers.zero w) in
  let sr := @Integers.lt w rhs (@Integers.zero w) in
  let sres := @Integers.lt w res (@Integers.zero w) in
  xorb sres (negb (Bool.eqb sl sr) && negb (Bool.eqb sl sres)) = @Integers.lt w lhs rhs.
Proof.
  intros w lhs rhs res sl sr sres.
  pose proof (@Integers.signed_range w lhs) as Hrl.
  pose proof (@Integers.signed_range w rhs) as Hrr.
  pose proof (@Integers.half_modulus_pos w) as Hhm.
  unfold sl, sr, sres, res, Integers.lt; rewrite !Integers.signed_zero.
  destruct (zlt (@Integers.signed w lhs) 0%Z),
           (zlt (@Integers.signed w rhs) 0%Z),
           (zlt (@Integers.signed w lhs) (@Integers.signed w rhs));
    try lia; try (cbn [Bool.eqb negb andb]; destruct (zlt _ 0%Z); reflexivity).
  all: cbn [Bool.eqb negb andb];
       rewrite Integers.sub_signed, Integers.signed_repr
         by (unfold Integers.min_signed, Integers.max_signed in *; lia);
       destruct (zlt _ 0%Z); [lia || reflexivity | lia || reflexivity].
Qed.

Definition sym_flags_agree {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (sfl : a64_sym_flags) (fl : a64_flags) : Prop :=
  eval_closed_cert_expr penv foracle (asf_n sfl) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_n fl then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
  eval_closed_cert_expr penv foracle (asf_z sfl) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_z fl then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
  eval_closed_cert_expr penv foracle (asf_c sfl) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_c fl then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
  eval_closed_cert_expr penv foracle (asf_v sfl) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if af_v fl then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
  eval_closed_cert_expr penv foracle (asf_n_ne_v sfl) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if xorb (af_n fl) (af_v fl) then @Integers.one 1%positive else @Integers.zero 1%positive))).

Lemma eval_a64_sym_is_neg_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w e v,
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa w v)) ->
    eval_closed_cert_expr penv foracle (a64_sym_is_neg w e) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
      (if @Integers.lt w v (@Integers.zero w) then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle w e v He; unfold a64_sym_is_neg.
  apply (eval_ce_icmp_eq_bool _ _ CIP_Slt); [exact He | rewrite eval_ce_const, repr_zero_N; reflexivity].
Qed.

Lemma eval_a64_sym_bool_not_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle e (b : bool),
    eval_closed_cert_expr penv foracle e =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle (a64_sym_bool_not e) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if negb b then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle e b He; unfold a64_sym_bool_not.
  rewrite eval_ce_binop, He, eval_ce_const, repr_one_N; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.xor Integers.one Integers.zero].
  pose proof (bool_to_bv1_xor b true) as Hx; rewrite xorb_true_r in Hx; rewrite Hx; reflexivity.
Qed.

Lemma eval_a64_sym_bool_xor_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle e1 e2 (b1 b2 : bool),
    eval_closed_cert_expr penv foracle e1 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b1 then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle e2 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b2 then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle (a64_sym_bool_xor e1 e2) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if xorb b1 b2 then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle e1 e2 b1 b2 H1 H2; unfold a64_sym_bool_xor.
  rewrite eval_ce_binop, H1, H2; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.xor Integers.one Integers.zero].
  rewrite bool_to_bv1_xor; reflexivity.
Qed.

Lemma eval_a64_sym_bool_eq_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle e1 e2 (b1 b2 : bool),
    eval_closed_cert_expr penv foracle e1 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b1 then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle e2 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b2 then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle (a64_sym_bool_eq e1 e2) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if Bool.eqb b1 b2 then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle e1 e2 b1 b2 H1 H2; unfold a64_sym_bool_eq.
  rewrite (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _ H1 H2), bool_to_bv1_eqb; reflexivity.
Qed.

Lemma eval_a64_sym_bool_and_or :
  forall {Pa : Params} (penv : param_env Pa) foracle e1 e2 (b1 b2 : bool),
    eval_closed_cert_expr penv foracle e1 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b1 then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle e2 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b2 then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    eval_closed_cert_expr penv foracle (CE_BinOp CB_And 1%positive no_binop_flags e1 e2) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b1 && b2 then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
    eval_closed_cert_expr penv foracle (CE_BinOp CB_Or 1%positive no_binop_flags e1 e2) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b1 || b2 then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle e1 e2 b1 b2 H1 H2; split;
    rewrite eval_ce_binop, H1, H2; cbn [eou_bind];
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op];
    destruct b1, b2; reflexivity.
Qed.

Lemma eval_a64_sym_add_sub_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w is_sub lhs rhs vl vr,
    eval_closed_cert_expr penv foracle lhs = raise_ret (DVALUE_Base (@DVALUE_I Pa w vl)) ->
    eval_closed_cert_expr penv foracle rhs = raise_ret (DVALUE_Base (@DVALUE_I Pa w vr)) ->
    eval_closed_cert_expr penv foracle (fst (a64_sym_add_sub w is_sub lhs rhs)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (fst (a64_eval_add_sub w is_sub vl vr)))) /\
    sym_flags_agree penv foracle (snd (a64_sym_add_sub w is_sub lhs rhs))
                                 (snd (a64_eval_add_sub w is_sub vl vr)).
Proof.
  intros Pa penv foracle w is_sub lhs rhs vl vr Hl Hr.
  unfold a64_sym_add_sub, a64_eval_add_sub; cbn [fst snd].
  assert (Hres : eval_closed_cert_expr penv foracle
                   (CE_BinOp (if is_sub then CB_Sub else CB_Add) w no_binop_flags lhs rhs) =
                 raise_ret (DVALUE_Base (@DVALUE_I Pa w (if is_sub then @Integers.sub w vl vr else @Integers.add w vl vr)))).
  { rewrite eval_ce_binop, Hl, Hr; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; destruct is_sub; reflexivity. }
  split; [exact Hres |].
  pose proof (eval_a64_sym_is_neg_sound _ _ _ _ _ Hres) as Hn.
  pose proof (eval_a64_sym_is_neg_sound _ _ _ _ _ Hl) as Hsl.
  pose proof (eval_a64_sym_is_neg_sound _ _ _ _ _ Hr) as Hsr.
  pose proof (eval_a64_sym_bool_eq_sound _ _ _ _ _ _ Hsl Hsr) as Heqlr.
  pose proof (eval_a64_sym_bool_xor_sound _ _ _ _ _ _ Hsl Hsr) as Hxorlr.
  pose proof (eval_a64_sym_bool_xor_sound _ _ _ _ _ _ Hsl Hn) as Hdif.
  repeat split; cbn [asf_n asf_z asf_c asf_v asf_n_ne_v af_n af_z af_c af_v].
  - exact Hn.
  - destruct is_sub; cbn [af_z].
    + rewrite subs_z_eq_iff.
      exact (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _ Hl Hr).
    + exact (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _ Hres (eval_ce_const _ _ _ 0%N)).
  - destruct is_sub; cbn [af_c].
    + exact (eval_ce_icmp_eq_bool _ _ CIP_Uge _ _ _ _ _ Hl Hr).
    + exact (eval_ce_icmp_eq_bool _ _ CIP_Ult _ _ _ _ _ Hres Hl).
  - destruct is_sub; cbn [af_v].
    + destruct (eval_a64_sym_bool_and_or _ _ _ _ _ _ Hxorlr Hdif) as [Ha _].
      destruct (@Integers.lt w vl (@Integers.zero w)),
               (@Integers.lt w vr (@Integers.zero w)),
               (@Integers.lt w (@Integers.sub w vl vr) (@Integers.zero w)); exact Ha.
    + destruct (eval_a64_sym_bool_and_or _ _ _ _ _ _ Heqlr Hdif) as [Ha _].
      destruct (@Integers.lt w vl (@Integers.zero w)),
               (@Integers.lt w vr (@Integers.zero w)),
               (@Integers.lt w (@Integers.add w vl vr) (@Integers.zero w)); exact Ha.
  - destruct is_sub; cbn [af_n af_v].
    + rewrite subs_n_xor_v_slt_iff.
      exact (eval_ce_icmp_eq_bool _ _ CIP_Slt _ _ _ _ _ Hl Hr).
    + destruct (eval_a64_sym_bool_and_or _ _ _ _ _ _ Heqlr Hdif) as [Ha _].
      pose proof (eval_a64_sym_bool_xor_sound _ _ _ _ _ _ Hn Ha) as Hnxv.
      destruct (@Integers.lt w (@Integers.add w vl vr) (@Integers.zero w)),
               (@Integers.lt w vl (@Integers.zero w)),
               (@Integers.lt w vr (@Integers.zero w)); exact Hnxv.
Qed.

Lemma eval_a64_sym_logic_flags_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w res v,
    eval_closed_cert_expr penv foracle res = raise_ret (DVALUE_Base (@DVALUE_I Pa w v)) ->
    sym_flags_agree penv foracle (a64_sym_logic_flags w res) (a64_eval_logic_flags w v).
Proof.
  intros Pa penv foracle w res v Hres; unfold a64_sym_logic_flags, a64_eval_logic_flags.
  pose proof (eval_a64_sym_is_neg_sound _ _ _ _ _ Hres) as Hn.
  pose proof (eval_ce_icmp_eq_bool _ _ CIP_Eq w res (CE_BvConst w 0%N) v (@Integers.zero w) Hres ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)) as Hz.
  unfold sym_flags_agree; cbn [asf_n asf_z asf_c asf_v asf_n_ne_v af_n af_z af_c af_v].
  split; [exact Hn | split; [exact Hz | split; [rewrite eval_ce_const, repr_zero_N; reflexivity
        | split; [rewrite eval_ce_const, repr_zero_N; reflexivity | rewrite xorb_false_r; exact Hn]]]].
Qed.

Lemma eval_a64_sym_cond_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle c sfl fl,
    sym_flags_agree penv foracle sfl fl ->
    eval_closed_cert_expr penv foracle (a64_sym_cond c sfl) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
      (if a64_eval_cond c fl then @Integers.one 1%positive else @Integers.zero 1%positive))).
Proof.
  intros Pa penv foracle c sfl fl (Hn & Hz & Hc & Hv & Hnxv).
  destruct c; unfold a64_sym_cond, a64_eval_cond.
  - exact Hz.
  - exact (eval_a64_sym_bool_not_sound _ _ _ _ Hz).
  - exact Hc.
  - exact (eval_a64_sym_bool_not_sound _ _ _ _ Hc).
  - exact Hn.
  - exact (eval_a64_sym_bool_not_sound _ _ _ _ Hn).
  - exact Hv.
  - exact (eval_a64_sym_bool_not_sound _ _ _ _ Hv).
  - pose proof (eval_a64_sym_bool_not_sound _ _ _ _ Hz) as Hnz.
    exact (proj1 (eval_a64_sym_bool_and_or _ _ _ _ _ _ Hc Hnz)).
  - pose proof (eval_a64_sym_bool_not_sound _ _ _ _ Hc) as Hnc.
    exact (proj2 (eval_a64_sym_bool_and_or _ _ _ _ _ _ Hnc Hz)).
  - pose proof (eval_a64_sym_bool_not_sound _ _ _ _ Hnxv) as Hn_eq_v.
    destruct (af_n fl), (af_v fl); exact Hn_eq_v.
  - exact Hnxv.
  - pose proof (eval_a64_sym_bool_not_sound _ _ _ _ Hz) as Hnz.
    pose proof (eval_a64_sym_bool_not_sound _ _ _ _ Hnxv) as Hn_eq_v.
    destruct (eval_a64_sym_bool_and_or _ _ _ _ _ _ Hnz Hn_eq_v) as [Ha _].
    destruct (af_z fl), (af_n fl), (af_v fl); exact Ha.
  - exact (proj2 (eval_a64_sym_bool_and_or _ _ _ _ _ _ Hz Hnxv)).
  - rewrite eval_ce_const, repr_one_N; reflexivity.
  - rewrite eval_ce_const, repr_one_N; reflexivity.
Qed.

Lemma eval_a64_sym_flags_imm4_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle nzcv,
    sym_flags_agree penv foracle (a64_sym_flags_of_imm4 nzcv) (a64_flags_of_imm4 nzcv).
Proof.
  intros Pa penv foracle nzcv; unfold a64_sym_flags_of_imm4, a64_flags_of_imm4, sym_flags_agree;
    cbn [asf_n asf_z asf_c asf_v asf_n_ne_v af_n af_z af_c af_v];
    repeat split; rewrite eval_ce_const;
    [ destruct (N.testbit nzcv 3%N)
    | destruct (N.testbit nzcv 2%N)
    | destruct (N.testbit nzcv 1%N)
    | destruct (N.testbit nzcv 0%N)
    | destruct (xorb (N.testbit nzcv 3%N) (N.testbit nzcv 0%N)) ];
    try rewrite repr_one_N; try rewrite repr_zero_N; reflexivity.
Qed.

Lemma eval_a64_sym_ite_flags_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle c (b : bool) st sf tfl ffl,
    eval_closed_cert_expr penv foracle c =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) ->
    sym_flags_agree penv foracle st tfl ->
    sym_flags_agree penv foracle sf ffl ->
    sym_flags_agree penv foracle (a64_sym_ite_flags c st sf) (if b then tfl else ffl).
Proof.
  intros Pa penv foracle c b st sf tfl ffl Hc
    (Htn & Htz & Htc & Htv & Htnxv) (Hfn & Hfz & Hfc & Hfv & Hfnxv).
  unfold a64_sym_ite_flags, sym_flags_agree;
    cbn [asf_n asf_z asf_c asf_v asf_n_ne_v].
  repeat split;
    [ pose proof (eval_ce_select_int _ _ 1%positive _ _ _ _ _ _ Hc Htn Hfn) as H
    | pose proof (eval_ce_select_int _ _ 1%positive _ _ _ _ _ _ Hc Htz Hfz) as H
    | pose proof (eval_ce_select_int _ _ 1%positive _ _ _ _ _ _ Hc Htc Hfc) as H
    | pose proof (eval_ce_select_int _ _ 1%positive _ _ _ _ _ _ Hc Htv Hfv) as H
    | pose proof (eval_ce_select_int _ _ 1%positive _ _ _ _ _ _ Hc Htnxv Hfnxv) as H ];
    destruct b; exact H.
Qed.

Lemma eval_a64_sym_shift_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w e v sh amt,
    (w = 32%positive \/ w = 64%positive) ->
    (amt < N.pos w)%N ->
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa w v)) ->
    eval_closed_cert_expr penv foracle (a64_sym_shift w e sh amt) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (a64_eval_shift w v sh amt))).
Proof.
  intros Pa penv foracle w e v sh amt Hw Hamt He.
  unfold a64_sym_shift, a64_eval_shift.
  assert (Hmod : N.modulo amt (N.pos w) = amt) by (apply N.mod_small; exact Hamt).
  assert (HmodZ : (Z.of_N amt mod Z.pos w = Z.of_N amt)%Z) by (apply Z.mod_small; lia).
  rewrite Hmod, HmodZ.
  pose proof (mod_lt_32_64 w Hw) as Hm3264.
  destruct sh; destruct (N.eqb amt 0%N) eqn:Ez.
  - apply N.eqb_eq in Ez; subst amt; rewrite He;
      change (@Integers.repr w (Z.of_N 0%N)) with (@Integers.zero w); rewrite Integers.shl_zero; reflexivity.
  - rewrite eval_ce_binop, He, eval_ce_const; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    cbn - [Integers.shl Integers.unsigned Integers.repr Z.geb Z.gtb Z.of_N].
    rewrite (@Integers.unsigned_repr w (Z.of_N amt)) by (unfold Integers.max_unsigned; lia).
    replace (Z.of_N amt >=? Z.pos w)%Z with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia); reflexivity.
  - apply N.eqb_eq in Ez; subst amt; rewrite He;
      change (@Integers.repr w (Z.of_N 0%N)) with (@Integers.zero w); rewrite Integers.shru_zero; reflexivity.
  - rewrite eval_ce_binop, He, eval_ce_const; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    cbn - [Integers.shru Integers.unsigned Integers.repr Z.geb Z.of_N].
    rewrite (@Integers.unsigned_repr w (Z.of_N amt)) by (unfold Integers.max_unsigned; lia).
    replace (Z.of_N amt >=? Z.pos w)%Z with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia); reflexivity.
  - apply N.eqb_eq in Ez; subst amt; rewrite He;
      change (@Integers.repr w (Z.of_N 0%N)) with (@Integers.zero w); rewrite Integers.shr_zero; reflexivity.
  - rewrite eval_ce_binop, He, eval_ce_const; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    cbn - [Integers.shr Integers.unsigned Integers.repr Z.geb Z.of_N].
    rewrite (@Integers.unsigned_repr w (Z.of_N amt)) by (unfold Integers.max_unsigned; lia).
    replace (Z.of_N amt >=? Z.pos w)%Z with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia); reflexivity.
  - exact He.
  - apply N.eqb_neq in Ez.
    assert (H1 : eval_closed_cert_expr penv foracle (CE_BinOp CB_LShr w no_binop_flags e (CE_BvConst w amt)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.shru w v (@Integers.repr w (Z.of_N amt)))))).
    { rewrite eval_ce_binop, He, eval_ce_const; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [Integers.shru Integers.unsigned Integers.repr Z.geb Z.of_N].
      rewrite (@Integers.unsigned_repr w (Z.of_N amt)) by (unfold Integers.max_unsigned; lia).
      replace (Z.of_N amt >=? Z.pos w)%Z with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia); reflexivity. }
    assert (H2 : eval_closed_cert_expr penv foracle (CE_BinOp CB_Shl w no_binop_flags e (CE_BvConst w (N.pos w - amt))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.shl w v (@Integers.repr w (Z.pos w - Z.of_N amt)))))).
    { set (d := (N.pos w - amt)%N).
      assert (HdZ : Z.of_N d = (Z.pos w - Z.of_N amt)%Z) by (unfold d; lia).
      rewrite eval_ce_binop, He, eval_ce_const; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [d N.sub Z.sub Integers.shl Integers.unsigned Integers.repr Z.geb Z.gtb Z.of_N].
      rewrite HdZ, (@Integers.unsigned_repr w (Z.pos w - Z.of_N amt)) by (unfold Integers.max_unsigned; lia).
      replace (Z.pos w - Z.of_N amt >=? Z.pos w)%Z with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia); reflexivity. }
    rewrite eval_ce_binop, H1, H2; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity.
Qed.

Lemma eval_a64_sym_extend_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w e64 v64 ext amt,
    (w = 32%positive \/ w = 64%positive) ->
    (amt <= 4)%N ->
    eval_closed_cert_expr penv foracle e64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) ->
    eval_closed_cert_expr penv foracle (a64_sym_extend w e64 ext amt) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (a64_eval_extend w v64 ext amt))).
Proof.
  intros Pa penv foracle w e64 v64 ext amt Hw Hamt He64.
  unfold a64_sym_extend, a64_eval_extend.
  destruct (a64_ext_bits ext) as [src_bits sgn].
  remember (Pos.min src_bits w) as eff eqn:Heff.
  assert (Hle64 : (eff <= 64)%positive)
    by (rewrite Heff; destruct Hw as [-> | ->]; [pose proof (Pos.le_min_r src_bits 32%positive) | pose proof (Pos.le_min_r src_bits 64%positive)]; lia).
  assert (Hsl : eval_closed_cert_expr penv foracle
    (if Pos.eqb eff 64%positive then e64
     else if Pos.eqb eff 32%positive then a64_sym_trunc32 e64
     else CE_Cast CCK_Trunc 64%positive eff no_cast_flags e64) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa eff (@Integers.repr eff (@Integers.unsigned 64%positive v64))))).
  { destruct (Pos.eqb eff 64%positive) eqn:E64.
    - apply Pos.eqb_eq in E64; clear Heff; subst eff; rewrite He64; do 3 f_equal; symmetry; apply (@Integers.repr_unsigned 64%positive).
    - destruct (Pos.eqb eff 32%positive) eqn:E32.
      + apply Pos.eqb_eq in E32; clear Heff; subst eff; exact (eval_a64_sym_trunc32_sound _ _ _ _ He64).
      + apply eval_ce_trunc; [| exact He64].
        apply Pos.ltb_lt; apply Pos.eqb_neq in E64; lia. }
  set (sl_e := if Pos.eqb eff 64%positive then e64
               else if Pos.eqb eff 32%positive then a64_sym_trunc32 e64
               else CE_Cast CCK_Trunc 64%positive eff no_cast_flags e64) in *.
  set (sl_v := @Integers.repr eff (@Integers.unsigned 64%positive v64)) in *.
  assert (Hext : eval_closed_cert_expr penv foracle
    (if Pos.eqb eff w then sl_e else CE_Cast (if sgn then CCK_SExt else CCK_ZExt) eff w no_cast_flags sl_e) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w
      (if Pos.eqb eff w then @Integers.repr w (@Integers.unsigned eff sl_v)
       else if sgn then @Integers.repr w (@Integers.signed eff sl_v)
       else @Integers.repr w (@Integers.unsigned eff sl_v))))).
  { destruct (Pos.eqb eff w) eqn:Eew.
    - apply Pos.eqb_eq in Eew; clear Heff; subst sl_e sl_v; subst eff; rewrite Hsl; do 3 f_equal; symmetry; apply (@Integers.repr_unsigned w).
    - assert (Hltw : (eff <? w)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.eqb_neq in Eew; rewrite Heff in *; pose proof (Pos.le_min_r src_bits w); lia).
      destruct sgn; [apply eval_ce_sext | apply eval_ce_zext]; assumption. }
  destruct (N.eqb amt 0%N) eqn:Ez; [exact Hext |].
  pose proof (mod_lt_32_64 w Hw) as Hm3264.
  assert (Hamtm : N.modulo amt (N.pos w) = amt /\ (Z.of_N amt mod Z.pos w = Z.of_N amt)%Z)
    by (split; [apply N.mod_small | apply Z.mod_small]; destruct Hw as [-> | ->]; lia).
  destruct Hamtm as [HmN HmZ]; rewrite HmN, HmZ.
  rewrite eval_ce_binop, Hext, eval_ce_const; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  cbn - [Integers.shl Integers.unsigned Integers.repr Z.geb Z.gtb Z.of_N].
  rewrite (@Integers.unsigned_repr w (Z.of_N amt)) by (unfold Integers.max_unsigned; destruct Hw as [-> | ->]; lia).
  replace (Z.of_N amt >=? Z.pos w)%Z with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; destruct Hw as [-> | ->]; lia).
  reflexivity.
Qed.

Lemma a64_sxtw_bitfield_eq : forall v : @Integers.bit_int 64%positive,
  @Integers.shr 64%positive
    (@Integers.shl 64%positive v (@Integers.repr 64%positive 32%Z))
    (@Integers.repr 64%positive 32%Z) =
  @Integers.repr 64%positive (@Integers.signed 32%positive (@Integers.repr 32%positive (@Integers.unsigned 64%positive v))).
Proof.
  intro v; apply Integers.same_bits_eq; intros i Hi.
  assert (Hi64 : (0 <= i < 64)%Z) by (replace 64%Z with (@Integers.zwordsize 64%positive) by reflexivity; exact Hi).
  assert (Hu32 : @Integers.unsigned 64%positive (@Integers.repr 64%positive 32%Z) = 32%Z)
    by (apply Integers.unsigned_repr; compute; split; discriminate).
  rewrite Integers.bits_shr by exact Hi.
  rewrite Hu32, (@Integers.testbit_repr 64%positive _ i Hi), Integers.bits_signed
    by (change (@Integers.zwordsize 32%positive) with 32%Z; lia).
  change (@Integers.zwordsize 32%positive) with 32%Z in *.
  change (@Integers.zwordsize 64%positive) with 64%Z in *.
  destruct (zlt (i + 32) 64) as [Hl | Hge]; destruct (zlt i 32) as [Hli | Hgi]; try lia.
  - rewrite Integers.bits_shl by (change (@Integers.zwordsize 64%positive) with 64%Z; lia).
    rewrite Hu32; destruct (zlt (i + 32) 32); [lia |].
    replace (i + 32 - 32)%Z with i by lia.
    rewrite (@Integers.testbit_repr 32%positive _ i ltac:(change (@Integers.zwordsize 32%positive) with 32%Z; lia)); reflexivity.
  - rewrite Integers.bits_shl by (change (@Integers.zwordsize 64%positive) with 64%Z; lia).
    rewrite Hu32; replace (64 - 1)%Z with 63%Z by lia; destruct (zlt 63 32); [lia |].
    replace (63 - 32)%Z with 31%Z by lia; replace (32 - 1)%Z with 31%Z by lia.
    rewrite (@Integers.testbit_repr 32%positive (@Integers.unsigned 64%positive v) 31%Z ltac:(change (@Integers.zwordsize 32%positive) with 32%Z; lia)); reflexivity.
Qed.

Lemma a64_uxtw_bitfield_eq : forall v : @Integers.bit_int 64%positive,
  @Integers.and 64%positive
    (@Integers.shru 64%positive v (@Integers.repr 64%positive 0%Z))
    (@Integers.repr 64%positive (Z.of_N (N.ones 32%N))) =
  @Integers.repr 64%positive (@Integers.unsigned 32%positive (@Integers.repr 32%positive (@Integers.unsigned 64%positive v))).
Proof.
  intro v; change (@Integers.repr 64%positive 0%Z) with (@Integers.zero 64%positive).
  rewrite Integers.shru_zero; apply Integers.same_bits_eq; intros i Hi.
  assert (Hi64 : (0 <= i < 64)%Z) by (replace 64%Z with (@Integers.zwordsize 64%positive) by reflexivity; exact Hi).
  rewrite Integers.bits_and, (@Integers.testbit_repr 64%positive _ i Hi), (@Integers.testbit_repr 64%positive _ i Hi) by exact Hi.
  change (Z.testbit (@Integers.unsigned 32%positive (@Integers.repr 32%positive (@Integers.unsigned 64%positive v))) i)
    with (@Integers.testbit 32%positive (@Integers.repr 32%positive (@Integers.unsigned 64%positive v)) i).
  replace (Z.of_N (N.ones 32%N)) with (Z.ones 32%Z) by reflexivity.
  destruct (Z.ltb i 32) eqn:Ei32.
  - apply Z.ltb_lt in Ei32; rewrite Z.ones_spec_low by lia; rewrite andb_true_r.
    rewrite (@Integers.testbit_repr 32%positive _ i ltac:(change (@Integers.zwordsize 32%positive) with 32%Z; lia)); reflexivity.
  - apply Z.ltb_ge in Ei32; rewrite Z.ones_spec_high by lia; rewrite andb_false_r.
    rewrite Integers.bits_above by (change (@Integers.zwordsize 32%positive) with 32%Z; lia); reflexivity.
Qed.

Lemma shamt_eval_const_lt :
  forall {Pa : Params} (penv : param_env Pa) foracle w e v k,
    (w = 32%positive \/ w = 64%positive) ->
    (k < N.pos w)%N ->
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa w v)) ->
    (forall op, (op = CB_Shl \/ op = CB_LShr \/ op = CB_AShr) ->
      eval_closed_cert_expr penv foracle (CE_BinOp op w no_binop_flags e (CE_BvConst w k)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w
        (match op with
         | CB_Shl => @Integers.shl w v (@Integers.repr w (Z.of_N k))
         | CB_LShr => @Integers.shru w v (@Integers.repr w (Z.of_N k))
         | _ => @Integers.shr w v (@Integers.repr w (Z.of_N k))
         end)))).
Proof.
  intros Pa penv foracle w e v k Hw Hk He op Hop.
  pose proof (mod_lt_32_64 w Hw) as Hm.
  assert (Hlt : (Z.of_N k < Z.pos w)%Z) by lia.
  rewrite eval_ce_binop, He, eval_ce_const; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  destruct Hop as [-> | [-> | ->]];
    cbn - [Integers.shl Integers.shru Integers.shr Integers.unsigned Integers.repr Z.geb Z.gtb Z.of_N];
    rewrite (@Integers.unsigned_repr w (Z.of_N k)) by (unfold Integers.max_unsigned; lia);
    replace (Z.of_N k >=? Z.pos w)%Z with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia); reflexivity.
Qed.

Lemma eval_a64_sym_bitfield_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle sf kind src dst vsrc vdst immr imms,
    (immr < a64_w_N sf)%N ->
    (imms < a64_w_N sf)%N ->
    eval_closed_cert_expr penv foracle src = raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) vsrc)) ->
    eval_closed_cert_expr penv foracle dst = raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) vdst)) ->
    eval_closed_cert_expr penv foracle (a64_sym_bitfield (a64_w sf) kind src dst immr imms) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (a64_eval_bitfield (a64_w sf) kind vsrc vdst immr imms))).
Proof.
  intros Pa penv foracle sf kind src dst vsrc vdst immr imms Hlr Hls Hsrc Hdst.
  set (w := a64_w sf) in *; set (wn := N.pos w) in *.
  assert (Hwn : wn = a64_w_N sf) by (destruct sf; reflexivity).
  assert (Hw3264 : w = 32%positive \/ w = 64%positive) by (destruct sf; auto).
  assert (Hmr : (Z.of_N immr mod Z.pos w = Z.of_N immr)%Z) by (apply Z.mod_small; lia).
  unfold a64_sym_bitfield, a64_eval_bitfield; fold w wn.
  rewrite Hmr.
  destruct (N.leb immr imms) eqn:Ele.
  - apply N.leb_le in Ele.
    set (len := (imms - immr + 1%N)%N).
    assert (Hlen_pos : (1 <= len <= wn)%N) by (unfold len; lia).
    assert (Hshr : eval_closed_cert_expr penv foracle
      (if N.eqb immr 0%N then src else CE_BinOp CB_LShr w no_binop_flags src (CE_BvConst w immr)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.shru w vsrc (@Integers.repr w (Z.of_N immr)))))).
    { destruct (N.eqb immr 0%N) eqn:Ez.
      - apply N.eqb_eq in Ez; subst immr; rewrite Hsrc;
          change (@Integers.repr w (Z.of_N 0%N)) with (@Integers.zero w); rewrite Integers.shru_zero; reflexivity.
      - apply (shamt_eval_const_lt penv foracle w src vsrc immr Hw3264 ltac:(lia) Hsrc CB_LShr (or_intror (or_introl eq_refl))). }
    destruct kind.
    + (* ABF_Sbfm *)
      assert (Hgen : eval_closed_cert_expr penv foracle
        (let shl_a := (wn - 1%N - imms)%N in
         let shr_a := (wn - len)%N in
         let sl := if N.eqb shl_a 0%N then src else CE_BinOp CB_Shl w no_binop_flags src (CE_BvConst w shl_a) in
         if N.eqb shr_a 0%N then sl else CE_BinOp CB_AShr w no_binop_flags sl (CE_BvConst w shr_a)) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa w
          (@Integers.shr w (@Integers.shl w vsrc (@Integers.repr w (Z.of_N ((wn - 1%N - imms) mod wn))))
                           (@Integers.repr w (Z.of_N ((wn - len) mod wn))))))).
      { assert (Hshl_m : ((wn - 1 - imms) mod wn = wn - 1 - imms)%N) by (apply N.mod_small; lia).
        assert (Hshr_m : ((wn - len) mod wn = wn - len)%N) by (apply N.mod_small; lia).
        rewrite Hshl_m, Hshr_m.
        assert (Hsl : eval_closed_cert_expr penv foracle
          (if N.eqb (wn - 1 - imms) 0%N then src else CE_BinOp CB_Shl w no_binop_flags src (CE_BvConst w (wn - 1 - imms))) =
          raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.shl w vsrc (@Integers.repr w (Z.of_N (wn - 1 - imms))))))).
        { destruct (N.eqb (wn - 1 - imms) 0%N) eqn:E0.
          - apply N.eqb_eq in E0; rewrite E0, Hsrc;
              change (@Integers.repr w (Z.of_N 0%N)) with (@Integers.zero w); rewrite Integers.shl_zero; reflexivity.
          - apply (shamt_eval_const_lt penv foracle w src vsrc (wn - 1 - imms) Hw3264 ltac:(lia) Hsrc CB_Shl (or_introl eq_refl)). }
        cbv zeta; destruct (N.eqb (wn - len) 0%N) eqn:E0'.
        - apply N.eqb_eq in E0'; rewrite E0', Hsl;
            change (@Integers.repr w (Z.of_N 0%N)) with (@Integers.zero w); rewrite Integers.shr_zero; reflexivity.
        - apply (shamt_eval_const_lt penv foracle w _ _ (wn - len) Hw3264 ltac:(lia) Hsl CB_AShr (or_intror (or_intror eq_refl))). }
      destruct (Pos.eqb w 64%positive && N.eqb immr 0%N && N.eqb imms 31%N) eqn:Esxtw; [| exact Hgen].
      rewrite !andb_true_iff in Esxtw; destruct Esxtw as ([Ew64 Er0] & Es31).
      apply Pos.eqb_eq in Ew64; apply N.eqb_eq in Er0; apply N.eqb_eq in Es31.
      destruct sf; [| discriminate Ew64].
      subst immr imms; clear Hlr Hls Ele; cbn [wn len].
      rewrite (eval_ce_sext _ _ 32%positive 64%positive _ _ eq_refl (eval_a64_sym_trunc32_sound _ _ _ _ Hsrc)).
      rewrite <- a64_sxtw_bitfield_eq; reflexivity.
    + (* ABF_Bfm *)
      assert (Hlow : eval_closed_cert_expr penv foracle
        (CE_BinOp CB_And w no_binop_flags
          (if N.eqb immr 0%N then src else CE_BinOp CB_LShr w no_binop_flags src (CE_BvConst w immr))
          (CE_BvConst w (N.ones len))) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa w
          (@Integers.and w (@Integers.shru w vsrc (@Integers.repr w (Z.of_N immr)))
                           (@Integers.repr w (Z.of_N (N.ones len))))))).
      { rewrite eval_ce_binop, Hshr, eval_ce_const; cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
      assert (Hkept : eval_closed_cert_expr penv foracle
        (CE_BinOp CB_And w no_binop_flags dst (a64_sym_not w (CE_BvConst w (N.ones len)))) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa w
          (@Integers.and w vdst (@Integers.not w (@Integers.repr w (Z.of_N (N.ones len)))))))).
      { rewrite eval_ce_binop, Hdst, (eval_ce_not _ _ w _ _ (eval_ce_const _ _ _ _)); cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
      rewrite eval_ce_binop, Hkept, Hlow; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity.
    + (* ABF_Ubfm *)
      assert (Hlow : eval_closed_cert_expr penv foracle
        (CE_BinOp CB_And w no_binop_flags
          (if N.eqb immr 0%N then src else CE_BinOp CB_LShr w no_binop_flags src (CE_BvConst w immr))
          (CE_BvConst w (N.ones len))) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa w
          (@Integers.and w (@Integers.shru w vsrc (@Integers.repr w (Z.of_N immr)))
                           (@Integers.repr w (Z.of_N (N.ones len))))))).
      { rewrite eval_ce_binop, Hshr, eval_ce_const; cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
      assert (Hmask_all : forall x : @Integers.bit_int w,
        len = wn -> @Integers.and w x (@Integers.repr w (Z.of_N (N.ones len))) = x).
      { intros x Hlw; rewrite Hlw; apply Integers.same_bits_eq; intros i Hi.
        rewrite Integers.bits_and, (@Integers.testbit_repr w _ i Hi) by exact Hi.
        replace (Z.of_N (N.ones wn)) with (Z.ones (Z.pos w)) by (unfold wn; rewrite Z.ones_equiv, N2Z.inj_pos || idtac; destruct Hw3264 as [-> | ->]; reflexivity).
        rewrite Z.ones_spec_low by (destruct Hw3264 as [-> | ->]; change (@Integers.zwordsize 32%positive) with 32%Z in Hi; change (@Integers.zwordsize 64%positive) with 64%Z in Hi; lia).
        rewrite andb_true_r; reflexivity. }
      destruct (N.eqb len wn) eqn:Ewn.
      { apply N.eqb_eq in Ewn; assert (Hr0 : immr = 0%N) by (unfold len in Ewn; lia).
        rewrite Hr0; change (@Integers.repr w (Z.of_N 0%N)) with (@Integers.zero w);
          rewrite Integers.shru_zero, Hmask_all by exact Ewn; exact Hsrc. }
      destruct (N.eqb imms (wn - 1%N)) eqn:Etop.
      { apply N.eqb_eq in Etop; rewrite Hshr; do 3 f_equal; symmetry.
        apply Integers.same_bits_eq; intros i Hi.
        assert (Hzw : @Integers.zwordsize w = Z.pos w) by (destruct Hw3264 as [-> | ->]; reflexivity).
        rewrite Integers.bits_and, (@Integers.testbit_repr w _ i Hi) by exact Hi.
        destruct (Z.ltb i (Z.of_N len)) eqn:Eil.
        - apply Z.ltb_lt in Eil.
          assert (Htb : Z.testbit (Z.of_N (N.ones len)) i = true).
          { rewrite <- (Z2N.id i ltac:(lia)), N2Z.inj_testbit, N.ones_spec_low by lia; reflexivity. }
          rewrite Htb, andb_true_r; reflexivity.
        - apply Z.ltb_ge in Eil; rewrite Integers.bits_shru by (rewrite Hzw in Hi |- *; lia).
          assert (Himmr_lt : (immr < N.pos w)%N) by (unfold w, a64_w, a64_w_N in *; destruct sf; lia).
          rewrite (@Integers.unsigned_repr w (Z.of_N immr))
            by (unfold Integers.max_unsigned; destruct Hw3264 as [-> | ->];
                [change (@Integers.modulus 32%positive) with (2 ^ 32)%Z | change (@Integers.modulus 64%positive) with (2 ^ 64)%Z]; lia).
          assert (Htb : Z.testbit (Z.of_N (N.ones len)) i = false)
            by (rewrite <- (Z2N.id i ltac:(lia)), N2Z.inj_testbit, N.ones_spec_high by lia; reflexivity).
          rewrite Htb, andb_false_r.
          assert (Hge : (i + Z.of_N immr >= Z.pos w)%Z) by (unfold len in Eil; rewrite Etop in Eil; lia).
          destruct (zlt (i + Z.of_N immr) (@Integers.zwordsize w)); [lia | reflexivity]. }
      destruct (Pos.eqb w 64%positive && N.eqb immr 0%N && N.eqb imms 31%N) eqn:Euxtw; [| exact Hlow].
      rewrite !andb_true_iff in Euxtw; destruct Euxtw as ([Ew64 Er0] & Es31).
      apply Pos.eqb_eq in Ew64; apply N.eqb_eq in Er0; apply N.eqb_eq in Es31.
      destruct sf; [| discriminate Ew64].
      subst immr imms; clear Hlr Hls Ele Ewn Etop; cbn [wn len].
      rewrite (eval_ce_zext _ _ 32%positive 64%positive _ _ eq_refl (eval_a64_sym_trunc32_sound _ _ _ _ Hsrc)).
      rewrite <- a64_uxtw_bitfield_eq; reflexivity.
  - (* imms < immr *)
    apply N.leb_gt in Ele.
    set (pos := (wn - immr)%N); set (len := (imms + 1%N)%N).
    assert (Hpos_m : (pos mod wn = pos)%N) by (unfold pos; apply N.mod_small; lia).
    rewrite Hpos_m.
    assert (Hlow : eval_closed_cert_expr penv foracle (CE_BinOp CB_And w no_binop_flags src (CE_BvConst w (N.ones len))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.and w vsrc (@Integers.repr w (Z.of_N (N.ones len))))))).
    { rewrite eval_ce_binop, Hsrc, eval_ce_const; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
    destruct kind.
    + (* ABF_Sbfm *)
      assert (Hsex_m : ((wn - len) mod wn = wn - len)%N) by (apply N.mod_small; unfold len; lia).
      rewrite Hsex_m.
      pose proof (shamt_eval_const_lt penv foracle w src vsrc (wn - len) Hw3264 ltac:(unfold len; lia) Hsrc CB_Shl (or_introl eq_refl)) as Hs1.
      pose proof (shamt_eval_const_lt penv foracle w _ _ (wn - len) Hw3264 ltac:(unfold len; lia) Hs1 CB_AShr (or_intror (or_intror eq_refl))) as Hs2.
      exact (shamt_eval_const_lt penv foracle w _ _ pos Hw3264 ltac:(unfold pos; lia) Hs2 CB_Shl (or_introl eq_refl)).
    + (* ABF_Bfm *)
      pose proof (shamt_eval_const_lt penv foracle w _ _ pos Hw3264 ltac:(unfold pos; lia) (eval_ce_const penv foracle w (N.ones len)) CB_Shl (or_introl eq_refl)) as Hmask.
      pose proof (eval_ce_not penv foracle w _ _ Hmask) as Hnmask.
      assert (Hkept : eval_closed_cert_expr penv foracle
        (CE_BinOp CB_And w no_binop_flags dst (a64_sym_not w (CE_BinOp CB_Shl w no_binop_flags (CE_BvConst w (N.ones len)) (CE_BvConst w pos)))) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa w
          (@Integers.and w vdst (@Integers.not w (@Integers.shl w (@Integers.repr w (Z.of_N (N.ones len))) (@Integers.repr w (Z.of_N pos)))))))).
      { rewrite eval_ce_binop, Hdst, Hnmask; cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
      pose proof (shamt_eval_const_lt penv foracle w _ _ pos Hw3264 ltac:(unfold pos; lia) Hlow CB_Shl (or_introl eq_refl)) as Hins.
      rewrite eval_ce_binop, Hkept, Hins; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity.
    + (* ABF_Ubfm *)
      exact (shamt_eval_const_lt penv foracle w _ _ pos Hw3264 ltac:(unfold pos; lia) Hlow CB_Shl (or_introl eq_refl)).
Qed.

Lemma eval_a64_sym_extr_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w hi lo vhi vlo lsb,
    (w = 32%positive \/ w = 64%positive) ->
    eval_closed_cert_expr penv foracle hi = raise_ret (DVALUE_Base (@DVALUE_I Pa w vhi)) ->
    eval_closed_cert_expr penv foracle lo = raise_ret (DVALUE_Base (@DVALUE_I Pa w vlo)) ->
    eval_closed_cert_expr penv foracle (a64_sym_extr w hi lo lsb) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (a64_eval_extr w vhi vlo lsb))).
Proof.
  intros Pa penv foracle w hi lo vhi vlo lsb Hw Hhi Hlo.
  unfold a64_sym_extr, a64_eval_extr.
  set (m := N.modulo lsb (N.pos w)).
  assert (Hm_lt : (m < N.pos w)%N) by (unfold m; apply N.mod_lt; discriminate).
  destruct (N.eqb m 0%N) eqn:Ez; [exact Hlo | apply N.eqb_neq in Ez].
  pose proof (shamt_eval_const_lt penv foracle w lo vlo m Hw Hm_lt Hlo CB_LShr (or_intror (or_introl eq_refl))) as Hshr.
  pose proof (shamt_eval_const_lt penv foracle w hi vhi (N.pos w - m) Hw ltac:(lia) Hhi CB_Shl (or_introl eq_refl)) as Hshl.
  rewrite eval_ce_binop, Hshr, Hshl; cbn [eou_bind].
  unfold eval_iop; rewrite eval_iop_integer_base_same_width.
  replace (Z.of_N (N.pos w - m)) with (Z.pos w - Z.of_N m)%Z by lia; reflexivity.
Qed.

Lemma eval_a64_sym_div_guarded_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle is_signed w a b va vb,
    (w = 32%positive \/ w = 64%positive) ->
    eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa w va)) ->
    eval_closed_cert_expr penv foracle b = raise_ret (DVALUE_Base (@DVALUE_I Pa w vb)) ->
    eval_closed_cert_expr penv foracle (a64_sym_div_guarded is_signed w a b) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w
      (if is_signed then a64_divs_total w va vb else a64_divu_total w va vb))).
Proof.
  intros Pa penv foracle is_signed w a b va vb Hw Ha Hb.
  assert (Hzw : (@Integers.zwordsize w > 1)%Z)
    by (destruct Hw as [-> | ->];
        [replace (@Integers.zwordsize 32%positive) with 32%Z by reflexivity
        | replace (@Integers.zwordsize 64%positive) with 64%Z by reflexivity]; lia).
  set (is_z := CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N)).
  destruct is_signed; cbn [a64_sym_div_guarded]; fold is_z.
  - (* signed *)
    set (imin := ce_int_min w).
    set (is_ovf := CE_BinOp CB_And 1%positive no_binop_flags
                     (CE_ICmp CIP_Eq false w a imin)
                     (CE_ICmp CIP_Eq false w b (ce_all_ones w))).
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
      cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op].
      destruct (@Integers.eq w va (@Integers.repr w (@Integers.min_signed w))) eqn:Ea,
               (@Integers.eq w vb (@Integers.mone w)) eqn:Eb,
               (Z.eqb (@Integers.signed w va) (@Integers.min_signed w)) eqn:Esa,
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
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if (cz || co)%bool then @Integers.one 1%positive else @Integers.zero 1%positive))))
      by exact (proj2 (eval_a64_sym_bool_and_or _ _ _ _ _ _ Hisz Hovf)).
    assert (Hsa : eval_closed_cert_expr penv foracle (CE_Select w is_ovf (CE_BvConst w 0%N) a) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if co then @Integers.zero w else va))))
      by (eapply eval_ce_select_int; [exact Hovf | rewrite eval_ce_const, repr_zero_N; reflexivity | exact Ha]).
    assert (Hsb : eval_closed_cert_expr penv foracle (CE_Select w (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) (CE_BvConst w 1%N) b) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if (cz || co)%bool then @Integers.one w else vb))))
      by (eapply eval_ce_select_int; [exact Hbad | rewrite eval_ce_const, repr_one_N; reflexivity | exact Hb]).
    assert (Hsdiv : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_SDiv w no_binop_flags (CE_Select w is_ovf (CE_BvConst w 0%N) a)
        (CE_Select w (CE_BinOp CB_Or 1%positive no_binop_flags is_z is_ovf) (CE_BvConst w 1%N) b)) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w
        (@Integers.divs w (if co then @Integers.zero w else va) (if (cz || co)%bool then @Integers.one w else vb))))).
    { rewrite eval_ce_binop, Hsa, Hsb; cbn [eou_bind].
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn - [Integers.signed Integers.min_signed Integers.divs Z.eqb].
      destruct (cz || co)%bool eqn:Ebc.
      - rewrite (@Integers.signed_one w) by exact Hzw; cbn [Z.eqb]; rewrite andb_false_r; reflexivity.
      - apply orb_false_iff in Ebc as [Hcz Hco]; unfold cz in Hcz; rewrite Hcz, Hco.
        rewrite (Z.eqb_sym (@Integers.min_signed w) (@Integers.signed w va)); unfold co in Hco; rewrite Hco; reflexivity. }
    unfold a64_divs_total; fold cz co.
    assert (Hzc : eval_closed_cert_expr penv foracle (CE_BvConst w 0%N) = raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))))
      by (rewrite eval_ce_const, repr_zero_N; reflexivity).
    destruct cz; [eapply (eval_ce_select_int _ _ _ _ _ _ true); [exact Hisz | exact Hzc | eapply eval_ce_select_int; [exact Hovf | exact (eval_ce_int_min _ _ _) | exact Hsdiv]] |].
    destruct co; [eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hisz | exact Hzc | eapply (eval_ce_select_int _ _ _ _ _ _ true); [exact Hovf | exact (eval_ce_int_min _ _ _) | exact Hsdiv]]
                 | eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hisz | exact Hzc | eapply (eval_ce_select_int _ _ _ _ _ _ false); [exact Hovf | exact (eval_ce_int_min _ _ _) | exact Hsdiv]]].
  - (* unsigned *)
    assert (Hisz : eval_closed_cert_expr penv foracle is_z =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if @Integers.eq w vb (@Integers.zero w) then @Integers.one 1%positive else @Integers.zero 1%positive))))
      by (unfold is_z; apply (eval_ce_icmp_eq_bool _ _ CIP_Eq); [exact Hb | rewrite eval_ce_const, repr_zero_N; reflexivity]).
    assert (Hsb : eval_closed_cert_expr penv foracle (CE_Select w is_z (CE_BvConst w 1%N) b) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (if @Integers.eq w vb (@Integers.zero w) then @Integers.one w else vb))))
      by (eapply eval_ce_select_int; [exact Hisz | rewrite eval_ce_const, repr_one_N; reflexivity | exact Hb]).
    assert (Hzc : eval_closed_cert_expr penv foracle (CE_BvConst w 0%N) = raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.zero w))))
      by (rewrite eval_ce_const, repr_zero_N; reflexivity).
    unfold a64_divu_total.
    destruct (@Integers.eq w vb (@Integers.zero w)) eqn:Ez.
    + apply integers_eq_zero_iff in Ez; rewrite Ez; cbn [Z.eqb].
      unfold a64_sym_div_guarded; cbn [negb]; fold is_z.
      eapply (eval_ce_select_int _ _ _ _ _ _ true); [rewrite Hisz; reflexivity | exact Hzc |].
      rewrite eval_ce_binop, Ha, Hsb; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [Integers.divu Integers.unsigned]; rewrite (@Integers.unsigned_one w); reflexivity.
    + assert (Hnz : (@Integers.unsigned w vb =? 0)%Z = false)
        by (destruct (Z.eqb (@Integers.unsigned w vb) 0%Z) eqn:Eb; [apply Z.eqb_eq, integers_eq_zero_iff in Eb; congruence | reflexivity]).
      rewrite Hnz.
      unfold a64_sym_div_guarded; cbn [negb]; fold is_z.
      eapply (eval_ce_select_int _ _ _ _ _ _ false); [rewrite Hisz; reflexivity | exact Hzc |].
      rewrite eval_ce_binop, Ha, Hsb; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [Integers.divu Integers.unsigned]; rewrite Hnz; reflexivity.
Qed.

Lemma eval_a64_sym_dp2_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w op lhs rhs vl vr,
    (w = 32%positive \/ w = 64%positive) ->
    eval_closed_cert_expr penv foracle lhs = raise_ret (DVALUE_Base (@DVALUE_I Pa w vl)) ->
    eval_closed_cert_expr penv foracle rhs = raise_ret (DVALUE_Base (@DVALUE_I Pa w vr)) ->
    eval_closed_cert_expr penv foracle (a64_sym_dp2 w op lhs rhs) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (a64_eval_dp2 w op vl vr))).
Proof.
  intros Pa penv foracle w op lhs rhs vl vr Hw Hl Hr.
  unfold a64_sym_dp2, a64_eval_dp2.
  assert (Hsh : eval_closed_cert_expr penv foracle
    (CE_BinOp CB_And w no_binop_flags rhs (CE_BvConst w (Z.to_N (Z.pos w - 1)))) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.land (@Integers.unsigned w vr) (Z.pos w - 1)))))).
  { rewrite eval_ce_binop, Hr, eval_ce_const; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    destruct Hw as [-> | ->]; cbn - [Integers.and Integers.unsigned Integers.repr Z.land]; unfold Integers.and;
      [rewrite (@Integers.unsigned_repr 32%positive 31%Z) by (compute; split; discriminate)
      | rewrite (@Integers.unsigned_repr 64%positive 63%Z) by (compute; split; discriminate)]; reflexivity. }
  destruct (land_mask_w_mod w vr Hw) as [Hsh_eq Hsh_lt].
  destruct op.
  - exact (eval_a64_sym_div_guarded_sound _ _ false _ _ _ _ _ Hw Hl Hr).
  - exact (eval_a64_sym_div_guarded_sound _ _ true _ _ _ _ _ Hw Hl Hr).
  - rewrite eval_ce_binop, Hl, Hsh; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    unfold a64_eval_dp2; cbn - [Integers.shl Integers.unsigned Integers.repr Z.geb Z.gtb Z.land Z.sub].
    rewrite Hsh_lt, Hsh_eq; reflexivity.
  - rewrite eval_ce_binop, Hl, Hsh; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    unfold a64_eval_dp2; cbn - [Integers.shru Integers.unsigned Integers.repr Z.geb Z.land Z.sub].
    rewrite Hsh_lt, Hsh_eq; reflexivity.
  - rewrite eval_ce_binop, Hl, Hsh; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    unfold a64_eval_dp2; cbn - [Integers.shr Integers.unsigned Integers.repr Z.geb Z.land Z.sub].
    rewrite Hsh_lt, Hsh_eq; reflexivity.
  - (* ADP2_Rorv *)
    assert (Hsub : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_Sub w no_binop_flags (CE_BvConst w (N.pos w))
        (CE_BinOp CB_And w no_binop_flags rhs (CE_BvConst w (Z.to_N (Z.pos w - 1))))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w
        (@Integers.sub w (@Integers.repr w (Z.pos w)) (rv_mask_shamt w (@Integers.unsigned w vr)))))).
    { rewrite eval_ce_binop, eval_ce_const, Hsh; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn [eval_int_op cert_to_ibinop]; rewrite Hsh_eq; reflexivity. }
    assert (Hinv : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_And w no_binop_flags
        (CE_BinOp CB_Sub w no_binop_flags (CE_BvConst w (N.pos w))
          (CE_BinOp CB_And w no_binop_flags rhs (CE_BvConst w (Z.to_N (Z.pos w - 1)))))
        (CE_BvConst w (Z.to_N (Z.pos w - 1)))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w
        (@Integers.repr w (Z.land (@Integers.unsigned w (@Integers.sub w (@Integers.repr w (Z.pos w)) (rv_mask_shamt w (@Integers.unsigned w vr)))) (Z.pos w - 1)))))).
    { rewrite eval_ce_binop, Hsub, eval_ce_const; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      destruct Hw as [-> | ->]; cbn - [Integers.and Integers.unsigned Integers.repr Z.land]; unfold Integers.and;
        [rewrite (@Integers.unsigned_repr 32%positive 31%Z) by (compute; split; discriminate)
        | rewrite (@Integers.unsigned_repr 64%positive 63%Z) by (compute; split; discriminate)]; reflexivity. }
    set (shv := rv_mask_shamt w (@Integers.unsigned w vr)) in *.
    set (inv_sub := @Integers.sub w (@Integers.repr w (Z.pos w)) shv) in *.
    destruct (land_mask_w_mod w inv_sub Hw) as [Hi_eq Hi_lt].
    assert (Heq_inv : rv_mask_shamt w (@Integers.unsigned w inv_sub) = rv_mask_shamt w (Z.pos w - @Integers.unsigned w shv)).
    { unfold inv_sub, rv_mask_shamt, Integers.sub; pose proof (mod_lt_32_64 w Hw) as Hm.
      rewrite (@Integers.unsigned_repr w (Z.pos w)) by (unfold Integers.max_unsigned; lia).
      rewrite Integers.unsigned_repr_eq.
      apply Integers.same_bits_eq; intros i Hi; rewrite !(@Integers.testbit_repr w _ i Hi).
      destruct Hw as [-> | ->].
      - change (@Integers.zwordsize 32%positive) with 32%Z in Hi.
        change (Z.pos 32) with (2 ^ 5)%Z; change (@Integers.modulus 32%positive) with (2 ^ 32)%Z.
        destruct (Z.ltb i 5) eqn:Ei5;
          [apply Z.ltb_lt in Ei5; rewrite !Z.mod_pow2_bits_low by lia; reflexivity
          | apply Z.ltb_ge in Ei5; rewrite !Z.mod_pow2_bits_high by lia; reflexivity].
      - change (@Integers.zwordsize 64%positive) with 64%Z in Hi.
        change (Z.pos 64) with (2 ^ 6)%Z; change (@Integers.modulus 64%positive) with (2 ^ 64)%Z.
        destruct (Z.ltb i 6) eqn:Ei6;
          [apply Z.ltb_lt in Ei6; rewrite !Z.mod_pow2_bits_low by lia; reflexivity
          | apply Z.ltb_ge in Ei6; rewrite !Z.mod_pow2_bits_high by lia; reflexivity]. }
    assert (H1 : eval_closed_cert_expr penv foracle (CE_BinOp CB_LShr w no_binop_flags lhs (CE_BinOp CB_And w no_binop_flags rhs (CE_BvConst w (Z.to_N (Z.pos w - 1))))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.shru w vl shv)))).
    { rewrite eval_ce_binop, Hl, Hsh; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [Integers.shru Integers.unsigned Integers.repr Z.geb Z.land Z.sub]; rewrite Hsh_lt, Hsh_eq; reflexivity. }
    assert (H2 : eval_closed_cert_expr penv foracle
      (CE_BinOp CB_Shl w no_binop_flags lhs
        (CE_BinOp CB_And w no_binop_flags
          (CE_BinOp CB_Sub w no_binop_flags (CE_BvConst w (N.pos w))
            (CE_BinOp CB_And w no_binop_flags rhs (CE_BvConst w (Z.to_N (Z.pos w - 1)))))
          (CE_BvConst w (Z.to_N (Z.pos w - 1))))) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa w (@Integers.shl w vl (rv_mask_shamt w (Z.pos w - @Integers.unsigned w shv)))))).
    { rewrite eval_ce_binop, Hl, Hinv; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width.
      cbn - [inv_sub Integers.shl Integers.unsigned Integers.repr Z.geb Z.gtb Z.land Z.sub]; rewrite Hi_lt, Hi_eq, Heq_inv; reflexivity. }
    cbn [a64_eval_dp2]; fold shv.
    rewrite eval_ce_binop, H1, H2; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity.
Qed.

Lemma eval_a64_sym_csel_sound :
  forall {Pa : Params} (penv : param_env Pa) foracle w kind cond sfl fl t_e m_e vt vm,
    sym_flags_agree penv foracle sfl fl ->
    eval_closed_cert_expr penv foracle t_e = raise_ret (DVALUE_Base (@DVALUE_I Pa w vt)) ->
    eval_closed_cert_expr penv foracle m_e = raise_ret (DVALUE_Base (@DVALUE_I Pa w vm)) ->
    eval_closed_cert_expr penv foracle (a64_sym_csel w kind cond sfl t_e m_e) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa w (a64_eval_csel w kind cond fl vt vm))).
Proof.
  intros Pa penv foracle w kind cond sfl fl t_e m_e vt vm Hfl Ht Hm.
  unfold a64_sym_csel, a64_eval_csel.
  eapply eval_ce_select_int; [exact (eval_a64_sym_cond_sound _ _ cond _ _ Hfl) | exact Ht |].
  destruct kind.
  - exact Hm.
  - rewrite eval_ce_binop, Hm, eval_ce_const, repr_one_N; cbn [eou_bind];
      unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity.
  - exact (eval_ce_not _ _ w _ _ Hm).
  - exact (eval_ce_neg _ _ w _ _ Hm).
Qed.

Lemma a64_orr_xzr_lsl0 : forall v : @Integers.bit_int 64%positive,
  @Integers.or 64%positive (@Integers.zero 64%positive)
    (a64_eval_shift 64%positive v ASH_Lsl 0%N) = v.
Proof.
  intro v; unfold a64_eval_shift.
  change (Z.of_N 0%N mod Z.pos 64)%Z with 0%Z.
  change (@Integers.repr 64%positive 0%Z) with (@Integers.zero 64%positive).
  rewrite Integers.shl_zero, Integers.or_zero_l; reflexivity.
Qed.

Definition a64_env_agrees {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (srf : a64_sym_regs) (def : a64_def_mask) (rf : a64_regfile) : Prop :=
  forall r,
    a64_def_read r def = true ->
    eval_closed_cert_expr penv foracle (a64_sym_read_reg r srf) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg r rf))).

Lemma a64_env_agrees_read_w :
  forall {Pa : Params} (penv : param_env Pa) foracle srf def rf sf r,
    a64_env_agrees penv foracle srf def rf ->
    a64_def_read r def = true ->
    eval_closed_cert_expr penv foracle (a64_sym_read_w sf r srf) =
    raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (a64_read_w sf r rf))).
Proof.
  intros Pa penv foracle srf def rf [|] r Hag Hr; cbn [a64_sym_read_w a64_read_w a64_w].
  - exact (Hag r Hr).
  - exact (eval_a64_sym_trunc32_sound _ _ _ _ (Hag r Hr)).
Qed.

Definition a64_val_regs_agrees {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (rf0 : a64_regfile) (sp0 : @Integers.bit_int 64%positive)
  (vrf : a64_val_regs) (rf : a64_regfile) : Prop :=
  forall r,
    mc_sym_val_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0
      (a64_val_read r vrf) (a64_read_reg r rf).

Lemma a64_val_regs_agrees_write {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 vrf rf rd sv v,
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_val_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 sv v ->
    a64_val_regs_agrees penv foracle rf0 sp0 (a64_val_write rd sv vrf) (a64_write_reg rd v rf).
Proof.
  intros penv foracle rf0 sp0 vrf rf rd sv v Hag Hv r.
  unfold a64_val_read, a64_val_write, a64_read_reg, a64_write_reg.
  destruct (N.leb 31%N r) eqn:Er31;
    [cbn [mc_sym_val_agrees]; rewrite eval_ce_const, repr_zero_N; reflexivity |].
  destruct (N.leb 31%N rd) eqn:Erd31.
  - pose proof (Hag r) as Hr; unfold a64_val_read, a64_read_reg in Hr; rewrite Er31 in Hr; exact Hr.
  - destruct (N.eqb r rd); [exact Hv |].
    pose proof (Hag r) as Hr; unfold a64_val_read, a64_read_reg in Hr; rewrite Er31 in Hr; exact Hr.
Qed.

Lemma a64_val_regs_agrees_write_w {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 vrf rf sf rd e v,
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) v)) ->
    a64_val_regs_agrees penv foracle rf0 sp0 (a64_val_write_w sf rd e vrf) (a64_write_w sf rd v rf).
Proof.
  intros penv foracle rf0 sp0 vrf rf sf rd e v Hag He.
  unfold a64_val_write_w, a64_write_w.
  apply a64_val_regs_agrees_write; [exact Hag |].
  destruct sf; cbn [a64_w mc_sym_val_agrees] in He |- *;
    [exact He | exact (eval_ce_zext _ _ 32%positive 64%positive _ _ eq_refl He)].
Qed.

Lemma a64_val_read_expr_w_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 vrf rf sf r e,
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    a64_val_read_expr_w sf r vrf = Some e ->
    eval_closed_cert_expr penv foracle e =
    raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (a64_read_w sf r rf))).
Proof.
  intros penv foracle rf0 sp0 vrf rf sf r e Hag He.
  unfold a64_val_read_expr_w in He.
  destruct (a64_val_read r vrf) as [| e64 | |] eqn:Er; try discriminate He.
  inversion He; subst e; clear He.
  pose proof (Hag r) as H64; rewrite Er in H64; cbn [mc_sym_val_agrees] in H64.
  destruct sf; cbn [a64_read_w a64_w]; [exact H64 | exact (eval_a64_sym_trunc32_sound _ _ _ _ H64)].
Qed.

Lemma a64_val_read_sp_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 sp_off vrf rf sp r sv,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    a64_val_read_sp r vrf sp_off = sv ->
    mc_sym_val_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 sv (a64_read_reg_sp r rf sp).
Proof.
  intros penv foracle rf0 sp0 sp_off vrf rf sp r sv Hrng Hsp Hag Hsv.
  unfold a64_val_read_sp, a64_read_reg_sp in *.
  destruct (N.eqb r 31%N); subst sv; [cbn [mc_sym_val_agrees]; split; assumption | exact (Hag r)].
Qed.

Lemma a64_val_write_sp_bounds : forall r sv sp_off vrf astk sp_off' vrf' astk',
  (- mc_frame_cap <= sp_off <= 0)%Z ->
  a64_val_write_sp r sv sp_off vrf astk = Some (sp_off', vrf', astk') ->
  (- mc_frame_cap <= sp_off' <= 0)%Z.
Proof.
  intros r sv sp_off vrf astk sp_off' vrf' astk' Hrng Hst.
  unfold a64_val_write_sp in Hst; destruct (N.eqb r 31%N).
  - destruct sv; try discriminate Hst.
    destruct (Z.leb (- mc_frame_cap) off && Z.leb off 0%Z) eqn:Eb; [| discriminate Hst].
    apply andb_true_iff in Eb as [Eb1 Eb2]; apply Z.leb_le in Eb1; apply Z.leb_le in Eb2.
    inversion Hst; subst; lia.
  - inversion Hst; subst; exact Hrng.
Qed.

Lemma a64_val_write_sp_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 rd sv v sp_off vrf astk rf sp mstk sp_off' vrf' astk',
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    mc_sym_val_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 sv v ->
    a64_val_write_sp rd sv sp_off vrf astk = Some (sp_off', vrf', astk') ->
    let '(rf', sp') := a64_write_reg_sp rd v rf sp in
    sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
    a64_val_regs_agrees penv foracle rf0 sp0 vrf' rf' /\
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk.
Proof.
  intros penv foracle rf0 sp0 rd sv v sp_off vrf astk rf sp mstk sp_off' vrf' astk' Hsp Hag Hastk Hv Hst.
  unfold a64_val_write_sp in Hst; unfold a64_write_reg_sp.
  destruct (N.eqb rd 31%N) eqn:Ed31.
  - destruct sv as [| | | off']; try discriminate Hst.
    destruct (Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z); [| discriminate Hst].
    inversion Hst; subst; cbn [mc_sym_val_agrees] in Hv; destruct Hv as [_ Hvp].
    repeat split; [exact Hvp | exact Hag | apply mc_sym_stk_prune_agrees; exact Hastk].
  - inversion Hst; subst sp_off' vrf' astk'; split; [exact Hsp | split; [apply a64_val_regs_agrees_write; assumption | exact Hastk]].
Qed.

Lemma a64_ldst_sym_load_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle (read_init : N -> @Integers.bit_int 64%positive)
         sp0 is_signed sf_dst sv0 sv1 v,
    mc_sym_val_agrees penv foracle read_init sp0 sv0 v ->
    a64_ldst_sym_load is_signed sf_dst sv0 = Some sv1 ->
    mc_sym_val_agrees penv foracle read_init sp0 sv1 (a64_ldst_apply_load is_signed sf_dst v).
Proof.
  intros penv foracle read_init sp0 is_signed sf_dst sv0 sv1 v Hag Hld.
  unfold a64_ldst_sym_load in Hld; unfold a64_ldst_apply_load.
  destruct (is_signed && negb sf_dst).
  - destruct sv0 as [| e | |]; try discriminate Hld; inversion Hld; subst sv1; clear Hld.
    cbn [mc_sym_val_agrees] in Hag |- *.
    exact (eval_ce_zext _ _ 32%positive 64%positive _ _ eq_refl (eval_a64_sym_trunc32_sound _ _ _ _ Hag)).
  - inversion Hld; subst sv1; exact Hag.
Qed.

Lemma a64_ldst_writeback_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 sp_off vrf1 astk1 rf1 sp mstk1 mode rn wb_off wb_addr,
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    (match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end) ->
    wb_addr = @Integers.add 64%positive sp0 (@Integers.repr 64%positive wb_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1 ->
    let '(sp_off2, vrf2, astk2) :=
      match mode with
      | AAM_SignedOffset => (sp_off, vrf1, astk1)
      | AAM_PreIndex | AAM_PostIndex =>
          if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
          else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
      end in
    let '(rf2, sp2) :=
      match mode with
      | AAM_SignedOffset => (rf1, sp)
      | AAM_PreIndex | AAM_PostIndex => a64_write_reg_sp rn wb_addr rf1 sp
      end in
    (- mc_frame_cap <= sp_off2 <= 0)%Z /\
    sp2 = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off2) /\
    a64_val_regs_agrees penv foracle rf0 sp0 vrf2 rf2 /\
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk2 mstk1.
Proof.
  intros penv foracle rf0 sp0 sp_off vrf1 astk1 rf1 sp mstk1 mode rn wb_off wb_addr Hrng Hsp Hwb Hwba Hag1 Hastk1.
  destruct mode; [repeat split; try lia; assumption | |].
  - unfold a64_write_reg_sp; destruct (N.eqb rn 31%N).
    + repeat split; try lia; try assumption; apply mc_sym_stk_prune_agrees; exact Hastk1.
    + repeat split; try lia; try assumption; apply a64_val_regs_agrees_write;
        [exact Hag1 | cbn [mc_sym_val_agrees]; split; assumption].
  - unfold a64_write_reg_sp; destruct (N.eqb rn 31%N).
    + repeat split; try lia; try assumption; apply mc_sym_stk_prune_agrees; exact Hastk1.
    + repeat split; try lia; try assumption; apply a64_val_regs_agrees_write;
        [exact Hag1 | cbn [mc_sym_val_agrees]; split; assumption].
Qed.

Lemma a64_sym_epilogue_ok_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle rf0 sp0 sp_off vrf rf sp,
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    a64_sym_epilogue_ok sp_off vrf = true ->
    sp = sp0 /\ a64_callee_saved_preserved rf0 rf.
Proof.
  intros penv foracle rf0 sp0 sp_off vrf rf sp Hsp Hag Hep.
  unfold a64_sym_epilogue_ok in Hep; apply andb_true_iff in Hep as [Hz Hforall].
  apply Z.eqb_eq in Hz; subst sp_off.
  split; [rewrite Hsp, mc_add_ptr_zero; reflexivity |].
  intros r Hcs; rewrite forallb_forall in Hforall.
  assert (Hin : In r a64_callee_saved_list).
  { unfold a64_is_callee_saved in Hcs; apply andb_true_iff in Hcs as [Hge Hle];
      apply N.leb_le in Hge; apply N.leb_le in Hle; cbn [a64_callee_saved_list In].
    assert (r = 19%N \/ r = 20%N \/ r = 21%N \/ r = 22%N \/ r = 23%N \/ r = 24%N \/
            r = 25%N \/ r = 26%N \/ r = 27%N \/ r = 28%N \/ r = 29%N \/ r = 30%N) by lia.
    repeat destruct H as [-> | H]; auto 15. }
  pose proof (Hforall r Hin) as Hm; destruct (a64_val_read r vrf) as [| | r0 |] eqn:Er; try discriminate Hm.
  apply N.eqb_eq in Hm; subst r0.
  pose proof (Hag r) as Hagr; rewrite Er in Hagr; cbn [mc_sym_val_agrees] in Hagr.
  unfold a64_is_callee_saved in Hcs; apply andb_true_iff in Hcs as [_ Hle]; apply N.leb_le in Hle.
  unfold a64_read_reg in Hagr; replace (N.leb 31%N r) with false in Hagr by (symmetry; apply N.leb_gt; lia); exact Hagr.
Qed.

Theorem summarize_a64_dag_at_sound :
  forall {Pa : Params} fuel insts im visited pc sp_off vrf astk sfl fl_def ret_w d_mc
         penv foracle rf0 sp0 rf sp fl mstk,
    (forall q, pt_get (N.succ_pos q) im = lookup_a64_inst insts q) ->
    rv_supported_arg_width ret_w = true ->
    forallb a64_inst_valid insts = true ->
    mc_valid_sp0 sp0 ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv foracle sfl fl) ->
    summarize_a64_dag_at fuel im visited pc sp_off vrf astk sfl fl_def ret_w = inr d_mc ->
    exists rf_end fl_end mstk_end,
      a64_exec_mem fuel insts pc sp0 rf sp fl mstk = Some (rf_end, sp0, fl_end, mstk_end) /\
      a64_callee_saved_preserved rf0 rf_end /\
      eval_cfg_dag penv foracle d_mc =
      DO_Ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end)))).
Proof.
  intros Pa fuel insts im visited pc sp_off vrf astk sfl fl_def ret_w d_mc
         penv foracle rf0 sp0 rf sp fl mstk Him.
  revert visited pc sp_off vrf astk sfl fl_def ret_w d_mc penv foracle rf0 sp0 rf sp fl mstk.
  induction fuel as [| fuel' IH];
    intros visited pc sp_off vrf astk sfl fl_def ret_w d_mc
           penv foracle rf0 sp0 rf sp fl mstk
           Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Hsum;
    cbn [summarize_a64_dag_at a64_exec_mem] in *.
  - destruct (pt_has_n pc visited); discriminate Hsum.
  - destruct (pt_has_n pc visited); [discriminate Hsum |].
    destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Elook; [| discriminate Hsum].
    rewrite Him in Elook; rewrite Elook.
    assert (Hdec_val : a64_inst_valid dec = true).
    { clear -Elook Hval; induction insts as [| d rest IHl]; cbn in *; [discriminate |].
      apply andb_true_iff in Hval as [Hd Hr]; destruct (N.eqb (dai_off d) pc);
        [inversion Elook; subst; exact Hd | exact (IHl Hr Elook)]. }
    destruct (dai_inst dec) as
      [ | sf is_sub set_fl rd rn imm
        | sf is_sub set_fl rd rn rm sh amt
        | sf is_sub set_fl rd rn rm ext amt
        | sf op set_fl rd rn mask
        | sf op inv_rm set_fl rd rn rm sh amt
        | sf kind rd imm16 shift
        | sf kind rd rn immr imms
        | sf rd rn rm lsb
        | sf is_sub rd rn rm ra
        | sgn is_sub rd rn rm ra
        | sf op rd rn rm
        | sf kind cond rd rn rm
        | sf is_sub cond rn rm nzcv
        | sf is_sub cond rn imm5 nzcv
        | is_load is_signed sf_dst sz mode rt rn imm
        | is_load sf mode rt1 rt2 rn imm
        | rel
        | cond rel
        | sf is_nz rt rel
        | is_nz rt bit rel
        | ] eqn:Ed.
    + (* A64_Nop *)
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Hsum).
    + (* A64_AddSubImm *)
      destruct (sf && negb set_fl) eqn:E64n.
      * set (sv_opt :=
          match a64_val_read_sp rn vrf sp_off with
          | MSV_StackPtr base_off =>
              let off' := if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z in
              if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z then Some (MSV_StackPtr off') else None
          | MSV_SavedReg r0 => if N.eqb imm 0%N then Some (MSV_SavedReg r0) else None
          | MSV_Expr e =>
              Some (MSV_Expr (fst (a64_sym_add_sub 64%positive is_sub e (ce_bv_z 64%positive (Z.of_N imm)))))
          | MSV_Undef => None
          end) in *.
        destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hsum].
        destruct (a64_val_write_sp rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
          [| discriminate Hsum].
        assert (Hsv_ag : mc_sym_val_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 sv
          (if is_sub then @Integers.sub 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive (Z.of_N imm))
           else @Integers.add 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive (Z.of_N imm)))).
        { pose proof (a64_val_read_sp_sound penv foracle rf0 sp0 sp_off vrf rf sp rn _ Hrng Hsp Hag eq_refl) as Hrn.
          subst sv_opt; destruct (a64_val_read_sp rn vrf sp_off) as [| e | r0 | base_off] eqn:Ern; try discriminate Esv.
          - inversion Esv; subst sv; clear Esv.
            cbn [mc_sym_val_agrees] in Hrn |- *.
            pose proof (eval_a64_sym_add_sub_sound penv foracle 64%positive is_sub _ _ _ _ Hrn (eval_ce_bv_z _ _ 64%positive (Z.of_N imm))) as [Hres _].
            cbn [a64_eval_add_sub fst] in Hres; exact Hres.
          - destruct (N.eqb imm 0%N) eqn:Ez; [| discriminate Esv].
            apply N.eqb_eq in Ez; subst imm; inversion Esv; subst sv; clear Esv.
            cbn [mc_sym_val_agrees] in Hrn |- *.
            destruct is_sub.
            + unfold Integers.sub; change (Z.of_N 0%N) with 0%Z; rewrite (@Integers.unsigned_repr 64%positive 0%Z) by (compute; split; discriminate); rewrite Z.sub_0_r, Integers.repr_unsigned; exact Hrn.
            + rewrite Hrn, mc_add_ptr_zero; reflexivity.
          - cbv zeta in Esv.
            set (off' := if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z) in *.
            destruct (Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z) eqn:Erng; [| discriminate Esv].
            apply andb_true_iff in Erng as [Er1 Er2]; apply Z.leb_le in Er1; apply Z.leb_le in Er2.
            inversion Esv; subst sv; clear Esv.
            cbn [mc_sym_val_agrees] in Hrn |- *; destruct Hrn as [_ Hptr]; split; [lia |].
            unfold off'; rewrite Hptr; destruct is_sub; [apply mc_sub_ptr_off | apply mc_add_ptr_off]. }
        pose proof (a64_val_write_sp_bounds _ _ _ _ _ _ _ _ Hrng Est) as Hrng'.
        pose proof (a64_val_write_sp_sound penv foracle rf0 sp0 rd sv _ sp_off vrf astk rf sp mstk sp_off' vrf' astk' Hsp Hag Hastk Hsv_ag Est) as Hwr.
        destruct (a64_write_reg_sp rd _ rf sp) as [rf' sp'] eqn:Ewr.
        destruct Hwr as (Hsp' & Hag' & Hastk').
        exact (IH _ _ sp_off' vrf' astk' sfl fl_def ret_w d_mc penv foracle rf0 sp0 rf' sp' fl mstk
                  Hrw Hval Hsp0 Hrng' Hsp' Hag' Hastk' Hfl Hsum).
      * destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hsum |].
        destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
        destruct (a64_sym_add_sub (a64_w sf) is_sub lhs (ce_bv_z (a64_w sf) (Z.of_N imm))) as [se sfl'] eqn:Esas.
        destruct (a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N imm))) as [vr fl'] eqn:Eeas.
        pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
                      (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
                      (eval_ce_bv_z _ _ (a64_w sf) (Z.of_N imm))) as [Hres Hfl'].
        rewrite Esas, Eeas in Hres, Hfl'; cbn [fst snd] in Hres, Hfl'.
        assert (Hfl_next : (set_fl || fl_def = true) -> sym_flags_agree penv foracle (if set_fl then sfl' else sfl) (if set_fl then fl' else fl))
          by (intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)]).
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                  (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl_next Hsum).
    + (* A64_AddSubShift *)
      destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hsum].
      unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply andb_true_iff in Hdec_val as [_ Hamt]; apply N.ltb_lt in Hamt.
      pose proof (eval_a64_sym_shift_sound _ _ (a64_w sf) _ _ sh amt (a64_w_32_64 sf) ltac:(destruct sf; exact Hamt)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as Hsh.
      destruct (a64_sym_add_sub (a64_w sf) is_sub lhs _) as [se sfl'] eqn:Esas.
      destruct (a64_eval_add_sub (a64_w sf) is_sub _ _) as [vr fl'] eqn:Eeas.
      pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) Hsh) as [Hres Hfl'].
      rewrite Esas, Eeas in Hres, Hfl'; cbn [fst snd] in Hres, Hfl'.
      assert (Hfl_next : (set_fl || fl_def = true) -> sym_flags_agree penv foracle (if set_fl then sfl' else sfl) (if set_fl then fl' else fl))
        by (intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)]).
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl_next Hsum).
    + (* A64_AddSubExt *)
      destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hsum |].
      destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read rm vrf) as [| rm64 | |] eqn:Erm; try discriminate Hsum.
      unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply N.leb_le in Hdec_val.
      pose proof (Hag rm) as Hm64; rewrite Erm in Hm64; cbn [mc_sym_val_agrees] in Hm64.
      pose proof (eval_a64_sym_extend_sound _ _ (a64_w sf) _ _ ext amt (a64_w_32_64 sf) Hdec_val Hm64) as Hext.
      destruct (a64_sym_add_sub (a64_w sf) is_sub lhs _) as [se sfl'] eqn:Esas.
      destruct (a64_eval_add_sub (a64_w sf) is_sub _ _) as [vr fl'] eqn:Eeas.
      pose proof (eval_a64_sym_add_sub_sound penv foracle (a64_w sf) is_sub _ _ _ _
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) Hext) as [Hres Hfl'].
      rewrite Esas, Eeas in Hres, Hfl'; cbn [fst snd] in Hres, Hfl'.
      assert (Hfl_next : (set_fl || fl_def = true) -> sym_flags_agree penv foracle (if set_fl then sfl' else sfl) (if set_fl then fl' else fl))
        by (intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)]).
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl_next Hsum).
    + (* A64_LogicalImm *)
      destruct (negb set_fl && N.eqb rd 31%N); [discriminate Hsum |].
      destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
      assert (Hres : eval_closed_cert_expr penv foracle (a64_sym_logic_op (a64_w sf) op lhs (ce_bv_z (a64_w sf) (Z.of_N mask))) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
          (a64_eval_logic_op (a64_w sf) op (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N mask)))))).
      { unfold a64_sym_logic_op, a64_eval_logic_op; rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern), eval_ce_bv_z; cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; destruct op; reflexivity. }
      assert (Hfl_next : (set_fl || fl_def = true) -> sym_flags_agree penv foracle
        (if set_fl then a64_sym_logic_flags (a64_w sf) _ else sfl)
        (if set_fl then a64_eval_logic_flags (a64_w sf) _ else fl))
        by (intro Hs; destruct set_fl; [exact (eval_a64_sym_logic_flags_sound _ _ _ _ _ Hres) | exact (Hfl Hs)]).
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl_next Hsum).
    + (* A64_LogicalShift *)
      destruct (a64_is_orr_mov64 sf op inv_rm set_fl rn sh amt) eqn:Emov.
      * unfold a64_is_orr_mov64 in Emov; rewrite !andb_true_iff in Emov.
        destruct Emov as ((((((Esf & Hinv) & Hsfl) & Hrn31) & Hamt0) & Hop) & Hsh).
        apply negb_true_iff in Hinv; apply negb_true_iff in Hsfl;
          apply N.eqb_eq in Hrn31; apply N.eqb_eq in Hamt0; subst sf inv_rm set_fl rn amt.
        destruct op; try discriminate Hop; destruct sh; try discriminate Hsh.
        destruct (a64_val_read rm vrf) eqn:Erm; try discriminate Hsum.
        all: cbn [a64_w a64_read_w a64_eval_logic_op a64_write_w];
          replace (a64_read_reg 31%N rf) with (@Integers.zero 64%positive) by reflexivity;
          rewrite a64_orr_xzr_lsl0;
          exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                    (a64_val_regs_agrees_write _ _ _ _ _ _ rd _ _ Hag ltac:(pose proof (Hag rm) as Hm0; rewrite Erm in Hm0; exact Hm0))
                    Hastk Hfl Hsum).
      * destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
        destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hsum].
        unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply N.ltb_lt in Hdec_val.
        pose proof (eval_a64_sym_shift_sound _ _ (a64_w sf) _ _ sh amt (a64_w_32_64 sf) ltac:(destruct sf; exact Hdec_val)
                      (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as Hsh.
        assert (Hrhs : eval_closed_cert_expr penv foracle (if inv_rm then a64_sym_not (a64_w sf) _ else _) =
          raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
            (if inv_rm then @Integers.not (a64_w sf) (a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt)
             else a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt))))
          by (destruct inv_rm; [exact (eval_ce_not _ _ _ _ _ Hsh) | exact Hsh]).
        set (vr_shift := a64_eval_shift (a64_w sf) (a64_read_w sf rm rf) sh amt) in *.
        set (se_shift := a64_sym_shift (a64_w sf) rm_e sh amt) in *.
        set (vr_rhs := if inv_rm then @Integers.not (a64_w sf) vr_shift else vr_shift) in *.
        set (se_rhs := if inv_rm then a64_sym_not (a64_w sf) se_shift else se_shift) in *.
        assert (Hres : eval_closed_cert_expr penv foracle (a64_sym_logic_op (a64_w sf) op lhs se_rhs) =
          raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (a64_eval_logic_op (a64_w sf) op (a64_read_w sf rn rf) vr_rhs)))).
        { unfold a64_sym_logic_op, a64_eval_logic_op; rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern), Hrhs; cbn [eou_bind].
          unfold eval_iop; rewrite eval_iop_integer_base_same_width; destruct op; reflexivity. }
        assert (Hfl_next : (set_fl || fl_def = true) -> sym_flags_agree penv foracle
          (if set_fl then a64_sym_logic_flags (a64_w sf) _ else sfl)
          (if set_fl then a64_eval_logic_flags (a64_w sf) _ else fl))
          by (intro Hs; destruct set_fl; [exact (eval_a64_sym_logic_flags_sound _ _ _ _ _ Hres) | exact (Hfl Hs)]).
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                  (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl_next Hsum).
    + (* A64_MoveWide *)
      destruct kind.
      * pose proof (eval_ce_not penv foracle (a64_w sf) _ _ (eval_ce_bv_z _ _ (a64_w sf) (Z.of_N (N.shiftl imm16 shift)))) as Hres.
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                  (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
      * pose proof (eval_ce_bv_z penv foracle (a64_w sf) (Z.of_N (N.shiftl imm16 shift))) as Hres.
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                  (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
      * destruct (a64_val_read_expr_w sf rd vrf) as [cur |] eqn:Erd; [| discriminate Hsum].
        assert (Hand : eval_closed_cert_expr penv foracle
          (CE_BinOp CB_And (a64_w sf) no_binop_flags cur
            (a64_sym_not (a64_w sf) (ce_bv_z (a64_w sf) (Z.of_N (N.shiftl 65535%N shift))))) =
          raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
            (@Integers.and (a64_w sf) (a64_read_w sf rd rf)
              (@Integers.not (a64_w sf) (@Integers.repr (a64_w sf) (Z.of_N (N.shiftl 65535%N shift)))))))).
        { rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erd),
                  (eval_ce_not _ _ _ _ _ (eval_ce_bv_z _ _ _ _)); cbn [eou_bind].
          unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
        assert (Hres : eval_closed_cert_expr penv foracle
          (CE_BinOp CB_Or (a64_w sf) no_binop_flags
            (CE_BinOp CB_And (a64_w sf) no_binop_flags cur
              (a64_sym_not (a64_w sf) (ce_bv_z (a64_w sf) (Z.of_N (N.shiftl 65535%N shift)))))
            (ce_bv_z (a64_w sf) (Z.of_N (N.shiftl imm16 shift)))) =
          raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
            (@Integers.or (a64_w sf)
              (@Integers.and (a64_w sf) (a64_read_w sf rd rf) (@Integers.not (a64_w sf) (@Integers.repr (a64_w sf) (Z.of_N (N.shiftl 65535%N shift)))))
              (@Integers.repr (a64_w sf) (Z.of_N (N.shiftl imm16 shift))))))).
        { rewrite eval_ce_binop, Hand, eval_ce_bv_z; cbn [eou_bind].
          unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                  (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
    + (* A64_Bitfield *)
      destruct (a64_val_read_expr_w sf rn vrf) as [src_e |] eqn:Ern; [| discriminate Hsum].
      unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply andb_true_iff in Hdec_val as [Hr1 Hs1];
        apply N.ltb_lt in Hr1; apply N.ltb_lt in Hs1.
      set (dst_opt := match kind with ABF_Bfm => a64_val_read_expr_w sf rd vrf | _ => Some (CE_BvConst (a64_w sf) 0%N) end) in *.
      destruct dst_opt as [dst_e |] eqn:Edst; [| discriminate Hsum].
      assert (Hres : eval_closed_cert_expr penv foracle (a64_sym_bitfield (a64_w sf) kind src_e dst_e immr imms) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (a64_eval_bitfield (a64_w sf) kind (a64_read_w sf rn rf) (a64_read_w sf rd rf) immr imms)))).
      { destruct kind.
        - subst dst_opt; inversion Edst; subst dst_e.
          epose proof (eval_a64_sym_bitfield_sound penv foracle sf ABF_Sbfm src_e (CE_BvConst (a64_w sf) 0%N) _ (@Integers.zero (a64_w sf)) immr imms Hr1 Hs1
                         (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)) as Hbf.
          cbn [a64_sym_bitfield a64_eval_bitfield] in Hbf |- *; destruct (N.leb immr imms); exact Hbf.
        - subst dst_opt; exact (eval_a64_sym_bitfield_sound _ _ sf ABF_Bfm _ _ _ _ _ _ Hr1 Hs1
                                  (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
                                  (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Edst)).
        - subst dst_opt; inversion Edst; subst dst_e.
          epose proof (eval_a64_sym_bitfield_sound penv foracle sf ABF_Ubfm src_e (CE_BvConst (a64_w sf) 0%N) _ (@Integers.zero (a64_w sf)) immr imms Hr1 Hs1
                         (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern) ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)) as Hbf.
          cbn [a64_sym_bitfield a64_eval_bitfield] in Hbf |- *; destruct (N.leb immr imms); exact Hbf. }
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
    + (* A64_Extr *)
      destruct (a64_val_read_expr_w sf rn vrf) as [hi_e |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [lo_e |] eqn:Erm; [| discriminate Hsum].
      pose proof (eval_a64_sym_extr_sound _ _ (a64_w sf) _ _ _ _ lsb (a64_w_32_64 sf)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as Hres.
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
    + (* A64_MulAddSub *)
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf ra vrf) as [ea |] eqn:Era; [| discriminate Hsum].
      assert (Hmul : eval_closed_cert_expr penv foracle (CE_BinOp CB_Mul (a64_w sf) no_binop_flags en em) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf) (@Integers.mul (a64_w sf) (a64_read_w sf rn rf) (a64_read_w sf rm rf))))).
      { rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern),
                  (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm); cbn [eou_bind].
        destruct sf; unfold eval_iop; rewrite eval_iop_integer_base_same_width;
          cbn - [Integers.mul a64_read_w]; reflexivity. }
      assert (Hres : eval_closed_cert_expr penv foracle
        (CE_BinOp (if is_sub then CB_Sub else CB_Add) (a64_w sf) no_binop_flags ea
          (CE_BinOp CB_Mul (a64_w sf) no_binop_flags en em)) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa (a64_w sf)
          (let p := @Integers.mul (a64_w sf) (a64_read_w sf rn rf) (a64_read_w sf rm rf) in
           let a := a64_read_w sf ra rf in
           if is_sub then @Integers.sub (a64_w sf) a p else @Integers.add (a64_w sf) a p)))).
      { rewrite eval_ce_binop, (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Era), Hmul; cbn [eou_bind].
        destruct sf, is_sub; unfold eval_iop; rewrite eval_iop_integer_base_same_width;
          cbn - [Integers.mul Integers.add Integers.sub a64_read_w]; reflexivity. }
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
    + (* A64_MulWidening *)
      destruct (a64_val_read_expr_w false rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w false rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      destruct (a64_val_read ra vrf) as [| ea | |] eqn:Era; try discriminate Hsum.
      set (en64 := CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags en).
      set (em64 := CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags em).
      set (vn64 := @Integers.repr 64%positive (if sgn then @Integers.signed 32%positive (a64_read_w false rn rf)
                                               else @Integers.unsigned 32%positive (a64_read_w false rn rf))).
      set (vm64 := @Integers.repr 64%positive (if sgn then @Integers.signed 32%positive (a64_read_w false rm rf)
                                               else @Integers.unsigned 32%positive (a64_read_w false rm rf))).
      assert (Hn64 : eval_closed_cert_expr penv foracle en64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive vn64)))
        by (unfold en64, vn64; destruct sgn; [apply eval_ce_sext | apply eval_ce_zext]; try reflexivity; exact (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)).
      assert (Hm64 : eval_closed_cert_expr penv foracle em64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive vm64)))
        by (unfold em64, vm64; destruct sgn; [apply eval_ce_sext | apply eval_ce_zext]; try reflexivity; exact (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)).
      assert (Hmul : eval_closed_cert_expr penv foracle (CE_BinOp CB_Mul 64%positive no_binop_flags en64 em64) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (@Integers.mul 64%positive vn64 vm64)))).
      { rewrite eval_ce_binop, Hn64, Hm64; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width;
          cbn - [Integers.mul vn64 vm64]; reflexivity. }
      pose proof (Hag ra) as Ha; rewrite Era in Ha; cbn [mc_sym_val_agrees] in Ha.
      assert (Hres : eval_closed_cert_expr penv foracle
        (CE_BinOp (if is_sub then CB_Sub else CB_Add) 64%positive no_binop_flags ea
          (CE_BinOp CB_Mul 64%positive no_binop_flags en64 em64)) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive
          (let p := @Integers.mul 64%positive vn64 vm64 in
           let a := a64_read_reg ra rf in
           if is_sub then @Integers.sub 64%positive a p else @Integers.add 64%positive a p)))).
      { rewrite eval_ce_binop, Ha, Hmul; cbn [eou_bind].
        unfold eval_iop; rewrite eval_iop_integer_base_same_width; destruct is_sub;
          cbn - [Integers.mul Integers.add Integers.sub vn64 vm64 a64_read_reg]; reflexivity. }
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write _ _ _ _ _ _ rd (MSV_Expr _) _ Hag Hres) Hastk Hfl Hsum).
    + (* A64_DataProc2 *)
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      pose proof (eval_a64_sym_dp2_sound _ _ (a64_w sf) op _ _ _ _ (a64_w_32_64 sf)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as Hres.
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
    + (* A64_CondSelect *)
      destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      pose proof (eval_a64_sym_csel_sound _ _ (a64_w sf) kind cond sfl fl _ _ _ _ (Hfl eq_refl)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as Hres.
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp
                (a64_val_regs_agrees_write_w _ _ _ _ _ _ sf rd _ _ Hag Hres) Hastk Hfl Hsum).
    + (* A64_CondCompareReg *)
      destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      destruct (a64_sym_add_sub (a64_w sf) is_sub en em) as [se csfl] eqn:Esas.
      destruct (a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) (a64_read_w sf rm rf)) as [vr cfl] eqn:Eeas.
      pose proof (eval_a64_sym_add_sub_sound _ _ (a64_w sf) is_sub _ _ _ _
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Erm)) as [_ Hcsfl].
      rewrite Esas, Eeas in Hcsfl; cbn [snd] in Hcsfl.
      pose proof (eval_a64_sym_ite_flags_sound _ _ _ _ _ _ _ _ (eval_a64_sym_cond_sound _ _ cond _ _ (Hfl eq_refl)) Hcsfl (eval_a64_sym_flags_imm4_sound _ _ nzcv)) as Hite.
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk (fun _ => Hite) Hsum).
    + (* A64_CondCompareImm *)
      destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_sym_add_sub (a64_w sf) is_sub en (ce_bv_z (a64_w sf) (Z.of_N imm5))) as [se csfl] eqn:Esas.
      destruct (a64_eval_add_sub (a64_w sf) is_sub (a64_read_w sf rn rf) (@Integers.repr (a64_w sf) (Z.of_N imm5))) as [vr cfl] eqn:Eeas.
      pose proof (eval_a64_sym_add_sub_sound _ _ (a64_w sf) is_sub _ _ _ _
                    (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ern)
                    (eval_ce_bv_z _ _ (a64_w sf) (Z.of_N imm5))) as [_ Hcsfl].
      rewrite Esas, Eeas in Hcsfl; cbn [snd] in Hcsfl.
      pose proof (eval_a64_sym_ite_flags_sound _ _ _ _ _ _ _ _ (eval_a64_sym_cond_sound _ _ cond _ _ (Hfl eq_refl)) Hcsfl (eval_a64_sym_flags_imm4_sound _ _ nzcv)) as Hite.
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk (fun _ => Hite) Hsum).
    + (* A64_LdStImm *)
      destruct Hsp0 as [Hsp0_cap Hsp0_al].
      assert (Hsp_to_off : mc_addr_to_off sp0 sp = sp_off)
        by (rewrite Hsp; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hrng]).
      rewrite Hsp_to_off.
      destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hsum |].
      destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off] eqn:Ern; try discriminate Hsum.
      pose proof (a64_val_read_sp_sound penv foracle rf0 sp0 sp_off vrf rf sp rn _ Hrng Hsp Hag Ern) as Hrn_ag.
      cbn [mc_sym_val_agrees] in Hrn_ag; destruct Hrn_ag as [Hbase_rng Hbase_ptr].
      set (wb_off := (base_off + imm)%Z) in *.
      set (wb_addr := @Integers.add 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive imm)) in *.
      assert (Hwb_ptr : wb_addr = @Integers.add 64%positive sp0 (@Integers.repr 64%positive wb_off))
        by (unfold wb_addr, wb_off; rewrite Hbase_ptr, mc_add_ptr_off; reflexivity).
      set (wb_ok := match mode with AAM_SignedOffset => true | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z end) in *.
      destruct wb_ok eqn:Ewb; cbn [negb] in Hsum; [| discriminate Hsum].
      assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end).
      { destruct mode; [exact I | |]; apply andb_true_iff in Ewb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; lia. }
      set (pair_off := match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end).
      destruct pair_off as [off sp_chk] eqn:Epo.
      cbv zeta in Hsum.
      assert (Hpo_eq : match mode with
                       | AAM_SignedOffset => (wb_off, sp_off)
                       | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
                       | AAM_PostIndex => (base_off, sp_off)
                       end = (off, sp_chk)) by exact Epo.
      rewrite Hpo_eq in Hsum; cbv iota in Hsum.
      destruct (mc_slot_in_frame sp_chk off sz) eqn:Eslot; [| discriminate Hsum].
      pose proof (mc_slot_in_frame_bounds _ _ _ Eslot) as (Hb1 & Hb2 & Hb3 & _).
      assert (Hsz_pos : (1 <= mc_mem_bytes_Z sz)%Z) by (destruct sz; cbn; lia).
      assert (Hc_eq :
        mc_addr_to_off sp0 (match mode with AAM_SignedOffset | AAM_PreIndex => wb_addr | AAM_PostIndex => a64_read_reg_sp rn rf sp end) = off /\
        mc_addr_to_off sp0 (match mode with AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp | _ => sp end) = sp_chk).
      { destruct mode; inversion Epo; subst off sp_chk; split.
        - rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia].
        - exact Hsp_to_off.
        - rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia].
        - destruct (N.eqb rn 31%N); [rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia] | exact Hsp_to_off].
        - rewrite Hbase_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hbase_rng].
        - exact Hsp_to_off. }
      destruct Hc_eq as [Hoff_c Hspchk_c].
      replace (match mode with AAM_SignedOffset => (wb_addr, sp) | AAM_PreIndex => (wb_addr, if N.eqb rn 31%N then wb_addr else sp) | AAM_PostIndex => (a64_read_reg_sp rn rf sp, sp) end)
        with ((match mode with AAM_SignedOffset | AAM_PreIndex => wb_addr | AAM_PostIndex => a64_read_reg_sp rn rf sp end),
              (match mode with AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp | _ => sp end))
        by (destruct mode; reflexivity).
      cbn [fst snd] in *; rewrite Hoff_c, Hspchk_c, Eslot.
      set (st_opt :=
        if is_load then
          match mc_sym_stk_load off sz is_signed astk with
          | None => None
          | Some sv0 =>
              match a64_ldst_sym_load is_signed sf_dst sv0 with
              | None => None
              | Some sv1 => Some (a64_val_write rt sv1 vrf, astk)
              end
          end
        else
          if a64_ldst_store_sym_ok sz (a64_val_read rt vrf) then Some (vrf, mc_sym_stk_store off sz (a64_val_read rt vrf) astk) else None) in *.
      destruct st_opt as [[vrf1 astk1] |] eqn:Est;
        [try (rewrite Est in Hsum; cbv iota in Hsum) | try rewrite Est in Hsum; discriminate Hsum].
      assert (Hstep1 :
        let '(rf1, mstk1) :=
          if is_load then (a64_write_reg rt (a64_ldst_apply_load is_signed sf_dst (mc_stk_load mstk off sz is_signed)) rf, mstk)
          else (rf, mc_stk_store mstk off sz (a64_read_reg rt rf)) in
        a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\
        mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1).
      { destruct is_load; unfold st_opt in Est.
        - destruct (mc_sym_stk_load off sz is_signed astk) as [sv0 |] eqn:Esl0; [| discriminate Est].
          destruct (a64_ldst_sym_load is_signed sf_dst sv0) as [sv1 |] eqn:Esl1; [| discriminate Est].
          inversion Est; subst vrf1 astk1; clear Est.
          pose proof (mc_sym_stk_load_sound _ _ _ _ _ _ _ _ _ _ Hastk Esl0) as Hsv0.
          pose proof (a64_ldst_sym_load_sound _ _ _ _ _ _ _ _ _ Hsv0 Esl1) as Hsv1.
          split; [apply a64_val_regs_agrees_write; assumption | exact Hastk].
        - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt vrf)) eqn:Eok; [| discriminate Est].
          inversion Est; subst vrf1 astk1; clear Est.
          assert (Hszm : match a64_val_read rt vrf with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end).
          { destruct (a64_val_read rt vrf); try exact I; apply mc_mem_size_eqb_eq; exact Eok. }
          split; [exact Hag | apply mc_sym_stk_store_agrees; [exact Hszm | exact (Hag rt) | exact Hastk]]. }
      set (rf1 := if is_load then a64_write_reg rt (a64_ldst_apply_load is_signed sf_dst (mc_stk_load mstk off sz is_signed)) rf else rf) in *.
      set (mstk1 := if is_load then mstk else mc_stk_store mstk off sz (a64_read_reg rt rf)) in *.
      assert (Hstep1' : a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\
                        mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1)
        by (destruct is_load; exact Hstep1).
      destruct Hstep1' as [Hag1 Hastk1].
      pose proof (a64_ldst_writeback_sound penv foracle rf0 sp0 sp_off vrf1 astk1 rf1 sp mstk1 mode rn wb_off wb_addr
                    Hrng Hsp Hwb_rng Hwb_ptr Hag1 Hastk1) as Hwb_s.
      destruct (match mode with AAM_SignedOffset => (sp_off, vrf1, astk1) | _ => if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1) else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1) end)
        as [[sp_off2 vrf2] astk2] eqn:Ewbs.
      destruct (match mode with AAM_SignedOffset => (rf1, sp) | _ => a64_write_reg_sp rn wb_addr rf1 sp end)
        as [rf2 sp2] eqn:Ewbc.
      try rewrite Ewbs in Hwb_s; try rewrite Ewbc in Hwb_s; cbv iota in Hwb_s.
      try (rewrite Ewbs in Hsum; cbv iota in Hsum).
      destruct Hwb_s as (Hrng2 & Hsp2 & Hag2 & Hastk2).
      replace (if is_load then (a64_write_reg rt (a64_ldst_apply_load is_signed sf_dst (mc_stk_load mstk off sz is_signed)) rf, mstk) else (rf, mc_stk_store mstk off sz (a64_read_reg rt rf)))
        with (rf1, mstk1) by (destruct is_load; reflexivity).
      rewrite Ewbc; exact (IH _ _ sp_off2 vrf2 astk2 sfl fl_def ret_w d_mc penv foracle rf0 sp0 rf2 sp2 fl mstk1
                             Hrw Hval (conj Hsp0_cap Hsp0_al) Hrng2 Hsp2 Hag2 Hastk2 Hfl Hsum).
    + (* A64_LdStPair *)
      destruct Hsp0 as [Hsp0_cap Hsp0_al].
      assert (Hsp_to_off : mc_addr_to_off sp0 sp = sp_off)
        by (rewrite Hsp; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hrng]).
      rewrite Hsp_to_off.
      destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hsum |].
      destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off] eqn:Ern; try discriminate Hsum.
      pose proof (a64_val_read_sp_sound penv foracle rf0 sp0 sp_off vrf rf sp rn _ Hrng Hsp Hag Ern) as Hrn_ag.
      cbn [mc_sym_val_agrees] in Hrn_ag; destruct Hrn_ag as [Hbase_rng Hbase_ptr].
      set (wb_off := (base_off + imm)%Z) in *.
      set (wb_addr := @Integers.add 64%positive (a64_read_reg_sp rn rf sp) (@Integers.repr 64%positive imm)) in *.
      assert (Hwb_ptr : wb_addr = @Integers.add 64%positive sp0 (@Integers.repr 64%positive wb_off))
        by (unfold wb_addr, wb_off; rewrite Hbase_ptr, mc_add_ptr_off; reflexivity).
      set (wb_ok := match mode with AAM_SignedOffset => true | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z end) in *.
      destruct wb_ok eqn:Ewb; cbn [negb] in Hsum; [| discriminate Hsum].
      assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end).
      { destruct mode; [exact I | |]; apply andb_true_iff in Ewb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; lia. }
      set (pair_off := match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end).
      destruct pair_off as [off sp_chk] eqn:Epo.
      cbv zeta in Hsum.
      assert (Hpo_eq : match mode with
                       | AAM_SignedOffset => (wb_off, sp_off)
                       | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
                       | AAM_PostIndex => (base_off, sp_off)
                       end = (off, sp_chk)) by exact Epo.
      rewrite Hpo_eq in Hsum; cbv iota in Hsum.
      set (sz := if sf then MS_8 else MS_4) in *; set (delta := mc_mem_bytes_Z sz) in *.
      destruct (mc_slot_in_frame sp_chk off sz && mc_slot_in_frame sp_chk (off + delta) sz) eqn:Eslots; [| discriminate Hsum].
      apply andb_true_iff in Eslots as [Esl1 Esl2].
      pose proof (mc_slot_in_frame_bounds _ _ _ Esl1) as (Hb1 & Hb2 & Hb3 & _).
      pose proof (mc_slot_in_frame_bounds _ _ _ Esl2) as (_ & Hb2' & Hb3' & _).
      assert (Hsz_pos : (1 <= delta)%Z) by (unfold delta, sz; destruct sf; cbn; lia).
      assert (Hc_eq :
        mc_addr_to_off sp0 (match mode with AAM_SignedOffset | AAM_PreIndex => wb_addr | AAM_PostIndex => a64_read_reg_sp rn rf sp end) = off /\
        mc_addr_to_off sp0 (match mode with AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp | _ => sp end) = sp_chk).
      { destruct mode; inversion Epo; subst off sp_chk; split.
        - rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia].
        - exact Hsp_to_off.
        - rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia].
        - destruct (N.eqb rn 31%N); [rewrite Hwb_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | lia] | exact Hsp_to_off].
        - rewrite Hbase_ptr; apply mc_addr_to_off_add; [exact Hsp0_cap | exact Hbase_rng].
        - exact Hsp_to_off. }
      destruct Hc_eq as [Hoff_c Hspchk_c].
      replace (match mode with AAM_SignedOffset => (wb_addr, sp) | AAM_PreIndex => (wb_addr, if N.eqb rn 31%N then wb_addr else sp) | AAM_PostIndex => (a64_read_reg_sp rn rf sp, sp) end)
        with ((match mode with AAM_SignedOffset | AAM_PreIndex => wb_addr | AAM_PostIndex => a64_read_reg_sp rn rf sp end),
              (match mode with AAM_PreIndex => if N.eqb rn 31%N then wb_addr else sp | _ => sp end))
        by (destruct mode; reflexivity).
      cbn [fst snd] in *; rewrite Hoff_c, Hspchk_c, Esl1, Esl2; cbn [andb].
      set (st_opt :=
        if is_load then
          match mc_sym_stk_load off sz false astk, mc_sym_stk_load (off + delta) sz false astk with
          | Some sv1, Some sv2 => Some (a64_val_write rt2 sv2 (a64_val_write rt1 sv1 vrf), astk)
          | _, _ => None
          end
        else
          if a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) && a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf) then
            Some (vrf, mc_sym_stk_store (off + delta) sz (a64_val_read rt2 vrf) (mc_sym_stk_store off sz (a64_val_read rt1 vrf) astk))
          else None) in *.
      destruct st_opt as [[vrf1 astk1] |] eqn:Est;
        [try (rewrite Est in Hsum; cbv iota in Hsum) | try rewrite Est in Hsum; discriminate Hsum].
      assert (Hstep1 :
        let '(rf1, mstk1) :=
          if is_load then (a64_write_reg rt2 (mc_stk_load mstk (off + delta) sz false) (a64_write_reg rt1 (mc_stk_load mstk off sz false) rf), mstk)
          else (rf, mc_stk_store (mc_stk_store mstk off sz (a64_read_reg rt1 rf)) (off + delta) sz (a64_read_reg rt2 rf)) in
        a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\
        mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1).
      { destruct is_load; unfold st_opt in Est.
        - destruct (mc_sym_stk_load off sz false astk) as [sv1 |] eqn:Esl_1; [| discriminate Est].
          destruct (mc_sym_stk_load (off + delta) sz false astk) as [sv2 |] eqn:Esl_2; [| discriminate Est].
          inversion Est; subst vrf1 astk1; clear Est.
          pose proof (mc_sym_stk_load_sound _ _ _ _ _ _ _ _ _ _ Hastk Esl_1) as Hsv1.
          pose proof (mc_sym_stk_load_sound _ _ _ _ _ _ _ _ _ _ Hastk Esl_2) as Hsv2.
          split; [apply a64_val_regs_agrees_write; [apply a64_val_regs_agrees_write; assumption | exact Hsv2] | exact Hastk].
        - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) && a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf)) eqn:Eok;
            [| discriminate Est].
          apply andb_true_iff in Eok as [Eok1 Eok2].
          inversion Est; subst vrf1 astk1; clear Est.
          assert (Hszm1 : match a64_val_read rt1 vrf with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end)
            by (destruct (a64_val_read rt1 vrf); try exact I; apply mc_mem_size_eqb_eq; exact Eok1).
          assert (Hszm2 : match a64_val_read rt2 vrf with MSV_SavedReg _ | MSV_StackPtr _ => sz = MS_8 | _ => True end)
            by (destruct (a64_val_read rt2 vrf); try exact I; apply mc_mem_size_eqb_eq; exact Eok2).
          split; [exact Hag |].
          apply mc_sym_stk_store_agrees; [exact Hszm2 | exact (Hag rt2) |].
          apply mc_sym_stk_store_agrees; [exact Hszm1 | exact (Hag rt1) | exact Hastk]. }
      set (rf1 := if is_load then a64_write_reg rt2 (mc_stk_load mstk (off + delta) sz false) (a64_write_reg rt1 (mc_stk_load mstk off sz false) rf) else rf) in *.
      set (mstk1 := if is_load then mstk else mc_stk_store (mc_stk_store mstk off sz (a64_read_reg rt1 rf)) (off + delta) sz (a64_read_reg rt2 rf)) in *.
      assert (Hstep1' : a64_val_regs_agrees penv foracle rf0 sp0 vrf1 rf1 /\
                        mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk1 mstk1)
        by (destruct is_load; exact Hstep1).
      destruct Hstep1' as [Hag1 Hastk1].
      pose proof (a64_ldst_writeback_sound penv foracle rf0 sp0 sp_off vrf1 astk1 rf1 sp mstk1 mode rn wb_off wb_addr
                    Hrng Hsp Hwb_rng Hwb_ptr Hag1 Hastk1) as Hwb_s.
      destruct (match mode with AAM_SignedOffset => (sp_off, vrf1, astk1) | _ => if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1) else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1) end)
        as [[sp_off2 vrf2] astk2] eqn:Ewbs.
      destruct (match mode with AAM_SignedOffset => (rf1, sp) | _ => a64_write_reg_sp rn wb_addr rf1 sp end)
        as [rf2 sp2] eqn:Ewbc.
      try rewrite Ewbs in Hwb_s; try rewrite Ewbc in Hwb_s; cbv iota in Hwb_s.
      try (rewrite Ewbs in Hsum; cbv iota in Hsum).
      destruct Hwb_s as (Hrng2 & Hsp2 & Hag2 & Hastk2).
      replace (if is_load then (a64_write_reg rt2 (mc_stk_load mstk (off + delta) sz false) (a64_write_reg rt1 (mc_stk_load mstk off sz false) rf), mstk)
               else (rf, mc_stk_store (mc_stk_store mstk off sz (a64_read_reg rt1 rf)) (off + delta) sz (a64_read_reg rt2 rf)))
        with (rf1, mstk1) by (destruct is_load; reflexivity).
      rewrite Ewbc; exact (IH _ _ sp_off2 vrf2 astk2 sfl fl_def ret_w d_mc penv foracle rf0 sp0 rf2 sp2 fl mstk1
                             Hrw Hval (conj Hsp0_cap Hsp0_al) Hrng2 Hsp2 Hag2 Hastk2 Hfl Hsum).
    + (* A64_B *)
      destruct (add_rel_off pc rel); [| discriminate Hsum].
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Hsum).
    + (* A64_BCond *)
      destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (add_rel_off pc rel) as [tgt_pc |]; [| discriminate Hsum].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk sfl true ret_w) as [| dt] eqn:Edt;
        [discriminate Hsum |].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) (pc + 4%N)%N sp_off vrf astk sfl true ret_w) as [| df] eqn:Edf;
        [discriminate Hsum |].
      inversion Hsum; subst d_mc; clear Hsum.
      pose proof (eval_a64_sym_cond_sound penv foracle cond sfl fl (Hfl eq_refl)) as Hc.
      cbn [eval_cfg_dag]; cbn [N.shiftl] in Hc; rewrite Hc.
      destruct (a64_eval_cond cond fl).
      * rewrite (@Integers.unsigned_one 1%positive); cbn [Z.eqb].
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Edt).
      * rewrite (@Integers.unsigned_zero 1%positive); cbn [Z.eqb].
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Edf).
    + (* A64_Cbz *)
      destruct (a64_val_read_expr_w sf rt vrf) as [rt_e |] eqn:Ert; [| discriminate Hsum].
      destruct (add_rel_off pc rel) as [tgt_pc |]; [| discriminate Hsum].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk sfl fl_def ret_w) as [| dt] eqn:Edt;
        [discriminate Hsum |].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) (pc + 4%N)%N sp_off vrf astk sfl fl_def ret_w) as [| df] eqn:Edf;
        [discriminate Hsum |].
      inversion Hsum; subst d_mc; clear Hsum.
      assert (Hc : eval_closed_cert_expr penv foracle
        (CE_ICmp (if is_nz then CIP_Ne else CIP_Eq) false (a64_w sf) rt_e (CE_BvConst (a64_w sf) 0%N)) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
          (if (if is_nz then negb (@Integers.eq (a64_w sf) (a64_read_w sf rt rf) (@Integers.zero (a64_w sf)))
               else @Integers.eq (a64_w sf) (a64_read_w sf rt rf) (@Integers.zero (a64_w sf)))
           then @Integers.one 1%positive else @Integers.zero 1%positive)))).
      { destruct is_nz;
          [exact (eval_ce_icmp_eq_bool _ _ CIP_Ne _ _ _ _ _ (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ert) ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity))
          | exact (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _ (a64_val_read_expr_w_sound _ _ _ _ _ _ _ _ _ Hag Ert) ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity))]. }
      cbn [eval_cfg_dag]; cbn [N.shiftl] in Hc; rewrite Hc.
      destruct (if is_nz then negb (@Integers.eq (a64_w sf) (a64_read_w sf rt rf) (@Integers.zero (a64_w sf)))
                else @Integers.eq (a64_w sf) (a64_read_w sf rt rf) (@Integers.zero (a64_w sf))).
      * rewrite (@Integers.unsigned_one 1%positive); cbn [Z.eqb].
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Edt).
      * rewrite (@Integers.unsigned_zero 1%positive); cbn [Z.eqb].
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Edf).
    + (* A64_Tbz *)
      destruct (a64_val_read rt vrf) as [| rt_e | |] eqn:Ert; try discriminate Hsum.
      destruct (add_rel_off pc rel) as [tgt_pc |]; [| discriminate Hsum].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk sfl fl_def ret_w) as [| dt] eqn:Edt;
        [discriminate Hsum |].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) (pc + 4%N)%N sp_off vrf astk sfl fl_def ret_w) as [| df] eqn:Edf;
        [discriminate Hsum |].
      inversion Hsum; subst d_mc; clear Hsum.
      unfold a64_inst_valid in Hdec_val; rewrite Ed in Hdec_val; apply N.ltb_lt in Hdec_val.
      pose proof (Hag rt) as Hrt; rewrite Ert in Hrt; cbn [mc_sym_val_agrees] in Hrt.
      assert (Hm : eval_closed_cert_expr penv foracle
        (CE_BinOp CB_And 64%positive no_binop_flags rt_e (CE_BvConst 64%positive (N.shiftl 1%N bit))) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive
          (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))))).
      { rewrite eval_ce_binop, Hrt, eval_ce_const; cbn [eou_bind];
          unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
      assert (Heq_tb : negb (@Integers.eq 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit)))) (@Integers.zero 64%positive)) =
                       Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit)).
      { pose proof (integers_eq_zero_iff 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))) as Hiz.
        destruct (@Integers.eq 64%positive _ _) eqn:Ez,
                 (Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit)) eqn:Etb;
          try reflexivity.
        - exfalso; pose proof (proj1 Hiz eq_refl) as Hz.
          assert (Hb : Z.testbit (@Integers.unsigned 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))) (Z.of_N bit) = false)
            by (rewrite Hz; apply Z.testbit_0_l).
          change (Z.testbit (@Integers.unsigned 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))))) (Z.of_N bit))
            with (@Integers.testbit 64%positive (@Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit)))) (Z.of_N bit)) in Hb.
          rewrite Integers.bits_and, (@Integers.testbit_repr 64%positive _ (Z.of_N bit)) in Hb
            by (change (@Integers.zwordsize 64%positive) with 64%Z; lia).
          rewrite N.shiftl_1_l, N2Z.inj_pow, Z.pow2_bits_true in Hb by lia.
          unfold Integers.testbit in Hb; rewrite Etb in Hb; discriminate Hb.
        - exfalso; assert (Hnz : @Integers.and 64%positive (a64_read_reg rt rf) (@Integers.repr 64%positive (Z.of_N (N.shiftl 1%N bit))) = @Integers.zero 64%positive).
          { apply Integers.same_bits_eq; intros i Hi; rewrite Integers.bits_zero, Integers.bits_and by exact Hi.
            rewrite (@Integers.testbit_repr 64%positive _ i Hi).
            change (@Integers.zwordsize 64%positive) with 64%Z in Hi.
            rewrite N.shiftl_1_l, N2Z.inj_pow; destruct (Z.eq_dec i (Z.of_N bit)) as [-> | Hne].
            - unfold Integers.testbit; rewrite Etb; reflexivity.
            - rewrite Z.pow2_bits_false by (try lia; exact Hne); rewrite andb_false_r; reflexivity. }
          pose proof (proj2 Hiz ltac:(rewrite Hnz, (@Integers.unsigned_zero 64%positive); reflexivity)) as Htru.
          discriminate Htru. }
      assert (Hc : eval_closed_cert_expr penv foracle
        (CE_ICmp (if is_nz then CIP_Ne else CIP_Eq) false 64%positive
          (CE_BinOp CB_And 64%positive no_binop_flags rt_e (CE_BvConst 64%positive (N.shiftl 1%N bit)))
          (CE_BvConst 64%positive 0%N)) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
          (if (if is_nz then Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit)
               else negb (Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit)))
           then @Integers.one 1%positive else @Integers.zero 1%positive)))).
      { rewrite <- Heq_tb.
        destruct is_nz.
        - exact (eval_ce_icmp_eq_bool _ _ CIP_Ne _ _ _ _ _ Hm ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)).
        - rewrite negb_involutive; exact (eval_ce_icmp_eq_bool _ _ CIP_Eq _ _ _ _ _ Hm ltac:(rewrite eval_ce_const, repr_zero_N; reflexivity)). }
      cbn [eval_cfg_dag]; cbn [N.shiftl] in Hc; rewrite Hc.
      destruct (if is_nz then Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit)
                else negb (Z.testbit (@Integers.unsigned 64%positive (a64_read_reg rt rf)) (Z.of_N bit))).
      * rewrite (@Integers.unsigned_one 1%positive); cbn [Z.eqb].
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Edt).
      * rewrite (@Integers.unsigned_zero 1%positive); cbn [Z.eqb].
        exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrw Hval Hsp0 Hrng Hsp Hag Hastk Hfl Edf).
    + (* A64_Ret *)
      destruct (a64_sym_epilogue_ok sp_off vrf) eqn:Hep; [| discriminate Hsum].
      destruct (a64_val_read 0%N vrf) as [| e_ret | |] eqn:Er0; try discriminate Hsum.
      inversion Hsum; subst d_mc; clear Hsum.
      destruct (a64_sym_epilogue_ok_sound penv foracle rf0 sp0 sp_off vrf rf sp Hsp Hag Hep) as [Hsp_end Hcs].
      rewrite Hsp_end; exists rf, fl, mstk; split; [reflexivity | split; [exact Hcs |]].
      cbn [eval_cfg_dag]; unfold rv_trunc_ret_expr, rv_trunc_ret_val.
      pose proof (Hag 0%N) as Ha0; rewrite Er0 in Ha0; cbn [mc_sym_val_agrees] in Ha0.
      destruct (Pos.eqb ret_w 64%positive) eqn:Ew64.
      * apply Pos.eqb_eq in Ew64; subst ret_w; rewrite Ha0, (@Integers.repr_unsigned 64%positive); reflexivity.
      * assert (Hlt64 : (ret_w <? 64)%positive = true) by exact (rv_supported_arg_width_lt64 _ Hrw Ew64).
        rewrite (eval_ce_trunc penv foracle 64%positive ret_w _ _ Hlt64 Ha0); reflexivity.
Qed.

(** *** 5.2 Zero-Axiom Symbolic Well-Formedness *)

Definition wf_sym_flags (allowed : list (string * positive)) (sfl : a64_sym_flags) : Prop :=
  wf_sym_expr allowed 1%positive (asf_n sfl) /\
  wf_sym_expr allowed 1%positive (asf_z sfl) /\
  wf_sym_expr allowed 1%positive (asf_c sfl) /\
  wf_sym_expr allowed 1%positive (asf_v sfl) /\
  wf_sym_expr allowed 1%positive (asf_n_ne_v sfl).

Definition wf_a64_val_regs (allowed : list (string * positive)) (vrf : a64_val_regs) : Prop :=
  forall r, mc_sym_val_wf allowed (a64_val_read r vrf).

Lemma a64_wf_sym_binop : forall allowed op w a b,
  wf_sym_expr allowed w a ->
  wf_sym_expr allowed w b ->
  wf_sym_expr allowed w (CE_BinOp op w no_binop_flags a b).
Proof.
  intros allowed op w a b (Hta & Hwa & Hlfa & Hva) (Htb & Hwb & Hlfb & Hvb).
  split; [| split; [| split]]; cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars].
  - destruct op; rewrite Hta, Htb, Hwa, Hwb, !Pos.eqb_refl; reflexivity.
  - reflexivity.
  - rewrite Hlfa, Hlfb; reflexivity.
  - apply vars_subset_app; assumption.
Qed.

Lemma wf_a64_sym_trunc32 : forall allowed e,
  wf_sym_expr allowed 64%positive e ->
  wf_sym_expr allowed 32%positive (a64_sym_trunc32 e).
Proof.
  intros allowed e Hwf.
  assert (Hfall : wf_sym_expr allowed 32%positive (ce_trunc64_32 e)) by (apply wf_sym_cast; [reflexivity | exact Hwf]).
  unfold a64_sym_trunc32.
  destruct (a64_sym_trunc32_match e) as [inner |] eqn:Em; [| exact Hfall].
  destruct e as [| | | op w1 fl l r | | k fw tw fl o | | |];
    cbn [a64_sym_trunc32_match] in Em; try discriminate Em.
  - destruct op; try discriminate Em.
    destruct l as [| | | | | kl fw tw fll ol | | |]; try discriminate Em.
    destruct kl; try discriminate Em.
    destruct r as [| | | opr w2 flr lr rr | | | | |]; try discriminate Em.
    destruct opr; try discriminate Em.
    destruct rr as [w3 mask | | | | | | | |]; try discriminate Em.
    destruct (Pos.eqb w1 64%positive && Pos.eqb fw 32%positive && Pos.eqb tw 64%positive &&
              Pos.eqb w2 64%positive && Pos.eqb w3 64%positive &&
              N.eqb (N.land mask 4294967295%N) 0%N) eqn:Eok; [| discriminate Em].
    inversion Em; subst inner; clear Em.
    rewrite !andb_true_iff in Eok; destruct Eok as (((((Ew1 & Efw) & Etw) & Ew2) & Ew3) & _).
    apply Pos.eqb_eq in Ew1; apply Pos.eqb_eq in Efw; apply Pos.eqb_eq in Etw;
      apply Pos.eqb_eq in Ew2; apply Pos.eqb_eq in Ew3; subst w1 fw tw w2 w3.
    destruct Hwf as (Hwt & _ & Hlf & Hvs);
      cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf, Hvs;
      repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end;
      match goal with H : (cert_expr_bit_width ol =? 32)%positive = true |- _ => apply Pos.eqb_eq in H end;
      unfold vars_subset_b in Hvs; rewrite forallb_app in Hvs; apply andb_true_iff in Hvs as [Hvo _];
      repeat split; assumption.
  - destruct k; try discriminate Em.
    destruct (Pos.eqb fw 32%positive && Pos.eqb tw 64%positive) eqn:Eok; [| discriminate Em].
    inversion Em; subst inner; clear Em.
    apply andb_true_iff in Eok as [Efw _]; apply Pos.eqb_eq in Efw; subst fw.
    destruct Hwf as (Hwt & _ & Hlf & Hvs);
      cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf, Hvs;
      repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end;
      match goal with H : (cert_expr_bit_width o =? 32)%positive = true |- _ => apply Pos.eqb_eq in H end;
      repeat split; assumption.
Qed.

Lemma wf_a64_val_write : forall allowed vrf rd sv,
  wf_a64_val_regs allowed vrf ->
  mc_sym_val_wf allowed sv ->
  wf_a64_val_regs allowed (a64_val_write rd sv vrf).
Proof.
  intros allowed vrf rd sv Hwf Hsv r.
  unfold a64_val_read, a64_val_write.
  destruct (N.leb 31%N r) eqn:Er31; [apply wf_sym_bv_const |].
  destruct (N.leb 31%N rd) eqn:Erd31.
  - pose proof (Hwf r) as Hr; unfold a64_val_read in Hr; rewrite Er31 in Hr; exact Hr.
  - destruct (N.eqb r rd); [exact Hsv | pose proof (Hwf r) as Hr; unfold a64_val_read in Hr; rewrite Er31 in Hr; exact Hr].
Qed.

Lemma wf_a64_val_write_w : forall allowed vrf sf rd e,
  wf_a64_val_regs allowed vrf ->
  wf_sym_expr allowed (a64_w sf) e ->
  wf_a64_val_regs allowed (a64_val_write_w sf rd e vrf).
Proof.
  intros allowed vrf sf rd e Hwf He.
  apply wf_a64_val_write; [exact Hwf |].
  destruct sf; cbn [mc_sym_val_wf a64_w] in He |- *;
    [exact He | apply wf_sym_cast; [reflexivity | exact He]].
Qed.

Lemma wf_a64_val_read_expr_w : forall allowed vrf sf r e,
  wf_a64_val_regs allowed vrf ->
  a64_val_read_expr_w sf r vrf = Some e ->
  wf_sym_expr allowed (a64_w sf) e.
Proof.
  intros allowed vrf sf r e Hwf He; unfold a64_val_read_expr_w in He.
  destruct (a64_val_read r vrf) as [| e64 | |] eqn:Er; try discriminate He.
  inversion He; subst e; clear He.
  pose proof (Hwf r) as H64; rewrite Er in H64; cbn [mc_sym_val_wf] in H64.
  destruct sf; cbn [a64_w]; [exact H64 | exact (wf_a64_sym_trunc32 _ _ H64)].
Qed.

Lemma wf_a64_val_read_sp : forall allowed vrf sp_off r sv,
  (- mc_frame_cap <= sp_off <= 0)%Z ->
  wf_a64_val_regs allowed vrf ->
  a64_val_read_sp r vrf sp_off = sv ->
  mc_sym_val_wf allowed sv.
Proof.
  intros allowed vrf sp_off r sv Hrng Hwf Hsv.
  unfold a64_val_read_sp in Hsv; destruct (N.eqb r 31%N); subst sv;
    [cbn [mc_sym_val_wf]; exact Hrng | exact (Hwf r)].
Qed.

Lemma a64_val_write_sp_wf : forall allowed rd sv sp_off vrf astk sp_off' vrf' astk',
  (- mc_frame_cap <= sp_off <= 0)%Z ->
  mc_sym_val_wf allowed sv ->
  wf_a64_val_regs allowed vrf ->
  mc_sym_stack_wf allowed sp_off astk ->
  a64_val_write_sp rd sv sp_off vrf astk = Some (sp_off', vrf', astk') ->
  (- mc_frame_cap <= sp_off' <= 0)%Z /\
  wf_a64_val_regs allowed vrf' /\
  mc_sym_stack_wf allowed sp_off' astk'.
Proof.
  intros allowed rd sv sp_off vrf astk sp_off' vrf' astk' Hrng Hsv Hwf Hstk Hst.
  unfold a64_val_write_sp in Hst; destruct (N.eqb rd 31%N).
  - destruct sv as [| | | off']; try discriminate Hst.
    destruct (Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z) eqn:Eb; [| discriminate Hst].
    apply andb_true_iff in Eb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2.
    inversion Hst; subst; repeat split; [lia | lia | exact Hwf | eapply mc_sym_stk_prune_wf; [lia | exact Hstk]].
  - inversion Hst; subst; repeat split; [lia | lia | apply wf_a64_val_write; assumption | exact Hstk].
Qed.

Lemma a64_ldst_sym_load_wf : forall allowed is_signed sf_dst sv0 sv1,
  mc_sym_val_wf allowed sv0 ->
  a64_ldst_sym_load is_signed sf_dst sv0 = Some sv1 ->
  mc_sym_val_wf allowed sv1.
Proof.
  intros allowed is_signed sf_dst sv0 sv1 Hwf Hld.
  unfold a64_ldst_sym_load in Hld; destruct (is_signed && negb sf_dst).
  - destruct sv0 as [| e | |]; try discriminate Hld; inversion Hld; subst sv1.
    cbn [mc_sym_val_wf] in Hwf |- *; apply wf_sym_cast; [reflexivity | exact (wf_a64_sym_trunc32 _ _ Hwf)].
  - inversion Hld; subst sv1; exact Hwf.
Qed.

Lemma a64_ldst_writeback_wf : forall allowed sp_off vrf1 astk1 mode rn wb_off,
  (- mc_frame_cap <= sp_off <= 0)%Z ->
  (match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end) ->
  wf_a64_val_regs allowed vrf1 ->
  mc_sym_stack_wf allowed sp_off astk1 ->
  let '(sp_off2, vrf2, astk2) :=
    match mode with
    | AAM_SignedOffset => (sp_off, vrf1, astk1)
    | AAM_PreIndex | AAM_PostIndex =>
        if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
        else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
    end in
  (- mc_frame_cap <= sp_off2 <= 0)%Z /\
  wf_a64_val_regs allowed vrf2 /\
  mc_sym_stack_wf allowed sp_off2 astk2.
Proof.
  intros allowed sp_off vrf1 astk1 mode rn wb_off Hrng Hwb Hwf1 Hstk1.
  destruct mode; [repeat split; [lia | lia | exact Hwf1 | exact Hstk1] | |].
  - destruct (N.eqb rn 31%N); repeat split;
      try lia; try assumption;
      [eapply mc_sym_stk_prune_wf; [lia | exact Hstk1]
      | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb]].
  - destruct (N.eqb rn 31%N); repeat split;
      try lia; try assumption;
      [eapply mc_sym_stk_prune_wf; [lia | exact Hstk1]
      | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb]].
Qed.

Lemma wf_a64_sym_add_sub : forall allowed w is_sub l r,
  wf_sym_expr allowed w l ->
  wf_sym_expr allowed w r ->
  wf_sym_expr allowed w (fst (a64_sym_add_sub w is_sub l r)) /\
  wf_sym_flags allowed (snd (a64_sym_add_sub w is_sub l r)).
Proof.
  intros allowed w [|] l r Hl Hr; unfold a64_sym_add_sub; cbn [fst snd].
  - assert (Hres : wf_sym_expr allowed w (CE_BinOp CB_Sub w no_binop_flags l r)) by (apply a64_wf_sym_binop; assumption).
    assert (Hn : wf_sym_expr allowed 1%positive (a64_sym_is_neg w (CE_BinOp CB_Sub w no_binop_flags l r))) by (apply wf_sym_icmp; [exact Hres | apply wf_sym_bv_const]).
    assert (Hsl : wf_sym_expr allowed 1%positive (a64_sym_is_neg w l)) by (apply wf_sym_icmp; [exact Hl | apply wf_sym_bv_const]).
    assert (Hsr : wf_sym_expr allowed 1%positive (a64_sym_is_neg w r)) by (apply wf_sym_icmp; [exact Hr | apply wf_sym_bv_const]).
    assert (Hdif : wf_sym_expr allowed 1%positive (a64_sym_bool_xor (a64_sym_is_neg w l) (a64_sym_is_neg w (CE_BinOp CB_Sub w no_binop_flags l r))))
      by (unfold a64_sym_bool_xor; apply a64_wf_sym_binop; assumption).
    assert (Hz : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Eq false w l r)) by (apply wf_sym_icmp; assumption).
    assert (Hc : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Uge false w l r)) by (apply wf_sym_icmp; assumption).
    assert (Hxor : wf_sym_expr allowed 1%positive (a64_sym_bool_xor (a64_sym_is_neg w l) (a64_sym_is_neg w r)))
      by (unfold a64_sym_bool_xor; apply a64_wf_sym_binop; assumption).
    assert (Hv : wf_sym_expr allowed 1%positive (CE_BinOp CB_And 1%positive no_binop_flags (a64_sym_bool_xor (a64_sym_is_neg w l) (a64_sym_is_neg w r)) (a64_sym_bool_xor (a64_sym_is_neg w l) (a64_sym_is_neg w (CE_BinOp CB_Sub w no_binop_flags l r))))) by (apply a64_wf_sym_binop; assumption).
    assert (Hnx : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Slt false w l r)) by (apply wf_sym_icmp; assumption).
    split; [exact Hres | unfold wf_sym_flags; cbn [asf_n asf_z asf_c asf_v asf_n_ne_v]; split; [exact Hn | split; [exact Hz | split; [exact Hc | split; [exact Hv | exact Hnx]]]]].
  - assert (Hres : wf_sym_expr allowed w (CE_BinOp CB_Add w no_binop_flags l r)) by (apply a64_wf_sym_binop; assumption).
    assert (Hn : wf_sym_expr allowed 1%positive (a64_sym_is_neg w (CE_BinOp CB_Add w no_binop_flags l r))) by (apply wf_sym_icmp; [exact Hres | apply wf_sym_bv_const]).
    assert (Hsl : wf_sym_expr allowed 1%positive (a64_sym_is_neg w l)) by (apply wf_sym_icmp; [exact Hl | apply wf_sym_bv_const]).
    assert (Hsr : wf_sym_expr allowed 1%positive (a64_sym_is_neg w r)) by (apply wf_sym_icmp; [exact Hr | apply wf_sym_bv_const]).
    assert (Hdif : wf_sym_expr allowed 1%positive (a64_sym_bool_xor (a64_sym_is_neg w l) (a64_sym_is_neg w (CE_BinOp CB_Add w no_binop_flags l r))))
      by (unfold a64_sym_bool_xor; apply a64_wf_sym_binop; assumption).
    assert (Hz : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Eq false w (CE_BinOp CB_Add w no_binop_flags l r) (CE_BvConst w 0%N))) by (apply wf_sym_icmp; [exact Hres | apply wf_sym_bv_const]).
    assert (Hc : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Ult false w (CE_BinOp CB_Add w no_binop_flags l r) l)) by (apply wf_sym_icmp; [exact Hres | exact Hl]).
    assert (Heqlr : wf_sym_expr allowed 1%positive (a64_sym_bool_eq (a64_sym_is_neg w l) (a64_sym_is_neg w r)))
      by (unfold a64_sym_bool_eq; apply wf_sym_icmp; assumption).
    assert (Hv : wf_sym_expr allowed 1%positive (CE_BinOp CB_And 1%positive no_binop_flags (a64_sym_bool_eq (a64_sym_is_neg w l) (a64_sym_is_neg w r)) (a64_sym_bool_xor (a64_sym_is_neg w l) (a64_sym_is_neg w (CE_BinOp CB_Add w no_binop_flags l r))))) by (apply a64_wf_sym_binop; assumption).
    assert (Hnx : wf_sym_expr allowed 1%positive (a64_sym_bool_xor (a64_sym_is_neg w (CE_BinOp CB_Add w no_binop_flags l r)) (CE_BinOp CB_And 1%positive no_binop_flags (a64_sym_bool_eq (a64_sym_is_neg w l) (a64_sym_is_neg w r)) (a64_sym_bool_xor (a64_sym_is_neg w l) (a64_sym_is_neg w (CE_BinOp CB_Add w no_binop_flags l r))))))
      by (unfold a64_sym_bool_xor; apply a64_wf_sym_binop; assumption).
    split; [exact Hres | unfold wf_sym_flags; cbn [asf_n asf_z asf_c asf_v asf_n_ne_v]; split; [exact Hn | split; [exact Hz | split; [exact Hc | split; [exact Hv | exact Hnx]]]]].
Qed.

Lemma wf_a64_sym_logic_flags : forall allowed w res,
  wf_sym_expr allowed w res ->
  wf_sym_flags allowed (a64_sym_logic_flags w res).
Proof.
  intros allowed w res Hres; unfold a64_sym_logic_flags, wf_sym_flags; cbn [asf_n asf_z asf_c asf_v asf_n_ne_v].
  assert (Hn : wf_sym_expr allowed 1%positive (a64_sym_is_neg w res)) by (apply wf_sym_icmp; [exact Hres | apply wf_sym_bv_const]).
  assert (Hz : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Eq false w res (CE_BvConst w 0%N))) by (apply wf_sym_icmp; [exact Hres | apply wf_sym_bv_const]).
  assert (Hf0 : wf_sym_expr allowed 1%positive (CE_BvConst 1%positive 0%N)) by apply wf_sym_bv_const.
  split; [exact Hn | split; [exact Hz | split; [exact Hf0 | split; [exact Hf0 | exact Hn]]]].
Qed.

Lemma wf_a64_sym_cond : forall allowed c sfl,
  wf_sym_flags allowed sfl ->
  wf_sym_expr allowed 1%positive (a64_sym_cond c sfl).
Proof.
  intros allowed c sfl (Hn & Hz & Hc & Hv & Hnxv).
  destruct c; unfold a64_sym_cond;
    repeat (first [assumption | apply wf_sym_bv_const | apply a64_wf_sym_binop]).
Qed.

Lemma wf_a64_sym_ite_flags : forall allowed c st sf,
  wf_sym_expr allowed 1%positive c ->
  wf_sym_flags allowed st ->
  wf_sym_flags allowed sf ->
  wf_sym_flags allowed (a64_sym_ite_flags c st sf).
Proof.
  intros allowed c st sf Hc (Htn & Htz & Htc & Htv & Htnxv) (Hfn & Hfz & Hfc & Hfv & Hfnxv).
  unfold a64_sym_ite_flags, wf_sym_flags; cbn [asf_n asf_z asf_c asf_v asf_n_ne_v].
  split; [apply wf_sym_select; assumption
        | split; [apply wf_sym_select; assumption
        | split; [apply wf_sym_select; assumption
        | split; [apply wf_sym_select; assumption
        | apply wf_sym_select; assumption]]]].
Qed.

Lemma wf_a64_sym_shift : forall allowed w e sh amt,
  wf_sym_expr allowed w e ->
  wf_sym_expr allowed w (a64_sym_shift w e sh amt).
Proof.
  intros allowed w e sh amt He; unfold a64_sym_shift.
  destruct sh, (N.eqb (N.modulo amt (N.pos w)) 0%N); try exact He;
    repeat apply a64_wf_sym_binop; first [exact He | apply wf_sym_bv_const].
Qed.

Lemma wf_a64_sym_extend : forall allowed w e64 ext amt,
  (w = 32%positive \/ w = 64%positive) ->
  wf_sym_expr allowed 64%positive e64 ->
  wf_sym_expr allowed w (a64_sym_extend w e64 ext amt).
Proof.
  intros allowed w e64 ext amt Hw He64; unfold a64_sym_extend.
  destruct (a64_ext_bits ext) as [sb sgn]; set (eff := Pos.min sb w).
  set (sl := if Pos.eqb eff 64%positive then e64
             else if Pos.eqb eff 32%positive then a64_sym_trunc32 e64
             else CE_Cast CCK_Trunc 64%positive eff no_cast_flags e64).
  assert (Hsl : wf_sym_expr allowed eff sl).
  { unfold sl; destruct (Pos.eqb eff 64%positive) eqn:E64.
    - apply Pos.eqb_eq in E64; rewrite E64; exact He64.
    - destruct (Pos.eqb eff 32%positive) eqn:E32.
      + apply Pos.eqb_eq in E32; rewrite E32; exact (wf_a64_sym_trunc32 _ _ He64).
      + apply wf_sym_cast; [| exact He64].
        apply Pos.ltb_lt; apply Pos.eqb_neq in E64; unfold eff in *; destruct Hw as [-> | ->];
          [pose proof (Pos.le_min_r sb 32%positive) | pose proof (Pos.le_min_r sb 64%positive)]; lia. }
  assert (Hext : wf_sym_expr allowed w
    (if Pos.eqb eff w then sl else CE_Cast (if sgn then CCK_SExt else CCK_ZExt) eff w no_cast_flags sl)).
  { destruct (Pos.eqb eff w) eqn:Eew.
    - apply Pos.eqb_eq in Eew; rewrite <- Eew; exact Hsl.
    - assert (Hlt : (eff <? w)%positive = true)
        by (apply Pos.ltb_lt; apply Pos.eqb_neq in Eew; unfold eff in *; pose proof (Pos.le_min_r sb w); lia).
      destruct sgn; apply wf_sym_cast; assumption. }
  destruct (N.eqb amt 0%N); [exact Hext | apply a64_wf_sym_binop; [exact Hext | apply wf_sym_bv_const]].
Qed.

Lemma wf_a64_sym_flags_imm4 : forall allowed nzcv,
  wf_sym_flags allowed (a64_sym_flags_of_imm4 nzcv).
Proof.
  intros allowed nzcv; unfold a64_sym_flags_of_imm4, wf_sym_flags; cbn [asf_n asf_z asf_c asf_v asf_n_ne_v];
    split; [apply wf_sym_bv_const | split; [apply wf_sym_bv_const | split; [apply wf_sym_bv_const | split; [apply wf_sym_bv_const | apply wf_sym_bv_const]]]].
Qed.

Lemma wf_a64_sym_bitfield : forall allowed sf kind src dst immr imms,
  wf_sym_expr allowed (a64_w sf) src ->
  wf_sym_expr allowed (a64_w sf) dst ->
  wf_sym_expr allowed (a64_w sf) (a64_sym_bitfield (a64_w sf) kind src dst immr imms).
Proof.
  intros allowed sf kind src dst immr imms Hs Hd; unfold a64_sym_bitfield.
  destruct (N.leb immr imms).
  - assert (Hshr : wf_sym_expr allowed (a64_w sf)
      (if N.eqb immr 0%N then src else CE_BinOp CB_LShr (a64_w sf) no_binop_flags src (CE_BvConst (a64_w sf) immr)))
      by (destruct (N.eqb immr 0%N); [exact Hs | apply a64_wf_sym_binop; [exact Hs | apply wf_sym_bv_const]]).
    destruct kind.
    + destruct (Pos.eqb (a64_w sf) 64%positive && N.eqb immr 0%N && N.eqb imms 31%N) eqn:Esx.
      * rewrite !andb_true_iff in Esx; destruct Esx as ([Ew64 _] & _); apply Pos.eqb_eq in Ew64.
        rewrite Ew64 in Hs |- *; apply wf_sym_cast; [reflexivity | exact (wf_a64_sym_trunc32 _ _ Hs)].
      * destruct (N.eqb (N.pos (a64_w sf) - 1%N - imms) 0%N), (N.eqb (N.pos (a64_w sf) - (imms - immr + 1%N)) 0%N);
          repeat apply a64_wf_sym_binop; first [exact Hs | apply wf_sym_bv_const].
    + unfold a64_sym_not; apply a64_wf_sym_binop;
        [apply a64_wf_sym_binop; [exact Hd | apply a64_wf_sym_binop; apply wf_sym_bv_const]
        | apply a64_wf_sym_binop; [exact Hshr | apply wf_sym_bv_const]].
    + destruct (N.eqb (imms - immr + 1%N) (N.pos (a64_w sf))); [exact Hs |].
      destruct (N.eqb imms (N.pos (a64_w sf) - 1%N)); [exact Hshr |].
      destruct (Pos.eqb (a64_w sf) 64%positive && N.eqb immr 0%N && N.eqb imms 31%N) eqn:Eux.
      * rewrite !andb_true_iff in Eux; destruct Eux as ([Ew64 _] & _); apply Pos.eqb_eq in Ew64.
        rewrite Ew64 in Hs |- *; apply wf_sym_cast; [reflexivity | exact (wf_a64_sym_trunc32 _ _ Hs)].
      * apply a64_wf_sym_binop; [exact Hshr | apply wf_sym_bv_const].
  - destruct kind; unfold a64_sym_not.
    + apply a64_wf_sym_binop; [apply a64_wf_sym_binop; [apply a64_wf_sym_binop; [exact Hs | apply wf_sym_bv_const] | apply wf_sym_bv_const] | apply wf_sym_bv_const].
    + apply a64_wf_sym_binop;
        [apply a64_wf_sym_binop; [exact Hd | apply a64_wf_sym_binop; [apply a64_wf_sym_binop; apply wf_sym_bv_const | apply wf_sym_bv_const]]
        | apply a64_wf_sym_binop; [apply a64_wf_sym_binop; [exact Hs | apply wf_sym_bv_const] | apply wf_sym_bv_const]].
    + apply a64_wf_sym_binop; [apply a64_wf_sym_binop; [exact Hs | apply wf_sym_bv_const] | apply wf_sym_bv_const].
Qed.

Lemma wf_a64_sym_div_guarded : forall allowed is_signed w a b,
  wf_sym_expr allowed w a ->
  wf_sym_expr allowed w b ->
  wf_sym_expr allowed w (a64_sym_div_guarded is_signed w a b).
Proof.
  intros allowed is_signed w a b Ha Hb; unfold a64_sym_div_guarded.
  assert (Hz : wf_sym_expr allowed w (CE_BvConst w 0%N)) by apply wf_sym_bv_const.
  assert (H1 : wf_sym_expr allowed w (CE_BvConst w 1%N)) by apply wf_sym_bv_const.
  assert (Hiz : wf_sym_expr allowed 1%positive (CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N)))
    by (apply wf_sym_icmp; assumption).
  destruct is_signed; cbn [negb].
  - assert (Hovf : wf_sym_expr allowed 1%positive
      (CE_BinOp CB_And 1%positive no_binop_flags (CE_ICmp CIP_Eq false w a (ce_int_min w)) (CE_ICmp CIP_Eq false w b (ce_all_ones w))))
      by (apply a64_wf_sym_binop; apply wf_sym_icmp; try assumption; apply wf_sym_bv_const).
    assert (Hbad : wf_sym_expr allowed 1%positive
      (CE_BinOp CB_Or 1%positive no_binop_flags (CE_ICmp CIP_Eq false w b (CE_BvConst w 0%N))
        (CE_BinOp CB_And 1%positive no_binop_flags (CE_ICmp CIP_Eq false w a (ce_int_min w)) (CE_ICmp CIP_Eq false w b (ce_all_ones w)))))
      by (apply a64_wf_sym_binop; assumption).
    apply wf_sym_select; [exact Hiz | exact Hz |].
    apply wf_sym_select; [exact Hovf | apply wf_sym_bv_const |].
    apply a64_wf_sym_binop; [apply wf_sym_select; assumption | apply wf_sym_select; assumption].
  - apply wf_sym_select; [exact Hiz | exact Hz |].
    apply a64_wf_sym_binop; [exact Ha | apply wf_sym_select; assumption].
Qed.

Lemma wf_a64_sym_dp2 : forall allowed w op l r,
  wf_sym_expr allowed w l ->
  wf_sym_expr allowed w r ->
  wf_sym_expr allowed w (a64_sym_dp2 w op l r).
Proof.
  intros allowed w op l r Hl Hr; unfold a64_sym_dp2.
  assert (Hsh : wf_sym_expr allowed w (CE_BinOp CB_And w no_binop_flags r (CE_BvConst w (Z.to_N (Z.pos w - 1)))))
    by (apply a64_wf_sym_binop; [exact Hr | apply wf_sym_bv_const]).
  assert (Hinv : wf_sym_expr allowed w
    (CE_BinOp CB_And w no_binop_flags
      (CE_BinOp CB_Sub w no_binop_flags (CE_BvConst w (N.pos w))
        (CE_BinOp CB_And w no_binop_flags r (CE_BvConst w (Z.to_N (Z.pos w - 1)))))
      (CE_BvConst w (Z.to_N (Z.pos w - 1)))))
    by (apply a64_wf_sym_binop; [apply a64_wf_sym_binop; [apply wf_sym_bv_const | exact Hsh] | apply wf_sym_bv_const]).
  destruct op;
    [ exact (wf_a64_sym_div_guarded _ false _ _ _ Hl Hr)
    | exact (wf_a64_sym_div_guarded _ true _ _ _ Hl Hr)
    | apply a64_wf_sym_binop; assumption
    | apply a64_wf_sym_binop; assumption
    | apply a64_wf_sym_binop; assumption
    | apply a64_wf_sym_binop; apply a64_wf_sym_binop; assumption ].
Qed.

Lemma wf_a64_sym_csel : forall allowed w kind cond sfl t m,
  wf_sym_flags allowed sfl ->
  wf_sym_expr allowed w t ->
  wf_sym_expr allowed w m ->
  wf_sym_expr allowed w (a64_sym_csel w kind cond sfl t m).
Proof.
  intros allowed w kind cond sfl t m Hfl Ht Hm; unfold a64_sym_csel, a64_sym_not, a64_sym_neg.
  apply wf_sym_select; [exact (wf_a64_sym_cond _ cond _ Hfl) | exact Ht |].
  destruct kind; [exact Hm | apply a64_wf_sym_binop; [exact Hm | apply wf_sym_bv_const]
                 | apply a64_wf_sym_binop; [exact Hm | apply wf_sym_bv_const]
                 | apply a64_wf_sym_binop; [apply wf_sym_bv_const | exact Hm]].
Qed.

Lemma wf_cfg_branch : forall allowed c dt df,
  wf_sym_expr allowed 1%positive c ->
  wf_cfg_dag allowed dt = true ->
  wf_cfg_dag allowed df = true ->
  wf_cfg_dag allowed (CD_Branch c dt df) = true.
Proof.
  intros allowed c dt df (Ht & Hw & Hlf & Hv) Hdt Hdf.
  cbn [wf_cfg_dag]; rewrite Ht, Hw, Hlf, Hv, Hdt, Hdf; reflexivity.
Qed.

Lemma mc_sym_stack_wf_mono : forall allowed sp1 sp2 stk,
  (- mc_frame_cap <= sp1)%Z ->
  (sp1 <= sp2)%Z ->
  mc_sym_stack_wf allowed sp2 stk ->
  mc_sym_stack_wf allowed sp1 stk.
Proof.
  intros allowed sp1 sp2 stk Hcap Hle Hstk.
  unfold mc_sym_stack_wf in *; apply Forall_forall; intros [[o s] sv] Hin.
  rewrite Forall_forall in Hstk; destruct (Hstk (o, s, sv) Hin) as [Hsl Hwf].
  split; [eapply mc_slot_in_frame_mono; [exact Hle | exact Hcap | exact Hsl] | exact Hwf].
Qed.

Theorem summarize_a64_dag_at_wf :
  forall fuel insts im visited pc allowed sp_off vrf astk sfl fl_def ret_w d_mc,
    (forall q, pt_get (N.succ_pos q) im = lookup_a64_inst insts q) ->
    rv_supported_arg_width ret_w = true ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    wf_a64_val_regs allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (fl_def = true -> wf_sym_flags allowed sfl) ->
    summarize_a64_dag_at fuel im visited pc sp_off vrf astk sfl fl_def ret_w = inr d_mc ->
    wf_cfg_dag allowed d_mc = true.
Proof.
  intros fuel insts im visited pc allowed sp_off vrf astk sfl fl_def ret_w d_mc Him.
  revert visited pc allowed sp_off vrf astk sfl fl_def ret_w d_mc.
  induction fuel as [| fuel' IH];
    intros visited pc allowed sp_off vrf astk sfl fl_def ret_w d_mc Hrw Hrng Hwf Hstk Hfl Hsum;
    cbn [summarize_a64_dag_at] in Hsum.
  - destruct (pt_has_n pc visited); discriminate Hsum.
  - destruct (pt_has_n pc visited); [discriminate Hsum |].
    destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Elook; [| discriminate Hsum].
    rewrite Him in Elook.
    destruct (dai_inst dec) as
      [ | sf is_sub set_fl rd rn imm
        | sf is_sub set_fl rd rn rm sh amt
        | sf is_sub set_fl rd rn rm ext amt
        | sf op set_fl rd rn mask
        | sf op inv_rm set_fl rd rn rm sh amt
        | sf kind rd imm16 shift
        | sf kind rd rn immr imms
        | sf rd rn rm lsb
        | sf is_sub rd rn rm ra
        | sgn is_sub rd rn rm ra
        | sf op rd rn rm
        | sf kind cond rd rn rm
        | sf is_sub cond rn rm nzcv
        | sf is_sub cond rn imm5 nzcv
        | is_load is_signed sf_dst sz mode rt rn imm
        | is_load sf mode rt1 rt2 rn imm
        | rel
        | cond rel
        | sf is_nz rt rel
        | is_nz rt bit rel
        | ].
    + exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Hsum).
    + destruct (sf && negb set_fl) eqn:E64n.
      * set (sv_opt :=
          match a64_val_read_sp rn vrf sp_off with
          | MSV_StackPtr base_off =>
              let off' := if is_sub then (base_off - Z.of_N imm)%Z else (base_off + Z.of_N imm)%Z in
              if Z.leb (- mc_frame_cap) off' && Z.leb off' 0%Z then Some (MSV_StackPtr off') else None
          | MSV_SavedReg r0 => if N.eqb imm 0%N then Some (MSV_SavedReg r0) else None
          | MSV_Expr e => Some (MSV_Expr (fst (a64_sym_add_sub 64%positive is_sub e (ce_bv_z 64%positive (Z.of_N imm)))))
          | MSV_Undef => None
          end) in *.
        destruct sv_opt as [sv |] eqn:Esv; [| discriminate Hsum].
        destruct (a64_val_write_sp rd sv sp_off vrf astk) as [[[sp_off' vrf'] astk'] |] eqn:Est;
          [| discriminate Hsum].
        assert (Hsv_wf : mc_sym_val_wf allowed sv).
        { subst sv_opt; destruct (a64_val_read_sp rn vrf sp_off) as [| e | r0 | base_off] eqn:Ern; try discriminate Esv.
          - inversion Esv; subst sv; clear Esv.
            pose proof (wf_a64_val_read_sp _ _ _ _ _ Hrng Hwf Ern) as He.
            exact (proj1 (wf_a64_sym_add_sub allowed 64%positive is_sub e _ He (wf_sym_bv_z allowed 64%positive (Z.of_N imm)))).
          - destruct (N.eqb imm 0%N); [inversion Esv; exact I | discriminate Esv].
          - cbv zeta in Esv.
            destruct (Z.leb (- mc_frame_cap) _ && Z.leb _ 0%Z) eqn:Eb; [| discriminate Esv].
            apply andb_true_iff in Eb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2.
            inversion Esv; cbn [mc_sym_val_wf]; lia. }
        destruct (a64_val_write_sp_wf _ _ _ _ _ _ _ _ _ Hrng Hsv_wf Hwf Hstk Est) as (Hrng' & Hwf' & Hstk').
        exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng' Hwf' Hstk' Hfl Hsum).
      * destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hsum |].
        destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
        destruct (a64_sym_add_sub (a64_w sf) is_sub lhs (ce_bv_z (a64_w sf) (Z.of_N imm))) as [se sfl'] eqn:Esas.
        pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _ (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_sym_bv_z allowed (a64_w sf) (Z.of_N imm))) as [Hre Hfl'].
        rewrite Esas in Hre, Hfl'; cbn [fst snd] in Hre, Hfl'.
        eapply IH; [exact Hrw | exact Hrng | exact (wf_a64_val_write_w _ _ sf rd _ Hwf Hre) | exact Hstk | | exact Hsum].
        intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)].
    + destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hsum].
      destruct (a64_sym_add_sub (a64_w sf) is_sub _ _) as [se sfl'] eqn:Esas.
      pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _
                    (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern)
                    (wf_a64_sym_shift _ _ _ sh amt (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm))) as [Hre Hfl'].
      rewrite Esas in Hre, Hfl'; cbn [fst snd] in Hre, Hfl'.
      eapply IH; [exact Hrw | exact Hrng | exact (wf_a64_val_write_w _ _ sf rd _ Hwf Hre) | exact Hstk | | exact Hsum].
      intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)].
    + destruct (N.eqb rn 31%N || (negb set_fl && N.eqb rd 31%N)); [discriminate Hsum |].
      destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read rm vrf) as [| rm64 | |] eqn:Erm; try discriminate Hsum.
      pose proof (Hwf rm) as Hm64; rewrite Erm in Hm64; cbn [mc_sym_val_wf] in Hm64.
      destruct (a64_sym_add_sub (a64_w sf) is_sub _ _) as [se sfl'] eqn:Esas.
      pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _
                    (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern)
                    (wf_a64_sym_extend _ _ _ ext amt (a64_w_32_64 sf) Hm64)) as [Hre Hfl'].
      rewrite Esas in Hre, Hfl'; cbn [fst snd] in Hre, Hfl'.
      eapply IH; [exact Hrw | exact Hrng | exact (wf_a64_val_write_w _ _ sf rd _ Hwf Hre) | exact Hstk | | exact Hsum].
      intro Hs; destruct set_fl; [exact Hfl' | exact (Hfl Hs)].
    + destruct (negb set_fl && N.eqb rd 31%N); [discriminate Hsum |].
      destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
      assert (Hre : wf_sym_expr allowed (a64_w sf) (a64_sym_logic_op (a64_w sf) op lhs (ce_bv_z (a64_w sf) (Z.of_N mask))))
        by (unfold a64_sym_logic_op; apply a64_wf_sym_binop; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) | apply wf_sym_bv_z]).
      eapply IH; [exact Hrw | exact Hrng | exact (wf_a64_val_write_w _ _ sf rd _ Hwf Hre) | exact Hstk | | exact Hsum].
      intro Hs; destruct set_fl; [exact (wf_a64_sym_logic_flags _ _ _ Hre) | exact (Hfl Hs)].
    + destruct (a64_is_orr_mov64 sf op inv_rm set_fl rn sh amt).
      * destruct (a64_val_read rm vrf) eqn:Erm; try discriminate Hsum;
          (eapply IH; [exact Hrw | exact Hrng | apply wf_a64_val_write; [exact Hwf | pose proof (Hwf rm) as Hm0; rewrite Erm in Hm0; exact Hm0] | exact Hstk | exact Hfl | exact Hsum]).
      * destruct (a64_val_read_expr_w sf rn vrf) as [lhs |] eqn:Ern; [| discriminate Hsum].
        destruct (a64_val_read_expr_w sf rm vrf) as [rm_e |] eqn:Erm; [| discriminate Hsum].
        assert (Hrhs : wf_sym_expr allowed (a64_w sf)
          (if inv_rm then a64_sym_not (a64_w sf) (a64_sym_shift (a64_w sf) rm_e sh amt)
           else a64_sym_shift (a64_w sf) rm_e sh amt)).
        { pose proof (wf_a64_sym_shift allowed (a64_w sf) _ sh amt (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)) as Hsh.
          destruct inv_rm; [apply a64_wf_sym_binop; [exact Hsh | apply wf_sym_bv_const] | exact Hsh]. }
        assert (Hre : wf_sym_expr allowed (a64_w sf) (a64_sym_logic_op (a64_w sf) op lhs _))
          by (unfold a64_sym_logic_op; apply a64_wf_sym_binop; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) | exact Hrhs]).
        eapply IH; [exact Hrw | exact Hrng | exact (wf_a64_val_write_w _ _ sf rd _ Hwf Hre) | exact Hstk | | exact Hsum].
        intro Hs; destruct set_fl; [exact (wf_a64_sym_logic_flags _ _ _ Hre) | exact (Hfl Hs)].
    + destruct kind.
      * eapply IH; [exact Hrw | exact Hrng | apply wf_a64_val_write_w; [exact Hwf | apply a64_wf_sym_binop; apply wf_sym_bv_const] | exact Hstk | exact Hfl | exact Hsum].
      * eapply IH; [exact Hrw | exact Hrng | apply wf_a64_val_write_w; [exact Hwf | apply wf_sym_bv_const] | exact Hstk | exact Hfl | exact Hsum].
      * destruct (a64_val_read_expr_w sf rd vrf) as [cur |] eqn:Erd; [| discriminate Hsum].
        eapply IH; [exact Hrw | exact Hrng | apply wf_a64_val_write_w; [exact Hwf | apply a64_wf_sym_binop; [apply a64_wf_sym_binop; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erd) | unfold a64_sym_not; apply a64_wf_sym_binop; apply wf_sym_bv_const] | apply wf_sym_bv_const]] | exact Hstk | exact Hfl | exact Hsum].
    + destruct (a64_val_read_expr_w sf rn vrf) as [src_e |] eqn:Ern; [| discriminate Hsum].
      set (dst_opt := match kind with ABF_Bfm => a64_val_read_expr_w sf rd vrf | _ => Some (CE_BvConst (a64_w sf) 0%N) end) in *.
      destruct dst_opt as [dst_e |] eqn:Edst; [| discriminate Hsum].
      assert (Hd_wf : wf_sym_expr allowed (a64_w sf) dst_e).
      { destruct kind; subst dst_opt;
          [inversion Edst; apply wf_sym_bv_const
          | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Edst)
          | inversion Edst; apply wf_sym_bv_const]. }
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng
                (wf_a64_val_write_w _ _ sf rd _ Hwf
                   (wf_a64_sym_bitfield allowed sf kind src_e dst_e immr imms
                      (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) Hd_wf))
                Hstk Hfl Hsum).
    + destruct (a64_val_read_expr_w sf rn vrf) as [hi_e |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [lo_e |] eqn:Erm; [| discriminate Hsum].
      assert (Hex : wf_sym_expr allowed (a64_w sf) (a64_sym_extr (a64_w sf) hi_e lo_e lsb)).
      { unfold a64_sym_extr; destruct (N.eqb (N.modulo lsb (N.pos (a64_w sf))) 0%N);
          [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)
          | apply a64_wf_sym_binop; apply a64_wf_sym_binop; first [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm) | apply wf_sym_bv_const]]. }
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng (wf_a64_val_write_w _ _ sf rd _ Hwf Hex) Hstk Hfl Hsum).
    + destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf ra vrf) as [ea |] eqn:Era; [| discriminate Hsum].
      eapply IH; [exact Hrw | exact Hrng | apply wf_a64_val_write_w; [exact Hwf | apply a64_wf_sym_binop; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Era) | apply a64_wf_sym_binop; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)]]] | exact Hstk | exact Hfl | exact Hsum].
    + destruct (a64_val_read_expr_w false rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w false rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      destruct (a64_val_read ra vrf) as [| ea | |] eqn:Era; try discriminate Hsum.
      pose proof (Hwf ra) as Ha; rewrite Era in Ha; cbn [mc_sym_val_wf] in Ha.
      assert (Hre : wf_sym_expr allowed 64%positive
        (CE_BinOp (if is_sub then CB_Sub else CB_Add) 64%positive no_binop_flags ea
          (CE_BinOp CB_Mul 64%positive no_binop_flags
            (CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags en)
            (CE_Cast (if sgn then CCK_SExt else CCK_ZExt) 32%positive 64%positive no_cast_flags em)))).
      { apply a64_wf_sym_binop; [exact Ha | apply a64_wf_sym_binop; destruct sgn; apply wf_sym_cast; try reflexivity; first [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) | exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)]]. }
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng (wf_a64_val_write _ _ rd (MSV_Expr _) Hwf Hre) Hstk Hfl Hsum).
    + destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng
                (wf_a64_val_write_w _ _ sf rd _ Hwf (wf_a64_sym_dp2 _ _ op _ _ (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)))
                Hstk Hfl Hsum).
    + destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng
                (wf_a64_val_write_w _ _ sf rd _ Hwf (wf_a64_sym_csel _ _ kind cond sfl _ _ (Hfl eq_refl) (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)))
                Hstk Hfl Hsum).
    + destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rm vrf) as [em |] eqn:Erm; [| discriminate Hsum].
      destruct (a64_sym_add_sub (a64_w sf) is_sub en em) as [se csfl] eqn:Esas.
      pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _ (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Erm)) as [_ Hcsfl].
      rewrite Esas in Hcsfl; cbn [snd] in Hcsfl.
      pose proof (wf_a64_sym_ite_flags allowed (a64_sym_cond cond sfl) csfl (a64_sym_flags_of_imm4 nzcv)
                    (wf_a64_sym_cond _ cond _ (Hfl eq_refl)) Hcsfl (wf_a64_sym_flags_imm4 allowed nzcv)) as Hfl'.
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk (fun _ => Hfl') Hsum).
    + destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (a64_val_read_expr_w sf rn vrf) as [en |] eqn:Ern; [| discriminate Hsum].
      destruct (a64_sym_add_sub (a64_w sf) is_sub en (ce_bv_z (a64_w sf) (Z.of_N imm5))) as [se csfl] eqn:Esas.
      pose proof (wf_a64_sym_add_sub allowed (a64_w sf) is_sub _ _ (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ern) (wf_sym_bv_z allowed (a64_w sf) (Z.of_N imm5))) as [_ Hcsfl].
      rewrite Esas in Hcsfl; cbn [snd] in Hcsfl.
      pose proof (wf_a64_sym_ite_flags allowed (a64_sym_cond cond sfl) csfl (a64_sym_flags_of_imm4 nzcv)
                    (wf_a64_sym_cond _ cond _ (Hfl eq_refl)) Hcsfl (wf_a64_sym_flags_imm4 allowed nzcv)) as Hfl'.
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk (fun _ => Hfl') Hsum).
    + (* A64_LdStImm *)
      destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hsum |].
      destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off]; try discriminate Hsum.
      set (wb_off := (base_off + imm)%Z) in *.
      set (wb_ok := match mode with AAM_SignedOffset => true | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z end) in *.
      destruct wb_ok eqn:Ewb; cbn [negb] in Hsum; [| discriminate Hsum].
      assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end).
      { destruct mode; [exact I | |]; apply andb_true_iff in Ewb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; lia. }
      set (pair_off := match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end).
      destruct pair_off as [off sp_chk] eqn:Epo.
      cbv zeta in Hsum.
      assert (Hpo_eq : match mode with
                       | AAM_SignedOffset => (wb_off, sp_off)
                       | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
                       | AAM_PostIndex => (base_off, sp_off)
                       end = (off, sp_chk)) by exact Epo.
      rewrite Hpo_eq in Hsum; cbv iota in Hsum.
      destruct (mc_slot_in_frame sp_chk off sz) eqn:Eslot; [| discriminate Hsum].
      pose proof (mc_slot_in_frame_bounds _ _ _ Eslot) as (Hchk_cap & _).
      set (sp_min := Z.min sp_off sp_chk).
      assert (Hstk_min : mc_sym_stack_wf allowed sp_min astk)
        by (eapply mc_sym_stack_wf_mono with (sp2 := sp_off); [unfold sp_min; lia | unfold sp_min; lia | exact Hstk]).
      assert (Hslot_min : mc_slot_in_frame sp_min off sz = true)
        by (eapply mc_slot_in_frame_mono with (sp2 := sp_chk); [unfold sp_min; lia | unfold sp_min; lia | exact Eslot]).
      set (st_opt :=
        if is_load then
          match mc_sym_stk_load off sz is_signed astk with
          | None => None
          | Some sv0 =>
              match a64_ldst_sym_load is_signed sf_dst sv0 with
              | None => None
              | Some sv1 => Some (a64_val_write rt sv1 vrf, astk)
              end
          end
        else
          if a64_ldst_store_sym_ok sz (a64_val_read rt vrf) then Some (vrf, mc_sym_stk_store off sz (a64_val_read rt vrf) astk) else None) in *.
      destruct st_opt as [[vrf1 astk1] |] eqn:Est;
        [try (rewrite Est in Hsum; cbv iota in Hsum) | try rewrite Est in Hsum; discriminate Hsum].
      assert (Hstep1 : wf_a64_val_regs allowed vrf1 /\ mc_sym_stack_wf allowed sp_min astk1).
      { destruct is_load; unfold st_opt in Est.
        - destruct (mc_sym_stk_load off sz is_signed astk) as [sv0 |] eqn:Esl0; [| discriminate Est].
          destruct (a64_ldst_sym_load is_signed sf_dst sv0) as [sv1 |] eqn:Esl1; [| discriminate Est].
          inversion Est; subst vrf1 astk1; clear Est.
          pose proof (mc_sym_stk_load_wf _ _ _ _ _ _ _ Hstk Esl0) as Hsv0.
          pose proof (a64_ldst_sym_load_wf _ _ _ _ _ Hsv0 Esl1) as Hsv1.
          split; [apply wf_a64_val_write; assumption | exact Hstk_min].
        - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt vrf)); [| discriminate Est].
          inversion Est; subst vrf1 astk1; clear Est.
          split; [exact Hwf | exact (mc_sym_stk_store_wf _ _ _ _ _ _ Hslot_min (Hwf rt) Hstk_min)]. }
      destruct Hstep1 as [Hwf1 Hstk1].
      assert (Hwb2 :
        let '(sp_off2, vrf2, astk2) :=
          match mode with
          | AAM_SignedOffset => (sp_off, vrf1, astk1)
          | AAM_PreIndex | AAM_PostIndex =>
              if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
              else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
          end in
        (- mc_frame_cap <= sp_off2 <= 0)%Z /\ wf_a64_val_regs allowed vrf2 /\ mc_sym_stack_wf allowed sp_off2 astk2).
      { destruct mode; inversion Epo; subst off sp_chk.
        - assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1.
          repeat split; [lia | lia | exact Hwf1 | exact Hstk1].
        - destruct (N.eqb rn 31%N);
            [repeat split; [lia | lia | exact Hwf1 | eapply mc_sym_stk_prune_wf; [lia | exact Hstk1]]
            | assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1;
              repeat split; [lia | lia | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb_rng] | exact Hstk1]].
        - destruct (N.eqb rn 31%N);
            [repeat split; [lia | lia | exact Hwf1 | eapply mc_sym_stk_prune_wf; [lia | exact Hstk1]]
            | assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1;
              repeat split; [lia | lia | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb_rng] | exact Hstk1]]. }
      destruct (match mode with AAM_SignedOffset => (sp_off, vrf1, astk1) | _ => if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1) else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1) end)
        as [[sp_off2 vrf2] astk2] eqn:Ewbs.
      try rewrite Ewbs in Hwb2; cbv iota in Hwb2.
      try (rewrite Ewbs in Hsum; cbv iota in Hsum).
      destruct Hwb2 as (Hrng2 & Hwf2 & Hstk2).
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng2 Hwf2 Hstk2 Hfl Hsum).
    + (* A64_LdStPair *)
      destruct (if N.eqb rn 31%N then negb (mc_sp_aligned16 sp_off) else false); [discriminate Hsum |].
      destruct (a64_val_read_sp rn vrf sp_off) as [| | | base_off]; try discriminate Hsum.
      set (wb_off := (base_off + imm)%Z) in *.
      set (wb_ok := match mode with AAM_SignedOffset => true | _ => Z.leb (- mc_frame_cap) wb_off && Z.leb wb_off 0%Z end) in *.
      destruct wb_ok eqn:Ewb; cbn [negb] in Hsum; [| discriminate Hsum].
      assert (Hwb_rng : match mode with AAM_SignedOffset => True | _ => (- mc_frame_cap <= wb_off <= 0)%Z end).
      { destruct mode; [exact I | |]; apply andb_true_iff in Ewb as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2; lia. }
      set (pair_off := match mode with AAM_SignedOffset => (wb_off, sp_off) | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off) | AAM_PostIndex => (base_off, sp_off) end).
      destruct pair_off as [off sp_chk] eqn:Epo.
      cbv zeta in Hsum.
      assert (Hpo_eq : match mode with
                       | AAM_SignedOffset => (wb_off, sp_off)
                       | AAM_PreIndex => (wb_off, if N.eqb rn 31%N then wb_off else sp_off)
                       | AAM_PostIndex => (base_off, sp_off)
                       end = (off, sp_chk)) by exact Epo.
      rewrite Hpo_eq in Hsum; cbv iota in Hsum.
      set (sz := if sf then MS_8 else MS_4) in *; set (delta := mc_mem_bytes_Z sz) in *.
      destruct (mc_slot_in_frame sp_chk off sz && mc_slot_in_frame sp_chk (off + delta) sz) eqn:Eslots; [| discriminate Hsum].
      apply andb_true_iff in Eslots as [Esl1 Esl2].
      pose proof (mc_slot_in_frame_bounds _ _ _ Esl1) as (Hchk_cap & _).
      set (sp_min := Z.min sp_off sp_chk).
      assert (Hstk_min : mc_sym_stack_wf allowed sp_min astk)
        by (eapply mc_sym_stack_wf_mono with (sp2 := sp_off); [unfold sp_min; lia | unfold sp_min; lia | exact Hstk]).
      assert (Hslot1_min : mc_slot_in_frame sp_min off sz = true)
        by (eapply mc_slot_in_frame_mono with (sp2 := sp_chk); [unfold sp_min; lia | unfold sp_min; lia | exact Esl1]).
      assert (Hslot2_min : mc_slot_in_frame sp_min (off + delta) sz = true)
        by (eapply mc_slot_in_frame_mono with (sp2 := sp_chk); [unfold sp_min; lia | unfold sp_min; lia | exact Esl2]).
      set (st_opt :=
        if is_load then
          match mc_sym_stk_load off sz false astk, mc_sym_stk_load (off + delta) sz false astk with
          | Some sv1, Some sv2 => Some (a64_val_write rt2 sv2 (a64_val_write rt1 sv1 vrf), astk)
          | _, _ => None
          end
        else
          if a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) && a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf) then
            Some (vrf, mc_sym_stk_store (off + delta) sz (a64_val_read rt2 vrf) (mc_sym_stk_store off sz (a64_val_read rt1 vrf) astk))
          else None) in *.
      destruct st_opt as [[vrf1 astk1] |] eqn:Est;
        [try (rewrite Est in Hsum; cbv iota in Hsum) | try rewrite Est in Hsum; discriminate Hsum].
      assert (Hstep1 : wf_a64_val_regs allowed vrf1 /\ mc_sym_stack_wf allowed sp_min astk1).
      { destruct is_load; unfold st_opt in Est.
        - destruct (mc_sym_stk_load off sz false astk) as [sv1 |] eqn:Esl_1; [| discriminate Est].
          destruct (mc_sym_stk_load (off + delta) sz false astk) as [sv2 |] eqn:Esl_2; [| discriminate Est].
          inversion Est; subst vrf1 astk1; clear Est.
          pose proof (mc_sym_stk_load_wf _ _ _ _ _ _ _ Hstk Esl_1) as Hsv1.
          pose proof (mc_sym_stk_load_wf _ _ _ _ _ _ _ Hstk Esl_2) as Hsv2.
          split; [apply wf_a64_val_write; [apply wf_a64_val_write; assumption | exact Hsv2] | exact Hstk_min].
        - destruct (a64_ldst_store_sym_ok sz (a64_val_read rt1 vrf) && a64_ldst_store_sym_ok sz (a64_val_read rt2 vrf));
            [| discriminate Est].
          inversion Est; subst vrf1 astk1; clear Est.
          split; [exact Hwf |].
          apply mc_sym_stk_store_wf; [exact Hslot2_min | exact (Hwf rt2) |].
          apply mc_sym_stk_store_wf; [exact Hslot1_min | exact (Hwf rt1) | exact Hstk_min]. }
      destruct Hstep1 as [Hwf1 Hstk1].
      assert (Hwb2 :
        let '(sp_off2, vrf2, astk2) :=
          match mode with
          | AAM_SignedOffset => (sp_off, vrf1, astk1)
          | AAM_PreIndex | AAM_PostIndex =>
              if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1)
              else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1)
          end in
        (- mc_frame_cap <= sp_off2 <= 0)%Z /\ wf_a64_val_regs allowed vrf2 /\ mc_sym_stack_wf allowed sp_off2 astk2).
      { destruct mode; inversion Epo; subst off sp_chk.
        - assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1.
          repeat split; [lia | lia | exact Hwf1 | exact Hstk1].
        - destruct (N.eqb rn 31%N);
            [repeat split; [lia | lia | exact Hwf1 | eapply mc_sym_stk_prune_wf; [lia | exact Hstk1]]
            | assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1;
              repeat split; [lia | lia | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb_rng] | exact Hstk1]].
        - destruct (N.eqb rn 31%N);
            [repeat split; [lia | lia | exact Hwf1 | eapply mc_sym_stk_prune_wf; [lia | exact Hstk1]]
            | assert (Hmin_eq : sp_min = sp_off) by (unfold sp_min; lia); rewrite Hmin_eq in Hstk1;
              repeat split; [lia | lia | apply wf_a64_val_write; [exact Hwf1 | cbn [mc_sym_val_wf]; exact Hwb_rng] | exact Hstk1]]. }
      destruct (match mode with AAM_SignedOffset => (sp_off, vrf1, astk1) | _ => if N.eqb rn 31%N then (wb_off, vrf1, mc_sym_stk_prune wb_off astk1) else (sp_off, a64_val_write rn (MSV_StackPtr wb_off) vrf1, astk1) end)
        as [[sp_off2 vrf2] astk2] eqn:Ewbs.
      try rewrite Ewbs in Hwb2; cbv iota in Hwb2.
      try (rewrite Ewbs in Hsum; cbv iota in Hsum).
      destruct Hwb2 as (Hrng2 & Hwf2 & Hstk2).
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng2 Hwf2 Hstk2 Hfl Hsum).
    + destruct (add_rel_off pc rel); [| discriminate Hsum].
      exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Hsum).
    + destruct fl_def eqn:Efld; cbn [negb] in Hsum; [| discriminate Hsum].
      destruct (add_rel_off pc rel) as [tgt_pc |]; [| discriminate Hsum].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk sfl true ret_w) as [| dt] eqn:Edt;
        [discriminate Hsum |].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) (pc + 4%N)%N sp_off vrf astk sfl true ret_w) as [| df] eqn:Edf;
        [discriminate Hsum |].
      inversion Hsum; subst d_mc; clear Hsum.
      exact (wf_cfg_branch allowed _ _ _ (wf_a64_sym_cond allowed cond sfl (Hfl eq_refl))
               (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Edt) (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Edf)).
    + destruct (a64_val_read_expr_w sf rt vrf) as [rt_e |] eqn:Ert; [| discriminate Hsum].
      destruct (add_rel_off pc rel) as [tgt_pc |]; [| discriminate Hsum].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk sfl fl_def ret_w) as [| dt] eqn:Edt;
        [discriminate Hsum |].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) (pc + 4%N)%N sp_off vrf astk sfl fl_def ret_w) as [| df] eqn:Edf;
        [discriminate Hsum |].
      inversion Hsum; subst d_mc; clear Hsum.
      apply wf_cfg_branch;
        [apply wf_sym_icmp; [exact (wf_a64_val_read_expr_w _ _ _ _ _ Hwf Ert) | apply wf_sym_bv_const]
        | exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Edt)
        | exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Edf)].
    + destruct (a64_val_read rt vrf) as [| rt_e | |] eqn:Ert; try discriminate Hsum.
      destruct (add_rel_off pc rel) as [tgt_pc |]; [| discriminate Hsum].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) tgt_pc sp_off vrf astk sfl fl_def ret_w) as [| dt] eqn:Edt;
        [discriminate Hsum |].
      destruct (summarize_a64_dag_at fuel' im (pt_add_n pc visited) (pc + 4%N)%N sp_off vrf astk sfl fl_def ret_w) as [| df] eqn:Edf;
        [discriminate Hsum |].
      inversion Hsum; subst d_mc; clear Hsum.
      pose proof (Hwf rt) as Hrt; rewrite Ert in Hrt; cbn [mc_sym_val_wf] in Hrt.
      assert (Hmsk : wf_sym_expr allowed 64%positive (CE_BinOp CB_And 64%positive no_binop_flags rt_e (CE_BvConst 64%positive (N.shiftl 1%N bit))))
        by (apply a64_wf_sym_binop; [exact Hrt | apply wf_sym_bv_const]).
      apply wf_cfg_branch;
        [apply wf_sym_icmp; [exact Hmsk | apply wf_sym_bv_const]
        | exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Edt)
        | exact (IH _ _ _ _ _ _ _ _ _ _ Hrw Hrng Hwf Hstk Hfl Edf)].
    + destruct (a64_sym_epilogue_ok sp_off vrf); [| discriminate Hsum].
      destruct (a64_val_read 0%N vrf) as [| e_ret | |] eqn:Er0; try discriminate Hsum.
      inversion Hsum; subst d_mc; clear Hsum.
      pose proof (Hwf 0%N) as Ha0; rewrite Er0 in Ha0; cbn [mc_sym_val_wf] in Ha0.
      assert (Hrte : wf_sym_expr allowed ret_w (rv_trunc_ret_expr ret_w e_ret)).
      { unfold rv_trunc_ret_expr; destruct (Pos.eqb ret_w 64%positive) eqn:Ew64.
        - apply Pos.eqb_eq in Ew64; subst ret_w; exact Ha0.
        - apply wf_sym_cast; [exact (rv_supported_arg_width_lt64 _ Hrw Ew64) | exact Ha0]. }
      destruct Hrte as (Hte & Hwe & Hlfe & Hve).
      cbn [wf_cfg_dag]; rewrite Hte, Hwe, Hlfe, Hve, Pos.eqb_refl; reflexivity.
Qed.

(** *** 5.3 AAPCS64 Upper-Bits Extension Environment & Top-Level [A64] Theorems *)

Definition a64_rf_matches_args {Pa : Params}
  (penv : param_env Pa) (specs : list rv_arg_spec) (rf : a64_regfile) : Prop :=
  forall (k : nat) sp,
    (k < List.length specs)%nat ->
    nth_error specs k = Some sp ->
    exists v : @Integers.bit_int (ras_width sp),
      penv (ras_name sp) = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
      match Pos.eqb (ras_width sp) 64%positive, ras_ext sp with
      | true, RAE_None =>
          a64_read_reg (N.of_nat k) rf = @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
      | false, RAE_None =>
          @Integers.repr (ras_width sp) (@Integers.unsigned 64%positive (a64_read_reg (N.of_nat k) rf)) = v
      | false, RAE_SignExt =>
          @Integers.repr 32%positive (@Integers.unsigned 64%positive (a64_read_reg (N.of_nat k) rf)) =
          @Integers.repr 32%positive (@Integers.signed (ras_width sp) v)
      | false, RAE_ZeroExt =>
          @Integers.repr 32%positive (@Integers.unsigned 64%positive (a64_read_reg (N.of_nat k) rf)) =
          @Integers.repr 32%positive (@Integers.unsigned (ras_width sp) v)
      | _, _ => False
      end.

Fixpoint a64_extend_penv_with_hi_at {Pa : Params}
  (idx : nat) (specs : list rv_arg_spec) (rf : a64_regfile) (penv : param_env Pa)
  : param_env Pa :=
  match specs with
  | [] => penv
  | sp :: rest =>
      let penv' := a64_extend_penv_with_hi_at (S idx) rest rf penv in
      if Pos.eqb (ras_width sp) 64%positive then penv'
      else
        let hnm := a64_hi_var_name (ras_name sp) in
        let rk := a64_read_reg (N.of_nat idx) rf in
        fun x =>
          if String.eqb x hnm then Some (DVALUE_Base (@DVALUE_I Pa 64%positive rk))
          else penv' x
  end.

Definition a64_extend_penv_with_hi {Pa : Params}
  (penv : param_env Pa) (specs : list rv_arg_spec) (rf : a64_regfile)
  : param_env Pa :=
  a64_extend_penv_with_hi_at 0%nat specs rf penv.

Lemma a64_hi_var_name_inj : forall s1 s2,
  a64_hi_var_name s1 = a64_hi_var_name s2 -> s1 = s2.
Proof.
  intros s1 s2 H; unfold a64_hi_var_name in H.
  do 9 (inversion H as [H']; clear H; rename H' into H).
  exact H.
Qed.

Lemma a64_extend_penv_at_orig :
  forall {Pa : Params} idx specs rf (penv : param_env Pa) nm,
    (forall sp, In sp specs -> a64_hi_var_name (ras_name sp) <> nm) ->
    a64_extend_penv_with_hi_at idx specs rf penv nm = penv nm.
Proof.
  intros Pa idx specs rf penv nm Hdis; revert idx; induction specs as [| sp rest IH]; intro idx; cbn; [reflexivity |].
  assert (Hrest : forall s, In s rest -> a64_hi_var_name (ras_name s) <> nm)
    by (intros s Hs; apply Hdis; right; exact Hs).
  destruct (Pos.eqb (ras_width sp) 64%positive); [exact (IH Hrest (S idx)) |].
  destruct (String.eqb nm (a64_hi_var_name (ras_name sp))) eqn:Eeq.
  - apply String.eqb_eq in Eeq; exfalso; eapply Hdis; [left; reflexivity | symmetry; exact Eeq].
  - exact (IH Hrest (S idx)).
Qed.

Lemma a64_extend_penv_at_hi :
  forall {Pa : Params} idx k specs sp rf (penv : param_env Pa),
    NoDup (List.map ras_name specs) ->
    nth_error specs k = Some sp ->
    (ras_width sp =? 64)%positive = false ->
    a64_extend_penv_with_hi_at idx specs rf penv (a64_hi_var_name (ras_name sp)) =
    Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (N.of_nat (idx + k)) rf))).
Proof.
  intros Pa idx k specs sp rf penv; revert idx k;
    induction specs as [| s0 rest IH]; intros idx k Hnd Hnth Hw64; cbn [nth_error] in Hnth.
  - destruct k; discriminate Hnth.
  - cbn [List.map] in Hnd; inversion Hnd as [| ? ? Hnin Hnd_rest]; subst.
    destruct k as [| k']; cbn [a64_extend_penv_with_hi_at].
    + inversion Hnth; subst s0; clear Hnth.
      rewrite Hw64, String.eqb_refl, Nat.add_0_r; reflexivity.
    + destruct (Pos.eqb (ras_width s0) 64%positive).
      * replace (idx + S k')%nat with (S idx + k')%nat by lia; exact (IH _ _ Hnd_rest Hnth Hw64).
      * destruct (String.eqb (a64_hi_var_name (ras_name sp)) (a64_hi_var_name (ras_name s0))) eqn:Eeq.
        -- apply String.eqb_eq, a64_hi_var_name_inj in Eeq.
           exfalso; apply Hnin; rewrite <- Eeq; apply in_map_iff; exists sp; split; [reflexivity | exact (nth_error_In rest k' Hnth)].
        -- replace (idx + S k')%nat with (S idx + k')%nat by lia; exact (IH _ _ Hnd_rest Hnth Hw64).
Qed.

Lemma or_low_hi_mask_eq :
  forall (k : positive) (rk : @Integers.bit_int 64%positive) (vlo : @Integers.bit_int k) (hi_mask : N),
    (k < 64)%positive ->
    hi_mask = (N.shiftl 1%N 64%N - N.shiftl 1%N (N.pos k))%N ->
    vlo = @Integers.repr k (@Integers.unsigned 64%positive rk) ->
    @Integers.or 64%positive
      (@Integers.repr 64%positive (@Integers.unsigned k vlo))
      (@Integers.and 64%positive rk (@Integers.repr 64%positive (Z.of_N hi_mask))) = rk.
Proof.
  intros k rk vlo hi_mask Hlt Hhm Hvlo.
  apply Integers.same_bits_eq; intros i Hi.
  assert (Hi64 : (0 <= i < 64)%Z) by (replace 64%Z with (@Integers.zwordsize 64%positive) by reflexivity; exact Hi).
  rewrite Integers.bits_or, Integers.bits_and, !(@Integers.testbit_repr 64%positive _ i Hi) by exact Hi.
  assert (Hhm_eq : Z.of_N hi_mask = (2 ^ 64 - 2 ^ Z.pos k)%Z).
  { rewrite Hhm, N2Z.inj_sub by (rewrite !N.shiftl_1_l; apply N.pow_le_mono_r; lia).
    rewrite !N.shiftl_1_l, !N2Z.inj_pow; reflexivity. }
  assert (Hhm_bits : Z.testbit (Z.of_N hi_mask) i = Z.leb (Z.pos k) i).
  { rewrite Hhm_eq.
    assert (Hones : (Z.ones (64 - Z.pos k) = 2 ^ (64 - Z.pos k) - 1)%Z)
      by (rewrite Z.ones_equiv; lia).
    replace (2 ^ 64 - 2 ^ Z.pos k)%Z with (Z.shiftl (Z.ones (64 - Z.pos k)) (Z.pos k))
      by (rewrite Z.shiftl_mul_pow2, Hones, Z.mul_sub_distr_r, Z.mul_1_l, <- Z.pow_add_r by lia;
          replace (64 - Z.pos k + Z.pos k)%Z with 64%Z by lia; reflexivity).
    rewrite Z.shiftl_spec by lia.
    destruct (Z.ltb i (Z.pos k)) eqn:Eik.
    - apply Z.ltb_lt in Eik.
      destruct (i - Z.pos k)%Z eqn:Ediff; try lia; symmetry; apply Z.leb_gt; lia.
    - apply Z.ltb_ge in Eik; rewrite Z.ones_spec_low by lia; symmetry; apply Z.leb_le; lia. }
  rewrite Hhm_bits.
  change (Z.testbit (@Integers.unsigned k vlo) i) with (@Integers.testbit k vlo i).
  assert (Hzwk : @Integers.zwordsize k = Z.pos k) by reflexivity.
  destruct (Z.ltb i (Z.pos k)) eqn:Eik.
  - apply Z.ltb_lt in Eik; replace (Z.leb (Z.pos k) i) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite andb_false_r, orb_false_r, Hvlo, (@Integers.testbit_repr k _ i) by (rewrite Hzwk; lia).
    change (Z.testbit (@Integers.unsigned 64%positive rk) i) with (@Integers.testbit 64%positive rk i); reflexivity.
  - apply Z.ltb_ge in Eik; replace (Z.leb (Z.pos k) i) with true by (symmetry; apply Z.leb_le; lia).
    rewrite andb_true_r, Integers.bits_above by (rewrite Hzwk; lia); rewrite orb_false_l.
    change (Z.testbit (@Integers.unsigned 64%positive rk) i) with (@Integers.testbit 64%positive rk i); reflexivity.
Qed.

Lemma a64_init_val_regs_wf : forall allowed_all specs,
  (forall sp, In sp specs -> In (ras_name sp, ras_width sp) allowed_all /\
                             (ras_width sp <> 64%positive -> In (a64_hi_var_name (ras_name sp), 64%positive) allowed_all)) ->
  forallb a64_valid_arg_spec specs = true ->
  wf_a64_val_regs allowed_all (a64_build_init_val_regs 0%N specs).
Proof.
  intros allowed_all specs Hall Hws.
  assert (Hgen : forall base xs,
    (forall sp, In sp xs -> In (ras_name sp, ras_width sp) allowed_all /\
                            (ras_width sp <> 64%positive -> In (a64_hi_var_name (ras_name sp), 64%positive) allowed_all)) ->
    forallb a64_valid_arg_spec xs = true ->
    wf_a64_val_regs allowed_all (a64_build_init_val_regs base xs)).
  { intros base xs; revert base; induction xs as [| sp rest IH]; intros base Hin Hws' r;
      cbn [a64_build_init_val_regs] in *.
    - unfold a64_val_read, a64_empty_val_regs.
      destruct (N.leb 31%N r); [apply wf_sym_bv_const | destruct (a64_is_callee_saved r); exact I].
    - apply andb_true_iff in Hws' as [Hwsp Hwrest].
      unfold a64_valid_arg_spec in Hwsp; rewrite !andb_true_iff in Hwsp; destruct Hwsp as ([Hwsp Hnd] & _).
      unfold a64_val_read in *.
      destruct (N.leb 31%N r) eqn:Er31; [apply wf_sym_bv_const |].
      destruct (N.eqb r base) eqn:Erb.
      + destruct (Hin sp (or_introl eq_refl)) as [Hin_lo Hin_hi].
        assert (Hvar : wf_sym_expr allowed_all (ras_width sp) (CE_Var (ras_name sp) (ras_width sp))).
        { split; [| split; [| split]]; cbn [wt_cert_expr lookup_let_width]; try exact Hnd; try reflexivity.
          apply incl_vars_subset_b; intros [nm0 w0] H0; cbn in H0; destruct H0 as [H0 | []]; inversion H0; subst; exact Hin_lo. }
        unfold a64_init_arg_expr.
        destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
        * apply Pos.eqb_eq in Ew64; rewrite Ew64 in Hvar |- *; exact Hvar.
        * assert (Hhi_var : wf_sym_expr allowed_all 64%positive (CE_Var (a64_hi_var_name (ras_name sp)) 64%positive)).
          { split; [| split; [| split]]; cbn [wt_cert_expr lookup_let_width]; try reflexivity.
            apply incl_vars_subset_b; intros [nm0 w0] H0; cbn in H0; destruct H0 as [H0 | []]; inversion H0; subst.
            apply Hin_hi; intro C; rewrite C in Ew64; discriminate Ew64. }
          destruct (Pos.eqb (ras_width sp) 32%positive) eqn:Ew32.
          -- apply Pos.eqb_eq in Ew32; rewrite Ew32 in Hvar |- *.
             apply a64_wf_sym_binop; [apply wf_sym_cast; [reflexivity | exact Hvar] | apply a64_wf_sym_binop; [exact Hhi_var | apply wf_sym_bv_const]].
          -- assert (Hlt32 : (ras_width sp <? 32)%positive = true) by exact (a64_supported_lt32 _ Hwsp Ew64 Ew32).
             assert (Hlt64 : (ras_width sp <? 64)%positive = true) by exact (rv_supported_arg_width_lt64 _ Hwsp Ew64).
             destruct (ras_ext sp).
             ++ apply a64_wf_sym_binop; [apply wf_sym_cast; [exact Hlt64 | exact Hvar] | apply a64_wf_sym_binop; [exact Hhi_var | apply wf_sym_bv_const]].
             ++ apply a64_wf_sym_binop; [apply wf_sym_cast; [reflexivity | apply wf_sym_cast; [exact Hlt32 | exact Hvar]] | apply a64_wf_sym_binop; [exact Hhi_var | apply wf_sym_bv_const]].
             ++ apply a64_wf_sym_binop; [apply wf_sym_cast; [reflexivity | apply wf_sym_cast; [exact Hlt32 | exact Hvar]] | apply a64_wf_sym_binop; [exact Hhi_var | apply wf_sym_bv_const]].
      + pose proof (IH (N.succ base) (fun s Hs => Hin s (or_intror Hs)) Hwrest r) as Hrec.
        unfold a64_val_read in Hrec; rewrite Er31 in Hrec; exact Hrec. }
  exact (Hgen 0%N specs Hall Hws).
Qed.

Lemma a64_init_val_regs_agrees :
  forall {Pa : Params} (penv : param_env Pa) foracle specs rf sp0,
    forallb a64_valid_arg_spec specs = true ->
    NoDup (List.map ras_name specs) ->
    (forall sp, In sp specs -> ~ In (a64_hi_var_name (ras_name sp)) (List.map ras_name specs)) ->
    a64_rf_matches_args penv specs rf ->
    a64_val_regs_agrees (a64_extend_penv_with_hi penv specs rf) foracle rf sp0
      (a64_build_init_val_regs 0%N specs) rf.
Proof.
  intros Pa penv foracle specs rf sp0 Hws Hnd Hdis Hm.
  unfold a64_extend_penv_with_hi.
  set (penv' := a64_extend_penv_with_hi_at 0%nat specs rf penv).
  assert (Hp_lo : forall sp, In sp specs -> penv' (ras_name sp) = penv (ras_name sp)).
  { intros sp Hsp; unfold penv'; apply a64_extend_penv_at_orig; intros s Hs Heq.
    apply (Hdis s Hs); rewrite Heq; apply in_map_iff; exists sp; split; [reflexivity | exact Hsp]. }
  assert (Hp_hi : forall k sp, nth_error specs k = Some sp -> (ras_width sp =? 64)%positive = false ->
    penv' (a64_hi_var_name (ras_name sp)) =
    Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (N.of_nat k) rf)))).
  { intros k sp Hnth Hw64; unfold penv'; rewrite (a64_extend_penv_at_hi 0%nat k specs sp rf penv Hnd Hnth Hw64); reflexivity. }
  assert (Hgen : forall base xs,
    (forall (j : nat) sp, (j < List.length xs)%nat -> nth_error xs j = Some sp ->
      exists v : @Integers.bit_int (ras_width sp),
        penv' (ras_name sp) = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v)) /\
        ((ras_width sp =? 64)%positive = false ->
          penv' (a64_hi_var_name (ras_name sp)) =
          Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (base + N.of_nat j) rf)))) /\
        match Pos.eqb (ras_width sp) 64%positive, ras_ext sp with
        | true, RAE_None =>
            a64_read_reg (base + N.of_nat j) rf = @Integers.repr 64%positive (@Integers.unsigned (ras_width sp) v)
        | false, RAE_None =>
            @Integers.repr (ras_width sp) (@Integers.unsigned 64%positive (a64_read_reg (base + N.of_nat j) rf)) = v
        | false, RAE_SignExt =>
            @Integers.repr 32%positive (@Integers.unsigned 64%positive (a64_read_reg (base + N.of_nat j) rf)) =
            @Integers.repr 32%positive (@Integers.signed (ras_width sp) v)
        | false, RAE_ZeroExt =>
            @Integers.repr 32%positive (@Integers.unsigned 64%positive (a64_read_reg (base + N.of_nat j) rf)) =
            @Integers.repr 32%positive (@Integers.unsigned (ras_width sp) v)
        | _, _ => False
        end) ->
    forallb a64_valid_arg_spec xs = true ->
    a64_val_regs_agrees penv' foracle rf sp0 (a64_build_init_val_regs base xs) rf).
  { intros base xs; revert base; induction xs as [| sp rest IH]; intros base Hm' Hws' r;
      cbn [a64_build_init_val_regs] in *.
    - unfold a64_val_read, a64_empty_val_regs, a64_read_reg.
      destruct (N.leb 31%N r) eqn:Er31; [cbn [mc_sym_val_agrees]; rewrite eval_ce_const, repr_zero_N; reflexivity |].
      destruct (a64_is_callee_saved r); [cbn [mc_sym_val_agrees]; rewrite Er31; reflexivity | exact I].
    - apply andb_true_iff in Hws' as [Hwsp Hwrest].
      unfold a64_valid_arg_spec in Hwsp; rewrite !andb_true_iff in Hwsp; destruct Hwsp as ([Hwsp _] & Hext_ok).
      unfold a64_val_read in *.
      destruct (N.leb 31%N r) eqn:Er31; [unfold a64_read_reg; rewrite Er31; cbn [mc_sym_val_agrees]; rewrite eval_ce_const, repr_zero_N; reflexivity |].
      destruct (N.eqb r base) eqn:Erb.
      + apply N.eqb_eq in Erb; subst base.
        destruct (Hm' 0%nat sp ltac:(cbn; lia) eq_refl) as (v & Hpv & Hphi & Hmatch).
        rewrite N.add_0_r in Hphi, Hmatch.
        assert (Hvar : eval_closed_cert_expr penv' foracle (CE_Var (ras_name sp) (ras_width sp)) =
                       raise_ret (DVALUE_Base (@DVALUE_I Pa (ras_width sp) v))).
        { unfold eval_closed_cert_expr; cbn [eval_cert_expr]; rewrite Hpv; cbn [lookup_let_val check_scalar_width]; rewrite Pos.eqb_refl; reflexivity. }
        cbn [mc_sym_val_agrees]; unfold a64_init_arg_expr.
        destruct (Pos.eqb (ras_width sp) 64%positive) eqn:Ew64.
        * apply Pos.eqb_eq in Ew64; destruct sp as [nm w ext]; cbn [ras_name ras_width ras_ext] in *; subst w.
          destruct ext; try contradiction; rewrite Hmatch, (@Integers.repr_unsigned 64%positive); exact Hvar.
        * pose proof (Hphi eq_refl) as Hhi_lk.
          assert (Hhi_var : eval_closed_cert_expr penv' foracle (CE_Var (a64_hi_var_name (ras_name sp)) 64%positive) =
                            raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg r rf)))).
          { unfold eval_closed_cert_expr; cbn [eval_cert_expr]; rewrite Hhi_lk; cbn [lookup_let_val check_scalar_width]; reflexivity. }
          assert (Hhi_and : forall msk,
            eval_closed_cert_expr penv' foracle (CE_BinOp CB_And 64%positive no_binop_flags (CE_Var (a64_hi_var_name (ras_name sp)) 64%positive) (CE_BvConst 64%positive msk)) =
            raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (@Integers.and 64%positive (a64_read_reg r rf) (@Integers.repr 64%positive (Z.of_N msk)))))).
          { intro msk; rewrite eval_ce_binop, Hhi_var, eval_ce_const; cbn [eou_bind]; unfold eval_iop; rewrite eval_iop_integer_base_same_width; reflexivity. }
          destruct (Pos.eqb (ras_width sp) 32%positive) eqn:Ew32.
          -- apply Pos.eqb_eq in Ew32; destruct sp as [nm w ext]; cbn [ras_name ras_width ras_ext] in *; subst w.
             destruct ext; try discriminate Hext_ok.
             rewrite eval_ce_binop, (eval_ce_zext _ _ 32%positive 64%positive _ v eq_refl Hvar), Hhi_and; cbn [eou_bind].
             unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op cert_to_ibinop]; cbn - [Integers.or Integers.and Integers.unsigned Integers.repr].
             do 3 f_equal; apply (@or_low_hi_mask_eq 32%positive (a64_read_reg r rf) v 18446744069414584320%N); [lia | reflexivity | symmetry; exact Hmatch].
          -- assert (Hlt32 : (ras_width sp <? 32)%positive = true) by exact (a64_supported_lt32 _ Hwsp Ew64 Ew32).
             assert (Hlt64 : (ras_width sp <? 64)%positive = true) by exact (rv_supported_arg_width_lt64 _ Hwsp Ew64).
             destruct (ras_ext sp).
             ++ rewrite eval_ce_binop, (eval_ce_zext _ _ _ 64%positive _ v Hlt64 Hvar), Hhi_and; cbn [eou_bind].
                unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op cert_to_ibinop]; cbn - [Integers.or Integers.and Integers.unsigned Integers.repr].
                do 3 f_equal; apply (@or_low_hi_mask_eq (ras_width sp) (a64_read_reg r rf) v _); [apply Pos.ltb_lt; exact Hlt64 | reflexivity | symmetry; exact Hmatch].
             ++ rewrite eval_ce_binop, (eval_ce_zext _ _ 32%positive 64%positive _ _ eq_refl (eval_ce_sext _ _ _ 32%positive _ v Hlt32 Hvar)), Hhi_and; cbn [eou_bind].
                unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op cert_to_ibinop]; cbn - [Integers.or Integers.and Integers.unsigned Integers.repr].
                do 3 f_equal; apply (@or_low_hi_mask_eq 32%positive (a64_read_reg r rf) _ 18446744069414584320%N); [lia | reflexivity | symmetry; exact Hmatch].
             ++ rewrite eval_ce_binop, (eval_ce_zext _ _ 32%positive 64%positive _ _ eq_refl (eval_ce_zext _ _ _ 32%positive _ v Hlt32 Hvar)), Hhi_and; cbn [eou_bind].
                unfold eval_iop; rewrite eval_iop_integer_base_same_width; cbn [eval_int_op cert_to_ibinop]; cbn - [Integers.or Integers.and Integers.unsigned Integers.repr].
                do 3 f_equal; apply (@or_low_hi_mask_eq 32%positive (a64_read_reg r rf) _ 18446744069414584320%N); [lia | reflexivity | symmetry; exact Hmatch].
      + assert (Hm_rec : forall (j : nat) sp0, (j < List.length rest)%nat -> nth_error rest j = Some sp0 ->
          exists v : @Integers.bit_int (ras_width sp0),
            penv' (ras_name sp0) = Some (DVALUE_Base (@DVALUE_I Pa (ras_width sp0) v)) /\
            ((ras_width sp0 =? 64)%positive = false ->
              penv' (a64_hi_var_name (ras_name sp0)) =
              Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (N.succ base + N.of_nat j) rf)))) /\
            match Pos.eqb (ras_width sp0) 64%positive, ras_ext sp0 with
            | true, RAE_None => a64_read_reg (N.succ base + N.of_nat j) rf = @Integers.repr 64%positive (@Integers.unsigned (ras_width sp0) v)
            | false, RAE_None => @Integers.repr (ras_width sp0) (@Integers.unsigned 64%positive (a64_read_reg (N.succ base + N.of_nat j) rf)) = v
            | false, RAE_SignExt => @Integers.repr 32%positive (@Integers.unsigned 64%positive (a64_read_reg (N.succ base + N.of_nat j) rf)) = @Integers.repr 32%positive (@Integers.signed (ras_width sp0) v)
            | false, RAE_ZeroExt => @Integers.repr 32%positive (@Integers.unsigned 64%positive (a64_read_reg (N.succ base + N.of_nat j) rf)) = @Integers.repr 32%positive (@Integers.unsigned (ras_width sp0) v)
            | _, _ => False
            end).
        { intros j sp1 Hj Hn; destruct (Hm' (S j) sp1 ltac:(cbn; lia) Hn) as (v & Hp0 & Hph0 & Hmt0).
          exists v; split; [exact Hp0 |]; replace (N.succ base + N.of_nat j)%N with (base + N.of_nat (S j))%N by lia; split; assumption. }
        pose proof (IH (N.succ base) Hm_rec Hwrest r) as Hrec.
        unfold a64_val_read in Hrec; rewrite Er31 in Hrec; exact Hrec. }
  apply (Hgen 0%N specs); [| exact Hws].
  intros j sp Hj Hnth.
  destruct (Hm j sp Hj Hnth) as [v [Hpv Hmt]].
  exists v; split; [rewrite (Hp_lo sp (nth_error_In _ _ Hnth)); exact Hpv |].
  split; [intro Hw64; rewrite N.add_0_l; exact (Hp_hi j sp Hnth Hw64) |].
  rewrite N.add_0_l; exact Hmt.
Qed.

Theorem summarize_a64_dag_wf :
  forall fuel insts arg_specs ret_w d_mc,
    forallb a64_inst_valid insts = true ->
    summarize_a64_dag fuel insts arg_specs ret_w = inr d_mc ->
    wf_cfg_dag
      (List.map (fun sp => (ras_name sp, ras_width sp)) arg_specs ++ a64_hi_vars arg_specs)
      d_mc = true.
Proof.
  intros fuel insts arg_specs ret_w d_mc _ Hsum.
  unfold summarize_a64_dag in Hsum.
  destruct (Nat.leb (List.length arg_specs) 8); [| discriminate Hsum].
  destruct (forallb a64_valid_arg_spec arg_specs) eqn:Hws; cbn [negb] in Hsum; [| discriminate Hsum].
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hsum; [| discriminate Hsum].
  eapply summarize_a64_dag_at_wf with (insts := insts) (sp_off := 0%Z) (fl_def := false);
    [exact (pt_of_list_first_lookup_a64 insts)
    | exact Hrw | unfold mc_frame_cap; lia | | apply mc_sym_stack_wf_empty | intros H; discriminate H | exact Hsum].
  apply a64_init_val_regs_wf; [| exact Hws].
  intros sp Hsp; split.
  - apply in_app_iff; left; apply in_map_iff; exists sp; split; [reflexivity | exact Hsp].
  - intro Hw64; apply in_app_iff; right; unfold a64_hi_vars; apply in_flat_map; exists sp; split; [exact Hsp |].
    destruct (Pos.eqb (ras_width sp) 64%positive) eqn:E64;
      [apply Pos.eqb_eq in E64; contradiction | left; reflexivity].
Qed.

Theorem summarize_a64_dag_sound :
  forall {Pa : Params} fuel raw_bytes insts arg_specs ret_w d_mc penv foracle rf0 sp0 fl0 mstk0,
    decode_a64_bytes raw_bytes = inr insts ->
    NoDup (List.map ras_name arg_specs) ->
    (forall sp, In sp arg_specs -> ~ In (a64_hi_var_name (ras_name sp)) (List.map ras_name arg_specs)) ->
    summarize_a64_dag fuel insts arg_specs ret_w = inr d_mc ->
    mc_valid_sp0 sp0 ->
    a64_rf_matches_args penv arg_specs rf0 ->
    exists rf_end fl_end mstk_end,
      a64_exec_mem fuel insts 0%N sp0 rf0 sp0 fl0 mstk0 = Some (rf_end, sp0, fl_end, mstk_end) /\
      a64_callee_saved_preserved rf0 rf_end /\
      eval_cfg_dag (a64_extend_penv_with_hi penv arg_specs rf0) foracle d_mc =
      DO_Ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end)))).
Proof.
  intros Pa fuel raw_bytes insts arg_specs ret_w d_mc penv foracle rf0 sp0 fl0 mstk0 Hdec Hnd Hdis Hsum Hsp0 Hm.
  pose proof (decode_a64_bytes_valid raw_bytes insts Hdec) as Hval.
  unfold summarize_a64_dag in Hsum.
  destruct (Nat.leb (List.length arg_specs) 8); [| discriminate Hsum].
  destruct (forallb a64_valid_arg_spec arg_specs) eqn:Hws; cbn [negb] in Hsum; [| discriminate Hsum].
  destruct (rv_supported_arg_width ret_w) eqn:Hrw; cbn [negb] in Hsum; [| discriminate Hsum].
  eapply summarize_a64_dag_at_sound with (insts := insts) (sp_off := 0%Z) (fl_def := false);
    [exact (pt_of_list_first_lookup_a64 insts)
    | exact Hrw | exact Hval | exact Hsp0 | unfold mc_frame_cap; lia | rewrite mc_add_ptr_zero; reflexivity
    | exact (a64_init_val_regs_agrees penv foracle arg_specs rf0 sp0 Hws Hnd Hdis Hm)
    | apply mc_sym_stack_agrees_empty | intros H; discriminate H | exact Hsum].
Qed.

