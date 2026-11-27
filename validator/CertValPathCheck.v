(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Path-Sensitive Certificate Obligation Checking, GEP & Padded Structs (Sec 5.6b) *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.String
  Ascii
  List
  Bool
  Lia
  PeanoNat
  Numbers.DecimalString.

From Paco Require Import paco.

From ITree Require Import
  ITree
  ITreeFacts
  Eq.Eqit.

From ExtLib Require Import
  Structures.Maps
  Structures.Monads
  Structures.Functor.

From Vellvm Require Import
  Utils
  Utils.ITreeUtil
  Utils.Assoc
  Utils.ListUtil
  Syntax.LLVMAst
  Syntax.AstLib
  Syntax.DynamicTypes
  Syntax.CFG
  Syntax.TypToDtyp
  Syntax.RawIdMaps
  Syntax.ModuleRefs
  Syntax.Traversal
  Numeric.Integers
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.LLVMEvents
  Semantics.Attributes
  Semantics.Denotation
  Semantics.IntrinsicsDefinitions
  Semantics.MemoryBytes
  Semantics.Operations.Compare
  Semantics.Operations.Conversion
  Semantics.Operations.Select
  Semantics.Operations.Freeze
  Semantics.Operations.Gep
  Theory.MemoryBytesFacts.

From CertValidator.common Require Import
  Diag.

From CertValidator Require Import
  CertFormat
  AigLrat
  AlgRules
  CfgDag
  CertValOpenWorld
  CertValExpReify
  CertValCfgDag
  CertValUbCheck.

Import ListNotations.
Import Sum.
Import Subevent.
Import Logic.

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
#[local] Arguments Integers.neg : simpl never.
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
#[local] Arguments Integers.rol : simpl never.
#[local] Arguments Integers.ror : simpl never.
#[local] Arguments Integers.rolm : simpl never.
#[local] Arguments Integers.negative : simpl never.
#[local] Arguments Integers.add_carry : simpl never.
#[local] Arguments Integers.add_overflow : simpl never.
#[local] Arguments Integers.sub_borrow : simpl never.
#[local] Arguments Integers.sub_overflow : simpl never.

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Lemma expand_lets_let_free_id :
  forall e, is_let_free_expr e = true -> expand_lets e = e.
Proof.
  unfold expand_lets; induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hlf; cbn [is_let_free_expr expand_lets_with] in Hlf |- *; try discriminate Hlf;
    try reflexivity.
  - apply andb_true_iff in Hlf as [Hl Hr]; rewrite (IHl Hl), (IHr Hr); reflexivity.
  - apply andb_true_iff in Hlf as [Hl Hr]; rewrite (IHl Hl), (IHr Hr); reflexivity.
  - rewrite (IHo Hlf); reflexivity.
  - rewrite !andb_true_iff in Hlf; destruct Hlf as ([Hc Ht] & Hf).
    rewrite (IHc Hc), (IHt Ht), (IHf Hf); reflexivity.
  - rewrite (IHo Hlf); reflexivity.
Qed.

Lemma bit1_unsigned_zero : @Integers.unsigned 1 (@Integers.zero 1) = 0%Z.
Proof.
  exact (@Integers.unsigned_zero 1).
Qed.

Lemma bit1_unsigned_one : @Integers.unsigned 1 (@Integers.one 1) = 1%Z.
Proof.
  exact (@Integers.unsigned_one 1).
Qed.

Definition is_zero_bv_const (e : cert_expr) : bool :=
  match e with
  | CE_BvConst w z => Z.eqb (@Integers.unsigned w (@Integers.repr w (Z.of_N z))) 0%Z
  | _ => false
  end.

Lemma is_zero_bv_const_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle e,
    is_zero_bv_const e = true ->
    exists w iz,
      eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa w iz)) /\
      @Integers.unsigned w iz = 0%Z.
Proof.
  intros penv foracle [w z | | | | | | | |] H; cbn in H; try discriminate H.
  apply Z.eqb_eq in H; exists w, (@Integers.repr w (Z.of_N z)).
  split; [reflexivity | exact H].
Qed.

Definition extract_branch_cond_assumptions (on_true : bool) (cs : cert_expr) : list ub_assumption :=
  let base := [UBA_BranchCondDefined cs] in
  match cs with
  | CE_ICmp pr _ _ l r =>
      if on_true then
        match pr with
        | CIP_Ne =>
            if is_zero_bv_const r then UBA_DivisorNonZero l :: base
            else if is_zero_bv_const l then UBA_DivisorNonZero r :: base
            else base
        | CIP_Ugt =>
            if is_zero_bv_const r then UBA_DivisorNonZero l :: base else base
        | CIP_Ult =>
            if is_zero_bv_const l then UBA_DivisorNonZero r :: base else base
        | _ => base
        end
      else
        match pr with
        | CIP_Eq =>
            if is_zero_bv_const r then UBA_DivisorNonZero l :: base
            else if is_zero_bv_const l then UBA_DivisorNonZero r :: base
            else base
        | _ => base
        end
  | _ => base
  end.

Lemma icmp_eval_cbit_operands {Pa : Params} :
  forall (penv : param_env Pa) foracle pr ss w l r (cbit : @Integers.bit_int 1),
    wt_cert_expr [] (CE_ICmp pr ss w l r) = true ->
    eval_closed_cert_expr penv foracle (CE_ICmp pr ss w l r) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit)) ->
    exists il ir : @Integers.bit_int w,
      eval_closed_cert_expr penv foracle l = raise_ret (DVALUE_Base (@DVALUE_I Pa w il)) /\
      eval_closed_cert_expr penv foracle r = raise_ret (DVALUE_Base (@DVALUE_I Pa w ir)) /\
      @eval_int_icmp Pa (@Integers.bit_int w) _ ss (cert_to_icmp pr) il ir =
        raise_ret (@DVALUE_I Pa 1 cbit).
Proof.
  intros penv foracle pr ss w l r cbit Hwt Hev.
  cbn [wt_cert_expr] in Hwt; rewrite !andb_true_iff in Hwt.
  destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr).
  apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
  unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev.
  destruct (eval_cert_expr penv [] foracle l) as [| | | vl] eqn:El; try discriminate Hev.
  cbn [eou_bind] in Hev.
  destruct (eval_cert_expr penv [] foracle r) as [| | | vr] eqn:Er; try discriminate Hev.
  cbn [eou_bind] in Hev.
  pose proof (eval_cert_expr_ret_wf_scalar l _ _ _ _ _ Hwtl El) as Hwfl; rewrite Hwl in Hwfl.
  pose proof (eval_cert_expr_ret_wf_scalar r _ _ _ _ _ Hwtr Er) as Hwfr; rewrite Hwr in Hwfr.
  destruct Hwfl as [-> | [il ->]]; destruct Hwfr as [-> | [ir ->]];
    try (cbn in Hev; discriminate Hev).
  unfold eval_icmp in Hev; rewrite eval_icmp_base_same_width in Hev.
  destruct (@eval_int_icmp Pa (@Integers.bit_int w) _ ss (cert_to_icmp pr) il ir)
    as [| | | db_out] eqn:Eint; cbn in Hev; try discriminate Hev.
  inversion Hev; subst db_out.
  exists il, ir; repeat split; assumption.
Qed.

Lemma extract_branch_cond_assumptions_sound {Pa : Params} :
  forall (penv : param_env Pa) foracle on_true cs (cbit : @Integers.bit_int 1) ctx,
    wt_cert_expr [] cs = true ->
    is_let_free_expr cs = true ->
    eval_closed_cert_expr penv foracle cs = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit)) ->
    ((@Integers.unsigned 1 cbit =? 1)%Z = on_true) ->
    ub_ctx_holds penv foracle ctx ->
    ub_ctx_holds penv foracle (extract_branch_cond_assumptions on_true cs ++ ctx).
Proof.
  intros penv foracle on_true cs cbit ctx Hwt Hlf Ecs Hon Hctx.
  assert (Hbase : ub_ctx_holds penv foracle (UBA_BranchCondDefined cs :: ctx)).
  { constructor; [| exact Hctx].
    cbn [ub_assumption_holds]; rewrite (expand_lets_let_free_id cs Hlf), Ecs.
    intros v Hv ->; discriminate Hv. }
  destruct cs as [| | | | pr ss w l r | | | |];
    cbn [extract_branch_cond_assumptions app]; try exact Hbase.
  cbn [is_let_free_expr] in Hlf; apply andb_true_iff in Hlf as [Hlfl Hlfr].
  destruct (icmp_eval_cbit_operands penv foracle pr ss w l r cbit Hwt Ecs)
    as (il & ir & El & Er & Eint).
  destruct on_true.
  - destruct pr; try exact Hbase.
    + (* CIP_Ne on true *)
      unfold cert_to_icmp, eval_int_icmp, dvp in Eint; cbn - [msamesign Integers.eq Integers.ltu] in Eint.
      destruct (ss && negb (msamesign il ir)); [discriminate Eint |].
      destruct (negb (@Integers.eq w il ir)) eqn:Ene;
        [| exfalso;
           apply (f_equal (fun e => match e with raise_ret v => DVALUE_Base v | _ => DVALUE_Base DVALUE_Poison end)) in Eint;
           cbn in Eint; apply dvalue_base_I_same_sz_inj in Eint; subst cbit;
           rewrite bit1_unsigned_zero in Hon; discriminate Hon].
      apply negb_true_iff in Ene; unfold Integers.eq in Ene.
      destruct (Numeric.Rocqlib.zeq (@Integers.unsigned w il) (@Integers.unsigned w ir)) as [Heq | Hneq];
        [discriminate Ene |].
      destruct (is_zero_bv_const r) eqn:Ezr.
      * constructor; [| exact Hbase].
        cbn [ub_assumption_holds]; rewrite (expand_lets_let_free_id l Hlfl).
        destruct (is_zero_bv_const_sound penv foracle r Ezr) as (wr & iz & Er' & Huz).
        rewrite Er in Er'.
        pose proof (eou_dvalue_I_width_eq _ _ _ _ Er') as <-.
        pose proof (eou_dvalue_I_same_sz_inj _ _ _ Er') as <-.
        exists w, il; split; [exact El | lia].
      * destruct (is_zero_bv_const l) eqn:Ezl; [| exact Hbase].
        constructor; [| exact Hbase].
        cbn [ub_assumption_holds]; rewrite (expand_lets_let_free_id r Hlfr).
        destruct (is_zero_bv_const_sound penv foracle l Ezl) as (wl & iz & El' & Huz).
        rewrite El in El'.
        pose proof (eou_dvalue_I_width_eq _ _ _ _ El') as <-.
        pose proof (eou_dvalue_I_same_sz_inj _ _ _ El') as <-.
        exists w, ir; split; [exact Er | lia].
    + (* CIP_Ult on true *)
      destruct (is_zero_bv_const l) eqn:Ezl; [| exact Hbase].
      unfold cert_to_icmp, eval_int_icmp, dvp in Eint; cbn - [msamesign Integers.eq Integers.ltu] in Eint.
      destruct (ss && negb (msamesign il ir)); [discriminate Eint |].
      destruct (@Integers.ltu w il ir) eqn:Elt;
        [| exfalso;
           apply (f_equal (fun e => match e with raise_ret v => DVALUE_Base v | _ => DVALUE_Base DVALUE_Poison end)) in Eint;
           cbn in Eint; apply dvalue_base_I_same_sz_inj in Eint; subst cbit;
           rewrite bit1_unsigned_zero in Hon; discriminate Hon].
      unfold Integers.ltu in Elt.
      destruct (Numeric.Rocqlib.zlt (@Integers.unsigned w il) (@Integers.unsigned w ir)) as [Hlt | _];
        [| discriminate Elt].
      constructor; [| exact Hbase].
      cbn [ub_assumption_holds]; rewrite (expand_lets_let_free_id r Hlfr).
      destruct (is_zero_bv_const_sound penv foracle l Ezl) as (wl & iz & El' & Huz).
      rewrite El in El'.
      pose proof (eou_dvalue_I_width_eq _ _ _ _ El') as <-.
      pose proof (eou_dvalue_I_same_sz_inj _ _ _ El') as <-.
      exists w, ir; split; [exact Er | lia].
    + (* CIP_Ugt on true *)
      destruct (is_zero_bv_const r) eqn:Ezr; [| exact Hbase].
      unfold cert_to_icmp, eval_int_icmp, dvp in Eint; cbn - [msamesign Integers.eq Integers.ltu] in Eint.
      destruct (ss && negb (msamesign il ir)); [discriminate Eint |].
      destruct (@Integers.ltu w ir il) eqn:Egt;
        [| exfalso;
           apply (f_equal (fun e => match e with raise_ret v => DVALUE_Base v | _ => DVALUE_Base DVALUE_Poison end)) in Eint;
           cbn in Eint; apply dvalue_base_I_same_sz_inj in Eint; subst cbit;
           rewrite bit1_unsigned_zero in Hon; discriminate Hon].
      unfold Integers.ltu in Egt.
      destruct (Numeric.Rocqlib.zlt (@Integers.unsigned w ir) (@Integers.unsigned w il)) as [Hgt | _];
        [| discriminate Egt].
      constructor; [| exact Hbase].
      cbn [ub_assumption_holds]; rewrite (expand_lets_let_free_id l Hlfl).
      destruct (is_zero_bv_const_sound penv foracle r Ezr) as (wr & iz & Er' & Huz).
      rewrite Er in Er'.
      pose proof (eou_dvalue_I_width_eq _ _ _ _ Er') as <-.
      pose proof (eou_dvalue_I_same_sz_inj _ _ _ Er') as <-.
      exists w, il; split; [exact El | lia].
  - destruct pr; try exact Hbase.
    (* CIP_Eq on false *)
    unfold cert_to_icmp, eval_int_icmp, dvp in Eint; cbn - [msamesign Integers.eq Integers.ltu] in Eint.
    destruct (ss && negb (msamesign il ir)); [discriminate Eint |].
    destruct (@Integers.eq w il ir) eqn:Eeq;
      [exfalso;
       apply (f_equal (fun e => match e with raise_ret v => DVALUE_Base v | _ => DVALUE_Base DVALUE_Poison end)) in Eint;
       cbn in Eint; apply dvalue_base_I_same_sz_inj in Eint; subst cbit;
       rewrite bit1_unsigned_one in Hon; discriminate Hon |].
    unfold Integers.eq in Eeq.
    destruct (Numeric.Rocqlib.zeq (@Integers.unsigned w il) (@Integers.unsigned w ir)) as [Heq | Hneq];
      [discriminate Eeq |].
    destruct (is_zero_bv_const r) eqn:Ezr.
    + constructor; [| exact Hbase].
      cbn [ub_assumption_holds]; rewrite (expand_lets_let_free_id l Hlfl).
      destruct (is_zero_bv_const_sound penv foracle r Ezr) as (wr & iz & Er' & Huz).
      rewrite Er in Er'.
      pose proof (eou_dvalue_I_width_eq _ _ _ _ Er') as <-.
      pose proof (eou_dvalue_I_same_sz_inj _ _ _ Er') as <-.
      exists w, il; split; [exact El | lia].
    + destruct (is_zero_bv_const l) eqn:Ezl; [| exact Hbase].
      constructor; [| exact Hbase].
      cbn [ub_assumption_holds]; rewrite (expand_lets_let_free_id r Hlfr).
      destruct (is_zero_bv_const_sound penv foracle l Ezl) as (wl & iz & El' & Huz).
      rewrite El in El'.
      pose proof (eou_dvalue_I_width_eq _ _ _ _ El') as <-.
      pose proof (eou_dvalue_I_same_sz_inj _ _ _ El') as <-.
      exists w, ir; split; [exact Er | lia].
Qed.

Fixpoint dag_node_count (d : cfg_dag) {struct d} : nat :=
  match d with
  | CD_Unreachable | CD_RetVoid | CD_RetScalar _ _ => 1%nat
  | CD_Eval _ _ next => S (dag_node_count next)
  | CD_BlockAssume _ next => S (dag_node_count next)
  | CD_Branch _ on_t on_f => S (dag_node_count on_t + dag_node_count on_f)
  end.

Definition as_block_assume (d : cfg_dag) : option (list ub_assumption * cfg_dag) :=
  match d with
  | CD_BlockAssume uas next => Some (uas, next)
  | _ => None
  end.

Lemma as_block_assume_some_inv : forall d uas next,
  as_block_assume d = Some (uas, next) -> d = CD_BlockAssume uas next.
Proof.
  intros [| | ? ? | ? ? ? | uas' nx' | ? ? ?] uas nx H; cbn in H; try discriminate H.
  inversion H; reflexivity.
Qed.

Definition neg_bool_expr (e : cert_expr) : cert_expr :=
  match e with
  | CE_ICmp pr ss wc l r => CE_ICmp (neg_cert_icmp pr) ss wc l r
  | _ => CE_BinOp CB_Xor 1%positive no_binop_flags e (CE_BvConst 1%positive 1%N)
  end.

Lemma neg_bool_expr_typing :
  forall e,
    wt_cert_expr [] e = true ->
    cert_expr_bit_width e = 1%positive ->
    is_let_free_expr e = true ->
    wt_cert_expr [] (neg_bool_expr e) = true /\
    cert_expr_bit_width (neg_bool_expr e) = 1%positive /\
    is_let_free_expr (neg_bool_expr e) = true /\
    incl (collect_free_vars [] (neg_bool_expr e)) (collect_free_vars [] e).
Proof.
  intros e Hwt Hbw Hlf;
    destruct e;
    cbn [neg_bool_expr wt_cert_expr cert_expr_bit_width is_let_free_expr collect_free_vars wf_binop_flags_for] in *;
    rewrite ?Hwt, ?Hbw, ?Hlf; cbn; rewrite ?app_nil_r;
    repeat split; try reflexivity; intros ? ?; assumption.
Qed.

Lemma neg_bool_expr_eval {Pa : Params} :
  forall e (penv : param_env Pa) foracle (cb : @Integers.bit_int 1%positive),
    wt_cert_expr [] e = true ->
    cert_expr_bit_width e = 1%positive ->
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive cb)) ->
    exists cb' : @Integers.bit_int 1%positive,
      eval_closed_cert_expr penv foracle (neg_bool_expr e) =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive cb')) /\
      (@Integers.unsigned 1%positive cb' =? 1)%Z =
      negb (@Integers.unsigned 1%positive cb =? 1)%Z.
Proof.
  intros e penv foracle cb Hwt Hbw Hev.
  assert (Hxor :
    forall e',
      eval_closed_cert_expr penv foracle e' = raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive cb)) ->
      exists cb' : @Integers.bit_int 1%positive,
        eval_closed_cert_expr penv foracle (CE_BinOp CB_Xor 1%positive no_binop_flags e' (CE_BvConst 1%positive 1%N)) =
          raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive cb')) /\
        (@Integers.unsigned 1%positive cb' =? 1)%Z =
        negb (@Integers.unsigned 1%positive cb =? 1)%Z).
  { intros e' Hev'; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
    rewrite Hev'; cbn [eou_bind].
    unfold eval_iop; rewrite eval_iop_integer_base_same_width.
    unfold cert_to_ibinop, eval_int_op, tdb, fmap;
      cbn [bind ret Functor_Monad ToDvalue_Int EOU_monad mxor VIntVMemInt VInt_Bounded];
      rewrite ?alg_pos_eq_dec_refl; cbn [eq_rec_r eq_rec eq_rect eq_sym].
    eexists; split; [reflexivity |].
    pose proof (alg_bit_int_1_cases cb) as Hcb1.
    destruct ((@Integers.unsigned 1%positive cb =? 1)%Z); rewrite Hcb1; cbn [negb];
      vm_compute; reflexivity. }
  destruct e as [| | | op w fl l r | pr ss wc l r | k fw tw fl o | w c t f | w o | bs body];
    cbn [neg_bool_expr] in *;
    try (unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev; discriminate Hev);
    try exact (Hxor _ Hev).
  cbn [wt_cert_expr] in Hwt; rewrite !andb_true_iff in Hwt.
  destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr);
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
  unfold eval_closed_cert_expr in *; cbn [eval_cert_expr] in *.
  destruct (eval_cert_expr penv [] foracle l) as [| | | vl] eqn:El;
    cbn [eou_bind] in Hev; try discriminate Hev.
  destruct (eval_cert_expr penv [] foracle r) as [| | | vr] eqn:Er;
    cbn [eou_bind] in Hev; try discriminate Hev.
  pose proof (eval_cert_expr_ret_wf_scalar l [] penv [] foracle vl Hwtl El) as Hwfl;
    rewrite Hwl in Hwfl.
  pose proof (eval_cert_expr_ret_wf_scalar r [] penv [] foracle vr Hwtr Er) as Hwfr;
    rewrite Hwr in Hwfr.
  destruct Hwfl as [-> | [il ->]], Hwfr as [-> | [ir ->]];
    try (unfold eval_icmp in Hev; cbn in Hev; discriminate Hev).
  cbn [eou_bind]; unfold eval_icmp in *; rewrite !eval_icmp_base_same_width in Hev |- *.
  destruct (eval_int_icmp_neg ss ss pr wc il ir ltac:(destruct ss; reflexivity))
    as [Hpsn | [b [Hb1 Hb2]]].
  - rewrite Hpsn in Hev; unfold fmap in Hev; cbn [bind ret EOU_monad] in Hev; discriminate Hev.
  - rewrite Hb1 in Hev; rewrite Hb2; unfold fmap in Hev |- *;
      cbn [liftM bind ret Functor_Monad EOU_monad] in Hev |- *.
    destruct b;
      (inversion Hev; subst; eexists; split;
       [reflexivity | rewrite ?(@Integers.unsigned_one 1%positive), ?(@Integers.unsigned_zero 1%positive); reflexivity]).
Qed.

Definition binop_always_non_poison_flags (op : cert_binop) (fl : cert_binop_flags) : bool :=
  match op with
  | CB_Add | CB_Sub | CB_Mul =>
      negb (cbf_nuw fl) && negb (cbf_nsw fl) && negb (cbf_exact fl) && negb (cbf_disjoint fl)
  | CB_And | CB_Xor => true
  | CB_Or => negb (cbf_disjoint fl)
  | _ => false
  end.

Fixpoint expr_non_poison_under_ctx (ctx : ub_ctx) (e : cert_expr) {struct e} : bool :=
  match e with
  | CE_BvConst _ _ => true
  | CE_Var nm w => ctx_has_var_nonpoison ctx nm w
  | CE_ICmp _ false _ l r =>
      expr_non_poison_under_ctx ctx l && expr_non_poison_under_ctx ctx r
  | CE_BinOp op _ fl l r =>
      binop_always_non_poison_flags op fl &&
      expr_non_poison_under_ctx ctx l && expr_non_poison_under_ctx ctx r
  | CE_Select _ c t f =>
      expr_non_poison_under_ctx ctx c &&
      expr_non_poison_under_ctx ctx t &&
      expr_non_poison_under_ctx ctx f
  | _ => false
  end.

Lemma expr_non_poison_under_ctx_sound {Pa : Params} :
  forall ctx e penv foracle v,
    expr_non_poison_under_ctx ctx e = true ->
    wt_cert_expr [] e = true ->
    eval_closed_cert_expr penv foracle e = raise_ret v ->
    ub_ctx_holds penv foracle ctx ->
    v <> DVALUE_Base DVALUE_Poison.
Proof.
  intros ctx e; induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros penv foracle v Hnp Hwt Hev Hctx;
    cbn [expr_non_poison_under_ctx] in Hnp; try discriminate Hnp.
  - unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev; inversion Hev; discriminate.
  - unfold eval_closed_cert_expr in Hev; cbn [eval_cert_expr] in Hev.
    destruct (penv nm) as [dv |] eqn:Epm; [| discriminate Hev].
    destruct (check_scalar_width_inv w dv v Hev) as [<- _].
    exact (ctx_has_var_nonpoison_sound penv foracle ctx nm w v Hnp Hctx Epm).
  - apply andb_true_iff in Hnp as [Hnp_fl Hnpr].
    apply andb_true_iff in Hnp_fl as [Hfl_ok Hnpl].
    cbn [wt_cert_expr] in Hwt; rewrite !andb_true_iff in Hwt.
    destruct Hwt as (((( _ & Hwtl) & Hwtr) & Hwl) & Hwr).
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr] in Hev.
    destruct (eval_cert_expr penv [] foracle l) as [| | | vl] eqn:El; cbn [eou_bind] in Hev; try discriminate.
    destruct (eval_cert_expr penv [] foracle r) as [| | | vr] eqn:Er; cbn [eou_bind] in Hev; try discriminate.
    pose proof (eval_cert_expr_ret_wf_scalar l [] penv [] foracle vl Hwtl El) as Hwfl; rewrite Hwl in Hwfl.
    pose proof (eval_cert_expr_ret_wf_scalar r [] penv [] foracle vr Hwtr Er) as Hwfr; rewrite Hwr in Hwfr.
    pose proof (IHl penv foracle vl Hnpl Hwtl El Hctx) as Hnvl.
    pose proof (IHr penv foracle vr Hnpr Hwtr Er Hctx) as Hnvr.
    destruct Hwfl as [-> | [il ->]]; [contradiction Hnvl; reflexivity |].
    destruct Hwfr as [-> | [ir ->]]; [contradiction Hnvr; reflexivity |].
    unfold eval_iop in Hev; rewrite eval_iop_integer_base_same_width in Hev.
    destruct op; cbn [binop_always_non_poison_flags] in Hfl_ok; try discriminate Hfl_ok;
      unfold cert_to_ibinop, eval_int_op, dvp, tdb in Hev; cbn - [andb orb] in Hev.
    + destruct (cbf_nuw fl), (cbf_nsw fl); cbn in Hfl_ok, Hev; try discriminate Hfl_ok;
        inversion Hev; discriminate.
    + destruct (cbf_nuw fl), (cbf_nsw fl); cbn in Hfl_ok, Hev; try discriminate Hfl_ok;
        inversion Hev; discriminate.
    + destruct (cbf_nuw fl), (cbf_nsw fl); cbn in Hfl_ok, Hev; try discriminate Hfl_ok;
        destruct (Pos.eqb w 1); cbn in Hev; inversion Hev; discriminate.
    + inversion Hev; discriminate.
    + destruct (cbf_disjoint fl); cbn in Hfl_ok, Hev; [discriminate Hfl_ok | inversion Hev; discriminate].
    + inversion Hev; discriminate.
  - destruct ss; [discriminate Hnp |].
    apply andb_true_iff in Hnp as [Hnpl Hnpr].
    cbn [wt_cert_expr] in Hwt; rewrite !andb_true_iff in Hwt.
    destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr).
    apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr] in Hev.
    destruct (eval_cert_expr penv [] foracle l) as [| | | vl] eqn:El; cbn [eou_bind] in Hev; try discriminate.
    destruct (eval_cert_expr penv [] foracle r) as [| | | vr] eqn:Er; cbn [eou_bind] in Hev; try discriminate.
    pose proof (eval_cert_expr_ret_wf_scalar l [] penv [] foracle vl Hwtl El) as Hwfl; rewrite Hwl in Hwfl.
    pose proof (eval_cert_expr_ret_wf_scalar r [] penv [] foracle vr Hwtr Er) as Hwfr; rewrite Hwr in Hwfr.
    pose proof (IHl penv foracle vl Hnpl Hwtl El Hctx) as Hnvl.
    pose proof (IHr penv foracle vr Hnpr Hwtr Er Hctx) as Hnvr.
    destruct Hwfl as [-> | [il ->]]; [contradiction Hnvl; reflexivity |].
    destruct Hwfr as [-> | [ir ->]]; [contradiction Hnvr; reflexivity |].
    unfold eval_icmp in Hev; rewrite eval_icmp_base_same_width in Hev.
    destruct pr; unfold cert_to_icmp, eval_int_icmp, dvp, tdb in Hev;
      cbn - [Integers.eq Integers.lt Integers.ltu] in Hev;
      repeat match type of Hev with context [if ?b then _ else _] => destruct b end;
      cbn in Hev; inversion Hev; discriminate.
  - apply andb_true_iff in Hnp as [Hnp_ct Hnpf]; apply andb_true_iff in Hnp_ct as [Hnpc Hnpt].
    cbn [wt_cert_expr] in Hwt; rewrite !andb_true_iff in Hwt.
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hwc) & _) & _).
    apply Pos.eqb_eq in Hwc.
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr] in Hev.
    destruct (eval_cert_expr penv [] foracle c) as [| | | vc] eqn:Ec; cbn [eou_bind] in Hev; try discriminate.
    destruct (eval_cert_expr penv [] foracle t) as [| | | vt] eqn:Et; cbn [eou_bind] in Hev; try discriminate.
    destruct (eval_cert_expr penv [] foracle f) as [| | | vf] eqn:Ef; cbn [eou_bind] in Hev; try discriminate.
    pose proof (eval_cert_expr_ret_wf_scalar c [] penv [] foracle vc Hwtc Ec) as Hwfc; rewrite Hwc in Hwfc.
    pose proof (IHc penv foracle vc Hnpc Hwtc Ec Hctx) as Hnvc.
    destruct Hwfc as [-> | [ic ->]]; [contradiction Hnvc; reflexivity |].
    cbn [eval_select eval_select_base_dvalue ret EOU_monad] in Hev.
    destruct (@Integers.unsigned 1 ic =? 1)%Z; inversion Hev; subst v;
      [exact (IHt penv foracle vt Hnpt Hwtt Et Hctx) | exact (IHf penv foracle vf Hnpf Hwtf Ef Hctx)].
Qed.

Definition path_entry_signed_rel (cs : cert_expr) (b : bool)
  : option (bool * cert_expr * cert_expr) :=
  match cs with
  | CE_ICmp pr false _ x y =>
      match pr, b with
      | CIP_Slt, true => Some (true, x, y)
      | CIP_Sle, true => Some (false, x, y)
      | CIP_Sgt, true => Some (true, y, x)
      | CIP_Sge, true => Some (false, y, x)
      | CIP_Slt, false => Some (false, y, x)
      | CIP_Sle, false => Some (true, y, x)
      | CIP_Sgt, false => Some (false, x, y)
      | CIP_Sge, false => Some (true, x, y)
      | _, _ => None
      end
  | _ => None
  end.

Lemma path_entry_signed_rel_sound {Pa : Params} :
  forall cs b (penv : param_env Pa) foracle cbit strict x y,
    wt_cert_expr [] cs = true ->
    eval_closed_cert_expr penv foracle cs = raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive cbit)) ->
    (@Integers.unsigned 1%positive cbit =? 1)%Z = b ->
    path_entry_signed_rel cs b = Some (strict, x, y) ->
    exists w (ix iy : @Integers.bit_int w),
      wt_cert_expr [] x = true /\
      wt_cert_expr [] y = true /\
      cert_expr_bit_width x = w /\
      cert_expr_bit_width y = w /\
      eval_closed_cert_expr penv foracle x = raise_ret (DVALUE_Base (@DVALUE_I Pa w ix)) /\
      eval_closed_cert_expr penv foracle y = raise_ret (DVALUE_Base (@DVALUE_I Pa w iy)) /\
      (if strict then (@Integers.signed w ix < @Integers.signed w iy)%Z
       else (@Integers.signed w ix <= @Integers.signed w iy)%Z).
Proof.
  intros cs b penv foracle cbit strict x y Hwt Ecs Ecbit Hrel.
  destruct cs as [| | | | pr ss wc l r | | | |]; cbn [path_entry_signed_rel] in Hrel; try discriminate.
  destruct ss; [discriminate |].
  cbn [wt_cert_expr] in Hwt; rewrite !andb_true_iff in Hwt.
  destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr).
  apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
  unfold eval_closed_cert_expr in *; cbn [eval_cert_expr] in Ecs.
  destruct (eval_cert_expr penv [] foracle l) as [| | | vl] eqn:El; cbn [eou_bind] in Ecs; try discriminate.
  destruct (eval_cert_expr penv [] foracle r) as [| | | vr] eqn:Er; cbn [eou_bind] in Ecs; try discriminate.
  pose proof (eval_cert_expr_ret_wf_scalar l [] penv [] foracle vl Hwtl El) as Hwfl; rewrite Hwl in Hwfl.
  pose proof (eval_cert_expr_ret_wf_scalar r [] penv [] foracle vr Hwtr Er) as Hwfr; rewrite Hwr in Hwfr.
  destruct Hwfl as [-> | [il ->]]; destruct Hwfr as [-> | [ir ->]];
    try (unfold eval_icmp in Ecs; cbn in Ecs; discriminate Ecs).
  unfold eval_icmp in Ecs; rewrite eval_icmp_base_same_width in Ecs.
  unfold cert_to_icmp, eval_int_icmp, Integers.cmp, dvp, tdb in Ecs.
  destruct pr; try discriminate Hrel; destruct b; cbn in Ecs, Hrel;
    repeat match type of Ecs with context [@Integers.lt ?sz ?a ?b] => destruct (@Integers.lt sz a b) eqn:? end;
    cbn in Ecs;
    (apply alg_ret_dvalue_I_inj in Ecs; subst cbit);
    rewrite ?(@Integers.unsigned_one 1%positive), ?(@Integers.unsigned_zero 1%positive) in Ecbit;
    cbn in Ecbit; try discriminate Ecbit;
    inversion Hrel; subst strict x y;
    exists wc;
    repeat match goal with
    | H : @Integers.lt _ _ _ = _ |- _ =>
        unfold Integers.lt in H; destruct (Numeric.Rocqlib.zlt _ _); try discriminate H
    end;
    first
      [ exists il, ir; repeat split; try assumption; lia
      | exists ir, il; repeat split; try assumption; lia ].
Qed.

Fixpoint path_implies_signed_rel
  (need_strict : bool) (path_ctx : list (cert_expr * bool)) (a b : cert_expr) {struct path_ctx} : bool :=
  match path_ctx with
  | [] => false
  | (cs, br) :: rest =>
      let here :=
        match path_entry_signed_rel cs br with
        | Some (strict, x, y) =>
            (strict || negb need_strict) && cert_expr_eqb x a && cert_expr_eqb y b
        | None => false
        end in
      here || path_implies_signed_rel need_strict rest a b
  end.

Definition path_implies_signed_lt (path_ctx : list (cert_expr * bool)) (a b : cert_expr) : bool :=
  path_implies_signed_rel true path_ctx a b.

Definition path_implies_signed_le (path_ctx : list (cert_expr * bool)) (a b : cert_expr) : bool :=
  path_implies_signed_rel false path_ctx a b.

Definition path_ctx_holds {Pa : Params}
  (allowed : list (string * positive)) (penv : param_env Pa) (foracle : freeze_oracle)
  (path_ctx : list (cert_expr * bool)) : Prop :=
  Forall (fun '(cs, b) =>
    wt_cert_expr [] cs = true /\
    cert_expr_bit_width cs = 1%positive /\
    is_let_free_expr cs = true /\
    incl (collect_free_vars [] cs) allowed /\
    exists cbit : @Integers.bit_int 1%positive,
      eval_closed_cert_expr penv foracle cs =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive cbit)) /\
      (@Integers.unsigned 1%positive cbit =? 1)%Z = b) path_ctx.

Lemma path_implies_signed_rel_sound {Pa : Params} :
  forall allowed need_strict path_ctx a b (penv : param_env Pa) foracle,
    path_ctx_holds allowed penv foracle path_ctx ->
    path_implies_signed_rel need_strict path_ctx a b = true ->
    exists w (ia ib : @Integers.bit_int w),
      wt_cert_expr [] a = true /\
      wt_cert_expr [] b = true /\
      cert_expr_bit_width a = w /\
      cert_expr_bit_width b = w /\
      eval_closed_cert_expr penv foracle a = raise_ret (DVALUE_Base (@DVALUE_I Pa w ia)) /\
      eval_closed_cert_expr penv foracle b = raise_ret (DVALUE_Base (@DVALUE_I Pa w ib)) /\
      (if need_strict then (@Integers.signed w ia < @Integers.signed w ib)%Z
       else (@Integers.signed w ia <= @Integers.signed w ib)%Z).
Proof.
  intros allowed need_strict path_ctx a b penv foracle Hph Himp.
  induction path_ctx as [| [cs br] rest IH]; cbn [path_implies_signed_rel] in Himp; [discriminate |].
  inversion Hph as [| ? ? Hcs Hrest]; subst; clear Hph.
  apply orb_true_iff in Himp as [Hhere | Hlater]; [| exact (IH Hrest Hlater)].
  destruct Hcs as (Hwt_cs & _ & _ & _ & [cbit [Ecs Ecbit]]).
  destruct (path_entry_signed_rel cs br) as [[[strict x] y] |] eqn:Erel; [| discriminate].
  rewrite !andb_true_iff in Hhere; destruct Hhere as [[Hst Ex] Ey].
  apply cert_expr_eqb_eq in Ex; apply cert_expr_eqb_eq in Ey; subst x y.
  destruct (path_entry_signed_rel_sound cs br penv foracle cbit strict a b Hwt_cs Ecs Ecbit Erel)
    as (w & ia & ib & Hwta & Hwtb & Hbwa & Hbwb & Ea & Eb & Hcmp).
  exists w, ia, ib; repeat split; try assumption.
  destruct need_strict, strict; cbn in Hst |- *; try discriminate Hst; lia.
Qed.

Definition path_implies_signed_ge_zero
  (path_ctx : list (cert_expr * bool)) (e : cert_expr) : bool :=
  (0 <=? fst (expr_srange e))%Z ||
  path_implies_signed_le path_ctx (CE_BvConst (cert_expr_bit_width e) 0%N) e ||
  existsb (fun '(cs, br) =>
    match path_entry_signed_rel cs br with
    | Some (_, x, y) =>
        cert_expr_eqb y e &&
        ((0 <=? fst (expr_srange x))%Z ||
         path_implies_signed_le path_ctx (CE_BvConst (cert_expr_bit_width x) 0%N) x)
    | None => false
    end) path_ctx.

Lemma path_entry_signed_rel_vars :
  forall cs b strict x y,
    path_entry_signed_rel cs b = Some (strict, x, y) ->
    incl (collect_free_vars [] x) (collect_free_vars [] cs) /\
    incl (collect_free_vars [] y) (collect_free_vars [] cs).
Proof.
  intros cs b strict x y Hrel.
  destruct cs as [| | | | pr ss wc l r | | | |]; cbn [path_entry_signed_rel] in Hrel; try discriminate.
  destruct ss; [discriminate |].
  destruct pr, b; cbn in Hrel; try discriminate;
    inversion Hrel; subst;
    cbn [collect_free_vars];
    split; intros z Hz; apply in_app_iff; first [left; exact Hz | right; exact Hz].
Qed.

Lemma path_implies_signed_ge_zero_sound {Pa : Params} :
  forall allowed path_ctx e (penv : param_env Pa) foracle w (ie : @Integers.bit_int w),
    wt_cert_expr [] e = true ->
    cert_expr_bit_width e = w ->
    wf_param_env_for allowed penv ->
    wf_param_env_for (collect_free_vars [] e) penv ->
    path_ctx_holds allowed penv foracle path_ctx ->
    path_implies_signed_ge_zero path_ctx e = true ->
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa w ie)) ->
    (0 <= @Integers.signed w ie)%Z.
Proof.
  intros allowed path_ctx e penv foracle w ie Hwt Hbw Hallowed Hpenv Hph Hge Hev.
  unfold path_implies_signed_ge_zero in Hge.
  apply orb_true_iff in Hge as [Hge1 | Htrans].
  - apply orb_true_iff in Hge1 as [Hsr | Hle0].
    + apply Z.leb_le in Hsr.
      pose proof (expr_srange_sound e w penv foracle ie Hbw Hwt Hpenv Hev) as Hsr_e.
      destruct (expr_srange e) as [lo hi]; cbn in Hsr; lia.
    + destruct (path_implies_signed_rel_sound allowed false path_ctx
                  (CE_BvConst (cert_expr_bit_width e) 0%N) e penv foracle Hph Hle0)
        as (w0 & iz & ie' & _ & _ & Hbwz & Hbwe & Ez & Ee & Hcmp).
      cbn [cert_expr_bit_width] in Hbwz; rewrite Hbw in Hbwz; subst w0.
      unfold eval_closed_cert_expr in Ez; cbn [eval_cert_expr] in Ez; rewrite Hbw in Ez;
        apply alg_ret_dvalue_I_inj in Ez; subst iz.
      rewrite repr_zero_N, (@Integers.signed_zero w) in Hcmp.
      rewrite Hev in Ee; apply alg_ret_dvalue_I_inj in Ee; subst ie'; exact Hcmp.
  - apply existsb_exists in Htrans as [[cs br] [Hin Hchk]].
    destruct (path_entry_signed_rel cs br) as [[[strict x] y] |] eqn:Erel; [| discriminate].
    apply andb_true_iff in Hchk as [Ey Hx].
    apply cert_expr_eqb_eq in Ey; subst y.
    assert (Hcs : wt_cert_expr [] cs = true /\
                  incl (collect_free_vars [] cs) allowed /\
                  exists cbit : @Integers.bit_int 1%positive,
                    eval_closed_cert_expr penv foracle cs = raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive cbit)) /\
                    (@Integers.unsigned 1%positive cbit =? 1)%Z = br).
    { unfold path_ctx_holds in Hph; rewrite Forall_forall in Hph; destruct (Hph (cs, br) Hin) as (H1 & _ & _ & H2 & H3);
        exact (conj H1 (conj H2 H3)). }
    destruct Hcs as (Hwt_cs & Hfv_cs & [cbit [Ecs Ecbit]]).
    destruct (path_entry_signed_rel_sound cs br penv foracle cbit strict x e Hwt_cs Ecs Ecbit Erel)
      as (wx & ix & ie' & Hwtx & _ & Hbwx & Hbwe & Ex & Ee & Hcmp).
    rewrite Hbwe in Hbw; subst wx.
    rewrite Hev in Ee; apply alg_ret_dvalue_I_inj in Ee; subst ie'.
    apply orb_true_iff in Hx as [Hsrx | Hle0x].
    + apply Z.leb_le in Hsrx.
      destruct (path_entry_signed_rel_vars cs br strict x e Erel) as [Hfvx _].
      assert (Hpx : wf_param_env_for (collect_free_vars [] x) penv)
        by (intros z wz Hz; exact (Hallowed z wz (Hfv_cs (z, wz) (Hfvx (z, wz) Hz)))).
      pose proof (expr_srange_sound x w penv foracle ix Hbwx Hwtx Hpx Ex) as Hsr_x.
      destruct (expr_srange x) as [lo hi]; cbn in Hsrx; destruct strict; lia.
    + destruct (path_implies_signed_rel_sound allowed false path_ctx
                  (CE_BvConst (cert_expr_bit_width x) 0%N) x penv foracle Hph Hle0x)
        as (w0 & iz & ix' & _ & _ & Hbwz & Hbwx' & Ez & Ex' & Hcmp0).
      cbn [cert_expr_bit_width] in Hbwz; rewrite Hbwx in Hbwz; subst w0.
      unfold eval_closed_cert_expr in Ez; cbn [eval_cert_expr] in Ez;
        rewrite Hbwx in Ez; apply alg_ret_dvalue_I_inj in Ez; subst iz.
      rewrite repr_zero_N, (@Integers.signed_zero w) in Hcmp0.
      rewrite Ex in Ex'; apply alg_ret_dvalue_I_inj in Ex'; subst ix'; destruct strict; lia.
Qed.

Fixpoint lookup_path_bool_direct
  (ctx : ub_ctx) (path_ctx : list (cert_expr * bool)) (c : cert_expr)
  {struct path_ctx} : option bool :=
  match path_ctx with
  | [] => None
  | (cs, b) :: rest =>
      if check_expr_refines ctx cs c then Some b
      else if check_expr_refines ctx (neg_bool_expr cs) c then Some (negb b)
      else lookup_path_bool_direct ctx rest c
  end.

Definition lookup_path_bool
  (ctx : ub_ctx) (path_ctx : list (cert_expr * bool)) (c : cert_expr) : option bool :=
  match lookup_path_bool_direct ctx path_ctx c with
  | Some b => Some b
  | None =>
      match c with
      | CE_ICmp pr false _ a b =>
          if ub_free_expr a && ub_free_expr b then
            match pr with
            | CIP_Slt =>
                if path_implies_signed_lt path_ctx a b then Some true
                else if path_implies_signed_le path_ctx b a then Some false
                else None
            | CIP_Sle =>
                if path_implies_signed_le path_ctx a b then Some true
                else if path_implies_signed_lt path_ctx b a then Some false
                else None
            | CIP_Sgt =>
                if path_implies_signed_lt path_ctx b a then Some true
                else if path_implies_signed_le path_ctx a b then Some false
                else None
            | CIP_Sge =>
                if path_implies_signed_le path_ctx b a then Some true
                else if path_implies_signed_lt path_ctx a b then Some false
                else None
            | _ => None
            end
          else None
      | _ => None
      end
  end.

Lemma lookup_path_bool_direct_sound {Pa : Params} :
  forall allowed ctx path_ctx c penv foracle b_out,
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv foracle ctx ->
    path_ctx_holds allowed penv foracle path_ctx ->
    incl (collect_free_vars [] c) allowed ->
    lookup_path_bool_direct ctx path_ctx c = Some b_out ->
    exists cbit : @Integers.bit_int 1%positive,
      eval_closed_cert_expr penv foracle c =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive cbit)) /\
      (@Integers.unsigned 1%positive cbit =? 1)%Z = b_out.
Proof.
  intros allowed ctx path_ctx c penv foracle b_out Hpenv Hctx Hph Hfv Hlk.
  induction path_ctx as [| [cs b] rest IH]; cbn [lookup_path_bool_direct] in Hlk; [discriminate |].
  inversion Hph as [| ? ? Hcs Hrest]; subst; clear Hph.
  destruct Hcs as (Hwt_cs & Hbw_cs & Hlf_cs & Hfv_cs & [cbit [Ecs Ecbit]]).
  pose proof (fun x wx Hx => Hpenv x wx (Hfv_cs (x, wx) Hx)) as Hpcs.
  pose proof (fun x wx Hx => Hpenv x wx (Hfv (x, wx) Hx)) as Hpc.
  destruct (check_expr_refines ctx cs c) eqn:E1.
  - inversion Hlk; subst b_out; clear Hlk.
    pose proof (check_expr_refines_sound ctx cs c penv foracle E1 Hpcs Hpc Hctx) as Href.
    rewrite Ecs in Href; cbn [refine_eou_dvalue] in Href.
    destruct (eval_closed_cert_expr penv foracle c) as [| | | dvc] eqn:Ec; try contradiction Href.
    destruct Href as [Hps | ->]; [discriminate Hps |].
    exists cbit; split; [reflexivity | exact Ecbit].
  - destruct (check_expr_refines ctx (neg_bool_expr cs) c) eqn:E2.
    + inversion Hlk; subst b_out; clear Hlk.
      destruct (neg_bool_expr_typing cs Hwt_cs Hbw_cs Hlf_cs) as (_ & _ & _ & Hfv_n).
      pose proof (fun x wx Hx => Hpcs x wx (Hfv_n (x, wx) Hx)) as Hpn.
      destruct (neg_bool_expr_eval cs penv foracle cbit Hwt_cs Hbw_cs Ecs) as [cbit' [En Enb]].
      pose proof (check_expr_refines_sound ctx (neg_bool_expr cs) c penv foracle E2 Hpn Hpc Hctx) as Href.
      rewrite En in Href; cbn [refine_eou_dvalue] in Href.
      destruct (eval_closed_cert_expr penv foracle c) as [| | | dvc] eqn:Ec; try contradiction Href.
      destruct Href as [Hps | ->]; [discriminate Hps |].
      exists cbit'; split; [reflexivity | rewrite Enb, Ecbit; reflexivity].
    + exact (IH Hrest Hlk).
Qed.

Lemma lookup_path_bool_sound {Pa : Params} :
  forall allowed ctx path_ctx c penv foracle b_out,
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv foracle ctx ->
    path_ctx_holds allowed penv foracle path_ctx ->
    incl (collect_free_vars [] c) allowed ->
    lookup_path_bool ctx path_ctx c = Some b_out ->
    exists cbit : @Integers.bit_int 1%positive,
      eval_closed_cert_expr penv foracle c =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive cbit)) /\
      (@Integers.unsigned 1%positive cbit =? 1)%Z = b_out.
Proof.
  intros allowed ctx path_ctx c penv foracle b_out Hpenv Hctx Hph Hfv Hlk.
  unfold lookup_path_bool in Hlk.
  destruct (lookup_path_bool_direct ctx path_ctx c) as [bd |] eqn:Ed.
  - inversion Hlk; subst b_out; exact (lookup_path_bool_direct_sound allowed ctx path_ctx c penv foracle bd Hpenv Hctx Hph Hfv Ed).
  - destruct c as [| | | | pr ss wc a b | | | |]; try discriminate Hlk.
    destruct ss; [discriminate Hlk |].
    destruct (ub_free_expr a && ub_free_expr b) eqn:Eub; [| discriminate Hlk].
    Local Ltac solve_cmp_from_rel allowed path_ctx penv foracle Hph Hrel :=
      destruct (path_implies_signed_rel_sound allowed _ path_ctx _ _ penv foracle Hph Hrel)
        as (w & ia & ib & _ & _ & _ & _ & Ea & Eb & Hcmp);
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
      rewrite Ea, Eb; cbn [eou_bind];
      unfold eval_icmp; rewrite eval_icmp_base_same_width;
      unfold cert_to_icmp, eval_int_icmp, Integers.cmp, dvp, tdb;
      cbn - [Integers.lt];
      unfold Integers.lt;
      repeat match goal with
      | |- context [Numeric.Rocqlib.zlt ?x ?y] =>
          destruct (Numeric.Rocqlib.zlt x y); [try lia | try lia]
      end;
      cbn; eexists; split; try reflexivity;
      rewrite ?(@Integers.unsigned_one 1%positive), ?(@Integers.unsigned_zero 1%positive);
      reflexivity.
    destruct pr; try discriminate Hlk;
      repeat match type of Hlk with
      | (if ?cond then Some ?bv else _) = Some b_out =>
          let Hc := fresh "Hc" in
          destruct cond eqn:Hc;
          [ inversion Hlk; subst b_out; solve_cmp_from_rel allowed path_ctx penv foracle Hph Hc
          | ]
      end; discriminate Hlk.
Qed.

Definition simplify_select_signed_minmax
  (path_ctx : list (cert_expr * bool)) (w : positive) (c t f : cert_expr)
  : option cert_expr :=
  match c with
  | CE_ICmp pr false wc a b =>
      if Pos.eqb wc w then
        match pr with
        | CIP_Slt | CIP_Sle =>
            if cert_expr_eqb a t && cert_expr_eqb b f then
              if path_implies_signed_le path_ctx a b then Some t
              else if path_implies_signed_le path_ctx b a then Some f
              else None
            else if cert_expr_eqb b t && cert_expr_eqb a f then
              if path_implies_signed_le path_ctx a b then Some t
              else if path_implies_signed_le path_ctx b a then Some f
              else None
            else None
        | CIP_Sgt | CIP_Sge =>
            if cert_expr_eqb a t && cert_expr_eqb b f then
              if path_implies_signed_le path_ctx a b then Some f
              else if path_implies_signed_le path_ctx b a then Some t
              else None
            else if cert_expr_eqb b t && cert_expr_eqb a f then
              if path_implies_signed_le path_ctx a b then Some f
              else if path_implies_signed_le path_ctx b a then Some t
              else None
            else None
        | _ => None
        end
      else None
  | _ => None
  end.

Lemma simplify_select_signed_minmax_inv :
  forall path_ctx w c t f res,
    simplify_select_signed_minmax path_ctx w c t f = Some res ->
    res = t \/ res = f.
Proof.
  intros path_ctx w [| | | | pr ss wc a b | | | |] t f res H;
    cbn [simplify_select_signed_minmax] in H; try discriminate.
  destruct ss; [discriminate |].
  destruct (Pos.eqb wc w); [| discriminate].
  destruct pr; try discriminate;
    repeat match type of H with
    | (if ?b then _ else _) = Some res => destruct b
    end; inversion H; subst; auto.
Qed.

Lemma simplify_select_signed_minmax_eval {Pa : Params} :
  forall allowed path_ctx w c t f res (penv : param_env Pa) foracle,
    wt_cert_expr [] c = true ->
    wt_cert_expr [] t = true ->
    wt_cert_expr [] f = true ->
    cert_expr_bit_width t = w ->
    cert_expr_bit_width f = w ->
    path_ctx_holds allowed penv foracle path_ctx ->
    simplify_select_signed_minmax path_ctx w c t f = Some res ->
    eval_closed_cert_expr penv foracle (CE_Select w c t f) =
    eval_closed_cert_expr penv foracle res.
Proof.
  intros allowed path_ctx w [| | | | pr ss wc a b | | | |] t f res penv foracle Hwtc Hwtt Hwtf Hbwt Hbwf Hph Hsm;
    cbn [simplify_select_signed_minmax] in Hsm; try discriminate.
  destruct ss; [discriminate |].
  destruct (Pos.eqb wc w) eqn:Ewc; [apply Pos.eqb_eq in Ewc; subst wc | discriminate].
  Local Ltac solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp Heqt Hres :=
    apply andb_true_iff in Heqt as [E1 E2];
    apply cert_expr_eqb_eq in E1; apply cert_expr_eqb_eq in E2;
    destruct (path_implies_signed_rel_sound allowed false path_ctx _ _ penv foracle Hph Hcmp)
      as (w0 & ix & iy & _ & _ & Hbwx & Hbwy & Ea & Eb & Hle);
    cbn [simplify_select_signed_minmax] in Hres;
    repeat match type of Hres with
    | context [Pos.eqb _ _] => rewrite Pos.eqb_refl in Hres
    end;
    repeat match goal with
    | H : (cert_expr_eqb _ _ && cert_expr_eqb _ _) = _ |- _ => rewrite H in Hres
    | H : path_implies_signed_le _ _ _ = _ |- _ => rewrite H in Hres
    end;
    inversion Hres; subst res;
    first
      [ rewrite E1, Hbwt in Hbwx; subst w0
      | rewrite E2, Hbwf in Hbwx; subst w0
      | rewrite E1, Hbwf in Hbwx; subst w0
      | rewrite E2, Hbwt in Hbwx; subst w0 ];
    subst t f;
    unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
    rewrite ?Ea, ?Eb;
    cbn [eou_bind];
    unfold eval_icmp; rewrite eval_icmp_base_same_width;
    unfold cert_to_icmp, eval_int_icmp, Integers.cmp, dvp, tdb;
    cbn - [Integers.lt]; unfold Integers.lt;
    repeat match goal with
    | |- context [Numeric.Rocqlib.zlt ?u ?v] =>
        destruct (Numeric.Rocqlib.zlt u v); cbn;
        rewrite ?(@Integers.unsigned_one 1%positive), ?(@Integers.unsigned_zero 1%positive); cbn
    end;
    try reflexivity;
    (f_equal; f_equal; f_equal; rewrite <- (@Integers.repr_signed w ix), <- (@Integers.repr_signed w iy); f_equal; lia).
  destruct pr; try discriminate Hsm.
  - destruct (cert_expr_eqb a t && cert_expr_eqb b f) eqn:Etf.
    + destruct (path_implies_signed_le path_ctx a b) eqn:Hcmp.
      * solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp Etf Hsm.
      * destruct (path_implies_signed_le path_ctx b a) eqn:Hcmp2; [| discriminate Hsm].
        solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp2 Etf Hsm.
    + destruct (cert_expr_eqb b t && cert_expr_eqb a f) eqn:Eft; [| discriminate Hsm].
      destruct (path_implies_signed_le path_ctx a b) eqn:Hcmp.
      * solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp Eft Hsm.
      * destruct (path_implies_signed_le path_ctx b a) eqn:Hcmp2; [| discriminate Hsm].
        solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp2 Eft Hsm.
  - destruct (cert_expr_eqb a t && cert_expr_eqb b f) eqn:Etf.
    + destruct (path_implies_signed_le path_ctx a b) eqn:Hcmp.
      * solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp Etf Hsm.
      * destruct (path_implies_signed_le path_ctx b a) eqn:Hcmp2; [| discriminate Hsm].
        solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp2 Etf Hsm.
    + destruct (cert_expr_eqb b t && cert_expr_eqb a f) eqn:Eft; [| discriminate Hsm].
      destruct (path_implies_signed_le path_ctx a b) eqn:Hcmp.
      * solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp Eft Hsm.
      * destruct (path_implies_signed_le path_ctx b a) eqn:Hcmp2; [| discriminate Hsm].
        solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp2 Eft Hsm.
  - destruct (cert_expr_eqb a t && cert_expr_eqb b f) eqn:Etf.
    + destruct (path_implies_signed_le path_ctx a b) eqn:Hcmp.
      * solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp Etf Hsm.
      * destruct (path_implies_signed_le path_ctx b a) eqn:Hcmp2; [| discriminate Hsm].
        solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp2 Etf Hsm.
    + destruct (cert_expr_eqb b t && cert_expr_eqb a f) eqn:Eft; [| discriminate Hsm].
      destruct (path_implies_signed_le path_ctx a b) eqn:Hcmp.
      * solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp Eft Hsm.
      * destruct (path_implies_signed_le path_ctx b a) eqn:Hcmp2; [| discriminate Hsm].
        solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp2 Eft Hsm.
  - destruct (cert_expr_eqb a t && cert_expr_eqb b f) eqn:Etf.
    + destruct (path_implies_signed_le path_ctx a b) eqn:Hcmp.
      * solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp Etf Hsm.
      * destruct (path_implies_signed_le path_ctx b a) eqn:Hcmp2; [| discriminate Hsm].
        solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp2 Etf Hsm.
    + destruct (cert_expr_eqb b t && cert_expr_eqb a f) eqn:Eft; [| discriminate Hsm].
      destruct (path_implies_signed_le path_ctx a b) eqn:Hcmp.
      * solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp Eft Hsm.
      * destruct (path_implies_signed_le path_ctx b a) eqn:Hcmp2; [| discriminate Hsm].
        solve_minmax_arm allowed path_ctx penv foracle w res t f Hbwt Hbwf Hph Hcmp2 Eft Hsm.
Qed.

Definition path_safe_nonpoison_i1
  (ctx : ub_ctx) (path_ctx : list (cert_expr * bool)) (x : cert_expr) : bool :=
  match lookup_path_bool ctx path_ctx x with
  | Some _ => true
  | None => ub_free_expr x && expr_non_poison_under_ctx ctx x
  end.

Fixpoint simplify_expr_with_path_aux
  (ctx : ub_ctx) (path_ctx : list (cert_expr * bool)) (e : cert_expr) {struct e} : cert_expr :=
  let go := simplify_expr_with_path_aux ctx path_ctx in
  match e with
  | CE_BvConst _ _ | CE_Poison _ | CE_Var _ _ | CE_Freeze _ _ | CE_Let _ _ => e
  | CE_BinOp op w fl l r =>
      let l' := go l in
      let r' := go r in
      match op with
      | CB_Or =>
          if Pos.eqb w 1%positive && negb (cbf_disjoint fl) then
            match lookup_path_bool ctx path_ctx l', lookup_path_bool ctx path_ctx r' with
            | Some true, _ =>
                if path_safe_nonpoison_i1 ctx path_ctx r' then CE_BvConst 1%positive 1%N
                else CE_BinOp op w fl l' r'
            | _, Some true =>
                if path_safe_nonpoison_i1 ctx path_ctx l' then CE_BvConst 1%positive 1%N
                else CE_BinOp op w fl l' r'
            | Some false, Some false => CE_BvConst 1%positive 0%N
            | Some false, None => if ub_free_expr r' then r' else CE_BinOp op w fl l' r'
            | None, Some false => if ub_free_expr l' then l' else CE_BinOp op w fl l' r'
            | _, _ => CE_BinOp op w fl l' r'
            end
          else CE_BinOp op w fl l' r'
      | CB_And =>
          if Pos.eqb w 1%positive then
            match lookup_path_bool ctx path_ctx l', lookup_path_bool ctx path_ctx r' with
            | Some false, _ =>
                if path_safe_nonpoison_i1 ctx path_ctx r' then CE_BvConst 1%positive 0%N
                else CE_BinOp op w fl l' r'
            | _, Some false =>
                if path_safe_nonpoison_i1 ctx path_ctx l' then CE_BvConst 1%positive 0%N
                else CE_BinOp op w fl l' r'
            | Some true, Some true => CE_BvConst 1%positive 1%N
            | Some true, None => if ub_free_expr r' then r' else CE_BinOp op w fl l' r'
            | None, Some true => if ub_free_expr l' then l' else CE_BinOp op w fl l' r'
            | _, _ => CE_BinOp op w fl l' r'
            end
          else CE_BinOp op w fl l' r'
      | CB_Sub =>
          if cbf_nsw fl && negb (cbf_nuw fl) && negb (cbf_exact fl) && negb (cbf_disjoint fl) &&
             path_implies_signed_ge_zero path_ctx l' &&
             path_implies_signed_ge_zero path_ctx r' then
            CE_BinOp CB_Sub w no_binop_flags l' r'
          else CE_BinOp CB_Sub w fl l' r'
      | _ => CE_BinOp op w fl l' r'
      end
  | CE_ICmp pr ss w l r => CE_ICmp pr ss w (go l) (go r)
  | CE_Cast k fw tw fl o => CE_Cast k fw tw fl (go o)
  | CE_Select w c t f =>
      let c' := go c in
      let t' := go t in
      let f' := go f in
      match lookup_path_bool ctx path_ctx c' with
      | Some true => if ub_free_expr f' then t' else CE_Select w c' t' f'
      | Some false => if ub_free_expr t' then f' else CE_Select w c' t' f'
      | None =>
          match simplify_select_signed_minmax path_ctx w c' t' f' with
          | Some res => res
          | None => CE_Select w c' t' f'
          end
      end
  end.

Definition simplify_expr_with_path
  (ctx : ub_ctx) (path_ctx : list (cert_expr * bool)) (e : cert_expr) : cert_expr :=
  match path_ctx with
  | [] => e
  | _ :: _ => simplify_expr_with_path_aux ctx path_ctx e
  end.

Lemma simplify_expr_with_path_typing :
  forall ctx path_ctx e,
    wt_cert_expr [] e = true ->
    is_let_free_expr e = true ->
    let out := simplify_expr_with_path ctx path_ctx e in
    wt_cert_expr [] out = true /\
    cert_expr_bit_width out = cert_expr_bit_width e /\
    is_let_free_expr out = true /\
    incl (collect_free_vars [] out) (collect_free_vars [] e).
Proof.
  intros ctx path_ctx e; destruct path_ctx as [| pc pcs].
  - intros Hwt Hlf; unfold simplify_expr_with_path;
      repeat split; try assumption; try reflexivity; intros ? ?; assumption.
  - unfold simplify_expr_with_path.
    induction e as
      [ w v | w | nm w
      | op w fl l IHl r IHr
      | pr ss w l IHl r IHr
      | k fw tw fl o IHo
      | w c IHc t IHt f IHf
      | w o IHo
      | bs body IHbs IHb ] using cert_expr_ind_nested;
      intros Hwt Hlf; cbn [simplify_expr_with_path_aux];
      try (repeat split; try assumption; try reflexivity; intros ? ?; assumption).
    + cbn [wt_cert_expr is_let_free_expr cert_expr_bit_width collect_free_vars] in Hwt, Hlf.
      rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
      destruct Hwt as ((((Hfl & Hwtl) & Hwtr) & Hwl) & Hwr);
        destruct Hlf as [Hlfl Hlfr].
      destruct (IHl Hwtl Hlfl) as (Hwl' & Hbwl' & Hlfl' & Hfvl').
      destruct (IHr Hwtr Hlfr) as (Hwr' & Hbwr' & Hlfr' & Hfvr').
      assert (Hdefault :
        wt_cert_expr [] (CE_BinOp op w fl
                           (simplify_expr_with_path_aux ctx (pc :: pcs) l)
                           (simplify_expr_with_path_aux ctx (pc :: pcs) r)) = true /\
        cert_expr_bit_width (CE_BinOp op w fl
                               (simplify_expr_with_path_aux ctx (pc :: pcs) l)
                               (simplify_expr_with_path_aux ctx (pc :: pcs) r)) = w /\
        is_let_free_expr (CE_BinOp op w fl
                            (simplify_expr_with_path_aux ctx (pc :: pcs) l)
                            (simplify_expr_with_path_aux ctx (pc :: pcs) r)) = true /\
        incl (collect_free_vars [] (CE_BinOp op w fl
                                      (simplify_expr_with_path_aux ctx (pc :: pcs) l)
                                      (simplify_expr_with_path_aux ctx (pc :: pcs) r)))
             (collect_free_vars [] l ++ collect_free_vars [] r)).
      { cbn [wt_cert_expr is_let_free_expr cert_expr_bit_width collect_free_vars].
        rewrite Hfl, Hwl', Hwr', Hbwl', Hbwr', Hwl, Hwr, Hlfl', Hlfr';
          repeat split; try reflexivity.
        intros x Hx; apply in_app_iff in Hx as [Hx | Hx];
          apply in_app_iff; [left; exact (Hfvl' x Hx) | right; exact (Hfvr' x Hx)]. }
      assert (Hconst1 : forall n, w = 1%positive ->
        wt_cert_expr [] (CE_BvConst 1%positive n) = true /\
        cert_expr_bit_width (CE_BvConst 1%positive n) = w /\
        is_let_free_expr (CE_BvConst 1%positive n) = true /\
        incl (collect_free_vars [] (CE_BvConst 1%positive n))
             (collect_free_vars [] l ++ collect_free_vars [] r)).
      { intros n ->; repeat split; try reflexivity; intros ? []. }
      assert (Hl'_ok : w = 1%positive ->
        wt_cert_expr [] (simplify_expr_with_path_aux ctx (pc :: pcs) l) = true /\
        cert_expr_bit_width (simplify_expr_with_path_aux ctx (pc :: pcs) l) = w /\
        is_let_free_expr (simplify_expr_with_path_aux ctx (pc :: pcs) l) = true /\
        incl (collect_free_vars [] (simplify_expr_with_path_aux ctx (pc :: pcs) l))
             (collect_free_vars [] l ++ collect_free_vars [] r)).
      { intros _; apply Pos.eqb_eq in Hwl; repeat split; try assumption;
          [rewrite Hbwl', Hwl; reflexivity
          | intros x Hx; apply in_app_iff; left; exact (Hfvl' x Hx)]. }
      assert (Hr'_ok : w = 1%positive ->
        wt_cert_expr [] (simplify_expr_with_path_aux ctx (pc :: pcs) r) = true /\
        cert_expr_bit_width (simplify_expr_with_path_aux ctx (pc :: pcs) r) = w /\
        is_let_free_expr (simplify_expr_with_path_aux ctx (pc :: pcs) r) = true /\
        incl (collect_free_vars [] (simplify_expr_with_path_aux ctx (pc :: pcs) r))
             (collect_free_vars [] l ++ collect_free_vars [] r)).
      { intros _; apply Pos.eqb_eq in Hwr; repeat split; try assumption;
          [rewrite Hbwr', Hwr; reflexivity
          | intros x Hx; apply in_app_iff; right; exact (Hfvr' x Hx)]. }
      destruct op; try exact Hdefault.
      * match goal with |- context [if ?cond then _ else _] => destruct cond; [| exact Hdefault] end.
        cbn [wt_cert_expr is_let_free_expr cert_expr_bit_width collect_free_vars wf_binop_flags_for].
        rewrite Hwl', Hwr', Hbwl', Hbwr', Hwl, Hwr, Hlfl', Hlfr';
          repeat split; try reflexivity.
        intros x Hx; apply in_app_iff in Hx as [Hx | Hx];
          apply in_app_iff; [left; exact (Hfvl' x Hx) | right; exact (Hfvr' x Hx)].
      * destruct (Pos.eqb w 1%positive) eqn:Ew1; [apply Pos.eqb_eq in Ew1 | exact Hdefault].
        destruct (lookup_path_bool ctx (pc :: pcs) (simplify_expr_with_path_aux ctx (pc :: pcs) l)) as [[|] |],
                 (lookup_path_bool ctx (pc :: pcs) (simplify_expr_with_path_aux ctx (pc :: pcs) r)) as [[|] |];
          repeat match goal with |- context [if ?b then _ else _] => destruct b end;
          first [exact (Hconst1 0%N Ew1) | exact (Hconst1 1%N Ew1) | exact (Hl'_ok Ew1) | exact (Hr'_ok Ew1) | exact Hdefault].
      * destruct (Pos.eqb w 1%positive && negb (cbf_disjoint fl)) eqn:Ew1;
          [apply andb_true_iff in Ew1 as [Ew1 _]; apply Pos.eqb_eq in Ew1 | exact Hdefault].
        destruct (lookup_path_bool ctx (pc :: pcs) (simplify_expr_with_path_aux ctx (pc :: pcs) l)) as [[|] |],
                 (lookup_path_bool ctx (pc :: pcs) (simplify_expr_with_path_aux ctx (pc :: pcs) r)) as [[|] |];
          repeat match goal with |- context [if ?b then _ else _] => destruct b end;
          first [exact (Hconst1 0%N Ew1) | exact (Hconst1 1%N Ew1) | exact (Hl'_ok Ew1) | exact (Hr'_ok Ew1) | exact Hdefault].
    + cbn [wt_cert_expr is_let_free_expr cert_expr_bit_width collect_free_vars] in *.
      rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
      destruct Hwt as (((Hwtl & Hwtr) & Hwl) & Hwr);
        destruct Hlf as [Hlfl Hlfr].
      destruct (IHl Hwtl Hlfl) as (Hwl' & Hbwl' & Hlfl' & Hfvl').
      destruct (IHr Hwtr Hlfr) as (Hwr' & Hbwr' & Hlfr' & Hfvr').
      rewrite Hwl', Hwr', Hbwl', Hbwr', Hwl, Hwr, Hlfl', Hlfr';
        repeat split; try reflexivity.
      intros x Hx; apply in_app_iff in Hx as [Hx | Hx];
        apply in_app_iff; [left; exact (Hfvl' x Hx) | right; exact (Hfvr' x Hx)].
    + cbn [wt_cert_expr is_let_free_expr cert_expr_bit_width collect_free_vars] in *.
      rewrite !andb_true_iff in Hwt; destruct Hwt as ((Hk & Hwto) & Hwo).
      destruct (IHo Hwto Hlf) as (Hwo' & Hbwo' & Hlfo' & Hfvo').
      rewrite Hk, Hwo', Hbwo', Hwo, Hlfo'; repeat split; try reflexivity; exact Hfvo'.
    + cbn [wt_cert_expr is_let_free_expr cert_expr_bit_width collect_free_vars] in *.
      rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf.
      destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hwc) & Hwtb) & Hwf).
      destruct Hlf as ([Hlfc Hlft] & Hlff).
      apply Pos.eqb_eq in Hwtb; apply Pos.eqb_eq in Hwf.
      destruct (IHc Hwtc Hlfc) as (Hwc' & Hbwc' & Hlfc' & Hfvc').
      destruct (IHt Hwtt Hlft) as (Hwt' & Hbwt' & Hlft' & Hfvt').
      destruct (IHf Hwtf Hlff) as (Hwf' & Hbwf' & Hlff' & Hfvf').
      assert (Hsel_def :
        wt_cert_expr [] (CE_Select w
                           (simplify_expr_with_path_aux ctx (pc :: pcs) c)
                           (simplify_expr_with_path_aux ctx (pc :: pcs) t)
                           (simplify_expr_with_path_aux ctx (pc :: pcs) f)) = true /\
        cert_expr_bit_width (CE_Select w
                               (simplify_expr_with_path_aux ctx (pc :: pcs) c)
                               (simplify_expr_with_path_aux ctx (pc :: pcs) t)
                               (simplify_expr_with_path_aux ctx (pc :: pcs) f)) = w /\
        is_let_free_expr (CE_Select w
                            (simplify_expr_with_path_aux ctx (pc :: pcs) c)
                            (simplify_expr_with_path_aux ctx (pc :: pcs) t)
                            (simplify_expr_with_path_aux ctx (pc :: pcs) f)) = true /\
        incl (collect_free_vars [] (CE_Select w
                                      (simplify_expr_with_path_aux ctx (pc :: pcs) c)
                                      (simplify_expr_with_path_aux ctx (pc :: pcs) t)
                                      (simplify_expr_with_path_aux ctx (pc :: pcs) f)))
             (collect_free_vars [] c ++ collect_free_vars [] t ++ collect_free_vars [] f)).
      { cbn [wt_cert_expr is_let_free_expr cert_expr_bit_width collect_free_vars].
        rewrite Hwc', Hwt', Hwf', Hbwc', Hbwt', Hbwf', Hwc, Hwtb, Hwf, !Pos.eqb_refl, Hlfc', Hlft', Hlff'.
        repeat split; try reflexivity.
        intros x Hx; apply in_app_iff in Hx as [Hx | Hx]; apply in_app_iff.
        - left; exact (Hfvc' x Hx).
        - right; apply in_app_iff in Hx as [Hx | Hx]; apply in_app_iff;
            [left; exact (Hfvt' x Hx) | right; exact (Hfvf' x Hx)]. }
      assert (Ht'_ok :
        wt_cert_expr [] (simplify_expr_with_path_aux ctx (pc :: pcs) t) = true /\
        cert_expr_bit_width (simplify_expr_with_path_aux ctx (pc :: pcs) t) = w /\
        is_let_free_expr (simplify_expr_with_path_aux ctx (pc :: pcs) t) = true /\
        incl (collect_free_vars [] (simplify_expr_with_path_aux ctx (pc :: pcs) t))
             (collect_free_vars [] c ++ collect_free_vars [] t ++ collect_free_vars [] f)).
      { repeat split; [exact Hwt' | rewrite Hbwt', Hwtb; reflexivity | exact Hlft' |].
        intros x Hx; apply in_app_iff; right; apply in_app_iff; left; exact (Hfvt' x Hx). }
      assert (Hf'_ok :
        wt_cert_expr [] (simplify_expr_with_path_aux ctx (pc :: pcs) f) = true /\
        cert_expr_bit_width (simplify_expr_with_path_aux ctx (pc :: pcs) f) = w /\
        is_let_free_expr (simplify_expr_with_path_aux ctx (pc :: pcs) f) = true /\
        incl (collect_free_vars [] (simplify_expr_with_path_aux ctx (pc :: pcs) f))
             (collect_free_vars [] c ++ collect_free_vars [] t ++ collect_free_vars [] f)).
      { repeat split; [exact Hwf' | rewrite Hbwf', Hwf; reflexivity | exact Hlff' |].
        intros x Hx; apply in_app_iff; right; apply in_app_iff; right; exact (Hfvf' x Hx). }
      destruct (lookup_path_bool ctx (pc :: pcs) (simplify_expr_with_path_aux ctx (pc :: pcs) c)) as [[|] |].
      * destruct (ub_free_expr (simplify_expr_with_path_aux ctx (pc :: pcs) f)); [exact Ht'_ok | exact Hsel_def].
      * destruct (ub_free_expr (simplify_expr_with_path_aux ctx (pc :: pcs) t)); [exact Hf'_ok | exact Hsel_def].
      * destruct (simplify_select_signed_minmax (pc :: pcs) w
                    (simplify_expr_with_path_aux ctx (pc :: pcs) c)
                    (simplify_expr_with_path_aux ctx (pc :: pcs) t)
                    (simplify_expr_with_path_aux ctx (pc :: pcs) f)) as [res |] eqn:Hsm.
        -- destruct (simplify_select_signed_minmax_inv _ _ _ _ _ _ Hsm) as [-> | ->];
             [exact Ht'_ok | exact Hf'_ok].
        -- exact Hsel_def.
Qed.

Lemma cert_eou_bind_equiv {Pa : Params} :
  forall (m1 m2 : EOU (@dvalue Pa)) (k1 k2 : @dvalue Pa -> EOU (@dvalue Pa)),
    equiv_eou_dvalue m1 m2 ->
    (forall v, equiv_eou_dvalue (k1 v) (k2 v)) ->
    equiv_eou_dvalue (eou_bind m1 k1) (eou_bind m2 k2).
Proof.
  intros m1 m2 k1 k2 Hm Hk.
  destruct m1, m2; cbn in *; try contradiction; trivial; subst; try reflexivity; apply Hk.
Qed.

Lemma path_safe_nonpoison_i1_sound {Pa : Params} :
  forall allowed ctx path_ctx x (penv : param_env Pa) foracle,
    wt_cert_expr [] x = true ->
    cert_expr_bit_width x = 1%positive ->
    incl (collect_free_vars [] x) allowed ->
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv foracle ctx ->
    path_ctx_holds allowed penv foracle path_ctx ->
    path_safe_nonpoison_i1 ctx path_ctx x = true ->
    exists ix : @Integers.bit_int 1%positive,
      eval_closed_cert_expr penv foracle x = raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive ix)).
Proof.
  intros allowed ctx path_ctx x penv foracle Hwt Hbw Hfv Hpenv Hctx Hph Hsn.
  unfold path_safe_nonpoison_i1 in Hsn.
  destruct (lookup_path_bool ctx path_ctx x) as [bx |] eqn:Elk.
  - destruct (lookup_path_bool_sound allowed ctx path_ctx x penv foracle bx Hpenv Hctx Hph Hfv Elk)
      as [ix [Ex _]]; exists ix; exact Ex.
  - apply andb_true_iff in Hsn as [Hub Hnp].
    assert (Hpx : wf_param_env_for (collect_free_vars [] x) penv)
      by (intros z wz Hz; exact (Hpenv z wz (Hfv (z, wz) Hz))).
    destruct (ub_free_expr_eval_ret x [] penv [] foracle Hub Hwt wf_let_val_env_nil Hpx)
      as [vx [Evx Hwfx]].
    pose proof (expr_non_poison_under_ctx_sound ctx x penv foracle vx Hnp Hwt Evx Hctx) as Hnpx.
    rewrite Hbw in Hwfx; destruct Hwfx as [Habs | [ix ->]];
      [contradiction Hnpx | exists ix; exact Evx].
Qed.

Lemma simplify_expr_with_path_eval {Pa : Params} :
  forall allowed ctx path_ctx e (penv : param_env Pa) foracle,
    wt_cert_expr [] e = true ->
    is_let_free_expr e = true ->
    incl (collect_free_vars [] e) allowed ->
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv foracle ctx ->
    path_ctx_holds allowed penv foracle path_ctx ->
    equiv_eou_dvalue
      (eval_closed_cert_expr penv foracle e)
      (eval_closed_cert_expr penv foracle (simplify_expr_with_path ctx path_ctx e)).
Proof.
  intros allowed ctx path_ctx e penv foracle.
  destruct path_ctx as [| pc pcs].
  - unfold simplify_expr_with_path; intros; apply equiv_eou_dvalue_refl.
  - unfold simplify_expr_with_path.
    induction e as
      [ w v | w | nm w
      | op w fl l IHl r IHr
      | pr ss w l IHl r IHr
      | k fw tw fl o IHo
      | w c IHc t IHt f IHf
      | w o IHo
      | bs body IHbs IHb ] using cert_expr_ind_nested;
      intros Hwt Hlf Hfv Hpenv Hctx Hph; cbn [simplify_expr_with_path_aux];
      try apply equiv_eou_dvalue_refl.
    + cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf, Hfv.
      rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf;
        destruct Hwt as ((((_ & Hwtl) & Hwtr) & Hwl) & Hwr);
        destruct Hlf as [Hlfl Hlfr].
      apply Pos.eqb_eq in Hwl; apply Pos.eqb_eq in Hwr.
      assert (Hfvl : incl (collect_free_vars [] l) allowed)
        by (intros x Hx; apply Hfv, in_app_iff; left; exact Hx).
      assert (Hfvr : incl (collect_free_vars [] r) allowed)
        by (intros x Hx; apply Hfv, in_app_iff; right; exact Hx).
      pose proof (IHl Hwtl Hlfl Hfvl Hpenv Hctx Hph) as EHl.
      pose proof (IHr Hwtr Hlfr Hfvr Hpenv Hctx Hph) as EHr.
      destruct (simplify_expr_with_path_typing ctx (pc :: pcs) l Hwtl Hlfl) as (Hwt_l' & Hbw_l' & _ & Hfv_l').
      destruct (simplify_expr_with_path_typing ctx (pc :: pcs) r Hwtr Hlfr) as (Hwt_r' & Hbw_r' & _ & Hfv_r').
      cbn [simplify_expr_with_path] in Hwt_l', Hbw_l', Hfv_l', Hwt_r', Hbw_r', Hfv_r'.
      set (l' := simplify_expr_with_path_aux ctx (pc :: pcs) l) in *.
      set (r' := simplify_expr_with_path_aux ctx (pc :: pcs) r) in *.
      assert (Hfvl' : incl (collect_free_vars [] l') allowed) by (intros x Hx; exact (Hfvl x (Hfv_l' x Hx))).
      assert (Hfvr' : incl (collect_free_vars [] r') allowed) by (intros x Hx; exact (Hfvr x (Hfv_r' x Hx))).
      assert (Hdefault :
        equiv_eou_dvalue
          (eval_closed_cert_expr penv foracle (CE_BinOp op w fl l r))
          (eval_closed_cert_expr penv foracle (CE_BinOp op w fl l' r'))).
      { unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        apply cert_eou_bind_equiv; [exact EHl | intros vl].
        apply cert_eou_bind_equiv; [exact EHr | intros vr].
        apply equiv_eou_dvalue_refl. }
      destruct op; try exact Hdefault.
      * destruct (cbf_nsw fl && negb (cbf_nuw fl) && negb (cbf_exact fl) && negb (cbf_disjoint fl) &&
                  path_implies_signed_ge_zero (pc :: pcs) l' &&
                  path_implies_signed_ge_zero (pc :: pcs) r') eqn:Estrip; [| exact Hdefault].
        rewrite !andb_true_iff in Estrip.
        destruct Estrip as (((((Hnsw & Hnuw) & Hex) & Hdj) & Hgel) & Hger).
        eapply equiv_eou_dvalue_trans; [exact Hdefault |].
        unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        destruct (eval_cert_expr penv [] foracle l') as [| | | vl'] eqn:El'; cbn [eou_bind];
          try apply equiv_eou_dvalue_refl.
        destruct (eval_cert_expr penv [] foracle r') as [| | | vr'] eqn:Er'; cbn [eou_bind];
          try apply equiv_eou_dvalue_refl.
        pose proof (eval_cert_expr_ret_wf_scalar l' [] penv [] foracle vl' Hwt_l' El') as Hwfl'.
        pose proof (eval_cert_expr_ret_wf_scalar r' [] penv [] foracle vr' Hwt_r' Er') as Hwfr'.
        rewrite Hbw_l', Hwl in Hwfl'; rewrite Hbw_r', Hwr in Hwfr'.
        destruct Hwfl' as [-> | [il ->]];
          [ assert (Hl_p : @eval_iop Pa (cert_to_ibinop CB_Sub fl) (DVALUE_Base DVALUE_Poison) vr' = raise_ret (DVALUE_Base DVALUE_Poison))
              by (destruct Hwfr' as [-> | [ir ->]]; reflexivity);
            assert (Hr_p : @eval_iop Pa (cert_to_ibinop CB_Sub no_binop_flags) (DVALUE_Base DVALUE_Poison) vr' = raise_ret (DVALUE_Base DVALUE_Poison))
              by (destruct Hwfr' as [-> | [ir ->]]; reflexivity);
            rewrite Hl_p, Hr_p; apply equiv_eou_dvalue_refl
          |].
        destruct Hwfr' as [-> | [ir ->]];
          [ assert (Hl_p : @eval_iop Pa (cert_to_ibinop CB_Sub fl) (DVALUE_Base (@DVALUE_I Pa w il)) (DVALUE_Base DVALUE_Poison) = raise_ret (DVALUE_Base DVALUE_Poison))
              by reflexivity;
            assert (Hr_p : @eval_iop Pa (cert_to_ibinop CB_Sub no_binop_flags) (DVALUE_Base (@DVALUE_I Pa w il)) (DVALUE_Base DVALUE_Poison) = raise_ret (DVALUE_Base DVALUE_Poison))
              by reflexivity;
            rewrite Hl_p, Hr_p; apply equiv_eou_dvalue_refl
          |].
        assert (Hpl' : wf_param_env_for (collect_free_vars [] l') penv)
          by (intros z wz Hz; exact (Hpenv z wz (Hfvl' (z, wz) Hz))).
        assert (Hpr' : wf_param_env_for (collect_free_vars [] r') penv)
          by (intros z wz Hz; exact (Hpenv z wz (Hfvr' (z, wz) Hz))).
        pose proof (path_implies_signed_ge_zero_sound allowed (pc :: pcs) l' penv foracle w il
                      Hwt_l' (eq_trans Hbw_l' Hwl) Hpenv Hpl' Hph Hgel El') as Hnonneg_l.
        pose proof (path_implies_signed_ge_zero_sound allowed (pc :: pcs) r' penv foracle w ir
                      Hwt_r' (eq_trans Hbw_r' Hwr) Hpenv Hpr' Hph Hger Er') as Hnonneg_r.
        pose proof (@Integers.signed_range w il) as Hsrl.
        pose proof (@Integers.signed_range w ir) as Hsrr.
        unfold eval_iop; rewrite !eval_iop_integer_base_same_width.
        unfold cert_to_ibinop, eval_int_op, dvp, tdb; cbn - [andb orb].
        apply negb_true_iff in Hnuw; rewrite Hnsw, Hnuw; cbn [andb orb].
        unfold Integers.sub_overflow; rewrite (@Integers.signed_zero w), Z.sub_0_r.
        destruct (Numeric.Rocqlib.zle (@Integers.min_signed w) (@Integers.signed w il - @Integers.signed w ir)%Z);
          [| unfold Integers.min_signed, Integers.max_signed in *; lia].
        destruct (Numeric.Rocqlib.zle (@Integers.signed w il - @Integers.signed w ir)%Z (@Integers.max_signed w));
          [| unfold Integers.min_signed, Integers.max_signed in *; lia].
        cbn [proj_sumbool andb];
          rewrite (@Integers.eq_false w (@Integers.zero w) (@Integers.one w)
                     (fun H => @Integers.one_not_zero w (eq_sym H)));
          cbn; reflexivity.
      * destruct (Pos.eqb w 1%positive) eqn:Ew1;
          [apply Pos.eqb_eq in Ew1; rewrite Ew1 in *; clear Ew1 | exact Hdefault].
        rewrite Hwl in Hbw_l'; rewrite Hwr in Hbw_r'.
        destruct (lookup_path_bool ctx (pc :: pcs) l') as [[|] |] eqn:El_k,
                 (lookup_path_bool ctx (pc :: pcs) r') as [[|] |] eqn:Er_k.
        -- destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) l' penv foracle true Hpenv Hctx Hph Hfvl' El_k)
             as [il [El' Eil]].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) r' penv foracle true Hpenv Hctx Hph Hfvr' Er_k)
             as [ir [Er' Eir]].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite El', Er'; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width;
             unfold cert_to_ibinop, eval_int_op; cbn [mand VIntVMemInt VInt_Bounded];
             pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil;
             pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir;
             subst il ir; vm_compute; reflexivity.
        -- destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) l' penv foracle true Hpenv Hctx Hph Hfvl' El_k)
             as [il [El' Eil]].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) r' penv foracle false Hpenv Hctx Hph Hfvr' Er_k)
             as [ir [Er' Eir]].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           destruct (path_safe_nonpoison_i1 ctx (pc :: pcs) l') eqn:Esn; [| exact (equiv_eou_dvalue_refl _)].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite El', Er'; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width;
             unfold cert_to_ibinop, eval_int_op; cbn [mand VIntVMemInt VInt_Bounded];
             pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil;
             pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir;
             subst il ir; vm_compute; reflexivity.
        -- destruct (ub_free_expr r') eqn:Eubr; [| eapply equiv_eou_dvalue_trans; [exact Hdefault | apply equiv_eou_dvalue_refl]].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) l' penv foracle true Hpenv Hctx Hph Hfvl' El_k)
             as [il [El' Eil]].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite El'; cbn [eou_bind].
           assert (Hpr' : wf_param_env_for (collect_free_vars [] r') penv)
             by (intros z wz Hz; exact (Hpenv z wz (Hfvr' (z, wz) Hz))).
           destruct (ub_free_expr_eval_ret r' [] penv [] foracle Eubr Hwt_r' wf_let_val_env_nil Hpr')
             as [vr' [Er' Hwfr']].
           rewrite Er'; cbn [eou_bind]; rewrite Hbw_r' in Hwfr'.
           pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil; subst il.
           destruct Hwfr' as [-> | [ir ->]].
           ++ assert (Hp_iop : @eval_iop Pa (cert_to_ibinop CB_And fl)
                                 (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
                                 (DVALUE_Base DVALUE_Poison) =
                               raise_ret (DVALUE_Base DVALUE_Poison)) by reflexivity.
              rewrite Hp_iop; apply equiv_eou_dvalue_refl.
           ++ unfold eval_iop; rewrite eval_iop_integer_base_same_width;
                unfold cert_to_ibinop, eval_int_op; cbn [mand VIntVMemInt VInt_Bounded].
              destruct ((@Integers.unsigned 1%positive ir =? 1)%Z) eqn:Eir;
                pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir; subst ir; vm_compute; reflexivity.
        -- destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) l' penv foracle false Hpenv Hctx Hph Hfvl' El_k)
             as [il [El' Eil]].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) r' penv foracle true Hpenv Hctx Hph Hfvr' Er_k)
             as [ir [Er' Eir]].
           destruct (path_safe_nonpoison_i1 ctx (pc :: pcs) r'); [| exact Hdefault].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite El', Er'; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width;
             unfold cert_to_ibinop, eval_int_op; cbn [mand VIntVMemInt VInt_Bounded];
             pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil;
             pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir;
             subst il ir; vm_compute; reflexivity.
        -- destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) l' penv foracle false Hpenv Hctx Hph Hfvl' El_k)
             as [il [El' Eil]].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) r' penv foracle false Hpenv Hctx Hph Hfvr' Er_k)
             as [ir [Er' Eir]].
           destruct (path_safe_nonpoison_i1 ctx (pc :: pcs) r'); [| exact Hdefault].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite El', Er'; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width;
             unfold cert_to_ibinop, eval_int_op; cbn [mand VIntVMemInt VInt_Bounded];
             pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil;
             pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir;
             subst il ir; vm_compute; reflexivity.
        -- destruct (path_safe_nonpoison_i1 ctx (pc :: pcs) r') eqn:Esn; [| exact Hdefault].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) l' penv foracle false Hpenv Hctx Hph Hfvl' El_k)
             as [il [El' Eil]].
           destruct (path_safe_nonpoison_i1_sound allowed ctx (pc :: pcs) r' penv foracle
                       Hwt_r' Hbw_r' Hfvr' Hpenv Hctx Hph Esn) as [ir Er'].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite El', Er'; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width;
             unfold cert_to_ibinop, eval_int_op; cbn [mand VIntVMemInt VInt_Bounded].
           pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil; subst il.
           destruct ((@Integers.unsigned 1%positive ir =? 1)%Z) eqn:Eir;
             pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir; subst ir; vm_compute; reflexivity.
        -- destruct (ub_free_expr l') eqn:Eubl; [| exact Hdefault].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) r' penv foracle true Hpenv Hctx Hph Hfvr' Er_k)
             as [ir [Er' Eir]].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Er'.
           assert (Hpl' : wf_param_env_for (collect_free_vars [] l') penv)
             by (intros z wz Hz; exact (Hpenv z wz (Hfvl' (z, wz) Hz))).
           destruct (ub_free_expr_eval_ret l' [] penv [] foracle Eubl Hwt_l' wf_let_val_env_nil Hpl')
             as [vl' [El' Hwfl']].
           rewrite El'; cbn [eou_bind]; rewrite Hbw_l' in Hwfl'.
           pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir; subst ir.
           destruct Hwfl' as [-> | [il ->]].
           ++ assert (Hp_iop : @eval_iop Pa (cert_to_ibinop CB_And fl)
                                 (DVALUE_Base DVALUE_Poison)
                                 (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive))) =
                               raise_ret (DVALUE_Base DVALUE_Poison)) by reflexivity.
              rewrite Hp_iop; apply equiv_eou_dvalue_refl.
           ++ unfold eval_iop; rewrite eval_iop_integer_base_same_width;
                unfold cert_to_ibinop, eval_int_op; cbn [mand VIntVMemInt VInt_Bounded].
              destruct ((@Integers.unsigned 1%positive il =? 1)%Z) eqn:Eil;
                pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil; subst il; vm_compute; reflexivity.
        -- destruct (path_safe_nonpoison_i1 ctx (pc :: pcs) l') eqn:Esn; [| exact Hdefault].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) r' penv foracle false Hpenv Hctx Hph Hfvr' Er_k)
             as [ir [Er' Eir]].
           destruct (path_safe_nonpoison_i1_sound allowed ctx (pc :: pcs) l' penv foracle
                       Hwt_l' Hbw_l' Hfvl' Hpenv Hctx Hph Esn) as [il El'].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite El', Er'; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width;
             unfold cert_to_ibinop, eval_int_op; cbn [mand VIntVMemInt VInt_Bounded].
           pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir; subst ir.
           destruct ((@Integers.unsigned 1%positive il =? 1)%Z) eqn:Eil;
             pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil; subst il; vm_compute; reflexivity.
        -- exact Hdefault.
      * destruct (Pos.eqb w 1%positive && negb (cbf_disjoint fl)) eqn:Ew1;
          [apply andb_true_iff in Ew1 as [Ew1 Hdj]; apply Pos.eqb_eq in Ew1; apply negb_true_iff in Hdj; rewrite Ew1 in *; clear Ew1
          | exact Hdefault].
        rewrite Hwl in Hbw_l'; rewrite Hwr in Hbw_r'.
        destruct (lookup_path_bool ctx (pc :: pcs) l') as [[|] |] eqn:El_k,
                 (lookup_path_bool ctx (pc :: pcs) r') as [[|] |] eqn:Er_k.
        -- destruct (path_safe_nonpoison_i1 ctx (pc :: pcs) r') eqn:Esn; [| exact Hdefault].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) l' penv foracle true Hpenv Hctx Hph Hfvl' El_k)
             as [il [El' Eil]].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) r' penv foracle true Hpenv Hctx Hph Hfvr' Er_k)
             as [ir [Er' Eir]].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite El', Er'; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width;
             unfold cert_to_ibinop, eval_int_op, tdb, dvp; rewrite Hdj; cbn - [andb];
             pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil;
             pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir;
             subst il ir; vm_compute; reflexivity.
        -- destruct (path_safe_nonpoison_i1 ctx (pc :: pcs) r') eqn:Esn; [| exact Hdefault].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) l' penv foracle true Hpenv Hctx Hph Hfvl' El_k)
             as [il [El' Eil]].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) r' penv foracle false Hpenv Hctx Hph Hfvr' Er_k)
             as [ir [Er' Eir]].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite El', Er'; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width;
             unfold cert_to_ibinop, eval_int_op, tdb, dvp; rewrite Hdj; cbn - [andb];
             pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil;
             pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir;
             subst il ir; vm_compute; reflexivity.
        -- destruct (path_safe_nonpoison_i1 ctx (pc :: pcs) r') eqn:Esn; [| exact Hdefault].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) l' penv foracle true Hpenv Hctx Hph Hfvl' El_k)
             as [il [El' Eil]].
           destruct (path_safe_nonpoison_i1_sound allowed ctx (pc :: pcs) r' penv foracle
                       Hwt_r' Hbw_r' Hfvr' Hpenv Hctx Hph Esn) as [ir Er'].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite El', Er'; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width;
             unfold cert_to_ibinop, eval_int_op, tdb, dvp; rewrite Hdj; cbn - [andb].
           pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil; subst il.
           destruct ((@Integers.unsigned 1%positive ir =? 1)%Z) eqn:Eir;
             pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir; subst ir; vm_compute; reflexivity.
        -- destruct (path_safe_nonpoison_i1 ctx (pc :: pcs) l') eqn:Esn; [| exact Hdefault].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) l' penv foracle false Hpenv Hctx Hph Hfvl' El_k)
             as [il [El' Eil]].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) r' penv foracle true Hpenv Hctx Hph Hfvr' Er_k)
             as [ir [Er' Eir]].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite El', Er'; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width;
             unfold cert_to_ibinop, eval_int_op, tdb, dvp; rewrite Hdj; cbn - [andb];
             pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil;
             pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir;
             subst il ir; vm_compute; reflexivity.
        -- destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) l' penv foracle false Hpenv Hctx Hph Hfvl' El_k)
             as [il [El' Eil]].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) r' penv foracle false Hpenv Hctx Hph Hfvr' Er_k)
             as [ir [Er' Eir]].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite El', Er'; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width;
             unfold cert_to_ibinop, eval_int_op, tdb, dvp; rewrite Hdj; cbn - [andb];
             pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil;
             pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir;
             subst il ir; vm_compute; reflexivity.
        -- destruct (ub_free_expr r') eqn:Eubr; [| exact Hdefault].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) l' penv foracle false Hpenv Hctx Hph Hfvl' El_k)
             as [il [El' Eil]].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite El'; cbn [eou_bind].
           assert (Hpr' : wf_param_env_for (collect_free_vars [] r') penv)
             by (intros z wz Hz; exact (Hpenv z wz (Hfvr' (z, wz) Hz))).
           destruct (ub_free_expr_eval_ret r' [] penv [] foracle Eubr Hwt_r' wf_let_val_env_nil Hpr')
             as [vr' [Er' Hwfr']].
           rewrite Er'; cbn [eou_bind]; rewrite Hbw_r' in Hwfr'.
           pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil; subst il.
           destruct Hwfr' as [-> | [ir ->]].
           ++ assert (Hp_iop : @eval_iop Pa (cert_to_ibinop CB_Or fl)
                                 (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.zero 1%positive)))
                                 (DVALUE_Base DVALUE_Poison) =
                               raise_ret (DVALUE_Base DVALUE_Poison)) by reflexivity.
              rewrite Hp_iop; apply equiv_eou_dvalue_refl.
           ++ unfold eval_iop; rewrite eval_iop_integer_base_same_width;
                unfold cert_to_ibinop, eval_int_op, tdb, dvp; rewrite Hdj; cbn - [andb].
              destruct ((@Integers.unsigned 1%positive ir =? 1)%Z) eqn:Eir;
                pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir; subst ir; vm_compute; reflexivity.
        -- destruct (path_safe_nonpoison_i1 ctx (pc :: pcs) l') eqn:Esn; [| exact Hdefault].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) r' penv foracle true Hpenv Hctx Hph Hfvr' Er_k)
             as [ir [Er' Eir]].
           destruct (path_safe_nonpoison_i1_sound allowed ctx (pc :: pcs) l' penv foracle
                       Hwt_l' Hbw_l' Hfvl' Hpenv Hctx Hph Esn) as [il El'].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite El', Er'; cbn [eou_bind].
           unfold eval_iop; rewrite eval_iop_integer_base_same_width;
             unfold cert_to_ibinop, eval_int_op, tdb, dvp; rewrite Hdj; cbn - [andb].
           pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir; subst ir.
           destruct ((@Integers.unsigned 1%positive il =? 1)%Z) eqn:Eil;
             pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil; subst il; vm_compute; reflexivity.
        -- destruct (ub_free_expr l') eqn:Eubl; [| exact Hdefault].
           destruct (lookup_path_bool_sound allowed ctx (pc :: pcs) r' penv foracle false Hpenv Hctx Hph Hfvr' Er_k)
             as [ir [Er' Eir]].
           eapply equiv_eou_dvalue_trans; [exact Hdefault |].
           unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Er'.
           assert (Hpl' : wf_param_env_for (collect_free_vars [] l') penv)
             by (intros z wz Hz; exact (Hpenv z wz (Hfvl' (z, wz) Hz))).
           destruct (ub_free_expr_eval_ret l' [] penv [] foracle Eubl Hwt_l' wf_let_val_env_nil Hpl')
             as [vl' [El' Hwfl']].
           rewrite El'; cbn [eou_bind]; rewrite Hbw_l' in Hwfl'.
           pose proof (alg_bit_int_1_cases ir) as Hir; rewrite Eir in Hir; subst ir.
           destruct Hwfl' as [-> | [il ->]].
           ++ assert (Hp_iop : @eval_iop Pa (cert_to_ibinop CB_Or fl)
                                 (DVALUE_Base DVALUE_Poison)
                                 (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.zero 1%positive))) =
                               raise_ret (DVALUE_Base DVALUE_Poison)) by reflexivity.
              rewrite Hp_iop; apply equiv_eou_dvalue_refl.
           ++ unfold eval_iop; rewrite eval_iop_integer_base_same_width;
                unfold cert_to_ibinop, eval_int_op, tdb, dvp; rewrite Hdj; cbn - [andb].
              destruct ((@Integers.unsigned 1%positive il =? 1)%Z) eqn:Eil;
                pose proof (alg_bit_int_1_cases il) as Hil; rewrite Eil in Hil; subst il; vm_compute; reflexivity.
        -- exact Hdefault.
    + cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf, Hfv.
      rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf;
        destruct Hwt as (((Hwtl & Hwtr) & _) & _);
        destruct Hlf as [Hlfl Hlfr].
      assert (Hfvl : incl (collect_free_vars [] l) allowed)
        by (intros x Hx; apply Hfv, in_app_iff; left; exact Hx).
      assert (Hfvr : incl (collect_free_vars [] r) allowed)
        by (intros x Hx; apply Hfv, in_app_iff; right; exact Hx).
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
      apply cert_eou_bind_equiv; [exact (IHl Hwtl Hlfl Hfvl Hpenv Hctx Hph) | intros vl].
      apply cert_eou_bind_equiv; [exact (IHr Hwtr Hlfr Hfvr Hpenv Hctx Hph) | intros vr].
      apply equiv_eou_dvalue_refl.
    + cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt.
      rewrite !andb_true_iff in Hwt; destruct Hwt as ((_ & Hwto) & _).
      unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
      apply cert_eou_bind_equiv; [exact (IHo Hwto Hlf Hfv Hpenv Hctx Hph) | intros vo].
      apply equiv_eou_dvalue_refl.
    + cbn [wt_cert_expr is_let_free_expr collect_free_vars] in Hwt, Hlf, Hfv.
      rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf;
        destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & _) & Hwtb) & Hwf);
        destruct Hlf as ([Hlfc Hlft] & Hlff).
      apply Pos.eqb_eq in Hwtb; apply Pos.eqb_eq in Hwf.
      assert (Hfvc : incl (collect_free_vars [] c) allowed)
        by (intros x Hx; apply Hfv, in_app_iff; left; exact Hx).
      assert (Hfvt : incl (collect_free_vars [] t) allowed)
        by (intros x Hx; apply Hfv, in_app_iff; right; apply in_app_iff; left; exact Hx).
      assert (Hfvf : incl (collect_free_vars [] f) allowed)
        by (intros x Hx; apply Hfv, in_app_iff; right; apply in_app_iff; right; exact Hx).
      pose proof (IHc Hwtc Hlfc Hfvc Hpenv Hctx Hph) as EHc.
      pose proof (IHt Hwtt Hlft Hfvt Hpenv Hctx Hph) as EHt.
      pose proof (IHf Hwtf Hlff Hfvf Hpenv Hctx Hph) as EHf.
      destruct (simplify_expr_with_path_typing ctx (pc :: pcs) c Hwtc Hlfc) as (Hwt_c' & _ & _ & Hfv_c').
      destruct (simplify_expr_with_path_typing ctx (pc :: pcs) t Hwtt Hlft) as (Hwt_t' & Hbw_t' & _ & Hfv_t').
      destruct (simplify_expr_with_path_typing ctx (pc :: pcs) f Hwtf Hlff) as (Hwt_f' & Hbw_f' & _ & Hfv_f').
      cbn [simplify_expr_with_path] in Hwt_c', Hfv_c', Hwt_t', Hbw_t', Hfv_t', Hwt_f', Hbw_f', Hfv_f'.
      assert (Hfvc' : incl (collect_free_vars [] (simplify_expr_with_path_aux ctx (pc :: pcs) c)) allowed)
        by (intros x Hx; exact (Hfvc x (Hfv_c' x Hx))).
      assert (Hsel_def :
        equiv_eou_dvalue
          (eval_closed_cert_expr penv foracle (CE_Select w c t f))
          (eval_closed_cert_expr penv foracle
             (CE_Select w
                (simplify_expr_with_path_aux ctx (pc :: pcs) c)
                (simplify_expr_with_path_aux ctx (pc :: pcs) t)
                (simplify_expr_with_path_aux ctx (pc :: pcs) f)))).
      { unfold eval_closed_cert_expr in *; cbn [eval_cert_expr].
        apply cert_eou_bind_equiv; [exact EHc | intros vc].
        apply cert_eou_bind_equiv; [exact EHt | intros vt].
        apply cert_eou_bind_equiv; [exact EHf | intros vf].
        apply equiv_eou_dvalue_refl. }
      destruct (lookup_path_bool ctx (pc :: pcs) (simplify_expr_with_path_aux ctx (pc :: pcs) c))
        as [[|] |] eqn:Elk.
      * destruct (ub_free_expr (simplify_expr_with_path_aux ctx (pc :: pcs) f)) eqn:Eubf; [| exact Hsel_def].
        destruct (lookup_path_bool_sound allowed ctx (pc :: pcs)
                    (simplify_expr_with_path_aux ctx (pc :: pcs) c) penv foracle true Hpenv Hctx Hph Hfvc' Elk)
          as [cbit [Ec' Ecbit]].
        assert (Hpf' : wf_param_env_for (collect_free_vars [] (simplify_expr_with_path_aux ctx (pc :: pcs) f)) penv)
          by (intros x wx Hx; exact (Hpenv x wx (Hfvf (x, wx) (Hfv_f' (x, wx) Hx)))).
        destruct (ub_free_expr_eval_ret (simplify_expr_with_path_aux ctx (pc :: pcs) f) [] penv [] foracle
                    Eubf Hwt_f' wf_let_val_env_nil Hpf') as [vf' [Ef' _]].
        unfold eval_closed_cert_expr in *; rewrite Ec' in EHc; rewrite Ef' in EHf; cbn [eval_cert_expr].
        destruct (eval_cert_expr penv [] foracle c) as [| | | vc] eqn:Ec; cbn in EHc; try contradiction EHc; subst vc.
        destruct (eval_cert_expr penv [] foracle f) as [| | | vf] eqn:Ef; cbn in EHf; try contradiction EHf; subst vf.
        cbn [eou_bind].
        destruct (eval_cert_expr penv [] foracle t) as [| | | vt] eqn:Et;
          destruct (eval_cert_expr penv [] foracle (simplify_expr_with_path_aux ctx (pc :: pcs) t))
            as [| | | vt'] eqn:Et';
          cbn in EHt |- *; try contradiction EHt; trivial; try exact EHt.
        subst vt'; cbn [eval_select eval_select_base_dvalue]; rewrite Ecbit; reflexivity.
      * destruct (ub_free_expr (simplify_expr_with_path_aux ctx (pc :: pcs) t)) eqn:Eubt; [| exact Hsel_def].
        destruct (lookup_path_bool_sound allowed ctx (pc :: pcs)
                    (simplify_expr_with_path_aux ctx (pc :: pcs) c) penv foracle false Hpenv Hctx Hph Hfvc' Elk)
          as [cbit [Ec' Ecbit]].
        assert (Hpt' : wf_param_env_for (collect_free_vars [] (simplify_expr_with_path_aux ctx (pc :: pcs) t)) penv)
          by (intros x wx Hx; exact (Hpenv x wx (Hfvt (x, wx) (Hfv_t' (x, wx) Hx)))).
        destruct (ub_free_expr_eval_ret (simplify_expr_with_path_aux ctx (pc :: pcs) t) [] penv [] foracle
                    Eubt Hwt_t' wf_let_val_env_nil Hpt') as [vt' [Et' _]].
        unfold eval_closed_cert_expr in *; rewrite Ec' in EHc; rewrite Et' in EHt; cbn [eval_cert_expr].
        destruct (eval_cert_expr penv [] foracle c) as [| | | vc] eqn:Ec; cbn in EHc; try contradiction EHc; subst vc.
        destruct (eval_cert_expr penv [] foracle t) as [| | | vt] eqn:Et; cbn in EHt; try contradiction EHt; subst vt.
        cbn [eou_bind].
        destruct (eval_cert_expr penv [] foracle f) as [| | | vf] eqn:Ef;
          destruct (eval_cert_expr penv [] foracle (simplify_expr_with_path_aux ctx (pc :: pcs) f))
            as [| | | vf'] eqn:Ef';
          cbn in EHf |- *; try contradiction EHf; trivial; try exact EHf.
        subst vf'; cbn [eval_select eval_select_base_dvalue]; rewrite Ecbit; reflexivity.
      * destruct (simplify_select_signed_minmax (pc :: pcs) w
                    (simplify_expr_with_path_aux ctx (pc :: pcs) c)
                    (simplify_expr_with_path_aux ctx (pc :: pcs) t)
                    (simplify_expr_with_path_aux ctx (pc :: pcs) f)) as [res |] eqn:Hsm;
          [| exact Hsel_def].
        eapply equiv_eou_dvalue_trans; [exact Hsel_def |].
        rewrite (simplify_select_signed_minmax_eval allowed (pc :: pcs) w _ _ _ res penv foracle
                   Hwt_c' Hwt_t' Hwt_f' (eq_trans Hbw_t' Hwtb) (eq_trans Hbw_f' Hwf) Hph Hsm).
        apply equiv_eou_dvalue_refl.
Qed.

Fixpoint check_dag_refines_cert_path
  (fuel : nat)
  (allowed : list (string * positive))
  (ctx : ub_ctx)
  (path_ctx : list (cert_expr * bool))
  (ro : return_obligation)
  (opt_pf : option (list lrat_step))
  (src_evals src_br_conds : list cert_expr)
  (d_src d_tgt : cfg_dag) {struct fuel} : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if spine_is_unreachable d_src || ctx_has_unreachable ctx then true
      else
        match as_block_assume d_src with
        | Some (uas, next_s) =>
            match check_ub_assumptions_list allowed src_evals src_br_conds next_s ctx uas with
            | Some ctx' =>
                check_dag_refines_cert_path fuel' allowed ctx' path_ctx ro opt_pf
                  src_evals src_br_conds next_s d_tgt
            | None => false
            end
        | None =>
            match as_block_assume d_tgt with
            | Some (uas_t, next_t) =>
                match uas_t with
                | [] =>
                    check_dag_refines_cert_path fuel' allowed ctx path_ctx ro opt_pf
                      src_evals src_br_conds d_src next_t
                | _ :: _ => false
                end
            | None =>
                if check_scalar_dag_via_ro allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt
                then true
                else
                  let opt_known_tgt_step :=
                    match d_tgt with
                    | CD_Branch ct tb ft =>
                        match lookup_path_bool ctx path_ctx (simplify_expr_with_path ctx path_ctx ct) with
                        | Some b => Some (if b then tb else ft)
                        | None => None
                        end
                    | _ => None
                    end in
                  match opt_known_tgt_step with
                  | Some next_tgt =>
                      check_dag_refines_cert_path fuel' allowed ctx path_ctx ro opt_pf
                        src_evals src_br_conds d_src next_tgt
                  | None =>
                      match d_src with
                      | CD_Unreachable => true
                      | CD_BlockAssume _ _ => false
                      | CD_Eval _ se next_s =>
                          check_dag_refines_cert_path fuel' allowed ctx path_ctx ro opt_pf
                            (se :: src_evals) src_br_conds next_s d_tgt
                      | CD_Branch cs ts fs =>
                          let ctx_t := extract_branch_cond_assumptions true cs ++ ctx in
                          let ctx_f := extract_branch_cond_assumptions false cs ++ ctx in
                          if spine_is_unreachable fs then
                            check_dag_refines_cert_path fuel' allowed ctx_t ((cs, true) :: path_ctx) ro opt_pf
                              (cs :: src_evals) (cs :: src_br_conds) ts d_tgt
                          else if spine_is_unreachable ts then
                            check_dag_refines_cert_path fuel' allowed ctx_f ((cs, false) :: path_ctx) ro opt_pf
                              (cs :: src_evals) (cs :: src_br_conds) fs d_tgt
                          else
                            match d_tgt with
                            | CD_Eval _ te next_t =>
                                expr_safe_under_src ctx src_evals te &&
                                check_dag_refines_cert_path fuel' allowed ctx path_ctx ro opt_pf
                                  src_evals src_br_conds d_src next_t
                            | CD_Branch ct tb ft =>
                                let ct_s := simplify_expr_with_path ctx path_ctx ct in
                                if check_expr_refines ctx cs ct_s &&
                                   check_dag_refines_cert_path fuel' allowed ctx_t ((cs, true) :: path_ctx) ro opt_pf
                                     (cs :: src_evals) (cs :: src_br_conds) ts tb &&
                                   check_dag_refines_cert_path fuel' allowed ctx_f ((cs, false) :: path_ctx) ro opt_pf
                                     (cs :: src_evals) (cs :: src_br_conds) fs ft
                                then true
                                else
                                  check_dag_refines_cert_path fuel' allowed ctx_t ((cs, true) :: path_ctx) ro opt_pf
                                    (cs :: src_evals) (cs :: src_br_conds) ts d_tgt &&
                                  check_dag_refines_cert_path fuel' allowed ctx_f ((cs, false) :: path_ctx) ro opt_pf
                                    (cs :: src_evals) (cs :: src_br_conds) fs d_tgt
                            | CD_RetScalar _ _ | CD_RetVoid =>
                                check_dag_refines_cert_path fuel' allowed ctx_t ((cs, true) :: path_ctx) ro opt_pf
                                  (cs :: src_evals) (cs :: src_br_conds) ts d_tgt &&
                                check_dag_refines_cert_path fuel' allowed ctx_f ((cs, false) :: path_ctx) ro opt_pf
                                  (cs :: src_evals) (cs :: src_br_conds) fs d_tgt
                            | _ => false
                            end
                      | CD_RetVoid =>
                          match ro with
                          | RO_VoidEquiv => tgt_dag_void_safe ctx src_evals src_br_conds d_tgt
                          | _ => false
                          end
                      | CD_RetScalar ws es =>
                          match d_tgt with
                          | CD_Eval _ te next_t =>
                              expr_safe_under_src ctx src_evals te &&
                              check_dag_refines_cert_path fuel' allowed ctx path_ctx ro opt_pf
                                src_evals src_br_conds d_src next_t
                          | CD_RetScalar wt et =>
                              match ro with
                              | RO_ScalarRefines w _ _ _ =>
                                  Pos.eqb ws w && Pos.eqb wt w &&
                                  check_expr_refines_with_lrat ctx es (simplify_expr_with_path ctx path_ctx et) opt_pf
                              | _ => false
                              end
                          | _ => false
                          end
                      end
                  end
            end
        end
  end.

Lemma check_dag_refines_cert_path_sound {Pa : Params} :
  forall fuel allowed ctx path_ctx ro opt_pf src_evals src_br_conds d_src d_tgt
         (penv : param_env Pa) foracle dv_src,
    wf_cfg_dag allowed d_src = true ->
    wf_cfg_dag allowed d_tgt = true ->
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv foracle ctx ->
    path_ctx_holds allowed penv foracle path_ctx ->
    (forall big, In big src_evals ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed) ->
    (forall big, In big src_evals ->
      exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv) ->
    (forall c, In c src_br_conds ->
      exists cbit : @Integers.bit_int 1,
        eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))) ->
    check_dag_refines_cert_path fuel allowed ctx path_ctx ro opt_pf src_evals src_br_conds d_src d_tgt = true ->
    eval_cfg_dag penv foracle d_src = DO_Ret dv_src ->
    exists dv_tgt,
      eval_cfg_dag penv foracle d_tgt = DO_Ret dv_tgt /\
      dvalue_refines dv_src dv_tgt.
Proof.
  induction fuel as [| fuel' IH];
    intros allowed ctx path_ctx ro opt_pf src_evals src_br_conds d_src d_tgt penv foracle dv_src
           Hwfs Hwft Hpenv Hctx Hph Hsrc_wf Hsrc_ret Hbr_ret Hchk Hevs;
    cbn [check_dag_refines_cert_path] in Hchk; [discriminate Hchk |].
  destruct (spine_is_unreachable d_src || ctx_has_unreachable ctx) eqn:Eunr.
  { exfalso; apply orb_true_iff in Eunr as [Hs_unr | Hc_unr].
    - rewrite (spine_is_unreachable_sound penv foracle d_src Hs_unr) in Hevs; discriminate Hevs.
    - exact (ctx_has_unreachable_sound penv foracle ctx Hc_unr Hctx). }
  destruct (as_block_assume d_src) as [[uas next_s] |] eqn:Eba_s.
  { pose proof (as_block_assume_some_inv d_src uas next_s Eba_s) as ->.
    cbn [wf_cfg_dag eval_cfg_dag] in Hwfs, Hevs.
    destruct (check_ub_assumptions_list allowed src_evals src_br_conds next_s ctx uas)
      as [ctx' |] eqn:Ectx'; [| discriminate Hchk].
    pose proof (check_ub_assumptions_list_sound uas allowed src_evals src_br_conds next_s ctx ctx'
                  penv foracle dv_src Hwfs Hpenv Hsrc_wf Hsrc_ret Hbr_ret Hevs Hctx Ectx') as Hctx'.
    exact (IH allowed ctx' path_ctx ro opt_pf src_evals src_br_conds next_s d_tgt
             penv foracle dv_src Hwfs Hwft Hpenv Hctx' Hph Hsrc_wf Hsrc_ret Hbr_ret Hchk Hevs). }
  destruct (as_block_assume d_tgt) as [[uas_t next_t] |] eqn:Eba_t.
  { pose proof (as_block_assume_some_inv d_tgt uas_t next_t Eba_t) as ->.
    destruct uas_t as [| u ur]; [| discriminate Hchk].
    cbn [wf_cfg_dag eval_cfg_dag] in Hwft |- *.
    exact (IH allowed ctx path_ctx ro opt_pf src_evals src_br_conds d_src next_t
             penv foracle dv_src Hwfs Hwft Hpenv Hctx Hph Hsrc_wf Hsrc_ret Hbr_ret Hchk Hevs). }
  destruct (check_scalar_dag_via_ro allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt) eqn:Ero.
  { exact (check_scalar_dag_via_ro_sound allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt
             penv foracle dv_src Hwfs Hwft Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Ero Hevs). }
  cbn zeta in Hchk.
  match type of Hchk with
  | match ?ok with Some _ => _ | None => _ end = true =>
      destruct ok as [next_tgt |] eqn:Eknown
  end.
  { destruct d_tgt as [| | | | | ct tb ft]; try discriminate Eknown.
    cbn [wf_cfg_dag] in Hwft; rewrite !andb_true_iff in Hwft.
    destruct Hwft as (((((Hwtct & _) & Hlfct) & Hfvct) & Hwftb) & Hwfft).
    destruct (lookup_path_bool ctx path_ctx (simplify_expr_with_path ctx path_ctx ct)) as [bt |] eqn:Elk;
      [| discriminate Eknown].
    inversion Eknown; subst next_tgt; clear Eknown.
    pose proof (vars_subset_b_incl _ _ Hfvct) as Hincl_ct.
    destruct (simplify_expr_with_path_typing ctx path_ctx ct Hwtct Hlfct) as (_ & _ & _ & Hfv_cts).
    assert (Hfv_cts_a : incl (collect_free_vars [] (simplify_expr_with_path ctx path_ctx ct)) allowed)
      by (intros x Hx; exact (Hincl_ct x (Hfv_cts x Hx))).
    destruct (lookup_path_bool_sound allowed ctx path_ctx (simplify_expr_with_path ctx path_ctx ct)
                penv foracle bt Hpenv Hctx Hph Hfv_cts_a Elk) as [cbit [Ects Ecbit]].
    pose proof (simplify_expr_with_path_eval allowed ctx path_ctx ct penv foracle
                  Hwtct Hlfct Hincl_ct Hpenv Hctx Hph) as Heq_ct.
    rewrite Ects in Heq_ct.
    destruct (eval_closed_cert_expr penv foracle ct) as [| | | dvct] eqn:Ect;
      cbn in Heq_ct; try contradiction Heq_ct; subst dvct.
    cbn [eval_cfg_dag]; rewrite Ect; cbn [eval_select_base_dvalue]; rewrite Ecbit.
    destruct bt;
      [exact (IH allowed ctx path_ctx ro opt_pf src_evals src_br_conds d_src tb
                penv foracle dv_src Hwfs Hwftb Hpenv Hctx Hph Hsrc_wf Hsrc_ret Hbr_ret Hchk Hevs)
      | exact (IH allowed ctx path_ctx ro opt_pf src_evals src_br_conds d_src ft
                penv foracle dv_src Hwfs Hwfft Hpenv Hctx Hph Hsrc_wf Hsrc_ret Hbr_ret Hchk Hevs)]. }
  clear Eknown.
  destruct d_src as [| | ws es | ws se next_s | uas next_s | cs ts fs].
  - discriminate Hevs.
  - (* CD_RetVoid *)
    destruct ro as [| ? ? ? ?]; [| discriminate Hchk].
    cbn [eval_cfg_dag] in Hevs; inversion Hevs; subst dv_src.
    exists NONE; split;
      [exact (tgt_dag_void_safe_sound allowed ctx src_evals src_br_conds d_tgt penv foracle
                Hwft Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hchk)
      | apply dvalue_refines_refl].
  - (* CD_RetScalar *)
    destruct d_tgt as [| | wt et | wt te next_t | uas_t next_t | ct tt ft]; try discriminate Hchk.
    + destruct ro as [| w ? ? ?]; [discriminate Hchk |].
      rewrite !andb_true_iff in Hchk; destruct Hchk as ([_ _] & Href).
      cbn [wf_cfg_dag eval_cfg_dag] in Hwfs, Hwft, Hevs.
      rewrite !andb_true_iff in Hwfs; rewrite !andb_true_iff in Hwft.
      destruct Hwfs as (((_ & _) & _) & Hfvs); destruct Hwft as (((Hwtt & _) & Hlft) & Hfvt).
      pose proof (vars_subset_b_wf_param _ allowed penv Hfvs Hpenv) as Hpes.
      pose proof (vars_subset_b_incl _ _ Hfvt) as Hincl_t.
      destruct (simplify_expr_with_path_typing ctx path_ctx et Hwtt Hlft) as (_ & _ & _ & Hfvt_s).
      pose proof (fun x wx Hx => Hpenv x wx (Hincl_t (x, wx) (Hfvt_s (x, wx) Hx))) as Hpet'.
      destruct (eval_closed_cert_expr penv foracle es) as [| | | dv_s] eqn:Ees; try discriminate Hevs.
      inversion Hevs; subst dv_s.
      pose proof (check_expr_refines_with_lrat_sound ctx es (simplify_expr_with_path ctx path_ctx et)
                    opt_pf penv foracle Href Hpes Hpet' Hctx) as Href_eou.
      rewrite Ees in Href_eou; cbn [refine_eou_dvalue] in Href_eou.
      destruct (eval_closed_cert_expr penv foracle (simplify_expr_with_path ctx path_ctx et))
        as [| | | dv_t] eqn:Eet'; try contradiction Href_eou.
      pose proof (simplify_expr_with_path_eval allowed ctx path_ctx et penv foracle
                    Hwtt Hlft Hincl_t Hpenv Hctx Hph) as Heq_t.
      rewrite Eet' in Heq_t.
      destruct (eval_closed_cert_expr penv foracle et) as [| | | dv_t0] eqn:Eet;
        cbn in Heq_t; try contradiction Heq_t; subst dv_t0.
      exists dv_t; cbn [eval_cfg_dag]; rewrite Eet; split; [reflexivity | exact Href_eou].
    + apply andb_true_iff in Hchk as [Hsafe Hchk'].
      cbn [wf_cfg_dag] in Hwft; rewrite !andb_true_iff in Hwft.
      destruct Hwft as ((((Hwte & _) & _) & Hfve) & Hwfnt).
      pose proof (vars_subset_b_wf_param _ allowed penv Hfve Hpenv) as Hpte.
      destruct (expr_safe_under_src_sound te ctx src_evals penv foracle Hsafe Hwte Hpte Hctx Hsrc_ret)
        as [dve [Ete _]].
      cbn [eval_cfg_dag]; rewrite Ete.
      exact (IH allowed ctx path_ctx ro opt_pf src_evals src_br_conds (CD_RetScalar ws es) next_t
               penv foracle dv_src Hwfs Hwfnt Hpenv Hctx Hph Hsrc_wf Hsrc_ret Hbr_ret Hchk' Hevs).
  - (* CD_Eval on d_src *)
    cbn [wf_cfg_dag eval_cfg_dag] in Hwfs, Hevs; rewrite !andb_true_iff in Hwfs.
    destruct Hwfs as ((((Hwtse & _) & Hlfse) & Hfvse) & Hwfns).
    destruct (eval_closed_cert_expr penv foracle se) as [| | | dvse] eqn:Ese; try discriminate Hevs.
    assert (Hsrc_wf' : forall big, In big (se :: src_evals) ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed).
    { intros big [<- | Hin];
        [exact (conj Hwtse (conj Hlfse (vars_subset_b_incl _ _ Hfvse))) | exact (Hsrc_wf big Hin)]. }
    assert (Hsrc_ret' : forall big, In big (se :: src_evals) ->
      exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv).
    { intros big [<- | Hin]; [exists dvse; exact Ese | exact (Hsrc_ret big Hin)]. }
    exact (IH allowed ctx path_ctx ro opt_pf (se :: src_evals) src_br_conds next_s d_tgt
             penv foracle dv_src Hwfns Hwft Hpenv Hctx Hph Hsrc_wf' Hsrc_ret' Hbr_ret Hchk Hevs).
  - (* CD_BlockAssume impossible since as_block_assume d_src = None *)
    discriminate Eba_s.
  - (* CD_Branch on d_src *)
    cbn zeta in Hchk.
    pose proof Hwfs as Hwfs_all; pose proof Hevs as Hevs_all.
    cbn [wf_cfg_dag eval_cfg_dag] in Hwfs, Hevs; rewrite !andb_true_iff in Hwfs.
    destruct Hwfs as (((((Hwtcs & Hbwcs) & Hlfcs) & Hfvcs) & Hwfts) & Hwffs).
    apply Pos.eqb_eq in Hbwcs.
    destruct (eval_closed_cert_expr penv foracle cs) as [| | | dvcs] eqn:Ecs; try discriminate Hevs.
    destruct dvcs as [dbcs | |]; try discriminate Hevs.
    destruct dbcs as [| wcs cbit | | | | | |]; try discriminate Hevs.
    destruct wcs as [| |]; try discriminate Hevs.
    assert (Hsrc_wf' : forall big, In big (cs :: src_evals) ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed).
    { intros big [<- | Hin];
        [exact (conj Hwtcs (conj Hlfcs (vars_subset_b_incl _ _ Hfvcs))) | exact (Hsrc_wf big Hin)]. }
    assert (Hsrc_ret' : forall big, In big (cs :: src_evals) ->
      exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv).
    { intros big [<- | Hin]; [eexists; exact Ecs | exact (Hsrc_ret big Hin)]. }
    assert (Hbr_ret' : forall c, In c (cs :: src_br_conds) ->
      exists cb0 : @Integers.bit_int 1,
        eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cb0))).
    { intros c [<- | Hin]; [exists cbit; exact Ecs | exact (Hbr_ret c Hin)]. }
    assert (Hph_step : forall b_br, (@Integers.unsigned 1 cbit =? 1)%Z = b_br ->
      path_ctx_holds allowed penv foracle ((cs, b_br) :: path_ctx)).
    { intros b_br Hb_br; constructor; [| exact Hph].
      repeat split; try assumption; [exact (vars_subset_b_incl _ _ Hfvcs) |].
      exists cbit; split; [exact Ecs | exact Hb_br]. }
    destruct (spine_is_unreachable fs) eqn:Eufs.
    + destruct (@Integers.unsigned 1 cbit =? 1)%Z eqn:Ecbit.
      * pose proof (extract_branch_cond_assumptions_sound penv foracle true cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_t.
        exact (IH allowed (extract_branch_cond_assumptions true cs ++ ctx) ((cs, true) :: path_ctx) ro opt_pf
                 (cs :: src_evals) (cs :: src_br_conds) ts d_tgt
                 penv foracle dv_src Hwfts Hwft Hpenv Hctx_t (Hph_step true eq_refl) Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk Hevs).
      * rewrite (spine_is_unreachable_sound penv foracle fs Eufs) in Hevs; discriminate Hevs.
    + destruct (spine_is_unreachable ts) eqn:Euts.
      * destruct (@Integers.unsigned 1 cbit =? 1)%Z eqn:Ecbit.
        -- rewrite (spine_is_unreachable_sound penv foracle ts Euts) in Hevs; discriminate Hevs.
        -- pose proof (extract_branch_cond_assumptions_sound penv foracle false cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_f.
           exact (IH allowed (extract_branch_cond_assumptions false cs ++ ctx) ((cs, false) :: path_ctx) ro opt_pf
                    (cs :: src_evals) (cs :: src_br_conds) fs d_tgt
                    penv foracle dv_src Hwffs Hwft Hpenv Hctx_f (Hph_step false eq_refl) Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk Hevs).
      * destruct d_tgt as [| | wt et | wt te next_t | uas_t next_t | ct tt ft]; try discriminate Hchk.
        -- (* d_tgt = CD_RetVoid *)
           apply andb_true_iff in Hchk as [Hchk_t Hchk_f].
           destruct (@Integers.unsigned 1 cbit =? 1)%Z eqn:Ecbit.
           ++ pose proof (extract_branch_cond_assumptions_sound penv foracle true cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_t.
              exact (IH allowed (extract_branch_cond_assumptions true cs ++ ctx) ((cs, true) :: path_ctx) ro opt_pf
                       (cs :: src_evals) (cs :: src_br_conds) ts CD_RetVoid
                       penv foracle dv_src Hwfts Hwft Hpenv Hctx_t (Hph_step true eq_refl) Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_t Hevs).
           ++ pose proof (extract_branch_cond_assumptions_sound penv foracle false cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_f.
              exact (IH allowed (extract_branch_cond_assumptions false cs ++ ctx) ((cs, false) :: path_ctx) ro opt_pf
                       (cs :: src_evals) (cs :: src_br_conds) fs CD_RetVoid
                       penv foracle dv_src Hwffs Hwft Hpenv Hctx_f (Hph_step false eq_refl) Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_f Hevs).
        -- (* d_tgt = CD_RetScalar wt et *)
           apply andb_true_iff in Hchk as [Hchk_t Hchk_f].
           destruct (@Integers.unsigned 1 cbit =? 1)%Z eqn:Ecbit.
           ++ pose proof (extract_branch_cond_assumptions_sound penv foracle true cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_t.
              exact (IH allowed (extract_branch_cond_assumptions true cs ++ ctx) ((cs, true) :: path_ctx) ro opt_pf
                       (cs :: src_evals) (cs :: src_br_conds) ts (CD_RetScalar wt et)
                       penv foracle dv_src Hwfts Hwft Hpenv Hctx_t (Hph_step true eq_refl) Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_t Hevs).
           ++ pose proof (extract_branch_cond_assumptions_sound penv foracle false cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_f.
              exact (IH allowed (extract_branch_cond_assumptions false cs ++ ctx) ((cs, false) :: path_ctx) ro opt_pf
                       (cs :: src_evals) (cs :: src_br_conds) fs (CD_RetScalar wt et)
                       penv foracle dv_src Hwffs Hwft Hpenv Hctx_f (Hph_step false eq_refl) Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_f Hevs).
        -- (* d_tgt = CD_Eval wt te next_t *)
           apply andb_true_iff in Hchk as [Hsafe Hchk'].
           cbn [wf_cfg_dag] in Hwft; rewrite !andb_true_iff in Hwft.
           destruct Hwft as ((((Hwte & _) & _) & Hfve) & Hwfnt).
           pose proof (vars_subset_b_wf_param _ allowed penv Hfve Hpenv) as Hpte.
           destruct (expr_safe_under_src_sound te ctx src_evals penv foracle Hsafe Hwte Hpte Hctx Hsrc_ret)
             as [dve [Ete _]].
           cbn [eval_cfg_dag]; rewrite Ete.
           exact (IH allowed ctx path_ctx ro opt_pf src_evals src_br_conds (CD_Branch cs ts fs) next_t
                    penv foracle dv_src Hwfs_all Hwfnt Hpenv Hctx Hph Hsrc_wf Hsrc_ret Hbr_ret Hchk' Hevs_all).
        -- (* d_tgt = CD_Branch ct tt ft *)
           cbn zeta in Hchk.
           destruct (check_expr_refines ctx cs (simplify_expr_with_path ctx path_ctx ct) &&
                     check_dag_refines_cert_path fuel' allowed (extract_branch_cond_assumptions true cs ++ ctx)
                       ((cs, true) :: path_ctx) ro opt_pf (cs :: src_evals) (cs :: src_br_conds) ts tt &&
                     check_dag_refines_cert_path fuel' allowed (extract_branch_cond_assumptions false cs ++ ctx)
                       ((cs, false) :: path_ctx) ro opt_pf (cs :: src_evals) (cs :: src_br_conds) fs ft) eqn:Hlock.
           ++ rewrite !andb_true_iff in Hlock; destruct Hlock as ([Hc_ref Hchk_t] & Hchk_f).
              cbn [wf_cfg_dag] in Hwft; rewrite !andb_true_iff in Hwft.
              destruct Hwft as (((((Hwtct & _) & Hlfct) & Hfvct) & Hwftt) & Hwfft).
              pose proof (vars_subset_b_wf_param _ allowed penv Hfvcs Hpenv) as Hpcs.
              pose proof (vars_subset_b_incl _ _ Hfvct) as Hincl_ct.
              destruct (simplify_expr_with_path_typing ctx path_ctx ct Hwtct Hlfct) as (_ & _ & _ & Hfv_cts).
              pose proof (fun x wx Hx => Hpenv x wx (Hincl_ct (x, wx) (Hfv_cts (x, wx) Hx))) as Hpcts.
              pose proof (check_expr_refines_sound ctx cs (simplify_expr_with_path ctx path_ctx ct)
                            penv foracle Hc_ref Hpcs Hpcts Hctx) as Hcref.
              rewrite Ecs in Hcref; cbn [refine_eou_dvalue] in Hcref.
              destruct (eval_closed_cert_expr penv foracle (simplify_expr_with_path ctx path_ctx ct))
                as [| | | dvct] eqn:Ects; try contradiction Hcref.
              destruct Hcref as [Hps | ->]; [discriminate Hps |].
              pose proof (simplify_expr_with_path_eval allowed ctx path_ctx ct penv foracle
                            Hwtct Hlfct Hincl_ct Hpenv Hctx Hph) as Heq_ct.
              rewrite Ects in Heq_ct.
              destruct (eval_closed_cert_expr penv foracle ct) as [| | | dvct0] eqn:Ect;
                cbn in Heq_ct; try contradiction Heq_ct; subst dvct0.
              cbn [eval_cfg_dag]; rewrite Ect.
              destruct (@Integers.unsigned 1 cbit =? 1)%Z eqn:Ecbit.
              ** pose proof (extract_branch_cond_assumptions_sound penv foracle true cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_t.
                 exact (IH allowed (extract_branch_cond_assumptions true cs ++ ctx) ((cs, true) :: path_ctx) ro opt_pf
                          (cs :: src_evals) (cs :: src_br_conds) ts tt
                          penv foracle dv_src Hwfts Hwftt Hpenv Hctx_t (Hph_step true eq_refl) Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_t Hevs).
              ** pose proof (extract_branch_cond_assumptions_sound penv foracle false cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_f.
                 exact (IH allowed (extract_branch_cond_assumptions false cs ++ ctx) ((cs, false) :: path_ctx) ro opt_pf
                          (cs :: src_evals) (cs :: src_br_conds) fs ft
                          penv foracle dv_src Hwffs Hwfft Hpenv Hctx_f (Hph_step false eq_refl) Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_f Hevs).
           ++ apply andb_true_iff in Hchk as [Hchk_t Hchk_f].
              destruct (@Integers.unsigned 1 cbit =? 1)%Z eqn:Ecbit.
              ** pose proof (extract_branch_cond_assumptions_sound penv foracle true cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_t.
                 exact (IH allowed (extract_branch_cond_assumptions true cs ++ ctx) ((cs, true) :: path_ctx) ro opt_pf
                          (cs :: src_evals) (cs :: src_br_conds) ts (CD_Branch ct tt ft)
                          penv foracle dv_src Hwfts Hwft Hpenv Hctx_t (Hph_step true eq_refl) Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_t Hevs).
              ** pose proof (extract_branch_cond_assumptions_sound penv foracle false cs cbit ctx Hwtcs Hlfcs Ecs Ecbit Hctx) as Hctx_f.
                 exact (IH allowed (extract_branch_cond_assumptions false cs ++ ctx) ((cs, false) :: path_ctx) ro opt_pf
                          (cs :: src_evals) (cs :: src_br_conds) fs (CD_Branch ct tt ft)
                          penv foracle dv_src Hwffs Hwft Hpenv Hctx_f (Hph_step false eq_refl) Hsrc_wf' Hsrc_ret' Hbr_ret' Hchk_f Hevs).
Qed.

Definition check_dag_refines_cert
  (fuel : nat)
  (allowed : list (string * positive))
  (ctx : ub_ctx)
  (ro : return_obligation)
  (opt_pf : option (list lrat_step))
  (src_evals src_br_conds : list cert_expr)
  (d_src d_tgt : cfg_dag) : bool :=
  check_dag_refines_cert_path fuel allowed ctx [] ro opt_pf src_evals src_br_conds d_src d_tgt.

Lemma check_dag_refines_cert_sound {Pa : Params} :
  forall fuel allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt
         (penv : param_env Pa) foracle dv_src,
    wf_cfg_dag allowed d_src = true ->
    wf_cfg_dag allowed d_tgt = true ->
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv foracle ctx ->
    (forall big, In big src_evals ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed) ->
    (forall big, In big src_evals ->
      exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv) ->
    (forall c, In c src_br_conds ->
      exists cbit : @Integers.bit_int 1,
        eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))) ->
    check_dag_refines_cert fuel allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt = true ->
    eval_cfg_dag penv foracle d_src = DO_Ret dv_src ->
    exists dv_tgt,
      eval_cfg_dag penv foracle d_tgt = DO_Ret dv_tgt /\
      dvalue_refines dv_src dv_tgt.
Proof.
  intros fuel allowed ctx ro opt_pf src_evals src_br_conds d_src d_tgt penv foracle dv_src
         Hwfs Hwft Hpenv Hctx Hsrc_wf Hsrc_ret Hbr_ret Hchk Hevs.
  exact (check_dag_refines_cert_path_sound fuel allowed ctx [] ro opt_pf src_evals src_br_conds d_src d_tgt
           penv foracle dv_src Hwfs Hwft Hpenv Hctx (Forall_nil _) Hsrc_wf Hsrc_ret Hbr_ret Hchk Hevs).
Qed.

Definition check_return_obligation_valid
  (allowed : list (string * positive))
  (ctx : ub_ctx)
  (ro : return_obligation)
  (opt_pf : option (list lrat_step)) : bool :=
  match ro with
  | RO_VoidEquiv => true
  | RO_ScalarRefines _ se te _ =>
      vars_subset_b (collect_free_vars [] se) allowed &&
      vars_subset_b (collect_free_vars [] te) allowed &&
      check_expr_refines_with_lrat ctx se te opt_pf
  end.

Definition check_value_equivalence_refines
  (ctx : ub_ctx) (ve : value_equivalence) : bool :=
  wf_value_equivalence ve &&
  check_expr_refines ctx (ve_src_expr ve) (ve_tgt_expr ve).

Lemma check_value_equivalence_refines_sound {Pa : Params} :
  forall ctx ve (penv : param_env Pa) foracle,
    check_value_equivalence_refines ctx ve = true ->
    wf_param_env_for (collect_free_vars [] (ve_src_expr ve)) penv ->
    wf_param_env_for (collect_free_vars [] (ve_tgt_expr ve)) penv ->
    ub_ctx_holds penv foracle ctx ->
    refine_eou_dvalue
      (eval_closed_cert_expr penv foracle (ve_src_expr ve))
      (eval_closed_cert_expr penv foracle (ve_tgt_expr ve)).
Proof.
  intros ctx ve penv foracle Hchk Hps Hpt Hctx.
  apply andb_true_iff in Hchk as [_ Href].
  exact (check_expr_refines_sound ctx (ve_src_expr ve) (ve_tgt_expr ve) penv foracle Href Hps Hpt Hctx).
Qed.

(** *** 5.6a [F-46]: [DTYPE_Pointer] Operations & 64-Bit Modular [OP_GetElementPtr] Reassociation *)

Definition wf_ptr_dvalue {Pa : Params} (v : @dvalue Pa) : Prop :=
  v = DVALUE_Base DVALUE_Poison \/ exists p : ptr, v = DVALUE_Base (DVALUE_Pointer p).

Lemma eval_select_ptr_refines {Pa : Params} :
  forall (dt : dtyp) (vc1 vc2 vp1 vp2 vq1 vq2 : @dvalue Pa),
    wf_scalar_dvalue 1%positive vc1 ->
    wf_scalar_dvalue 1%positive vc2 ->
    dvalue_refines vc1 vc2 ->
    dvalue_refines vp1 vp2 ->
    dvalue_refines vq1 vq2 ->
    refine_eou_dvalue (eval_select vc1 dt vp1 vq1) (eval_select vc2 dt vp2 vq2).
Proof.
  intros dt vc1 vc2 vp1 vp2 vq1 vq2 Hsc1 Hsc2 Hrc Hrp Hrq.
  destruct Hsc1 as [-> | [ic1 ->]].
  - destruct Hsc2 as [-> | [ic2 ->]]; cbn.
    + left; reflexivity.
    + destruct (@Integers.unsigned 1%positive ic2 =? 1)%Z; cbn; left; reflexivity.
  - destruct Hrc as [Habs | ->]; [discriminate Habs |].
    cbn; destruct (@Integers.unsigned 1%positive ic1 =? 1)%Z; cbn; assumption.
Qed.

Lemma eval_icmp_ptr_poison_l {Pa : Params} :
  forall samesign cmp (v2 : @dvalue Pa),
    wf_ptr_dvalue v2 ->
    eval_icmp samesign cmp (DVALUE_Base DVALUE_Poison) v2 =
    raise_ret (DVALUE_Base DVALUE_Poison).
Proof.
  intros samesign cmp v2 [-> | [p2 ->]]; reflexivity.
Qed.

Lemma eval_icmp_ptr_poison_r {Pa : Params} :
  forall samesign cmp (v1 : @dvalue Pa),
    wf_ptr_dvalue v1 ->
    eval_icmp samesign cmp v1 (DVALUE_Base DVALUE_Poison) =
    raise_ret (DVALUE_Base DVALUE_Poison).
Proof.
  intros samesign cmp v1 [-> | [p1 ->]]; reflexivity.
Qed.

Lemma eval_icmp_ptr_defined {Pa : Params} :
  forall samesign cmp (p1 p2 : @ptr _ (@PTR Pa)),
    eval_icmp samesign cmp
      (DVALUE_Base (DVALUE_Pointer p1))
      (DVALUE_Base (DVALUE_Pointer p2)) =
    Functor.fmap (fun b => DVALUE_Base b)
      (eval_int_icmp samesign cmp (ptr_to_int p1) (ptr_to_int p2)).
Proof.
  intros samesign cmp p1 p2; reflexivity.
Qed.

Theorem gep_inbounds_ptr_wrap64_sound {Pa : Params} :
  forall flags (dt : dtyp) (a p' : @ptr _ (@PTR Pa)) (vs : list (@dvalue Pa)) steps,
    @pointer_size Pa = 8%N ->
    (0 <= ptr_to_int a < 2 ^ 64)%Z ->
    gep_steps dt vs = raise_ret (Some steps) ->
    steps <> [] ->
    gep_inbounds flags = true ->
    handle_gep_ptr flags dt a vs = raise_ret (Some p') ->
    ptr_provenance p' = ptr_provenance a /\
    ptr_to_int p' = (ptr_to_int a + gep_offset steps)%Z /\
    (0 <= ptr_to_int p' < 2 ^ 64)%Z /\
    wrap_ptr64 (ptr_to_int p') = ptr_to_int p'.
Proof.
  intros flags dt a p' vs steps Hptr64 Hbase Hsteps Hne Hinb Hgep.
  unfold handle_gep_ptr in Hgep; rewrite Hsteps in Hgep; cbn in Hgep.
  destruct (gep_flags_violated flags (ptr_to_int a) steps) eqn:Hviol;
    [discriminate Hgep |].
  destruct (int_to_ptr (ptr_to_int a + gep_offset steps)%Z (ptr_provenance a))
    as [| | | q] eqn:Hitp; cbn in Hgep; try discriminate Hgep.
  inversion Hgep; subst q; clear Hgep.
  assert (Hprov : ptr_provenance p' = ptr_provenance a) by (eapply int_to_ptr_provenance; exact Hitp).
  assert (Haddr : ptr_to_int p' = (ptr_to_int a + gep_offset steps)%Z) by (eapply ptr_to_int_int_to_ptr; exact Hitp).
  destruct (@gep_inbounds_flags_implies_wrap64_eq Pa flags (ptr_to_int a) steps
              Hptr64 Hbase Hne Hinb Hviol)
    as [Hrng Hwrap].
  rewrite Haddr.
  split; [exact Hprov | split; [reflexivity | split; [exact Hrng | exact Hwrap]]].
Qed.

Theorem gep_chained_no_flags_reassoc_sound {Pa : Params} :
  forall (dt1 dt2 : dtyp) (p0 p1 p2 : @ptr _ (@PTR Pa))
         (vs1 vs2 : list (@dvalue Pa)) steps1 steps2,
    gep_steps dt1 vs1 = raise_ret (Some steps1) ->
    gep_steps dt2 vs2 = raise_ret (Some steps2) ->
    handle_gep_ptr gep_no_flags dt1 p0 vs1 = raise_ret (Some p1) ->
    handle_gep_ptr gep_no_flags dt2 p1 vs2 = raise_ret (Some p2) ->
    ptr_provenance p2 = ptr_provenance p0 /\
    ptr_to_int p2 = (ptr_to_int p0 + gep_offset (steps1 ++ steps2))%Z /\
    wrap_ptr64 (ptr_to_int p2) =
      wrap_ptr64 (wrap_ptr64 (ptr_to_int p0 + gep_offset steps1) + gep_offset steps2)%Z.
Proof.
  intros dt1 dt2 p0 p1 p2 vs1 vs2 steps1 steps2 Hs1 Hs2 Hg1 Hg2.
  unfold handle_gep_ptr in Hg1, Hg2.
  rewrite Hs1 in Hg1; rewrite Hs2 in Hg2; cbn in Hg1, Hg2.
  destruct (int_to_ptr (ptr_to_int p0 + gep_offset steps1)%Z (ptr_provenance p0))
    as [| | | q1] eqn:Hitp1; cbn in Hg1; try discriminate Hg1.
  inversion Hg1; subst q1; clear Hg1.
  destruct (int_to_ptr (ptr_to_int p1 + gep_offset steps2)%Z (ptr_provenance p1))
    as [| | | q2] eqn:Hitp2; cbn in Hg2; try discriminate Hg2.
  inversion Hg2; subst q2; clear Hg2.
  assert (Hpr1 : ptr_provenance p1 = ptr_provenance p0) by (eapply int_to_ptr_provenance; exact Hitp1).
  assert (Had1 : ptr_to_int p1 = (ptr_to_int p0 + gep_offset steps1)%Z) by (eapply ptr_to_int_int_to_ptr; exact Hitp1).
  assert (Hpr2 : ptr_provenance p2 = ptr_provenance p1) by (eapply int_to_ptr_provenance; exact Hitp2).
  assert (Had2 : ptr_to_int p2 = (ptr_to_int p1 + gep_offset steps2)%Z) by (eapply ptr_to_int_int_to_ptr; exact Hitp2).
  rewrite Hpr2, Hpr1, Had2, Had1.
  split; [reflexivity | split].
  - rewrite gep_offset_app; lia.
  - symmetry; rewrite gep_steps_wrap64_reassoc, gep_offset_app.
    f_equal; lia.
Qed.

(** *** 5.6b [F-48]: Padded-Aggregate Slice Forwarding & Memory/Alias Certificate Obligations *)

Theorem validator_padded_struct_slice_forwarding_sound {Pa : Params} :
  forall (packed : bool) (dts : list dtyp) (dv_src dv_tgt : @dvalue Pa)
         (ta : option N) (mb_tgt : list memory_byte)
         (idx : nat) (ft : dtyp),
    serializable (DTYPE_Struct packed dts) ->
    dvalue_has_dtyp dv_src (DTYPE_Struct packed dts) ->
    dvalue_has_dtyp dv_tgt (DTYPE_Struct packed dts) ->
    dvalue_refines dv_src dv_tgt ->
    dvalue_to_memory_bytes (DTYPE_Struct packed dts) dv_tgt ta = raise_ret mb_tgt ->
    nth_error dts idx = Some ft ->
    exists foff fv_src fv_tgt,
      struct_field_offset packed dts idx = Some foff /\
      project_struct_field dv_src idx = Some fv_src /\
      project_struct_field dv_tgt idx = Some fv_tgt /\
      dvalue_refines fv_src fv_tgt /\
      (foff + store_size_dtyp ft <= N.of_nat (List.length mb_tgt))%N /\
      memory_bytes_to_dvalue (take (store_size_dtyp ft) (drop foff mb_tgt)) ft = raise_ret fv_tgt.
Proof.
  intros packed dts dv_src dv_tgt ta mb_tgt idx ft Hser Htys Htyt Href Hwt Hnth.
  destruct (@padded_struct_dvalue_field_slice_round_trip Pa
              packed dts dv_tgt ta mb_tgt idx ft Hser Htyt Hwt Hnth)
    as (foff & fv_tgt & Hfoff & Hpt & Hlen & Hrd).
  destruct Href as [-> | ->].
  - exists foff, (DVALUE_Base DVALUE_Poison), fv_tgt.
    split; [exact Hfoff | split; [reflexivity | split; [exact Hpt |]]].
    split; [left; reflexivity | split; [exact Hlen | exact Hrd]].
  - exists foff, fv_tgt, fv_tgt.
    split; [exact Hfoff | split; [exact Hpt | split; [exact Hpt |]]].
    split; [right; reflexivity | split; [exact Hlen | exact Hrd]].
Qed.

Definition cfg_alloca_slot_names (G : CFG.cfg dtyp) : list string :=
  List.flat_map (fun b =>
    List.flat_map (fun '(iid, ins, _) =>
      match iid, ins with
      | IId r, INSTR_Alloca _ _ => [cert_reg_name r]
      | _, _ => []
      end) (blk_code b)) (blks G).

Definition check_memory_invariant_valid
  (allowed : list (string * positive))
  (ctx : ub_ctx)
  (mi : memory_invariant) : bool :=
  wf_memory_invariant mi &&
  match mi with
  | MI_AllocaPromoted _ _ pe =>
      vars_subset_b (collect_free_vars [] pe) allowed &&
      check_expr_refines ctx pe pe
  | MI_SlotRefines _ _ _ se te =>
      vars_subset_b (collect_free_vars [] se) allowed &&
      vars_subset_b (collect_free_vars [] te) allowed &&
      check_expr_refines ctx se te
  end.

Lemma check_memory_invariant_valid_sound {Pa : Params} :
  forall allowed ctx mi (penv : param_env Pa) foracle,
    check_memory_invariant_valid allowed ctx mi = true ->
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv foracle ctx ->
    match mi with
    | MI_AllocaPromoted _ _ pe =>
        refine_eou_dvalue
          (eval_closed_cert_expr penv foracle pe)
          (eval_closed_cert_expr penv foracle pe)
    | MI_SlotRefines _ _ _ se te =>
        refine_eou_dvalue
          (eval_closed_cert_expr penv foracle se)
          (eval_closed_cert_expr penv foracle te)
    end.
Proof.
  intros allowed ctx mi penv foracle Hchk Hpenv Hctx.
  unfold check_memory_invariant_valid in Hchk.
  apply andb_true_iff in Hchk as [_ Hbody].
  destruct mi as [ss w pe | ss ts w se te].
  - apply andb_true_iff in Hbody as [Hsub Href].
    pose proof (vars_subset_b_wf_param _ allowed penv Hsub Hpenv) as Hpf.
    exact (check_expr_refines_sound ctx pe pe penv foracle Href Hpf Hpf Hctx).
  - rewrite !andb_true_iff in Hbody; destruct Hbody as ([Hs1 Hs2] & Href).
    exact (check_expr_refines_sound ctx se te penv foracle Href
             (vars_subset_b_wf_param _ allowed penv Hs1 Hpenv)
             (vars_subset_b_wf_param _ allowed penv Hs2 Hpenv) Hctx).
Qed.

Definition check_alias_witness_valid
  (src_alloca_slots : list string)
  (aw : alias_witness) : bool :=
  wf_alias_witness aw &&
  match aw_kind aw with
  | ARK_MustAlias => String.eqb (aw_lhs_ptr aw) (aw_rhs_ptr aw)
  | ARK_NoAlias =>
      negb (String.eqb (aw_lhs_ptr aw) (aw_rhs_ptr aw)) &&
      string_in_list (aw_lhs_ptr aw) src_alloca_slots &&
      string_in_list (aw_rhs_ptr aw) src_alloca_slots
  end.

Lemma check_alias_witness_valid_inv :
  forall src_alloca_slots aw,
    check_alias_witness_valid src_alloca_slots aw = true ->
    match aw_kind aw with
    | ARK_MustAlias => aw_lhs_ptr aw = aw_rhs_ptr aw
    | ARK_NoAlias =>
        aw_lhs_ptr aw <> aw_rhs_ptr aw /\
        string_in_list (aw_lhs_ptr aw) src_alloca_slots = true /\
        string_in_list (aw_rhs_ptr aw) src_alloca_slots = true
    end.
Proof.
  intros slots aw H; unfold check_alias_witness_valid in H.
  apply andb_true_iff in H as [_ Hb].
  destruct (aw_kind aw).
  - rewrite !andb_true_iff in Hb; destruct Hb as ([Hneq Hl] & Hr).
    apply negb_true_iff in Hneq.
    split; [intros Heq; apply String.eqb_eq in Heq; congruence | split; assumption].
  - apply String.eqb_eq; exact Hb.
Qed.

