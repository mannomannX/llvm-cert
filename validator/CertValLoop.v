(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Single-Header Natural Loop Cut-Point Validator ([CertValidator.CertValLoop])

    Purpose:
      Defines pure loop-body reification ([reify_pure_exp], [reify_pure_phis],
      [reify_pure_code]), natural-loop extraction ([reify_natural_loop]), and
      coinductive loop validation ([check_loop_cutpoint_cfg]).

    Trust Contract & Fail-Closed Boundary:
      Fail-closed loop cut-point validator ([F-26],
      [check_loop_cutpoint_cfg_open_sound]); accepts only single-header natural
      loops whose cut-point, branch, and return checks pass UB/LRAT checks.

    Assumptions:
      Depends on Stdlib, [Paco], [ITree], [ExtLib], [Vellvm], [Diag], and
      [CertFormat]/[AigLrat]/[AlgRules]/[CfgDag]/[CertVal*]; zero custom axioms.

    Section Outline:
      5.6c [F-26] Single-Header Natural Loop Cut-Point Validator: pure SSA
      reification & stepping; Relational Cut-State Bijection & Coinductive Check. *)

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
  CertValCfgSum
  CertValUbCheck
  CertValPathCheck.

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

(** *** 5.6c [F-26]: Single-Header Natural Loop Cut-Point Validator & Coinductive Soundness *)

Lemma dvalue_refines_antisym {Pa : Params} :
  forall (v1 v2 : @dvalue Pa),
    dvalue_refines v1 v2 -> dvalue_refines v2 v1 -> v1 = v2.
Proof.
  intros v1 v2 [H1 | H1] [H2 | H2]; congruence.
Qed.

Definition dummy_freeze_oracle : freeze_oracle := fun _ _ => 0%Z.

Fixpoint reify_pure_exp
  (lmap : rmap (positive * cert_expr))
  (top : option dtyp)
  (o : exp dtyp)
  {struct o} : option (positive * cert_expr) :=
  match o with
  | EXP_Ident (ID_Local r) =>
      match RM.find r lmap with
      | Some (w, ce) =>
          if check_opt_int_width top w then Some (w, ce) else None
      | None => None
      end
  | EXP_Integer x =>
      match top with
      | Some (DTYPE_Base (DTYPE_I w)) =>
          Some (w, CE_BvConst w (reify_int_const w (denote_int_syntax x)))
      | _ => None
      end
  | EXP_Bool b =>
      if check_opt_int_width top 1%positive
      then Some (1%positive, CE_BvConst 1%positive (if b then 1%N else 0%N))
      else None
  | EXP_Undef | EXP_Poison =>
      match top with
      | Some (DTYPE_Base (DTYPE_I w)) => Some (w, CE_Poison w)
      | _ => None
      end
  | OP_IBinop iop (DTYPE_Base (DTYPE_I w)) e1 e2 =>
      if check_opt_int_width top w then
        match reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) e1,
              reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) e2 with
        | Some (_, ce1), Some (_, ce2) =>
            let '(cop, cfl) := ibinop_to_cert iop in
            Some (w, CE_BinOp cop w cfl ce1 ce2)
        | _, _ => None
        end
      else None
  | OP_ICmp ss cmp (DTYPE_Base (DTYPE_I w)) e1 e2 =>
      if check_opt_int_width top 1%positive then
        match reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) e1,
              reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) e2 with
        | Some (_, ce1), Some (_, ce2) =>
            Some (1%positive, CE_ICmp (icmp_to_cert cmp) ss w ce1 ce2)
        | _, _ => None
        end
      else None
  | OP_Conversion (CONV_Pure pc) (DTYPE_Base (DTYPE_I fw)) e1 (DTYPE_Base (DTYPE_I tw)) =>
      if check_opt_int_width top tw then
        match pure_conv_to_cert pc with
        | Some (ck, cfl) =>
            let w_ok :=
              match ck with
              | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
              | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg cfl) && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
              | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg cfl)
              end in
            if w_ok then
              match reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I fw))) e1 with
              | Some (_, ce1) => Some (tw, CE_Cast ck fw tw cfl ce1)
              | None => None
              end
            else None
        | None => None
        end
      else None
  | OP_Select _ (DTYPE_Base (DTYPE_I 1%positive), ec)
                (DTYPE_Base (DTYPE_I w1), e1)
                (DTYPE_Base (DTYPE_I w2), e2) =>
      if Pos.eqb w1 w2 && check_opt_int_width top w1 then
        match reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I 1%positive))) ec,
              reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e1,
              reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e2 with
        | Some (_, cec), Some (_, ce1), Some (_, ce2) =>
            Some (w1, CE_Select w1 cec ce1 ce2)
        | _, _, _ => None
        end
      else None
  | _ => None
  end.

Definition wf_pure_lmap
  (allowed : list (string * positive))
  (lmap : rmap (positive * cert_expr)) : Prop :=
  forall r w ce,
    RM.find r lmap = Some (w, ce) ->
    wt_cert_expr [] ce = true /\
    cert_expr_bit_width ce = w /\
    is_let_free_expr ce = true /\
    incl (collect_free_vars [] ce) allowed.

Lemma reify_pure_exp_typing :
  forall (o : exp dtyp) allowed lmap top w ce,
    wf_pure_lmap allowed lmap ->
    reify_pure_exp lmap top o = Some (w, ce) ->
    check_opt_int_width top w = true /\
    wt_cert_expr [] ce = true /\
    cert_expr_bit_width ce = w /\
    is_let_free_expr ce = true /\
    incl (collect_free_vars [] ce) allowed.
Proof.
  apply (scalar_exp_ind (fun o =>
    forall allowed lmap top w ce,
      wf_pure_lmap allowed lmap ->
      reify_pure_exp lmap top o = Some (w, ce) ->
      check_opt_int_width top w = true /\
      wt_cert_expr [] ce = true /\
      cert_expr_bit_width ce = w /\
      is_let_free_expr ce = true /\
      incl (collect_free_vars [] ce) allowed)).
  - intros iop dt e1 e2 IH1 IH2 allowed lmap top w ce Hlmap Hr.
    cbn [reify_pure_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate | discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e1) as [[w1 ce1] |] eqn:Hr1; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e2) as [[w2 ce2] |] eqn:Hr2; [| discriminate].
    destruct (ibinop_to_cert iop) as [cop cfl] eqn:Hiop.
    inversion Hr; subst wb ce; clear Hr.
    destruct (ibinop_to_cert_roundtrip iop cop cfl Hiop) as [_ Hfl].
    destruct (IH1 allowed lmap _ w1 ce1 Hlmap Hr1) as (Hcw1 & Hwt1 & Hbw1 & Hlf1 & Hfv1).
    destruct (IH2 allowed lmap _ w2 ce2 Hlmap Hr2) as (Hcw2 & Hwt2 & Hbw2 & Hlf2 & Hfv2).
    apply check_opt_int_width_some_inv in Hcw1; apply check_opt_int_width_some_inv in Hcw2; subst w1 w2.
    repeat split; [exact Hcw | | |].
    + cbn; rewrite Hfl, Hwt1, Hwt2, Hbw1, Hbw2, !Pos.eqb_refl; reflexivity.
    + cbn; rewrite Hlf1, Hlf2; reflexivity.
    + cbn; apply incl_app; assumption.
  - intros ss cmp dt e1 e2 IH1 IH2 allowed lmap top w ce Hlmap Hr.
    cbn [reify_pure_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate | discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e1) as [[w1 ce1] |] eqn:Hr1; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e2) as [[w2 ce2] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w ce; clear Hr.
    destruct (IH1 allowed lmap _ w1 ce1 Hlmap Hr1) as (Hcw1 & Hwt1 & Hbw1 & Hlf1 & Hfv1).
    destruct (IH2 allowed lmap _ w2 ce2 Hlmap Hr2) as (Hcw2 & Hwt2 & Hbw2 & Hlf2 & Hfv2).
    apply check_opt_int_width_some_inv in Hcw1; apply check_opt_int_width_some_inv in Hcw2; subst w1 w2.
    repeat split; [exact Hcw | | |].
    + cbn; rewrite Hwt1, Hwt2, Hbw1, Hbw2, !Pos.eqb_refl; reflexivity.
    + cbn; rewrite Hlf1, Hlf2; reflexivity.
    + cbn; apply incl_app; assumption.
  - intros ct dtf e1 dtt IH1 allowed lmap top w ce Hlmap Hr.
    cbn [reify_pure_exp] in Hr.
    destruct ct as [| pc | ic]; try discriminate.
    destruct dtf as [tbf | |]; try discriminate; destruct tbf as [fw | | | | | | | | | |]; try discriminate.
    destruct dtt as [tbt | |]; try discriminate; destruct tbt as [tw | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top tw) eqn:Hcw; [| discriminate].
    destruct (pure_conv_to_cert pc) as [[ck cfl] |] eqn:Hpc; [| discriminate].
    set (w_ok :=
      match ck with
      | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg cfl) && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg cfl)
      end) in *.
    destruct w_ok eqn:Hwok; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I fw))) e1) as [[w1 ce1] |] eqn:Hr1; [| discriminate].
    inversion Hr; subst w ce; clear Hr.
    destruct (IH1 allowed lmap _ w1 ce1 Hlmap Hr1) as (Hcw1 & Hwt1 & Hbw1 & Hlf1 & Hfv1).
    apply check_opt_int_width_some_inv in Hcw1; subst w1.
    repeat split; [exact Hcw | | exact Hlf1 | exact Hfv1].
    + cbn; unfold w_ok in Hwok; rewrite Hwok, Hwt1, Hbw1, Pos.eqb_refl; reflexivity.
  - intros fm dtc ec dt1 e1 dt2 e2 IHc IH1 IH2 allowed lmap top w ce Hlmap Hr.
    cbn [reify_pure_exp] in Hr.
    destruct dtc as [tbc | |]; try discriminate; destruct tbc as [wc | | | | | | | | | |]; try discriminate.
    destruct wc as [| |]; try discriminate.
    destruct dt1 as [tb1 | |]; try discriminate; destruct tb1 as [w1 | | | | | | | | | |]; try discriminate.
    destruct dt2 as [tb2 | |]; try discriminate; destruct tb2 as [w2 | | | | | | | | | |]; try discriminate.
    destruct (Pos.eqb w1 w2 && check_opt_int_width top w1) eqn:Hcw; [| discriminate].
    apply andb_true_iff in Hcw as [Hw12 Hcw]; apply Pos.eqb_eq in Hw12; subst w2.
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I 1%positive))) ec)
      as [[wc' cec] |] eqn:Hrc; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e1) as [[wa ce1] |] eqn:Hr1; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e2) as [[wb ce2] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w1 ce; clear Hr.
    destruct (IHc allowed lmap _ wc' cec Hlmap Hrc) as (Hcwc & Hwtc & Hbwc & Hlfc & Hfvc).
    destruct (IH1 allowed lmap _ wa ce1 Hlmap Hr1) as (Hcwa & Hwta & Hbwa & Hlfa & Hfva).
    destruct (IH2 allowed lmap _ wb ce2 Hlmap Hr2) as (Hcwb & Hwtb & Hbwb & Hlfb & Hfvb).
    apply check_opt_int_width_some_inv in Hcwc;
    apply check_opt_int_width_some_inv in Hcwa;
    apply check_opt_int_width_some_inv in Hcwb; subst wc' wa wb.
    repeat split; [exact Hcw | | |].
    + cbn; rewrite Hwtc, Hwta, Hwtb, Hbwc, Hbwa, Hbwb, !Pos.eqb_refl; reflexivity.
    + cbn; rewrite Hlfc, Hlfa, Hlfb; reflexivity.
    + cbn; apply incl_app; [exact Hfvc | apply incl_app; assumption].
  - intros dt e1 _ allowed lmap top w ce _ Hr; cbn [reify_pure_exp] in Hr; discriminate Hr.
  - intros o; destruct o; try exact I;
      intros allowed lmap top w ce Hlmap Hr; cbn [reify_pure_exp] in Hr; try discriminate.
    + destruct id as [| r]; [discriminate |].
      destruct (RM.find r lmap) as [[wr cer] |] eqn:Hf; [| discriminate].
      destruct (check_opt_int_width top wr) eqn:Hcw; [| discriminate].
      inversion Hr; subst wr ce; clear Hr.
      destruct (Hlmap r w cer Hf) as (Hwt & Hbw & Hlf & Hfv).
      repeat split; assumption.
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce; clear Hr.
      repeat split; [cbn; apply Pos.eqb_refl | intros u []].
    + destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
      inversion Hr; subst w ce; clear Hr.
      repeat split; [exact Hcw | intros u []].
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce; clear Hr.
      repeat split; [cbn; apply Pos.eqb_refl | intros u []].
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce; clear Hr.
      repeat split; [cbn; apply Pos.eqb_refl | intros u []].
Qed.

Definition lmap_matches_env {Pa : Params}
  (penv : param_env Pa)
  (lmap : rmap (positive * cert_expr))
  (env : rmap (@dvalue Pa)) : Prop :=
  forall r w ce,
    RM.find r lmap = Some (w, ce) ->
    exists dv,
      RM.find r env = Some dv /\
      eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
      wf_scalar_dvalue w dv.

Lemma lmap_matches_env_add {Pa : Params} :
  forall (penv : param_env Pa) lmap env id w ce dv,
    lmap_matches_env penv lmap env ->
    eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv ->
    wf_scalar_dvalue w dv ->
    lmap_matches_env penv (RM.add id (w, ce) lmap) (RM.add id dv env).
Proof.
  intros penv lmap env id w ce dv Henv Hev Hsc r wr cer Hf.
  destruct (RawIDOrd.eq_dec id r) as [Heq | Hneq].
  - rewrite RMF.F.add_eq_o in Hf by exact Heq; inversion Hf; subst r wr cer.
    exists dv; split; [apply RMF.F.add_eq_o; reflexivity | split; assumption].
  - rewrite RMF.F.add_neq_o in Hf by exact Hneq.
    destruct (Henv r wr cer Hf) as [dv' [Hfe [Hev' Hsc']]].
    exists dv'; split; [rewrite RMF.F.add_neq_o by exact Hneq; exact Hfe | split; assumption].
Qed.

Lemma reify_pure_exp_top_width :
  forall (o : exp dtyp) lmap top w ce,
    reify_pure_exp lmap top o = Some (w, ce) ->
    check_opt_int_width top w = true.
Proof.
  apply (scalar_exp_ind (fun o =>
    forall lmap top w ce,
      reify_pure_exp lmap top o = Some (w, ce) ->
      check_opt_int_width top w = true)).
  - intros iop dt e1 e2 _ _ lmap top w ce Hr; cbn [reify_pure_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate | discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e1) as [[w1 ce1] |]; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e2) as [[w2 ce2] |]; [| discriminate].
    destruct (ibinop_to_cert iop); inversion Hr; subst; exact Hcw.
  - intros ss cmp dt e1 e2 _ _ lmap top w ce Hr; cbn [reify_pure_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate | discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e1) as [[w1 ce1] |]; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e2) as [[w2 ce2] |]; [| discriminate].
    inversion Hr; subst; exact Hcw.
  - intros ct dtf e1 dtt _ lmap top w ce Hr; cbn [reify_pure_exp] in Hr.
    destruct ct as [| pc | ic]; try discriminate.
    destruct dtf as [tbf | |]; try discriminate; destruct tbf as [fw | | | | | | | | | |]; try discriminate.
    destruct dtt as [tbt | |]; try discriminate; destruct tbt as [tw | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top tw) eqn:Hcw; [| discriminate].
    destruct (pure_conv_to_cert pc) as [[ck cfl] |]; [| discriminate].
    destruct (match ck with CCK_ZExt => _ | CCK_SExt => _ | CCK_Trunc => _ end); [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I fw))) e1) as [[w1 ce1] |]; [| discriminate].
    inversion Hr; subst; exact Hcw.
  - intros fm dtc ec dt1 e1 dt2 e2 _ _ _ lmap top w ce Hr; cbn [reify_pure_exp] in Hr.
    destruct dtc as [tbc | |]; try discriminate; destruct tbc as [wc | | | | | | | | | |]; try discriminate.
    destruct wc as [| |]; try discriminate.
    destruct dt1 as [tb1 | |]; try discriminate; destruct tb1 as [w1 | | | | | | | | | |]; try discriminate.
    destruct dt2 as [tb2 | |]; try discriminate; destruct tb2 as [w2 | | | | | | | | | |]; try discriminate.
    destruct (Pos.eqb w1 w2 && check_opt_int_width top w1) eqn:Hcw; [| discriminate].
    apply andb_true_iff in Hcw as [_ Hcw].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I 1%positive))) ec) as [[wc' cec] |]; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e1) as [[wa ce1] |]; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e2) as [[wb ce2] |]; [| discriminate].
    inversion Hr; subst; exact Hcw.
  - intros dt e1 _ lmap top w ce Hr; cbn [reify_pure_exp] in Hr; discriminate Hr.
  - intros o; destruct o; try exact I;
      intros lmap top w ce Hr; cbn [reify_pure_exp] in Hr; try discriminate.
    + destruct id as [| r]; [discriminate |].
      destruct (RM.find r lmap) as [[wr cer] |]; [| discriminate].
      destruct (check_opt_int_width top wr) eqn:Hcw; [| discriminate].
      inversion Hr; subst; exact Hcw.
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst; cbn; apply Pos.eqb_refl.
    + destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
      inversion Hr; subst; exact Hcw.
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst; cbn; apply Pos.eqb_refl.
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst; cbn; apply Pos.eqb_refl.
Qed.

Inductive pure_mcfg_steps {Pa : Params} {R : Type}
  : rmap (@dvalue Pa) -> MCFGtop R -> rmap (@dvalue Pa) -> R -> Prop :=
| PMS_Ret env (t : MCFGtop R) (r : R) :
    observe t = RetF r ->
    pure_mcfg_steps env t env r
| PMS_Tau env (t t' : MCFGtop R) env' r :
    observe t = TauF t' ->
    pure_mcfg_steps env t' env' r ->
    pure_mcfg_steps env t env' r
| PMS_LocalRead env (t : MCFGtop R) id dv (k : @dvalue Pa -> MCFGtop R) env' r :
    observe t = VisF (@subevent LocalE MCFGEtop _ (@dvalue Pa) (LocalRead id)) k ->
    RM.find id env = Some dv ->
    pure_mcfg_steps env (k dv) env' r ->
    pure_mcfg_steps env t env' r
| PMS_LocalWrite env (t : MCFGtop R) id dv (k : unit -> MCFGtop R) env' r :
    observe t = VisF (@subevent LocalE MCFGEtop _ unit (LocalWrite id dv)) k ->
    pure_mcfg_steps (RM.add id dv env) (k tt) env' r ->
    pure_mcfg_steps env t env' r.

Inductive pure_cfg_steps {Pa : Params} {R : Type}
  : rmap (@dvalue Pa) -> CFGtop R -> rmap (@dvalue Pa) -> R -> Prop :=
| PCS_Ret env (t : CFGtop R) (r : R) :
    observe t = RetF r ->
    pure_cfg_steps env t env r
| PCS_Tau env (t t' : CFGtop R) env' r :
    observe t = TauF t' ->
    pure_cfg_steps env t' env' r ->
    pure_cfg_steps env t env' r
| PCS_LocalRead env (t : CFGtop R) id dv (k : @dvalue Pa -> CFGtop R) env' r :
    observe t = VisF (@subevent LocalE CFGEtop _ (@dvalue Pa) (LocalRead id)) k ->
    RM.find id env = Some dv ->
    pure_cfg_steps env (k dv) env' r ->
    pure_cfg_steps env t env' r
| PCS_LocalWrite env (t : CFGtop R) id dv (k : unit -> CFGtop R) env' r :
    observe t = VisF (@subevent LocalE CFGEtop _ unit (LocalWrite id dv)) k ->
    pure_cfg_steps (RM.add id dv env) (k tt) env' r ->
    pure_cfg_steps env t env' r.

Lemma pure_mcfg_steps_obs {Pa : Params} {R : Type} :
  forall env (t1 t2 : MCFGtop R) env' r,
    observe t1 = observe t2 ->
    @pure_mcfg_steps Pa R env t1 env' r ->
    @pure_mcfg_steps Pa R env t2 env' r.
Proof.
  intros env t1 t2 env' r Ho H.
  inversion H; subst;
    [apply PMS_Ret | eapply PMS_Tau | eapply PMS_LocalRead | eapply PMS_LocalWrite];
    try (rewrite <- Ho; eassumption); eassumption.
Qed.

Lemma pure_mcfg_steps_bind {Pa : Params} {R S : Type} :
  forall env0 (t : MCFGtop R) env1 x (k : R -> MCFGtop S) env2 y,
    @pure_mcfg_steps Pa R env0 t env1 x ->
    @pure_mcfg_steps Pa S env1 (k x) env2 y ->
    @pure_mcfg_steps Pa S env0 (ITree.bind t k) env2 y.
Proof.
  intros env0 t env1 x k env2 y H1 H2.
  induction H1 as
    [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH].
  - eapply pure_mcfg_steps_obs; [symmetry; rewrite observe_bind, Ho; reflexivity | exact H2].
  - eapply PMS_Tau; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
  - eapply PMS_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact (IH H2)].
  - eapply PMS_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
Qed.

Lemma pure_mcfg_to_mcfg_ret {Pa : Params} {R : Type} :
  forall (sigma : @draw_strat Pa) env (t : MCFGtop R) env' r,
    @pure_mcfg_steps Pa R env t env' r ->
    mcfg_steps_to_ret sigma env t sigma env' r.
Proof.
  intros sigma env t env' r H.
  induction H as
    [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH].
  - apply MSR_Ret; exact Ho.
  - eapply MSR_Tau; [exact Ho | exact IH].
  - eapply MSR_LocalRead; [exact Ho | exact Hf | exact IH].
  - eapply MSR_LocalWrite; [exact Ho | exact IH].
Qed.

Lemma pure_mcfg_to_pure_cfg {Pa : Params} {R : Type} :
  forall env (t : MCFGtop R) env' r,
    @pure_mcfg_steps Pa R env t env' r ->
    @pure_cfg_steps Pa R env (withCall t) env' r.
Proof.
  intros env t env' r H.
  induction H as
    [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH];
    unfold withCall in *.
  - apply PCS_Ret; rewrite observe_translate, Ho; reflexivity.
  - eapply PCS_Tau; [rewrite observe_translate, Ho; reflexivity | exact IH].
  - eapply PCS_LocalRead; [rewrite observe_translate, Ho; reflexivity | exact Hf | exact IH].
  - eapply PCS_LocalWrite; [rewrite observe_translate, Ho; reflexivity | exact IH].
Qed.

Lemma pure_cfg_steps_obs {Pa : Params} {R : Type} :
  forall env (t1 t2 : CFGtop R) env' r,
    observe t1 = observe t2 ->
    @pure_cfg_steps Pa R env t1 env' r ->
    @pure_cfg_steps Pa R env t2 env' r.
Proof.
  intros env t1 t2 env' r Ho H.
  inversion H; subst;
    [apply PCS_Ret | eapply PCS_Tau | eapply PCS_LocalRead | eapply PCS_LocalWrite];
    try (rewrite <- Ho; eassumption); eassumption.
Qed.

Lemma pure_cfg_steps_bind {Pa : Params} {R S : Type} :
  forall env0 (t : CFGtop R) env1 x (k : R -> CFGtop S) env2 y,
    @pure_cfg_steps Pa R env0 t env1 x ->
    @pure_cfg_steps Pa S env1 (k x) env2 y ->
    @pure_cfg_steps Pa S env0 (ITree.bind t k) env2 y.
Proof.
  intros env0 t env1 x k env2 y H1 H2.
  induction H1 as
    [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH].
  - eapply pure_cfg_steps_obs; [symmetry; rewrite observe_bind, Ho; reflexivity | exact H2].
  - eapply PCS_Tau; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
  - eapply PCS_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact (IH H2)].
  - eapply PCS_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
Qed.

Lemma pure_cfg_steps_lwrite {Pa : Params} :
  forall (env : rmap (@dvalue Pa)) (id : raw_id) (dv : @dvalue Pa),
    pure_cfg_steps env (lwrite (E := CFGEtop) id dv) (RM.add id dv env) tt.
Proof.
  intros env id dv; eapply PCS_LocalWrite; [reflexivity | apply PCS_Ret; reflexivity].
Qed.

Lemma pure_cfg_steps_lwrite_list {Pa : Params} :
  forall (dvs : list (raw_id * @dvalue Pa)) (env : rmap (@dvalue Pa)),
    pure_cfg_steps env
      (map_monad (m := CFGtop) (fun '(id, dv) => lwrite id dv) dvs)
      (apply_phi_env env dvs) (List.map (fun _ => tt) dvs).
Proof.
  induction dvs as [| [id dv] rest IH]; intros env; cbn [map_monad apply_phi_env List.map].
  - apply PCS_Ret; reflexivity.
  - eapply pure_cfg_steps_bind; [apply pure_cfg_steps_lwrite |].
    eapply pure_cfg_steps_bind; [apply IH | apply PCS_Ret; reflexivity].
Qed.

Lemma pure_cfg_steps_det_ref_bind_l {Pa : Params} {A R1 R2 : Type}
  (RR : R1 -> R2 -> Prop)
  (self : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop) :
  forall (s1 : @draw_strat Pa) env1 (t1 : CFGtop A) env1' x1
         (k1 : A -> CFGtop R1) (u2 : itree (@Det_OW_E Pa) R2),
    @pure_cfg_steps Pa A env1 t1 env1' x1 ->
    det_ref_ (Pa := Pa) RR self
      (run_draws s1 (run_cfg_locals env1' (k1 x1))) u2 ->
    det_ref_ (Pa := Pa) RR self
      (run_draws s1 (run_cfg_locals env1 (ITree.bind t1 k1))) u2.
Proof.
  intros s1 env1 t1 env1' x1 k1 u2 H1 Hk.
  induction H1 as
    [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH].
  - eapply det_ref__obs_eq;
      [symmetry; rewrite !observe_run_draws, !observe_run_cfg_locals, observe_bind, Ho; reflexivity
      | reflexivity | exact Hk].
  - eapply DR_TauL;
      [rewrite observe_run_draws, observe_run_cfg_locals, observe_bind, Ho; reflexivity | exact (IH Hk)].
  - eapply DR_TauL;
      [rewrite observe_run_draws, observe_run_cfg_locals, observe_bind, Ho; cbn; rewrite Hf; reflexivity
      | exact (IH Hk)].
  - eapply DR_TauL;
      [rewrite observe_run_draws, observe_run_cfg_locals, observe_bind, Ho; reflexivity | exact (IH Hk)].
Qed.

Lemma pure_cfg_steps_det_ref_bind_r {Pa : Params} {A R1 R2 : Type}
  (RR : R1 -> R2 -> Prop)
  (self : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop) :
  forall (u1 : itree (@Det_OW_E Pa) R1)
         (s2 : @draw_strat Pa) env2 (t2 : CFGtop A) env2' x2 (k2 : A -> CFGtop R2),
    @pure_cfg_steps Pa A env2 t2 env2' x2 ->
    det_ref_ (Pa := Pa) RR self
      u1 (run_draws s2 (run_cfg_locals env2' (k2 x2))) ->
    det_ref_ (Pa := Pa) RR self
      u1 (run_draws s2 (run_cfg_locals env2 (ITree.bind t2 k2))).
Proof.
  intros u1 s2 env2 t2 env2' x2 k2 H2 Hk.
  induction H2 as
    [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH].
  - eapply det_ref__obs_eq;
      [reflexivity
      | symmetry; rewrite !observe_run_draws, !observe_run_cfg_locals, observe_bind, Ho; reflexivity
      | exact Hk].
  - eapply DR_TauR;
      [rewrite observe_run_draws, observe_run_cfg_locals, observe_bind, Ho; reflexivity | exact (IH Hk)].
  - eapply DR_TauR;
      [rewrite observe_run_draws, observe_run_cfg_locals, observe_bind, Ho; cbn; rewrite Hf; reflexivity
      | exact (IH Hk)].
  - eapply DR_TauR;
      [rewrite observe_run_draws, observe_run_cfg_locals, observe_bind, Ho; reflexivity | exact (IH Hk)].
Qed.

Lemma eval_reified_pure_exp {Pa : Params} :
  forall (o : exp dtyp) (penv : param_env Pa)
         lmap (env : rmap (@dvalue Pa)) top w ce,
    lmap_matches_env penv lmap env ->
    reify_pure_exp lmap top o = Some (w, ce) ->
    ((forall sigma, mcfg_steps_to_ub sigma env (denote_exp top o)) /\
     exists msg, eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ub msg) \/
    (exists dv,
       eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
       wf_scalar_dvalue w dv /\
       pure_mcfg_steps env (denote_exp top o) env dv).
Proof.
  apply (scalar_exp_ind (fun o =>
    forall (penv : param_env Pa)
           lmap (env : rmap (@dvalue Pa)) top w ce,
      lmap_matches_env penv lmap env ->
      reify_pure_exp lmap top o = Some (w, ce) ->
      ((forall sigma, mcfg_steps_to_ub sigma env (denote_exp top o)) /\
       exists msg, eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ub msg) \/
      (exists dv,
         eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv /\
         wf_scalar_dvalue w dv /\
         pure_mcfg_steps env (denote_exp top o) env dv))).
  - intros iop dt e1 e2 IH1 IH2 penv lmap env top w ce Henv Hr.
    cbn [reify_pure_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate | discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top wb) eqn:Hcw; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e1) as [[w1 ce1] |] eqn:Hr1; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e2) as [[w2 ce2] |] eqn:Hr2; [| discriminate].
    destruct (ibinop_to_cert iop) as [cop cfl] eqn:Hiop.
    inversion Hr; subst wb ce; clear Hr.
    destruct (ibinop_to_cert_roundtrip iop cop cfl Hiop) as [Heq_iop _].
    destruct (IH1 penv lmap env (Some (DTYPE_Base (DTYPE_I w))) w1 ce1 Henv Hr1)
      as [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]].
    + left; split.
      * intros sigma; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hub1 sigma).
      * exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + destruct (IH2 penv lmap env (Some (DTYPE_Base (DTYPE_I w))) w2 ce2 Henv Hr2)
        as [[Hub2 [msg2 Hev2]] | [dv2 [Hev2 [Hsc2 Hst2]]]].
      * left; split;
          [intros sigma; cbn [denote_exp]; eapply mcfg_steps_to_ub_bind_r;
             [exact (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1) | apply mcfg_steps_to_ub_bind_l; exact (Hub2 sigma)]
          | exists msg2; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
              rewrite Hev1, Hev2; reflexivity].
      * pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr1)) as Hw1.
        pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr2)) as Hw2.
        subst w1 w2.
        destruct (eval_iop_wf_scalar cop cfl w dv1 dv2 Hsc1 Hsc2)
          as [[msg_op Hev_op] | [vout [Hev_op Hsc_out]]].
        -- left; split.
           ++ intros sigma; cbn [denote_exp]; eapply mcfg_steps_to_ub_bind_r;
                [exact (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1) |].
              eapply mcfg_steps_to_ub_bind_r;
                [exact (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst2) |].
              rewrite <- Heq_iop, Hev_op; apply mcfg_steps_eou_ub.
           ++ exists msg_op; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hev1, Hev2; cbn [eou_bind]; exact Hev_op.
        -- right; exists vout; split; [| split; [exact Hsc_out |]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hev1, Hev2; cbn [eou_bind]; exact Hev_op.
           ++ cbn [denote_exp]; eapply pure_mcfg_steps_bind; [exact Hst1 |].
              eapply pure_mcfg_steps_bind; [exact Hst2 |].
              rewrite <- Heq_iop, Hev_op; apply PMS_Ret; reflexivity.
  - intros ss cmp dt e1 e2 IH1 IH2 penv lmap env top w ce Henv Hr.
    cbn [reify_pure_exp] in Hr.
    destruct dt as [tb | |]; [| discriminate | discriminate]; destruct tb as [wb | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e1) as [[w1 ce1] |] eqn:Hr1; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I wb))) e2) as [[w2 ce2] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w ce; clear Hr.
    destruct (IH1 penv lmap env (Some (DTYPE_Base (DTYPE_I wb))) w1 ce1 Henv Hr1)
      as [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]].
    + left; split.
      * intros sigma; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hub1 sigma).
      * exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + destruct (IH2 penv lmap env (Some (DTYPE_Base (DTYPE_I wb))) w2 ce2 Henv Hr2)
        as [[Hub2 [msg2 Hev2]] | [dv2 [Hev2 [Hsc2 Hst2]]]].
      * left; split;
          [intros sigma; cbn [denote_exp]; eapply mcfg_steps_to_ub_bind_r;
             [exact (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1) | apply mcfg_steps_to_ub_bind_l; exact (Hub2 sigma)]
          | exists msg2; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
              rewrite Hev1, Hev2; reflexivity].
      * pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr1)) as Hw1.
        pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr2)) as Hw2.
        subst w1 w2.
        destruct (eval_icmp_wf_scalar ss (icmp_to_cert cmp) wb dv1 dv2 Hsc1 Hsc2)
          as [vout [Hev_cmp Hsc_out]].
        right; exists vout; split; [| split; [exact Hsc_out |]].
        -- unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
             rewrite Hev1, Hev2; cbn [eou_bind]; exact Hev_cmp.
        -- cbn [denote_exp]; eapply pure_mcfg_steps_bind; [exact Hst1 |].
           eapply pure_mcfg_steps_bind; [exact Hst2 |].
           rewrite <- (icmp_to_cert_roundtrip cmp), Hev_cmp; apply PMS_Ret; reflexivity.
  - intros ct dtf e1 dtt IH1 penv lmap env top w ce Henv Hr.
    cbn [reify_pure_exp] in Hr.
    destruct ct as [| pc | ic]; try discriminate.
    destruct dtf as [tbf | |]; try discriminate; destruct tbf as [fw | | | | | | | | | |]; try discriminate.
    destruct dtt as [tbt | |]; try discriminate; destruct tbt as [tw | | | | | | | | | |]; try discriminate.
    destruct (check_opt_int_width top tw) eqn:Hcw; [| discriminate].
    destruct (pure_conv_to_cert pc) as [[ck cfl] |] eqn:Hpc; [| discriminate].
    set (w_ok :=
      match ck with
      | CCK_ZExt => (fw <? tw)%positive && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_SExt => (fw <? tw)%positive && negb (ccf_nneg cfl) && negb (ccf_nuw cfl) && negb (ccf_nsw cfl)
      | CCK_Trunc => (tw <? fw)%positive && negb (ccf_nneg cfl)
      end) in *.
    destruct w_ok eqn:Hwok; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I fw))) e1) as [[w1 ce1] |] eqn:Hr1; [| discriminate].
    inversion Hr; subst w ce; clear Hr.
    pose proof (pure_conv_to_cert_roundtrip pc ck cfl Hpc) as Heq_pc.
    destruct (IH1 penv lmap env (Some (DTYPE_Base (DTYPE_I fw))) w1 ce1 Henv Hr1)
      as [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]].
    + left; split.
      * intros sigma; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hub1 sigma).
      * exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; reflexivity.
    + pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr1)) as Hw1.
      subst w1; unfold w_ok in Hwok.
      destruct (eval_cast_wf_scalar ck fw tw cfl dv1 Hwok Hsc1) as [vout [Hev_cast Hsc_out]].
      right; exists vout; split; [| split; [exact Hsc_out |]].
      * unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev1; cbn [eou_bind]; exact Hev_cast.
      * cbn [denote_exp convert]; eapply pure_mcfg_steps_bind; [exact Hst1 |].
        rewrite <- Heq_pc, Hev_cast; apply PMS_Ret; reflexivity.
  - intros fm dtc ec dt1 e1 dt2 e2 IHc IH1 IH2 penv lmap env top w ce Henv Hr.
    cbn [reify_pure_exp] in Hr.
    destruct dtc as [tbc | |]; try discriminate; destruct tbc as [wc | | | | | | | | | |]; try discriminate.
    destruct wc as [| |]; try discriminate.
    destruct dt1 as [tb1 | |]; try discriminate; destruct tb1 as [w1 | | | | | | | | | |]; try discriminate.
    destruct dt2 as [tb2 | |]; try discriminate; destruct tb2 as [w2 | | | | | | | | | |]; try discriminate.
    destruct (Pos.eqb w1 w2 && check_opt_int_width top w1) eqn:Hcw; [| discriminate].
    apply andb_true_iff in Hcw as [Hw12 Hcw]; apply Pos.eqb_eq in Hw12; subst w2.
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I 1%positive))) ec)
      as [[wc' cec] |] eqn:Hrc; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e1) as [[wa ce1] |] eqn:Hr1; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w1))) e2) as [[wb ce2] |] eqn:Hr2; [| discriminate].
    inversion Hr; subst w1 ce; clear Hr.
    destruct (IHc penv lmap env (Some (DTYPE_Base (DTYPE_I 1%positive))) wc' cec Henv Hrc)
      as [[Hubc [msgc Hevc]] | [dvc [Hevc [Hscc Hstc]]]].
    + left; split.
      * intros sigma; cbn [denote_exp]; apply mcfg_steps_to_ub_bind_l; exact (Hubc sigma).
      * exists msgc; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hevc; reflexivity.
    + destruct (IH1 penv lmap env (Some (DTYPE_Base (DTYPE_I w))) wa ce1 Henv Hr1)
        as [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]].
      * left; split;
          [intros sigma; cbn [denote_exp]; eapply mcfg_steps_to_ub_bind_r;
             [exact (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hstc) | apply mcfg_steps_to_ub_bind_l; exact (Hub1 sigma)]
          | exists msg1; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
              rewrite Hevc, Hev1; reflexivity].
      * destruct (IH2 penv lmap env (Some (DTYPE_Base (DTYPE_I w))) wb ce2 Henv Hr2)
          as [[Hub2 [msg2 Hev2]] | [dv2 [Hev2 [Hsc2 Hst2]]]].
        -- left; split;
             [intros sigma; cbn [denote_exp];
                eapply mcfg_steps_to_ub_bind_r; [exact (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hstc) |];
                eapply mcfg_steps_to_ub_bind_r; [exact (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1)
                                                 | apply mcfg_steps_to_ub_bind_l; exact (Hub2 sigma)]
             | exists msg2; unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                 rewrite Hevc, Hev1, Hev2; reflexivity].
        -- pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hrc)) as Hwc.
           pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr1)) as Hwa.
           pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr2)) as Hwb.
           subst wc' wa wb.
           destruct (eval_select_wf_scalar w dvc dv1 dv2 Hscc Hsc1 Hsc2) as [vout [Hev_sel Hsc_out]].
           right; exists vout; split; [| split; [exact Hsc_out |]].
           ++ unfold eval_closed_cert_expr in *; cbn [eval_cert_expr];
                rewrite Hevc, Hev1, Hev2; cbn [eou_bind]; exact Hev_sel.
           ++ cbn [denote_exp]; eapply pure_mcfg_steps_bind; [exact Hstc |].
              eapply pure_mcfg_steps_bind; [exact Hst1 |].
              eapply pure_mcfg_steps_bind; [exact Hst2 |].
              rewrite Hev_sel; apply PMS_Ret; reflexivity.
  - intros dt e1 _ penv lmap env top w ce _ Hr; cbn [reify_pure_exp] in Hr; discriminate Hr.
  - intros o; destruct o; try exact I;
      intros penv lmap env top w ce Henv Hr; cbn [reify_pure_exp] in Hr; try discriminate.
    + destruct id as [| r]; [discriminate |].
      destruct (RM.find r lmap) as [[wr cer] |] eqn:Hf; [| discriminate].
      destruct (check_opt_int_width top wr) eqn:Hcw; [| discriminate].
      inversion Hr; subst wr ce; clear Hr.
      destruct (Henv r w cer Hf) as [dv [Hfe [Hev Hsc]]].
      right; exists dv; split; [exact Hev | split; [exact Hsc |]].
      cbn [denote_exp lookup_id]; eapply PMS_LocalRead; [reflexivity | exact Hfe | apply PMS_Ret; reflexivity].
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce; clear Hr.
      right;
        exists (DVALUE_Base (@DVALUE_I Pa w (@Integers.repr w (Z.of_N (reify_int_const w (denote_int_syntax x)))))).
      split; [reflexivity | split; [right; eexists; reflexivity |]].
      cbn [denote_exp]; rewrite repr_reify_int_const; apply PMS_Ret; reflexivity.
    + destruct (check_opt_int_width top 1%positive) eqn:Hcw; [| discriminate].
      inversion Hr; subst w ce; clear Hr.
      right; destruct b.
      * exists (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.repr 1%positive (Z.of_N 1%N)))).
        split; [reflexivity | split; [right; eexists; reflexivity |]].
        cbn [denote_exp]; rewrite repr_one_N; apply PMS_Ret; reflexivity.
      * exists (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.repr 1%positive (Z.of_N 0%N)))).
        split; [reflexivity | split; [right; eexists; reflexivity |]].
        cbn [denote_exp]; rewrite repr_zero_N; apply PMS_Ret; reflexivity.
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce; clear Hr.
      right; exists (DVALUE_Base DVALUE_Poison).
      split; [reflexivity | split; [left; reflexivity | apply PMS_Ret; reflexivity]].
    + destruct top as [dt |]; [| discriminate].
      destruct dt as [tb | |]; try discriminate; destruct tb as [wt | | | | | | | | | |]; try discriminate.
      inversion Hr; subst wt ce; clear Hr.
      right; exists (DVALUE_Base DVALUE_Poison).
      split; [reflexivity | split; [left; reflexivity | apply PMS_Ret; reflexivity]].
Qed.

Fixpoint reify_pure_phis
  (bid_from : block_id)
  (lmap : rmap (positive * cert_expr))
  (phis : list (local_id * phi dtyp * list (metadata dtyp)))
  {struct phis} : option (list (raw_id * positive * cert_expr)) :=
  match phis with
  | [] => Some []
  | (id, Phi _ (DTYPE_Base (DTYPE_I w)) pargs, _) :: rest =>
      if is_supported_bit_width w then
        match assoc bid_from pargs with
        | Some op =>
            match reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) op,
                  reify_pure_phis bid_from lmap rest with
            | Some (_, ce), Some rrest => Some ((id, w, ce) :: rrest)
            | _, _ => None
            end
        | None => None
        end
      else None
  | _ :: _ => None
  end.

Definition wf_pure_eval_entry (allowed : list (string * positive)) (ce : cert_expr) : Prop :=
  wt_cert_expr [] ce = true /\
  is_let_free_expr ce = true /\
  incl (collect_free_vars [] ce) allowed.

Lemma reify_pure_phis_typing :
  forall phis allowed bid_from lmap pevals,
    wf_pure_lmap allowed lmap ->
    reify_pure_phis bid_from lmap phis = Some pevals ->
    Forall (fun '(_, w, ce) =>
      is_supported_bit_width w = true /\
      cert_expr_bit_width ce = w /\
      wf_pure_eval_entry allowed ce) pevals.
Proof.
  induction phis as [| [[id [fm dt pargs]] md] rest IH];
    intros allowed bid_from lmap pevals Hlmap Hr;
    cbn [reify_pure_phis] in Hr.
  - inversion Hr; constructor.
  - destruct dt as [tb | |]; try discriminate; destruct tb as [w | | | | | | | | | |]; try discriminate.
    destruct (is_supported_bit_width w) eqn:Hsup; [| discriminate].
    destruct (assoc bid_from pargs) as [op |] eqn:Hassoc; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) op) as [[w1 ce] |] eqn:Hre; [| discriminate].
    destruct (reify_pure_phis bid_from lmap rest) as [rrest |] eqn:Hrr; [| discriminate].
    inversion Hr; subst pevals; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hre)) as ->.
    destruct (reify_pure_exp_typing op allowed lmap (Some (DTYPE_Base (DTYPE_I w))) w ce Hlmap Hre)
      as (_ & Hwt & Hbw & Hlf & Hfv).
    constructor; [repeat split; assumption | exact (IH allowed bid_from lmap rrest Hlmap Hrr)].
Qed.

Lemma eval_reified_pure_phis {Pa : Params} :
  forall phis (penv : param_env Pa) bid_from lmap (env : rmap (@dvalue Pa)) pevals,
    lmap_matches_env penv lmap env ->
    reify_pure_phis bid_from lmap phis = Some pevals ->
    ((forall sigma, cfg_steps_to_ub sigma env (map_monad (m := CFGtop) (denote_phi bid_from) phis)) /\
     exists id w ce msg,
       In (id, w, ce) pevals /\
       eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ub msg) \/
    (exists dvs,
       Forall2 (phi_eval_pair_matches penv dummy_freeze_oracle) pevals dvs /\
       pure_cfg_steps env (map_monad (m := CFGtop) (denote_phi bid_from) phis) env dvs).
Proof.
  induction phis as [| [[id [fm dt pargs]] md] rest IH];
    intros penv bid_from lmap env pevals Henv Hr;
    cbn [reify_pure_phis] in Hr.
  - inversion Hr; subst pevals; right; exists []; split.
    + constructor.
    + apply PCS_Ret; reflexivity.
  - destruct dt as [tb | |]; try discriminate; destruct tb as [w | | | | | | | | | |]; try discriminate.
    destruct (is_supported_bit_width w); [| discriminate].
    destruct (assoc bid_from pargs) as [op |] eqn:Hassoc; [| discriminate].
    destruct (reify_pure_exp lmap (Some (DTYPE_Base (DTYPE_I w))) op) as [[w1 ce] |] eqn:Hre; [| discriminate].
    destruct (reify_pure_phis bid_from lmap rest) as [rrest |] eqn:Hrr; [| discriminate].
    inversion Hr; subst pevals; clear Hr.
    pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hre)) as ->.
    destruct (eval_reified_pure_exp op penv lmap env (Some (DTYPE_Base (DTYPE_I w))) w ce Henv Hre)
      as [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]].
    + left; split.
      * intros sigma; cbn [map_monad denote_phi]; rewrite Hassoc; unfold denote_exp'.
        apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub1 sigma).
      * exists id, w, ce, msg1; split; [left; reflexivity | exact Hev1].
    + destruct (IH penv bid_from lmap env rrest Henv Hrr)
        as [[Hub2 (id2 & w2 & ce2 & msg2 & Hin2 & Hev2)] | [dvs_r [Hpm_r Hst_r]]].
      * left; split.
        -- intros sigma; cbn [map_monad denote_phi]; rewrite Hassoc; unfold denote_exp'.
           eapply cfg_steps_to_ub_bind_r.
           ++ eapply cfg_steps_to_ret_bind;
                [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1))
                | apply CSR_Ret; reflexivity].
           ++ apply cfg_steps_to_ub_bind_l; exact (Hub2 sigma).
        -- exists id2, w2, ce2, msg2; split; [right; exact Hin2 | exact Hev2].
      * right; exists ((id, dv1) :: dvs_r); split.
        -- constructor; [split; [reflexivity | split; assumption] | exact Hpm_r].
        -- cbn [map_monad denote_phi]; rewrite Hassoc; unfold denote_exp'.
           eapply pure_cfg_steps_bind.
           ++ eapply pure_cfg_steps_bind; [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst1) | apply PCS_Ret; reflexivity].
           ++ eapply pure_cfg_steps_bind; [exact Hst_r | apply PCS_Ret; reflexivity].
Qed.

Fixpoint reify_pure_code
  (lmap : rmap (positive * cert_expr))
  (c : code dtyp)
  {struct c} : option (list cert_expr * rmap (positive * cert_expr)) :=
  match c with
  | [] => Some ([], lmap)
  | (IId id, INSTR_Op op, _) :: rest =>
      match reify_pure_exp lmap None op with
      | Some (w, ce) =>
          match reify_pure_code (RM.add id (w, ce) lmap) rest with
          | Some (cevals, lmap2) => Some (ce :: cevals, lmap2)
          | None => None
          end
      | None => None
      end
  | (IVoid _, INSTR_Comment _, _) :: rest =>
      reify_pure_code lmap rest
  | _ :: _ => None
  end.

Definition code_written_ids (c : code dtyp) : list raw_id :=
  List.flat_map (fun '(iid, _, _) =>
    match iid with
    | IId id => [id]
    | IVoid _ => []
    end) c.

Lemma wf_pure_lmap_add :
  forall allowed lmap id w ce,
    wf_pure_lmap allowed lmap ->
    wt_cert_expr [] ce = true ->
    cert_expr_bit_width ce = w ->
    is_let_free_expr ce = true ->
    incl (collect_free_vars [] ce) allowed ->
    wf_pure_lmap allowed (RM.add id (w, ce) lmap).
Proof.
  intros allowed lmap id w ce Hlmap Hwt Hbw Hlf Hfv r wr cer Hf.
  destruct (RawIDOrd.eq_dec id r) as [Heq | Hneq].
  - rewrite RMF.F.add_eq_o in Hf by exact Heq; inversion Hf; subst wr cer; repeat split; assumption.
  - rewrite RMF.F.add_neq_o in Hf by exact Hneq; exact (Hlmap r wr cer Hf).
Qed.

Lemma reify_pure_code_typing :
  forall c allowed lmap0 cevals lmap2,
    wf_pure_lmap allowed lmap0 ->
    reify_pure_code lmap0 c = Some (cevals, lmap2) ->
    Forall (wf_pure_eval_entry allowed) cevals /\
    wf_pure_lmap allowed lmap2.
Proof.
  induction c as [| [[iid ins] md] rest IH];
    intros allowed lmap0 cevals lmap2 Hlmap0 Hr;
    cbn [reify_pure_code] in Hr.
  - inversion Hr; subst; split; [constructor | exact Hlmap0].
  - destruct iid as [id | vid]; destruct ins; try discriminate Hr.
    + destruct (reify_pure_exp lmap0 None op) as [[w ce] |] eqn:Hre; [| discriminate].
      destruct (reify_pure_code (RM.add id (w, ce) lmap0) rest) as [[cevals_r lmap2'] |] eqn:Hrr; [| discriminate].
      inversion Hr; subst cevals lmap2'; clear Hr.
      destruct (reify_pure_exp_typing op allowed lmap0 None w ce Hlmap0 Hre)
        as (_ & Hwt & Hbw & Hlf & Hfv).
      pose proof (wf_pure_lmap_add allowed lmap0 id w ce Hlmap0 Hwt Hbw Hlf Hfv) as Hlmap1.
      destruct (IH allowed (RM.add id (w, ce) lmap0) cevals_r lmap2 Hlmap1 Hrr) as [Hfa Hlmap2].
      split; [constructor; [repeat split; assumption | exact Hfa] | exact Hlmap2].
    + exact (IH allowed lmap0 cevals lmap2 Hlmap0 Hr).
Qed.

Lemma eval_reified_pure_code {Pa : Params} :
  forall c (varargs : option (@ptr _ (@PTR Pa))) (penv : param_env Pa)
         lmap0 (env0 : rmap (@dvalue Pa)) cevals lmap2,
    lmap_matches_env penv lmap0 env0 ->
    reify_pure_code lmap0 c = Some (cevals, lmap2) ->
    ((forall sigma, cfg_steps_to_ub sigma env0 (denote_code c varargs)) /\
     exists ce msg,
       In ce cevals /\
       eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ub msg) \/
    (exists env2,
       lmap_matches_env penv lmap2 env2 /\
       Forall (fun ce => exists dv, eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv) cevals /\
       (forall r, ~ In r (code_written_ids c) -> RM.find r env2 = RM.find r env0) /\
       pure_cfg_steps env0 (denote_code c varargs) env2 tt).
Proof.
  induction c as [| [[iid ins] md] rest IH];
    intros varargs penv lmap0 env0 cevals lmap2 Henv0 Hr;
    cbn [reify_pure_code] in Hr.
  - inversion Hr; subst cevals lmap2; right; exists env0.
    split; [exact Henv0 |].
    split; [apply Forall_nil |].
    split; [intros r _; reflexivity | apply PCS_Ret; reflexivity].
  - destruct iid as [id | vid]; destruct ins; try discriminate Hr.
    + destruct (reify_pure_exp lmap0 None op) as [[w ce] |] eqn:Hre; [| discriminate].
      destruct (reify_pure_code (RM.add id (w, ce) lmap0) rest) as [[cevals_r lmap2'] |] eqn:Hrr; [| discriminate].
      inversion Hr; subst cevals lmap2'; clear Hr.
      destruct (eval_reified_pure_exp op penv lmap0 env0 None w ce Henv0 Hre)
        as [[Hub1 [msg1 Hev1]] | [dv1 [Hev1 [Hsc1 Hst1]]]].
      * left; split.
        -- intros sigma; unfold denote_code; cbn [loop_monad denote_instr]; unfold denote_exp'.
           apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub1 sigma).
        -- exists ce, msg1; split; [left; reflexivity | exact Hev1].
      * pose proof (lmap_matches_env_add penv lmap0 env0 id w ce dv1 Henv0 Hev1 Hsc1) as Henv1.
        destruct (IH varargs penv (RM.add id (w, ce) lmap0) (RM.add id dv1 env0) cevals_r lmap2 Henv1 Hrr)
          as [[Hub2 (ce2 & msg2 & Hin2 & Hev2)] | (env2 & Henv2 & Hfa2 & Hpres2 & Hst2)].
        -- left; split.
           ++ intros sigma; unfold denote_code; cbn [loop_monad denote_instr]; unfold denote_exp'.
              eapply cfg_steps_to_ub_bind_r.
              ** eapply cfg_steps_to_ret_bind;
                   [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst1)) |].
                 eapply cfg_steps_to_ret_bind; [apply cfg_steps_lwrite | apply CSR_Ret; reflexivity].
              ** exact (Hub2 sigma).
           ++ exists ce2, msg2; split; [right; exact Hin2 | exact Hev2].
        -- right; exists env2; split; [exact Henv2 | split; [| split]].
           ++ constructor; [exists dv1; exact Hev1 | exact Hfa2].
           ++ intros r Hnin; cbn [code_written_ids] in Hnin.
              rewrite (Hpres2 r (fun Hin => Hnin (or_intror Hin))).
              rewrite RMF.F.add_neq_o; [reflexivity | intros ->; exact (Hnin (or_introl eq_refl))].
           ++ unfold denote_code; cbn [loop_monad denote_instr]; unfold denote_exp'.
              eapply pure_cfg_steps_bind.
              ** eapply pure_cfg_steps_bind; [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst1) |].
                 eapply pure_cfg_steps_bind; [apply pure_cfg_steps_lwrite | apply PCS_Ret; reflexivity].
              ** exact Hst2.
    + destruct (IH varargs penv lmap0 env0 cevals lmap2 Henv0 Hr)
        as [[Hub2 Hce2] | (env2 & Henv2 & Hfa2 & Hpres2 & Hst2)].
      * left; split; [| exact Hce2].
        intros sigma; unfold denote_code; cbn [loop_monad denote_instr].
        eapply cfg_steps_to_ub_bind_r; [apply CSR_Ret; reflexivity | exact (Hub2 sigma)].
      * right; exists env2; repeat split; try assumption.
        unfold denote_code; cbn [loop_monad denote_instr].
        eapply pure_cfg_steps_bind; [apply PCS_Ret; reflexivity | exact Hst2].
Qed.

(** **** Relational Cut-State Bijection & Coinductive Natural-Loop Checker ([F-26]) *)

Definition cut_p_name (k : nat) : string := ("!p" ++ show_Z_dec (Z.of_nat k))%string.
Definition cut_v_name (k : nat) : string := ("!v" ++ show_Z_dec (Z.of_nat k))%string.

Lemma cut_p_name_not_dollar : forall k, starts_with_dollar (cut_p_name k) = false.
Proof. reflexivity. Qed.

Lemma cut_v_name_not_dollar : forall k, starts_with_dollar (cut_v_name k) = false.
Proof. reflexivity. Qed.

Definition cut_src_expr (k : nat) (w : positive) : cert_expr :=
  CE_Select w (CE_Var (cut_p_name k) 1%positive) (CE_Var (cut_v_name k) w) (CE_Poison w).

Definition cut_tgt_expr (k : nat) (w : positive) : cert_expr :=
  CE_Var (cut_v_name k) w.

Fixpoint extend_penv {Pa : Params}
  (bs : list (string * @dvalue Pa)) (penv : param_env Pa)
  {struct bs} : param_env Pa :=
  match bs with
  | [] => penv
  | (nm, dv) :: rest =>
      fun q => if String.eqb q nm then Some dv else extend_penv rest penv q
  end.

Lemma extend_penv_not_in {Pa : Params} :
  forall bs (penv : param_env Pa) q,
    ~ In q (List.map fst bs) ->
    extend_penv bs penv q = penv q.
Proof.
  induction bs as [| [nm dv] rest IH]; intros penv q Hnin; cbn in *; [reflexivity |].
  destruct (String.eqb q nm) eqn:Eq.
  - apply String.eqb_eq in Eq; exfalso; exact (Hnin (or_introl (eq_sym Eq))).
  - exact (IH penv q (fun H => Hnin (or_intror H))).
Qed.

Lemma extend_penv_nodup_in {Pa : Params} :
  forall bs (penv : param_env Pa) nm dv,
    NoDup (List.map fst bs) ->
    In (nm, dv) bs ->
    extend_penv bs penv nm = Some dv.
Proof.
  induction bs as [| [nm0 dv0] rest IH]; intros penv nm dv Hnd Hin; cbn in *; [contradiction |].
  inversion Hnd as [| ? ? Hnin Hndr]; subst.
  destruct Hin as [Heq | Hin_r].
  - inversion Heq; subst nm0 dv0; rewrite String.eqb_refl; reflexivity.
  - destruct (String.eqb nm nm0) eqn:Eq.
    + apply String.eqb_eq in Eq; subst nm0.
      exfalso; apply Hnin; exact (in_map fst rest (nm, dv) Hin_r).
    + exact (IH penv nm dv Hndr Hin_r).
Qed.

Lemma eval_let_free_penv_agree {Pa : Params} :
  forall (ce : cert_expr) (penv1 penv2 : param_env Pa) foracle,
    is_let_free_expr ce = true ->
    (forall nm w, In (nm, w) (collect_free_vars [] ce) -> penv1 nm = penv2 nm) ->
    eval_closed_cert_expr penv1 foracle ce = eval_closed_cert_expr penv2 foracle ce.
Proof.
  unfold eval_closed_cert_expr.
  induction ce as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body _ _ ] using cert_expr_ind_nested;
    intros penv1 penv2 foracle Hlf Hag;
    cbn [is_let_free_expr collect_free_vars eval_cert_expr lookup_let_val] in Hlf, Hag |- *;
    try reflexivity; try discriminate Hlf.
  - rewrite (Hag nm w (or_introl eq_refl)); reflexivity.
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    rewrite (IHl penv1 penv2 foracle Hlfl (fun n w0 H => Hag n w0 (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHr penv1 penv2 foracle Hlfr (fun n w0 H => Hag n w0 (proj2 (in_app_iff _ _ _) (or_intror H)))).
    reflexivity.
  - apply andb_true_iff in Hlf as [Hlfl Hlfr].
    rewrite (IHl penv1 penv2 foracle Hlfl (fun n w0 H => Hag n w0 (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHr penv1 penv2 foracle Hlfr (fun n w0 H => Hag n w0 (proj2 (in_app_iff _ _ _) (or_intror H)))).
    reflexivity.
  - rewrite (IHo penv1 penv2 foracle Hlf Hag); reflexivity.
  - rewrite !andb_true_iff in Hlf; destruct Hlf as ([Hlfc Hlft] & Hlff).
    rewrite (IHc penv1 penv2 foracle Hlfc (fun n w0 H => Hag n w0 (proj2 (in_app_iff _ _ _) (or_introl H)))).
    rewrite (IHt penv1 penv2 foracle Hlft
      (fun n w0 H => Hag n w0 (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl H)))))).
    rewrite (IHf penv1 penv2 foracle Hlff
      (fun n w0 H => Hag n w0 (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_intror H)))))).
    reflexivity.
  - rewrite (IHo penv1 penv2 foracle Hlf Hag); reflexivity.
Qed.

Lemma bit1_zero_unsigned :
  (@Integers.unsigned 1%positive (@Integers.zero 1%positive) =? 1)%Z = false.
Proof.
  rewrite (@Integers.unsigned_zero 1%positive); reflexivity.
Qed.

Lemma bit1_one_unsigned :
  (@Integers.unsigned 1%positive (@Integers.one 1%positive) =? 1)%Z = true.
Proof.
  unfold Integers.one; rewrite (@Integers.unsigned_repr 1%positive 1); [reflexivity |].
  unfold Integers.max_unsigned.
  rewrite (@Integers.modulus_two_power_nat 1%positive), (@Integers.natwordsize_def 1%positive).
  vm_compute; split; discriminate.
Qed.

Definition cut_p_dvalue {Pa : Params} (dv_s : @dvalue Pa) : @dvalue Pa :=
  match dv_s with
  | DVALUE_Base DVALUE_Poison => DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.zero 1%positive))
  | _ => DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive))
  end.

Lemma eval_cut_pair {Pa : Params} :
  forall (penv : param_env Pa) k w (dv_s dv_t : @dvalue Pa),
    wf_scalar_dvalue w dv_s ->
    wf_scalar_dvalue w dv_t ->
    dvalue_refines dv_s dv_t ->
    penv (cut_p_name k) = Some (cut_p_dvalue dv_s) ->
    penv (cut_v_name k) = Some dv_t ->
    eval_closed_cert_expr penv dummy_freeze_oracle (cut_src_expr k w) = raise_ret dv_s /\
    eval_closed_cert_expr penv dummy_freeze_oracle (cut_tgt_expr k w) = raise_ret dv_t.
Proof.
  intros penv k w dv_s dv_t Hsc_s Hsc_t Href Hp Hv.
  assert (Hev_t : eval_closed_cert_expr penv dummy_freeze_oracle (cut_tgt_expr k w) = raise_ret dv_t).
  { unfold cut_tgt_expr, eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val].
    rewrite Hv.
    destruct Hsc_t as [-> | [it ->]];
      [reflexivity | cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity]. }
  split; [| exact Hev_t].
  unfold cut_src_expr, eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val].
  assert (Hcw_t : check_scalar_width w dv_t = raise_ret dv_t)
    by (destruct Hsc_t as [-> | [it ->]]; [reflexivity | cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity]).
  rewrite Hp, Hv, Hcw_t.
  destruct Hsc_s as [-> | [is0 ->]].
  - cbn [cut_p_dvalue check_scalar_width]; rewrite Pos.eqb_refl;
      cbn [eou_bind eval_select eval_select_base_dvalue]; rewrite bit1_zero_unsigned; reflexivity.
  - destruct Href as [Habs | ->]; [discriminate Habs |].
    cbn [cut_p_dvalue check_scalar_width]; rewrite Pos.eqb_refl;
      cbn [eou_bind eval_select eval_select_base_dvalue]; rewrite bit1_one_unsigned; reflexivity.
Qed.

Fixpoint cut_names_from (idx : nat) (pspecs : list (raw_id * raw_id * positive))
  {struct pspecs} : list string :=
  match pspecs with
  | [] => []
  | _ :: rest => cut_p_name idx :: cut_v_name idx :: cut_names_from (S idx) rest
  end.

Fixpoint cut_vars_from (idx : nat) (pspecs : list (raw_id * raw_id * positive))
  {struct pspecs} : list (string * positive) :=
  match pspecs with
  | [] => []
  | (_, _, w) :: rest =>
      (cut_p_name idx, 1%positive) :: (cut_v_name idx, w) :: cut_vars_from (S idx) rest
  end.

Fixpoint cut_bindings_from {Pa : Params}
  (idx : nat)
  (pspecs : list (raw_id * raw_id * positive))
  (dvs_s dvs_t : list (raw_id * @dvalue Pa))
  {struct pspecs} : list (string * @dvalue Pa) :=
  match pspecs, dvs_s, dvs_t with
  | _ :: rp, (_, dv_s) :: rs, (_, dv_t) :: rt =>
      (cut_p_name idx, cut_p_dvalue dv_s) ::
      (cut_v_name idx, dv_t) ::
      cut_bindings_from (S idx) rp rs rt
  | _, _, _ => []
  end.

Fixpoint overlay_cut_lmap_s
  (idx : nat) (lmap : rmap (positive * cert_expr))
  (pspecs : list (raw_id * raw_id * positive))
  {struct pspecs} : rmap (positive * cert_expr) :=
  match pspecs with
  | [] => lmap
  | (id_s, _, w) :: rest =>
      overlay_cut_lmap_s (S idx) (RM.add id_s (w, cut_src_expr idx w) lmap) rest
  end.

Fixpoint overlay_cut_lmap_t
  (idx : nat) (lmap : rmap (positive * cert_expr))
  (pspecs : list (raw_id * raw_id * positive))
  {struct pspecs} : rmap (positive * cert_expr) :=
  match pspecs with
  | [] => lmap
  | (_, id_t, w) :: rest =>
      overlay_cut_lmap_t (S idx) (RM.add id_t (w, cut_tgt_expr idx w) lmap) rest
  end.

Inductive cut_phi_rel {Pa : Params}
  : list (raw_id * raw_id * positive) ->
    list (raw_id * @dvalue Pa) ->
    list (raw_id * @dvalue Pa) -> Prop :=
| CPR_Nil : cut_phi_rel [] [] []
| CPR_Cons id_s id_t w dv_s dv_t rest rs rt :
    is_supported_bit_width w = true ->
    wf_scalar_dvalue w dv_s ->
    wf_scalar_dvalue w dv_t ->
    dvalue_refines dv_s dv_t ->
    cut_phi_rel rest rs rt ->
    cut_phi_rel ((id_s, id_t, w) :: rest) ((id_s, dv_s) :: rs) ((id_t, dv_t) :: rt).

Lemma cut_bindings_fst {Pa : Params} :
  forall pspecs (dvs_s dvs_t : list (raw_id * @dvalue Pa)) idx,
    cut_phi_rel pspecs dvs_s dvs_t ->
    List.map fst (cut_bindings_from idx pspecs dvs_s dvs_t) = cut_names_from idx pspecs.
Proof.
  intros pspecs dvs_s dvs_t idx Hrel; revert idx.
  induction Hrel as [| id_s id_t w dv_s dv_t rest rs rt _ _ _ _ _ IH]; intros idx; cbn; [reflexivity |].
  f_equal; f_equal; exact (IH (S idx)).
Qed.

Lemma overlay_cut_lmap_typing :
  forall pspecs idx allowed lmap_s lmap_t,
    Forall (fun '(_, _, w) => is_supported_bit_width w = true) pspecs ->
    incl (cut_vars_from idx pspecs) allowed ->
    wf_pure_lmap allowed lmap_s ->
    wf_pure_lmap allowed lmap_t ->
    wf_pure_lmap allowed (overlay_cut_lmap_s idx lmap_s pspecs) /\
    wf_pure_lmap allowed (overlay_cut_lmap_t idx lmap_t pspecs).
Proof.
  induction pspecs as [| [[id_s id_t] w] rest IH];
    intros idx allowed lmap_s lmap_t Hfa Hinc Hs Ht; cbn [overlay_cut_lmap_s overlay_cut_lmap_t cut_vars_from] in *.
  - split; assumption.
  - inversion Hfa as [| ? ? Hsup Hfa_r]; subst.
    assert (Hin_p : In (cut_p_name idx, 1%positive) allowed) by (apply Hinc; left; reflexivity).
    assert (Hin_v : In (cut_v_name idx, w) allowed) by (apply Hinc; right; left; reflexivity).
    assert (Hinc_r : incl (cut_vars_from (S idx) rest) allowed)
      by (intros u Hu; apply Hinc; right; right; exact Hu).
    assert (Hs' : wf_pure_lmap allowed (RM.add id_s (w, cut_src_expr idx w) lmap_s)).
    { apply wf_pure_lmap_add; try assumption.
      - unfold cut_src_expr; cbn [wt_cert_expr cert_expr_bit_width].
        rewrite cut_p_name_not_dollar, cut_v_name_not_dollar, !Pos.eqb_refl; reflexivity.
      - reflexivity.
      - reflexivity.
      - intros u Hu; cbn [cut_src_expr collect_free_vars] in Hu.
        destruct Hu as [<- | [<- | []]]; assumption. }
    assert (Ht' : wf_pure_lmap allowed (RM.add id_t (w, cut_tgt_expr idx w) lmap_t)).
    { apply wf_pure_lmap_add; try assumption.
      - unfold cut_tgt_expr; cbn [wt_cert_expr]; rewrite cut_v_name_not_dollar; reflexivity.
      - reflexivity.
      - reflexivity.
      - intros u Hu; cbn [cut_tgt_expr collect_free_vars] in Hu; destruct Hu as [<- | []]; exact Hin_v. }
    exact (IH (S idx) allowed _ _ Hfa_r Hinc_r Hs' Ht').
Qed.

Lemma cut_p_dvalue_wf_1 {Pa : Params} :
  forall (dv : @dvalue Pa), wf_scalar_dvalue 1%positive (cut_p_dvalue dv).
Proof.
  intros dv; unfold cut_p_dvalue; destruct dv as [db | |];
    try (right; eexists; reflexivity);
    destruct db; right; eexists; reflexivity.
Qed.

Lemma cut_bindings_wf_param {Pa : Params} :
  forall pspecs (dvs_s dvs_t : list (raw_id * @dvalue Pa)) idx
         (all_bs : list (string * @dvalue Pa)) (penv : param_env Pa),
    cut_phi_rel pspecs dvs_s dvs_t ->
    NoDup (List.map fst all_bs) ->
    incl (cut_bindings_from idx pspecs dvs_s dvs_t) all_bs ->
    wf_param_env_for (cut_vars_from idx pspecs) (extend_penv all_bs penv).
Proof.
  intros pspecs dvs_s dvs_t idx all_bs penv Hrel Hnd.
  revert idx; induction Hrel as [| id_s id_t w dv_s dv_t rest rs rt _ Hsc_s Hsc_t _ _ IH];
    intros idx Hinc nm w0 Hin; cbn [cut_vars_from cut_bindings_from] in *.
  - contradiction Hin.
  - destruct Hin as [Heq | [Heq | Hin_r]].
    + inversion Heq; subst nm w0.
      exists (cut_p_dvalue dv_s); split;
        [apply extend_penv_nodup_in; [exact Hnd | apply Hinc; left; reflexivity]
        | apply cut_p_dvalue_wf_1].
    + inversion Heq; subst nm w0.
      exists dv_t; split;
        [apply extend_penv_nodup_in; [exact Hnd | apply Hinc; right; left; reflexivity]
        | exact Hsc_t].
    + exact (IH (S idx) (fun u Hu => Hinc u (or_intror (or_intror Hu))) nm w0 Hin_r).
Qed.

Lemma overlay_cut_lmap_matches {Pa : Params} :
  forall pspecs (dvs_s dvs_t : list (raw_id * @dvalue Pa)) idx
         (all_bs : list (string * @dvalue Pa)) (penv : param_env Pa)
         lmap_s lmap_t env_s env_t,
    cut_phi_rel pspecs dvs_s dvs_t ->
    NoDup (List.map fst all_bs) ->
    incl (cut_bindings_from idx pspecs dvs_s dvs_t) all_bs ->
    lmap_matches_env (extend_penv all_bs penv) lmap_s env_s ->
    lmap_matches_env (extend_penv all_bs penv) lmap_t env_t ->
    lmap_matches_env (extend_penv all_bs penv)
      (overlay_cut_lmap_s idx lmap_s pspecs) (apply_phi_env env_s dvs_s) /\
    lmap_matches_env (extend_penv all_bs penv)
      (overlay_cut_lmap_t idx lmap_t pspecs) (apply_phi_env env_t dvs_t).
Proof.
  intros pspecs dvs_s dvs_t idx all_bs penv lmap_s lmap_t env_s env_t Hrel Hnd.
  revert idx lmap_s lmap_t env_s env_t.
  induction Hrel as [| id_s id_t w dv_s dv_t rest rs rt _ Hsc_s Hsc_t Href _ IH];
    intros idx lmap_s lmap_t env_s env_t Hinc Hs Ht;
    cbn [overlay_cut_lmap_s overlay_cut_lmap_t apply_phi_env cut_bindings_from] in *.
  - split; assumption.
  - assert (Hp : extend_penv all_bs penv (cut_p_name idx) = Some (cut_p_dvalue dv_s))
      by (apply extend_penv_nodup_in; [exact Hnd | apply Hinc; left; reflexivity]).
    assert (Hv : extend_penv all_bs penv (cut_v_name idx) = Some dv_t)
      by (apply extend_penv_nodup_in; [exact Hnd | apply Hinc; right; left; reflexivity]).
    destruct (eval_cut_pair (extend_penv all_bs penv) idx w dv_s dv_t Hsc_s Hsc_t Href Hp Hv)
      as [Hev_s Hev_t].
    exact (IH (S idx)
             (RM.add id_s (w, cut_src_expr idx w) lmap_s)
             (RM.add id_t (w, cut_tgt_expr idx w) lmap_t)
             (RM.add id_s dv_s env_s)
             (RM.add id_t dv_t env_t)
             (fun u Hu => Hinc u (or_intror (or_intror Hu)))
             (lmap_matches_env_add _ _ _ _ _ _ _ Hs Hev_s Hsc_s)
             (lmap_matches_env_add _ _ _ _ _ _ _ Ht Hev_t Hsc_t)).
Qed.

Fixpoint init_param_lmap
  (params : list raw_id) (src_pnames : list string) (uses : list (nat * dtyp))
  {struct uses} : rmap (positive * cert_expr) :=
  match uses with
  | [] => RM.empty _
  | (idx, DTYPE_Base (DTYPE_I w)) :: rest =>
      let rmap_r := init_param_lmap params src_pnames rest in
      if is_supported_bit_width w then
        match nth_error params idx, nth_error src_pnames idx with
        | Some r, Some pnm =>
            if starts_with_dollar pnm then rmap_r
            else RM.add r (w, CE_Var pnm w) rmap_r
        | _, _ => rmap_r
        end
      else rmap_r
  | _ :: rest => init_param_lmap params src_pnames rest
  end.

Lemma init_param_lmap_typing :
  forall uses params src_pnames allowed,
    (forall idx w pnm,
      In (idx, DTYPE_Base (DTYPE_I w)) uses ->
      nth_error src_pnames idx = Some pnm ->
      In (pnm, w) allowed) ->
    wf_pure_lmap allowed (init_param_lmap params src_pnames uses).
Proof.
  induction uses as [| [idx dt] rest IH]; intros params src_pnames allowed Hpu;
    cbn [init_param_lmap].
  - intros r w ce Hf; rewrite RMF.F.empty_o in Hf; discriminate Hf.
  - pose proof (IH params src_pnames allowed (fun i w0 p Hin => Hpu i w0 p (or_intror Hin))) as Hrest.
    destruct dt as [tb | |]; try exact Hrest; destruct tb as [w | | | | | | | | | |]; try exact Hrest.
    destruct (is_supported_bit_width w) eqn:Hsup; [| exact Hrest].
    destruct (nth_error params idx) as [r |]; [| exact Hrest].
    destruct (nth_error src_pnames idx) as [pnm |] eqn:Hpnm; [| exact Hrest].
    destruct (starts_with_dollar pnm) eqn:Ed; [exact Hrest |].
    apply wf_pure_lmap_add; [exact Hrest | cbn; rewrite Ed; reflexivity | reflexivity | reflexivity |].
    intros u Hu; cbn [collect_free_vars] in Hu; destruct Hu as [<- | []].
    exact (Hpu idx w pnm (or_introl eq_refl) Hpnm).
Qed.

Lemma init_param_lmap_dom :
  forall uses params src_pnames r w ce,
    RM.find r (init_param_lmap params src_pnames uses) = Some (w, ce) ->
    In r params.
Proof.
  induction uses as [| [idx dt] rest IH]; intros params src_pnames r w ce Hf;
    cbn [init_param_lmap] in Hf.
  - rewrite RMF.F.empty_o in Hf; discriminate Hf.
  - destruct dt as [tb | |]; try exact (IH _ _ _ _ _ Hf);
      destruct tb as [w0 | | | | | | | | | |]; try exact (IH _ _ _ _ _ Hf).
    destruct (is_supported_bit_width w0); [| exact (IH _ _ _ _ _ Hf)].
    destruct (nth_error params idx) as [r0 |] eqn:Hnth; [| exact (IH _ _ _ _ _ Hf)].
    destruct (nth_error src_pnames idx) as [pnm |]; [| exact (IH _ _ _ _ _ Hf)].
    destruct (starts_with_dollar pnm); [exact (IH _ _ _ _ _ Hf) |].
    destruct (RawIDOrd.eq_dec r0 r) as [Heq | Hneq].
    + subst r0; exact (nth_error_In params idx Hnth).
    + rewrite RMF.F.add_neq_o in Hf by exact Hneq; exact (IH _ _ _ _ _ Hf).
Qed.

Lemma init_param_lmap_matches {Pa : Params} :
  forall uses params src_pnames arg_dtys (vs : list (@dvalue Pa)),
    NoDup params ->
    NoDup src_pnames ->
    List.length params = List.length vs ->
    List.length src_pnames = List.length vs ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx dt, In (idx, dt) uses -> nth_error arg_dtys idx = Some dt) ->
    lmap_matches_env (build_param_env src_pnames vs)
      (init_param_lmap params src_pnames uses)
      (init_cfg_locals params vs).
Proof.
  induction uses as [| [idx dt] rest IH];
    intros params src_pnames arg_dtys vs Hnd_p Hnd_s Hlp Hls Hvs Hdt;
    cbn [init_param_lmap].
  - intros r w ce Hf; rewrite RMF.F.empty_o in Hf; discriminate Hf.
  - pose proof (IH params src_pnames arg_dtys vs Hnd_p Hnd_s Hlp Hls Hvs
                  (fun i d Hin => Hdt i d (or_intror Hin))) as Hrest.
    destruct dt as [tb | |]; try exact Hrest;
      destruct tb as [w | | | | | | | | | |]; try exact Hrest.
    destruct (is_supported_bit_width w) eqn:Hsup; [| exact Hrest].
    destruct (nth_error params idx) as [r0 |] eqn:Hnth_r; [| exact Hrest].
    destruct (nth_error src_pnames idx) as [pnm |] eqn:Hnth_p; [| exact Hrest].
    destruct (starts_with_dollar pnm) eqn:Ed; [exact Hrest |].
    destruct (init_cfg_locals_nth params vs idx r0 Hnd_p Hlp Hnth_r) as [dv [Hnth_v Hfe]].
    destruct (build_param_env_nth src_pnames vs idx pnm Hnd_s Hls Hnth_p) as [dv' [Hnth_v' Hp]].
    rewrite Hnth_v in Hnth_v'; injection Hnth_v' as <-.
    pose proof (Hdt idx (DTYPE_Base (DTYPE_I w)) (or_introl eq_refl)) as Hnth_dt.
    pose proof (Forall2_nth_error_l dvalue_has_dtyp vs arg_dtys Hvs
                  idx dv (DTYPE_Base (DTYPE_I w)) Hnth_v Hnth_dt) as Hty.
    apply dvalue_has_dtyp_i_iff_wf_scalar in Hty.
    intros r wr cer Hf.
    destruct (RawIDOrd.eq_dec r0 r) as [Heq | Hneq].
    + rewrite RMF.F.add_eq_o in Hf by exact Heq; inversion Hf; subst r wr cer.
      exists dv; split; [exact Hfe | split; [| exact Hty]].
      unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite Hp.
      destruct Hty as [-> | [iv ->]];
        [reflexivity | cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity].
    + rewrite RMF.F.add_neq_o in Hf by exact Hneq; exact (Hrest r wr cer Hf).
Qed.

Lemma apply_phi_env_preserves_not_in {Pa : Params} :
  forall (dvs : list (raw_id * @dvalue Pa)) (env : rmap (@dvalue Pa)) r,
    ~ In r (List.map fst dvs) ->
    RM.find r (apply_phi_env env dvs) = RM.find r env.
Proof.
  induction dvs as [| [id dv] rest IH]; intros env r Hnin; cbn in *; [reflexivity |].
  rewrite (IH (RM.add id dv env) r (fun H => Hnin (or_intror H))).
  rewrite RMF.F.add_neq_o; [reflexivity | intros ->; exact (Hnin (or_introl eq_refl))].
Qed.

Lemma lmap_dom_code :
  forall c lmap0 cevals lmap2 dom0,
    (forall r w ce, RM.find r lmap0 = Some (w, ce) -> In r dom0) ->
    reify_pure_code lmap0 c = Some (cevals, lmap2) ->
    forall r w ce, RM.find r lmap2 = Some (w, ce) -> In r (dom0 ++ code_written_ids c).
Proof.
  induction c as [| [[iid ins] md] rest IH];
    intros lmap0 cevals lmap2 dom0 Hdom0 Hr r w ce Hf;
    cbn [reify_pure_code code_written_ids] in *.
  - inversion Hr; subst; rewrite app_nil_r; exact (Hdom0 r w ce Hf).
  - destruct iid as [id | vid]; destruct ins; try discriminate Hr.
    + destruct (reify_pure_exp lmap0 None op) as [[w0 ce0] |]; [| discriminate Hr].
      destruct (reify_pure_code (RM.add id (w0, ce0) lmap0) rest) as [[cr l2] |] eqn:Hrr; [| discriminate Hr].
      inversion Hr; subst cevals lmap2; clear Hr.
      assert (Hdom1 :
        forall r' w' ce', RM.find r' (RM.add id (w0, ce0) lmap0) = Some (w', ce') -> In r' (dom0 ++ [id])).
      { intros r' w' ce' Hf'.
        destruct (RawIDOrd.eq_dec id r') as [<- | Hneq].
        - apply in_app_iff; right; left; reflexivity.
        - rewrite RMF.F.add_neq_o in Hf' by exact Hneq; apply in_app_iff; left; exact (Hdom0 r' w' ce' Hf'). }
      pose proof (IH _ _ _ _ Hdom1 Hrr r w ce Hf) as Hin.
      rewrite <- app_assoc in Hin; exact Hin.
    + exact (IH _ _ _ _ Hdom0 Hr r w ce Hf).
Qed.

Lemma lmap_matches_env_transfer {Pa : Params} :
  forall allowed dom (penv1 penv2 : param_env Pa) lmap (env1 env2 : rmap (@dvalue Pa)),
    wf_pure_lmap allowed lmap ->
    (forall r w ce, RM.find r lmap = Some (w, ce) -> In r dom) ->
    (forall nm w, In (nm, w) allowed -> penv1 nm = penv2 nm) ->
    (forall r, In r dom -> RM.find r env2 = RM.find r env1) ->
    lmap_matches_env penv1 lmap env1 ->
    lmap_matches_env penv2 lmap env2.
Proof.
  intros allowed dom penv1 penv2 lmap env1 env2 Hwf Hdom Hp He Henv r w ce Hf.
  destruct (Henv r w ce Hf) as [dv [Hfe1 [Hev1 Hsc]]].
  destruct (Hwf r w ce Hf) as (_ & _ & Hlf & Hfv).
  exists dv; split; [rewrite (He r (Hdom r w ce Hf)); exact Hfe1 | split; [| exact Hsc]].
  rewrite <- (eval_let_free_penv_agree ce penv1 penv2 dummy_freeze_oracle Hlf
               (fun nm w0 Hin => Hp nm w0 (Hfv (nm, w0) Hin))).
  exact Hev1.
Qed.

Inductive pure_cfg_steps_to_tau {Pa : Params} {R : Type}
  : rmap (@dvalue Pa) -> CFGtop R -> rmap (@dvalue Pa) -> CFGtop R -> Prop :=
| PCT_Tau env (t m : CFGtop R) :
    observe t = TauF m ->
    pure_cfg_steps_to_tau env t env m
| PCT_StepTau env (t t' : CFGtop R) env' m :
    observe t = TauF t' ->
    pure_cfg_steps_to_tau env t' env' m ->
    pure_cfg_steps_to_tau env t env' m
| PCT_LocalRead env (t : CFGtop R) id dv (k : @dvalue Pa -> CFGtop R) env' m :
    observe t = VisF (@subevent LocalE CFGEtop _ (@dvalue Pa) (LocalRead id)) k ->
    RM.find id env = Some dv ->
    pure_cfg_steps_to_tau env (k dv) env' m ->
    pure_cfg_steps_to_tau env t env' m
| PCT_LocalWrite env (t : CFGtop R) id dv (k : unit -> CFGtop R) env' m :
    observe t = VisF (@subevent LocalE CFGEtop _ unit (LocalWrite id dv)) k ->
    pure_cfg_steps_to_tau (RM.add id dv env) (k tt) env' m ->
    pure_cfg_steps_to_tau env t env' m.

Lemma pure_cfg_steps_to_tau_obs {Pa : Params} {R : Type} :
  forall env (t1 t2 : CFGtop R) env' m,
    observe t1 = observe t2 ->
    @pure_cfg_steps_to_tau Pa R env t1 env' m ->
    @pure_cfg_steps_to_tau Pa R env t2 env' m.
Proof.
  intros env t1 t2 env' m Ho H.
  inversion H; subst;
    [apply PCT_Tau | eapply PCT_StepTau | eapply PCT_LocalRead | eapply PCT_LocalWrite];
    try (rewrite <- Ho; eassumption); eassumption.
Qed.

Lemma pure_cfg_steps_bind_to_tau {Pa : Params} {R S : Type} :
  forall env0 (t : CFGtop R) env1 x (k : R -> CFGtop S) env2 m,
    @pure_cfg_steps Pa R env0 t env1 x ->
    @pure_cfg_steps_to_tau Pa S env1 (k x) env2 m ->
    @pure_cfg_steps_to_tau Pa S env0 (ITree.bind t k) env2 m.
Proof.
  intros env0 t env1 x k env2 m H1 H2.
  induction H1 as
    [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH].
  - eapply pure_cfg_steps_to_tau_obs; [symmetry; rewrite observe_bind, Ho; reflexivity | exact H2].
  - eapply PCT_StepTau; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
  - eapply PCT_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact (IH H2)].
  - eapply PCT_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact (IH H2)].
Qed.

Lemma pure_cfg_steps_to_tau_bind {Pa : Params} {R S : Type} :
  forall env0 (t : CFGtop R) env1 m (k : R -> CFGtop S),
    @pure_cfg_steps_to_tau Pa R env0 t env1 m ->
    @pure_cfg_steps_to_tau Pa S env0 (ITree.bind t k) env1 (ITree.bind m k).
Proof.
  intros env0 t env1 m k H.
  induction H as
    [env t m Ho | env t t' env' m Ho _ IH | env t id dv ke env' m Ho Hf _ IH | env t id dv ke env' m Ho _ IH].
  - apply PCT_Tau; rewrite observe_bind, Ho; reflexivity.
  - eapply PCT_StepTau; [rewrite observe_bind, Ho; reflexivity | exact IH].
  - eapply PCT_LocalRead; [rewrite observe_bind, Ho; reflexivity | exact Hf | exact IH].
  - eapply PCT_LocalWrite; [rewrite observe_bind, Ho; reflexivity | exact IH].
Qed.

Lemma pure_cfg_steps_to_tau_trans {Pa : Params} {R : Type} :
  forall env0 (t0 : CFGtop R) env1 m1 env2 m2,
    @pure_cfg_steps_to_tau Pa R env0 t0 env1 m1 ->
    @pure_cfg_steps_to_tau Pa R env1 m1 env2 m2 ->
    @pure_cfg_steps_to_tau Pa R env0 t0 env2 m2.
Proof.
  intros env0 t0 env1 m1 env2 m2 H1 H2.
  induction H1 as
    [env t m Ho | env t t' env' m Ho _ IH | env t id dv ke env' m Ho Hf _ IH | env t id dv ke env' m Ho _ IH].
  - eapply PCT_StepTau; [exact Ho | exact H2].
  - eapply PCT_StepTau; [exact Ho | exact (IH H2)].
  - eapply PCT_LocalRead; [exact Ho | exact Hf | exact (IH H2)].
  - eapply PCT_LocalWrite; [exact Ho | exact (IH H2)].
Qed.

Lemma pure_cfg_steps_to_tau_then_ret {Pa : Params} {R : Type} :
  forall env0 (t0 : CFGtop R) env1 m1 env2 v,
    @pure_cfg_steps_to_tau Pa R env0 t0 env1 m1 ->
    @pure_cfg_steps Pa R env1 m1 env2 v ->
    @pure_cfg_steps Pa R env0 t0 env2 v.
Proof.
  intros env0 t0 env1 m1 env2 v H1 H2.
  induction H1 as
    [env t m Ho | env t t' env' m Ho _ IH | env t id dv ke env' m Ho Hf _ IH | env t id dv ke env' m Ho _ IH].
  - eapply PCS_Tau; [exact Ho | exact H2].
  - eapply PCS_Tau; [exact Ho | exact (IH H2)].
  - eapply PCS_LocalRead; [exact Ho | exact Hf | exact (IH H2)].
  - eapply PCS_LocalWrite; [exact Ho | exact (IH H2)].
Qed.

Lemma pure_cfg_steps_to_tau_then_ub {Pa : Params} {R : Type} :
  forall (sigma : @draw_strat Pa) env0 (t0 : CFGtop R) env1 m1,
    @pure_cfg_steps_to_tau Pa R env0 t0 env1 m1 ->
    cfg_steps_to_ub sigma env1 m1 ->
    cfg_steps_to_ub sigma env0 t0.
Proof.
  intros sigma env0 t0 env1 m1 H1 H2.
  induction H1 as
    [env t m Ho | env t t' env' m Ho _ IH | env t id dv ke env' m Ho Hf _ IH | env t id dv ke env' m Ho _ IH].
  - eapply CSU_Tau; [exact Ho | exact H2].
  - eapply CSU_Tau; [exact Ho | exact (IH H2)].
  - eapply CSU_LocalRead; [exact Ho | exact Hf | exact (IH H2)].
  - eapply CSU_LocalWrite; [exact Ho | exact (IH H2)].
Qed.

Lemma pure_cfg_steps_to_tau_det_ref_l {Pa : Params} {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop)
  (self : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop) :
  forall (s1 : @draw_strat Pa) env1 (t1 : CFGtop R1) env1' m1 (u2 : itree (@Det_OW_E Pa) R2),
    @pure_cfg_steps_to_tau Pa R1 env1 t1 env1' m1 ->
    det_ref_ (Pa := Pa) RR self
      (run_draws s1 (run_cfg_locals env1' m1)) u2 ->
    det_ref_ (Pa := Pa) RR self
      (run_draws s1 (run_cfg_locals env1 t1)) u2.
Proof.
  intros s1 env1 t1 env1' m1 u2 H1 Hk.
  induction H1 as
    [env t m Ho | env t t' env' m Ho _ IH | env t id dv ke env' m Ho Hf _ IH | env t id dv ke env' m Ho _ IH].
  - eapply DR_TauL; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | exact Hk].
  - eapply DR_TauL; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | exact (IH Hk)].
  - eapply DR_TauL;
      [rewrite observe_run_draws, observe_run_cfg_locals, Ho; cbn; rewrite Hf; reflexivity | exact (IH Hk)].
  - eapply DR_TauL; [rewrite observe_run_draws, observe_run_cfg_locals, Ho; reflexivity | exact (IH Hk)].
Qed.

Lemma pure_cfg_steps_to_tau_sync {Pa : Params} {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop)
  (self : itree (@Det_OW_E Pa) R1 -> itree (@Det_OW_E Pa) R2 -> Prop) :
  forall (s1 s2 : @draw_strat Pa)
         env1 (t1 : CFGtop R1) env1' m1
         env2 (t2 : CFGtop R2) env2' m2,
    @pure_cfg_steps_to_tau Pa R1 env1 t1 env1' m1 ->
    @pure_cfg_steps_to_tau Pa R2 env2 t2 env2' m2 ->
    self (run_draws s1 (run_cfg_locals env1' m1))
         (run_draws s2 (run_cfg_locals env2' m2)) ->
    det_ref_ (Pa := Pa) RR self
      (run_draws s1 (run_cfg_locals env1 t1))
      (run_draws s2 (run_cfg_locals env2 t2)).
Proof.
  intros s1 s2 env1 t1 env1' m1 env2 t2 env2' m2 H1 H2 Hself.
  induction H1 as
    [env t m Ho1 | env t t' env' m Ho1 _ IH1 | env t id dv ke env' m Ho1 Hf _ IH1 | env t id dv ke env' m Ho1 _ IH1].
  - induction H2 as
      [eb tb mb Ho2 | eb tb tb' eb' mb Ho2 _ IH2 | eb tb id dv ke eb' mb Ho2 Hf _ IH2
      | eb tb id dv ke eb' mb Ho2 _ IH2].
    + apply DR_Step; unfold det_step_body.
      rewrite !observe_run_draws, !observe_run_cfg_locals, Ho1, Ho2; exact Hself.
    + eapply DR_TauR; [rewrite observe_run_draws, observe_run_cfg_locals, Ho2; reflexivity | exact (IH2 Hself)].
    + eapply DR_TauR;
        [rewrite observe_run_draws, observe_run_cfg_locals, Ho2; cbn; rewrite Hf; reflexivity | exact (IH2 Hself)].
    + eapply DR_TauR; [rewrite observe_run_draws, observe_run_cfg_locals, Ho2; reflexivity | exact (IH2 Hself)].
  - eapply DR_TauL; [rewrite observe_run_draws, observe_run_cfg_locals, Ho1; reflexivity | exact (IH1 Hself)].
  - eapply DR_TauL;
      [rewrite observe_run_draws, observe_run_cfg_locals, Ho1; cbn; rewrite Hf; reflexivity | exact (IH1 Hself)].
  - eapply DR_TauL; [rewrite observe_run_draws, observe_run_cfg_locals, Ho1; reflexivity | exact (IH1 Hself)].
Qed.

Lemma denote_ocfg_map_step_varargs_obs {Pa : Params} :
  forall (bmap : rmap (block dtyp)) (varargs : option (@ptr _ (@PTR Pa)))
         (bid_from bid_cur : block_id) (b : block dtyp),
    RM.find bid_cur bmap = Some b ->
    observe (@denote_ocfg_map Pa bmap varargs (bid_from, bid_cur)) =
    observe (ITree.bind
      (ITree.bind (denote_block b bid_from varargs)
        (fun bd => match bd with
                   | inr dv => Ret (inr (inr dv))
                   | inl bid_target => Ret (inl (bid_cur, bid_target))
                   end))
      (fun lr => match lr with
                 | inl j => Tau (denote_ocfg_map bmap varargs j)
                 | inr r => Ret r
                 end)).
Proof.
  intros bmap varargs bid_from bid_cur b Hf.
  unfold denote_ocfg_map; rewrite observe_iter; cbn beta; rewrite Hf; reflexivity.
Qed.

Definition denote_cfg_from {Pa : Params}
  (bmap : rmap (block dtyp)) (varargs : option (@ptr _ (@PTR Pa)))
  (j : block_id * block_id) : CFGtop (@dvalue Pa) :=
  r <- @denote_ocfg_map Pa bmap varargs j ;;
  match r with
  | inl bid => raise ("Can't find block in denote_cfg " ++ show (snd bid))%string
  | inr uv => ret uv
  end.

Lemma denote_cfg_from_block_ub {Pa : Params} :
  forall bmap varargs bid_from bid_cur b (sigma : @draw_strat Pa) env,
    RM.find bid_cur bmap = Some b ->
    cfg_steps_to_ub sigma env (denote_block b bid_from varargs) ->
    cfg_steps_to_ub sigma env (@denote_cfg_from Pa bmap varargs (bid_from, bid_cur)).
Proof.
  intros bmap varargs bid_from bid_cur b sigma env Hfb Hub.
  unfold denote_cfg_from; apply cfg_steps_to_ub_bind_l.
  eapply cfg_steps_to_ub_obs; [symmetry; exact (denote_ocfg_map_step_varargs_obs _ _ _ _ _ Hfb) |].
  apply cfg_steps_to_ub_bind_l, cfg_steps_to_ub_bind_l; exact Hub.
Qed.

Lemma denote_cfg_from_block_jump {Pa : Params} :
  forall bmap varargs bid_from bid_cur b env0 env1 bid_next,
    RM.find bid_cur bmap = Some b ->
    @pure_cfg_steps Pa (block_id + @dvalue Pa) env0 (denote_block b bid_from varargs) env1 (inl bid_next) ->
    @pure_cfg_steps_to_tau Pa (@dvalue Pa)
      env0 (denote_cfg_from bmap varargs (bid_from, bid_cur))
      env1 (denote_cfg_from bmap varargs (bid_cur, bid_next)).
Proof.
  intros bmap varargs bid_from bid_cur b env0 env1 bid_next Hfb Hst.
  unfold denote_cfg_from; apply pure_cfg_steps_to_tau_bind.
  eapply pure_cfg_steps_to_tau_obs; [symmetry; exact (denote_ocfg_map_step_varargs_obs _ _ _ _ _ Hfb) |].
  eapply pure_cfg_steps_bind_to_tau.
  - eapply pure_cfg_steps_bind; [exact Hst | apply PCS_Ret; reflexivity].
  - apply PCT_Tau; reflexivity.
Qed.

Lemma denote_cfg_from_block_ret {Pa : Params} :
  forall bmap varargs bid_from bid_cur b env0 env1 dv,
    RM.find bid_cur bmap = Some b ->
    @pure_cfg_steps Pa (block_id + @dvalue Pa) env0 (denote_block b bid_from varargs) env1 (inr dv) ->
    @pure_cfg_steps Pa (@dvalue Pa)
      env0 (denote_cfg_from bmap varargs (bid_from, bid_cur))
      env1 dv.
Proof.
  intros bmap varargs bid_from bid_cur b env0 env1 dv Hfb Hst.
  unfold denote_cfg_from; eapply pure_cfg_steps_bind.
  - eapply pure_cfg_steps_obs; [symmetry; exact (denote_ocfg_map_step_varargs_obs _ _ _ _ _ Hfb) |].
    eapply pure_cfg_steps_bind.
    + eapply pure_cfg_steps_bind; [exact Hst | apply PCS_Ret; reflexivity].
    + apply PCS_Ret; reflexivity.
  - apply PCS_Ret; reflexivity.
Qed.

Definition eff_loop_cond (pol : bool) (ce : cert_expr) : cert_expr :=
  if pol then ce
  else CE_Select 1%positive ce (CE_BvConst 1%positive 0%N) (CE_BvConst 1%positive 1%N).

Lemma bit1_repr_zero_unsigned :
  (@Integers.unsigned 1%positive (@Integers.repr 1%positive (Z.of_N 0%N)) =? 1)%Z = false.
Proof.
  cbn [Z.of_N]; rewrite (@Integers.unsigned_repr 1%positive 0); [reflexivity |].
  unfold Integers.max_unsigned.
  rewrite (@Integers.modulus_two_power_nat 1%positive), (@Integers.natwordsize_def 1%positive).
  vm_compute; split; discriminate.
Qed.

Lemma bit1_repr_one_unsigned :
  (@Integers.unsigned 1%positive (@Integers.repr 1%positive (Z.of_N 1%N)) =? 1)%Z = true.
Proof.
  cbn [Z.of_N]; rewrite (@Integers.unsigned_repr 1%positive 1); [reflexivity |].
  unfold Integers.max_unsigned.
  rewrite (@Integers.modulus_two_power_nat 1%positive), (@Integers.natwordsize_def 1%positive).
  vm_compute; split; discriminate.
Qed.

Lemma eval_eff_loop_cond {Pa : Params} :
  forall (penv : param_env Pa) pol ce (cbit : @Integers.bit_int 1),
    eval_closed_cert_expr penv dummy_freeze_oracle ce =
    raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit)) ->
    exists ebit : @Integers.bit_int 1,
      eval_closed_cert_expr penv dummy_freeze_oracle (eff_loop_cond pol ce) =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1 ebit)) /\
      (@Integers.unsigned 1 ebit =? 1)%Z = Bool.eqb (@Integers.unsigned 1 cbit =? 1)%Z pol.
Proof.
  intros penv pol ce cbit Hev; destruct pol; cbn [eff_loop_cond].
  - exists cbit; split; [exact Hev | destruct (@Integers.unsigned 1 cbit =? 1)%Z; reflexivity].
  - unfold eval_closed_cert_expr in *; cbn [eval_cert_expr]; rewrite Hev;
      cbn [eou_bind eval_select eval_select_base_dvalue].
    destruct (@Integers.unsigned 1 cbit =? 1)%Z.
    + exists (@Integers.repr 1%positive (Z.of_N 0%N)); split; [reflexivity | exact bit1_repr_zero_unsigned].
    + exists (@Integers.repr 1%positive (Z.of_N 1%N)); split; [reflexivity | exact bit1_repr_one_unsigned].
Qed.

Fixpoint extract_hdr_phi_specs
  (phis : list (local_id * phi dtyp * list (metadata dtyp)))
  {struct phis} : option (list (raw_id * positive)) :=
  match phis with
  | [] => Some []
  | (id, Phi _ (DTYPE_Base (DTYPE_I w)) _, _) :: rest =>
      if is_supported_bit_width w then
        match extract_hdr_phi_specs rest with
        | Some r => Some ((id, w) :: r)
        | None => None
        end
      else None
  | _ :: _ => None
  end.

Fixpoint pair_phi_specs
  (xs ys : list (raw_id * positive))
  {struct xs} : option (list (raw_id * raw_id * positive)) :=
  match xs, ys with
  | [], [] => Some []
  | (id_s, w_s) :: rx, (id_t, w_t) :: ry =>
      if Pos.eqb w_s w_t && is_supported_bit_width w_s then
        match pair_phi_specs rx ry with
        | Some r => Some ((id_s, id_t, w_s) :: r)
        | None => None
        end
      else None
  | _, _ => None
  end.

Lemma pair_phi_specs_supported :
  forall xs ys pspecs,
    pair_phi_specs xs ys = Some pspecs ->
    Forall (fun '(_, _, w) => is_supported_bit_width w = true) pspecs.
Proof.
  induction xs as [| [id_s w_s] rx IH]; intros ys pspecs H;
    destruct ys as [| [id_t w_t] ry]; cbn [pair_phi_specs] in H; try discriminate H.
  - inversion H; constructor.
  - destruct (Pos.eqb w_s w_t && is_supported_bit_width w_s) eqn:E; [| discriminate H].
    apply andb_true_iff in E as [_ Hsup].
    destruct (pair_phi_specs rx ry) as [r |] eqn:Er; [| discriminate H].
    inversion H; subst; constructor; [exact Hsup | exact (IH ry r Er)].
Qed.

Fixpoint check_pevals_refine
  (ctx : ub_ctx) (opt_pf : option (list lrat_step))
  (pspecs : list (raw_id * raw_id * positive))
  (pevals_s pevals_t : list (raw_id * positive * cert_expr))
  {struct pspecs} : bool :=
  match pspecs, pevals_s, pevals_t with
  | [], [], [] => true
  | (id_s, id_t, w) :: rp, (id_s', w_s, ce_s) :: rs, (id_t', w_t, ce_t) :: rt =>
      raw_id_eqb id_s id_s' && raw_id_eqb id_t id_t' &&
      Pos.eqb w w_s && Pos.eqb w w_t &&
      is_supported_bit_width w &&
      check_expr_refines_with_lrat ctx ce_s ce_t opt_pf &&
      check_pevals_refine ctx opt_pf rp rs rt
  | _, _, _ => false
  end.

Lemma check_pevals_refine_sound {Pa : Params} :
  forall pspecs pevals_s pevals_t dvs_s dvs_t allowed ctx opt_pf (penv : param_env Pa),
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv dummy_freeze_oracle ctx ->
    Forall (fun '(_, w, ce) =>
      is_supported_bit_width w = true /\ cert_expr_bit_width ce = w /\ wf_pure_eval_entry allowed ce) pevals_s ->
    Forall (fun '(_, w, ce) =>
      is_supported_bit_width w = true /\ cert_expr_bit_width ce = w /\ wf_pure_eval_entry allowed ce) pevals_t ->
    Forall2 (phi_eval_pair_matches penv dummy_freeze_oracle) pevals_s dvs_s ->
    Forall2 (phi_eval_pair_matches penv dummy_freeze_oracle) pevals_t dvs_t ->
    check_pevals_refine ctx opt_pf pspecs pevals_s pevals_t = true ->
    cut_phi_rel pspecs dvs_s dvs_t /\
    List.map fst dvs_s = List.map (fun '(id_s, _, _) => id_s) pspecs /\
    List.map fst dvs_t = List.map (fun '(_, id_t, _) => id_t) pspecs.
Proof.
  induction pspecs as [| [[id_s id_t] w] rp IH];
    intros pevals_s pevals_t dvs_s dvs_t allowed ctx opt_pf penv Hpenv Hctx Hfas Hfat Hms Hmt Hchk;
    destruct pevals_s as [| [[id_s' w_s] ce_s] rs];
    destruct pevals_t as [| [[id_t' w_t] ce_t] rt];
    cbn [check_pevals_refine] in Hchk; try discriminate Hchk.
  - inversion Hms; inversion Hmt; subst; repeat split; constructor.
  - rewrite !andb_true_iff in Hchk.
    destruct Hchk as ((((((Heqs & Heqt) & Hws) & Hwt) & Hsup) & Href) & Hrest).
    apply raw_id_eqb_eq in Heqs; apply raw_id_eqb_eq in Heqt;
      apply Pos.eqb_eq in Hws; apply Pos.eqb_eq in Hwt; subst id_s' id_t' w_s w_t.
    unfold wf_pure_eval_entry in Hfas, Hfat.
    inversion Hfas as [| ? ? Hhds Hfas_r]; subst.
    cbn in Hhds; destruct Hhds as (_ & _ & (_ & _ & Hfvs)).
    inversion Hfat as [| ? ? Hhdt Hfat_r]; subst.
    cbn in Hhdt; destruct Hhdt as (_ & _ & (_ & _ & Hfvt)).
    inversion Hms as [| ? [id_sd dv_s] ? dvs_sr Hpms Hms_r]; subst.
    cbn [phi_eval_pair_matches] in Hpms; destruct Hpms as [-> [Hev_s Hsc_s]].
    inversion Hmt as [| ? [id_td dv_t] ? dvs_tr Hpmt Hmt_r]; subst.
    cbn [phi_eval_pair_matches] in Hpmt; destruct Hpmt as [-> [Hev_t Hsc_t]].
    pose proof (fun nm w0 H => Hpenv nm w0 (Hfvs (nm, w0) H)) as Hps.
    pose proof (fun nm w0 H => Hpenv nm w0 (Hfvt (nm, w0) H)) as Hpt.
    pose proof (check_expr_refines_with_lrat_sound ctx ce_s ce_t opt_pf penv
                  dummy_freeze_oracle Href Hps Hpt Hctx) as Hdv.
    rewrite Hev_s, Hev_t in Hdv; cbn [refine_eou_dvalue] in Hdv.
    destruct (IH rs rt dvs_sr dvs_tr allowed ctx opt_pf penv Hpenv Hctx Hfas_r Hfat_r Hms_r Hmt_r Hrest)
      as (Hrel_r & Hmap_s & Hmap_t).
    split; [exact (CPR_Cons id_s id_t w dv_s dv_t rp dvs_sr dvs_tr Hsup Hsc_s Hsc_t Hdv Hrel_r) |].
    cbn; split; f_equal; assumption.
Qed.

Definition disjoint_raw_ids (xs ys : list raw_id) : bool :=
  forallb (fun x => negb (raw_id_in_list x ys)) xs.

Lemma disjoint_raw_ids_spec :
  forall xs ys r,
    disjoint_raw_ids xs ys = true ->
    In r xs ->
    ~ In r ys.
Proof.
  intros xs ys r Hdisj Hin Hiny.
  unfold disjoint_raw_ids in Hdisj; rewrite forallb_forall in Hdisj.
  pose proof (Hdisj r Hin) as Hnr.
  apply raw_id_in_list_spec in Hiny; rewrite Hiny in Hnr; discriminate Hnr.
Qed.

Lemma exprs_safe_under_src_sound {Pa : Params} :
  forall es allowed ctx src_evals (penv : param_env Pa),
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv dummy_freeze_oracle ctx ->
    (forall big, In big src_evals -> exists dv, eval_closed_cert_expr penv dummy_freeze_oracle big = raise_ret dv) ->
    Forall (wf_pure_eval_entry allowed) es ->
    forallb (expr_safe_under_src ctx src_evals) es = true ->
    forall ce msg, In ce es -> eval_closed_cert_expr penv dummy_freeze_oracle ce <> raise_ub msg.
Proof.
  intros es allowed ctx src_evals penv Hpenv Hctx Hsrc Hfa Hsafe ce msg Hin Hev.
  rewrite Forall_forall in Hfa; rewrite forallb_forall in Hsafe.
  destruct (Hfa ce Hin) as (Hwt & _ & Hfv).
  pose proof (Hsafe ce Hin) as Hsc.
  pose proof (fun nm w0 H => Hpenv nm w0 (Hfv (nm, w0) H)) as Hpce.
  destruct (expr_safe_under_src_sound ce ctx src_evals penv dummy_freeze_oracle Hsc Hwt Hpce Hctx Hsrc)
    as [dv [Hret _]].
  rewrite Hret in Hev; discriminate Hev.
Qed.

Definition peval_exprs (pevals : list (raw_id * positive * cert_expr)) : list cert_expr :=
  List.map (fun '(_, _, ce) => ce) pevals.

Lemma peval_exprs_typing :
  forall allowed pevals,
    Forall (fun '(_, w, ce) =>
      is_supported_bit_width w = true /\ cert_expr_bit_width ce = w /\ wf_pure_eval_entry allowed ce) pevals ->
    Forall (wf_pure_eval_entry allowed) (peval_exprs pevals).
Proof.
  intros allowed pevals Hfa; induction Hfa as [| [[id w] ce] rest (_ & _ & Hwf) _ IH];
    cbn [peval_exprs List.map]; [constructor | constructor; assumption].
Qed.

Lemma peval_exprs_ret {Pa : Params} :
  forall (penv : param_env Pa) pevals dvs,
    Forall2 (phi_eval_pair_matches penv dummy_freeze_oracle) pevals dvs ->
    Forall (fun ce => exists dv, eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv)
      (peval_exprs pevals).
Proof.
  intros penv pevals dvs Hfa2.
  induction Hfa2 as [| [[id w] ce] [id' dv] rp rd [_ [Hev _]] _ IH];
    cbn [peval_exprs List.map]; [constructor | constructor; [exists dv; exact Hev | exact IH]].
Qed.

Lemma pure_phis_denote_step {Pa : Params} :
  forall phis (penv : param_env Pa) bid_from lmap (env : rmap (@dvalue Pa)) pevals,
    lmap_matches_env penv lmap env ->
    reify_pure_phis bid_from lmap phis = Some pevals ->
    ((forall sigma, cfg_steps_to_ub sigma env (denote_phis bid_from phis)) /\
     exists ce msg,
       In ce (peval_exprs pevals) /\
       eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ub msg) \/
    (exists dvs,
       Forall2 (phi_eval_pair_matches penv dummy_freeze_oracle) pevals dvs /\
       pure_cfg_steps env (denote_phis bid_from phis) (apply_phi_env env dvs) tt).
Proof.
  intros phis penv bid_from lmap env pevals Henv Hr.
  destruct (eval_reified_pure_phis phis penv bid_from lmap env pevals Henv Hr)
    as [[Hub (id & w & ce & msg & Hin & Hev)] | [dvs [Hpm Hst]]].
  - left; split.
    + intros sigma; unfold denote_phis; apply cfg_steps_to_ub_bind_l; exact (Hub sigma).
    + exists ce, msg; split; [| exact Hev].
      unfold peval_exprs; exact (in_map (fun '(_, _, e) => e) pevals (id, w, ce) Hin).
  - right; exists dvs; split; [exact Hpm |].
    unfold denote_phis; eapply pure_cfg_steps_bind; [exact Hst |].
    eapply pure_cfg_steps_bind; [apply pure_cfg_steps_lwrite_list | apply PCS_Ret; reflexivity].
Qed.

Definition is_latch_edge_b (bmap : rmap (block dtyp)) (bid_hdr br : block_id) : bool :=
  if raw_id_eqb br bid_hdr then true
  else
    match RM.find br bmap with
    | Some b_body =>
        list_empty_b (blk_phis b_body) &&
        match blk_term b_body with
        | (_, TERM_Br_1 br_back, _) => raw_id_eqb br_back bid_hdr
        | _ => false
        end
    | None => false
    end.

Record natural_loop_summary : Type := mk_natural_loop_summary {
  nls_bid_hdr : block_id;
  nls_bid_latch_entry : block_id;
  nls_bid_latch_from : block_id;
  nls_bid_exit : block_id;
  nls_latch_on_true : bool;
  nls_evals_entry : list cert_expr;
  nls_lmap_entry : rmap (positive * cert_expr);
  nls_init_pevals : list (raw_id * positive * cert_expr);
  nls_evals_hdr : list cert_expr;
  nls_lmap_hdr_c : rmap (positive * cert_expr);
  nls_ce_cond : cert_expr;
  nls_evals_body : list cert_expr;
  nls_lmap_latch : rmap (positive * cert_expr);
  nls_next_pevals : list (raw_id * positive * cert_expr);
  nls_evals_exit : list cert_expr;
  nls_w_ret : positive;
  nls_ce_ret : cert_expr;
}.

Definition reify_natural_loop
  (G : CFG.cfg dtyp)
  (hdr_name : string)
  (lmap0 : rmap (positive * cert_expr))
  (wrap_cut : rmap (positive * cert_expr) -> list (raw_id * positive) -> rmap (positive * cert_expr))
  : option (list (raw_id * positive) * natural_loop_summary) :=
  let bmap := ocfg_map (blks G) in
  match RM.find (init G) bmap with
  | None => None
  | Some b_entry =>
      if negb (list_empty_b (blk_phis b_entry)) then None
      else
        match blk_term b_entry with
        | (_, TERM_Br_1 bid_hdr, _) =>
            if negb (cert_block_matches_id hdr_name bid_hdr) || raw_id_eqb bid_hdr (init G) then None
            else
              match RM.find bid_hdr bmap, reify_pure_code lmap0 (blk_code b_entry) with
              | Some b_hdr, Some (evals_entry, lmap_entry) =>
                  match extract_hdr_phi_specs (blk_phis b_hdr),
                        reify_pure_phis (init G) lmap_entry (blk_phis b_hdr) with
                  | Some hspecs, Some init_pevals =>
                      let lmap_hdr0 := wrap_cut lmap_entry hspecs in
                      match reify_pure_code lmap_hdr0 (blk_code b_hdr) with
                      | None => None
                      | Some (evals_hdr, lmap_hdr_c) =>
                          match blk_term b_hdr with
                          | (_, TERM_Br (DTYPE_Base (DTYPE_I 1%positive), op_cond) br1 br2, _) =>
                              match reify_pure_exp lmap_hdr_c (Some (DTYPE_Base (DTYPE_I 1%positive))) op_cond with
                              | None => None
                              | Some (_, ce_cond) =>
                                  let l1 := is_latch_edge_b bmap bid_hdr br1 in
                                  let l2 := is_latch_edge_b bmap bid_hdr br2 in
                                  let opt_pol :=
                                    if l1 && negb l2 then Some (true, br1, br2)
                                    else if l2 && negb l1 then Some (false, br2, br1)
                                    else None in
                                  match opt_pol with
                                  | None => None
                                  | Some (pol, br_latch, br_exit) =>
                                      let opt_latch :=
                                        if raw_id_eqb br_latch bid_hdr then
                                          Some (bid_hdr, [], lmap_hdr_c, [] : list raw_id)
                                        else
                                          match RM.find br_latch bmap with
                                          | Some b_body =>
                                              if list_empty_b (blk_phis b_body) then
                                                match blk_term b_body, reify_pure_code lmap_hdr_c (blk_code b_body) with
                                                | (_, TERM_Br_1 br_back, _), Some (evals_body, lmap_latch) =>
                                                    if raw_id_eqb br_back bid_hdr then
                                                      Some (br_latch, evals_body, lmap_latch,
                                                            code_written_ids (blk_code b_body))
                                                    else None
                                                | _, _ => None
                                                end
                                              else None
                                          | None => None
                                          end in
                                      match opt_latch with
                                      | None => None
                                      | Some (bid_latch_from, evals_body, lmap_latch, body_wr) =>
                                          let dom_entry := args G ++ code_written_ids (blk_code b_entry) in
                                          let loop_wr :=
                                            List.map fst hspecs ++ code_written_ids (blk_code b_hdr) ++ body_wr in
                                          if negb (disjoint_raw_ids dom_entry loop_wr) ||
                                             raw_id_eqb br_exit bid_hdr then None
                                          else
                                            match reify_pure_phis bid_latch_from lmap_latch (blk_phis b_hdr),
                                                  RM.find br_exit bmap with
                                            | Some next_pevals, Some b_exit =>
                                                if negb (list_empty_b (blk_phis b_exit)) then None
                                                else
                                                  match reify_pure_code lmap_hdr_c (blk_code b_exit),
                                                        blk_term b_exit with
                                                  | Some (evals_exit, lmap_exit),
                                                    (_, TERM_Ret (DTYPE_Base (DTYPE_I w_ret), op_ret), _) =>
                                                      if is_supported_bit_width w_ret then
                                                        match reify_pure_exp lmap_exit
                                                                (Some (DTYPE_Base (DTYPE_I w_ret))) op_ret with
                                                        | Some (_, ce_ret) =>
                                                            Some (hspecs, {|
                                                              nls_bid_hdr := bid_hdr;
                                                              nls_bid_latch_entry := br_latch;
                                                              nls_bid_latch_from := bid_latch_from;
                                                              nls_bid_exit := br_exit;
                                                              nls_latch_on_true := pol;
                                                              nls_evals_entry := evals_entry;
                                                              nls_lmap_entry := lmap_entry;
                                                              nls_init_pevals := init_pevals;
                                                              nls_evals_hdr := evals_hdr;
                                                              nls_lmap_hdr_c := lmap_hdr_c;
                                                              nls_ce_cond := ce_cond;
                                                              nls_evals_body := evals_body;
                                                              nls_lmap_latch := lmap_latch;
                                                              nls_next_pevals := next_pevals;
                                                              nls_evals_exit := evals_exit;
                                                              nls_w_ret := w_ret;
                                                              nls_ce_ret := ce_ret;
                                                            |})
                                                        | None => None
                                                        end
                                                      else None
                                                  | _, _ => None
                                                  end
                                            | _, _ => None
                                            end
                                      end
                                  end
                              end
                          | _ => None
                          end
                      end
                  | _, _ => None
                  end
              | _, _ => None
              end
        | _ => None
        end
  end.

Lemma list_empty_b_nil {A : Type} : forall (xs : list A), list_empty_b xs = true -> xs = [].
Proof. intros [| x xs] H; [reflexivity | discriminate H]. Qed.

Lemma denote_empty_phis_ret {Pa : Params} :
  forall bid_from (env : rmap (@dvalue Pa)),
    pure_cfg_steps env (denote_phis bid_from []) env tt.
Proof.
  intros bid_from env; unfold denote_phis; cbn [map_monad].
  eapply pure_cfg_steps_bind; [apply PCS_Ret; reflexivity |].
  eapply pure_cfg_steps_bind; [apply PCS_Ret; reflexivity | apply PCS_Ret; reflexivity].
Qed.

Fixpoint overlay_hspecs_s
  (idx : nat) (lmap : rmap (positive * cert_expr))
  (hspecs : list (raw_id * positive))
  {struct hspecs} : rmap (positive * cert_expr) :=
  match hspecs with
  | [] => lmap
  | (id_s, w) :: rest =>
      overlay_hspecs_s (S idx) (RM.add id_s (w, cut_src_expr idx w) lmap) rest
  end.

Fixpoint overlay_hspecs_t
  (idx : nat) (lmap : rmap (positive * cert_expr))
  (hspecs : list (raw_id * positive))
  {struct hspecs} : rmap (positive * cert_expr) :=
  match hspecs with
  | [] => lmap
  | (id_t, w) :: rest =>
      overlay_hspecs_t (S idx) (RM.add id_t (w, cut_tgt_expr idx w) lmap) rest
  end.

Lemma pair_phi_specs_overlay :
  forall hspecs_s hspecs_t pspecs idx lmap_s lmap_t,
    pair_phi_specs hspecs_s hspecs_t = Some pspecs ->
    overlay_hspecs_s idx lmap_s hspecs_s = overlay_cut_lmap_s idx lmap_s pspecs /\
    overlay_hspecs_t idx lmap_t hspecs_t = overlay_cut_lmap_t idx lmap_t pspecs /\
    List.map fst hspecs_s = List.map (fun '(id_s, _, _) => id_s) pspecs /\
    List.map fst hspecs_t = List.map (fun '(_, id_t, _) => id_t) pspecs.
Proof.
  induction hspecs_s as [| [id_s w_s] rx IH];
    intros hspecs_t pspecs idx lmap_s lmap_t H;
    destruct hspecs_t as [| [id_t w_t] ry]; cbn [pair_phi_specs] in H; try discriminate H.
  - inversion H; subst; repeat split; reflexivity.
  - destruct (Pos.eqb w_s w_t && is_supported_bit_width w_s) eqn:E; [| discriminate H].
    apply andb_true_iff in E as [Heqw _]; apply Pos.eqb_eq in Heqw; subst w_t.
    destruct (pair_phi_specs rx ry) as [r |] eqn:Er; [| discriminate H].
    inversion H; subst pspecs; cbn.
    destruct (IH ry r (S idx)
                (RM.add id_s (w_s, cut_src_expr idx w_s) lmap_s)
                (RM.add id_t (w_s, cut_tgt_expr idx w_s) lmap_t) Er)
      as (Hs & Ht & Hms & Hmt).
    repeat split; [exact Hs | exact Ht | f_equal; exact Hms | f_equal; exact Hmt].
Qed.

Lemma pure_cfg_to_cfg_ret {Pa : Params} {R : Type} :
  forall (sigma : @draw_strat Pa) env (t : CFGtop R) env' r,
    @pure_cfg_steps Pa R env t env' r ->
    cfg_steps_to_ret sigma env t sigma env' r.
Proof.
  intros sigma env t env' r H.
  induction H as
    [env t r Ho | env t t' env' r Ho _ IH | env t id dv ke env' r Ho Hf _ IH | env t id dv ke env' r Ho _ IH].
  - apply CSR_Ret; exact Ho.
  - eapply CSR_Tau; [exact Ho | exact IH].
  - eapply CSR_LocalRead; [exact Ho | exact Hf | exact IH].
  - eapply CSR_LocalWrite; [exact Ho | exact IH].
Qed.

Local Lemma reify_natural_loop_latch_step {Pa : Params} :
  forall (bmap : rmap (block dtyp)) bid_hdr br_latch bid_latch_from
         evals_body lmap_latch body_wr lmap_hdr_c
         (dom_entry h_wr : list raw_id)
         (varargs : option (@ptr _ (@PTR Pa))) (penv_cut : param_env Pa)
         bid_prev (env_prev env_hdr_c : rmap (@dvalue Pa)),
    disjoint_raw_ids dom_entry (h_wr ++ body_wr) = true ->
    (if raw_id_eqb br_latch bid_hdr
     then Some (bid_hdr, @nil cert_expr, lmap_hdr_c, @nil raw_id)
     else
       match RM.find br_latch bmap with
       | Some b_body =>
           if list_empty_b (blk_phis b_body) then
             match blk_term b_body, reify_pure_code lmap_hdr_c (blk_code b_body) with
             | (_, TERM_Br_1 br_back, _), Some (evals_b, lmap_b) =>
                 if raw_id_eqb br_back bid_hdr
                 then Some (br_latch, evals_b, lmap_b, code_written_ids (blk_code b_body))
                 else None
             | _, _ => None
             end
           else None
       | None => None
       end) = Some (bid_latch_from, evals_body, lmap_latch, body_wr) ->
    lmap_matches_env penv_cut lmap_hdr_c env_hdr_c ->
    (forall r, In r dom_entry -> ~ In r body_wr -> RM.find r env_hdr_c = RM.find r env_prev) ->
    pure_cfg_steps_to_tau env_prev
      (denote_cfg_from bmap varargs (bid_prev, bid_hdr))
      env_hdr_c
      (denote_cfg_from bmap varargs (bid_hdr, br_latch)) ->
    ((forall sigma, cfg_steps_to_ub sigma env_prev (denote_cfg_from bmap varargs (bid_prev, bid_hdr))) /\
     exists ce msg, In ce evals_body /\
       eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ub msg) \/
    (exists env_latch,
       lmap_matches_env penv_cut lmap_latch env_latch /\
       Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
         evals_body /\
       (forall r, In r dom_entry -> RM.find r env_latch = RM.find r env_prev) /\
       pure_cfg_steps_to_tau env_prev (denote_cfg_from bmap varargs (bid_prev, bid_hdr))
         env_latch (denote_cfg_from bmap varargs (bid_latch_from, bid_hdr))).
Proof.
  intros bmap bid_hdr br_latch bid_latch_from evals_body lmap_latch body_wr lmap_hdr_c
         dom_entry h_wr varargs penv_cut bid_prev env_prev env_hdr_c
         Edisj Elatch Henv_hc Hpres_hc_dom Hhdr_jump.
  destruct (raw_id_eqb br_latch bid_hdr) eqn:Eself.
  - apply raw_id_eqb_eq in Eself; inversion Elatch;
      subst br_latch bid_latch_from evals_body lmap_latch body_wr.
    right; exists env_hdr_c.
    split; [exact Henv_hc |].
    split; [constructor |].
    split; [intros r Hr; exact (Hpres_hc_dom r Hr (fun H => H)) | exact Hhdr_jump].
  - destruct (RM.find br_latch bmap) as [b_body |] eqn:Hf_body; [| discriminate Elatch].
    destruct (list_empty_b (blk_phis b_body)) eqn:Ep_body; [| discriminate Elatch].
    apply list_empty_b_nil in Ep_body.
    destruct (blk_term b_body) as [[ti_b tm_b] md_b] eqn:Htm_body.
    destruct tm_b as [| | | br_back | | | | |]; try discriminate Elatch.
    destruct (reify_pure_code lmap_hdr_c (blk_code b_body))
      as [[eb0 ll0] |] eqn:Hr_body; [| discriminate Elatch].
    destruct (raw_id_eqb br_back bid_hdr) eqn:Eback; [| discriminate Elatch].
    apply raw_id_eqb_eq in Eback; inversion Elatch;
      subst br_back bid_latch_from evals_body lmap_latch body_wr; clear Elatch.
    destruct (eval_reified_pure_code (blk_code b_body) varargs penv_cut
                lmap_hdr_c env_hdr_c eb0 ll0 Henv_hc Hr_body)
      as [[Hub_b Hce_b] | (env_latch & Henv_l & Hfa_ev_b & Hpres_b & Hst_b)].
    + left; split; [| exact Hce_b].
      intros sigma; eapply pure_cfg_steps_to_tau_then_ub; [exact Hhdr_jump |].
      eapply denote_cfg_from_block_ub; [exact Hf_body |].
      unfold denote_block; rewrite Ep_body, Htm_body.
      eapply cfg_steps_to_ub_bind_r;
        [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ (denote_empty_phis_ret bid_hdr env_hdr_c))
        | apply cfg_steps_to_ub_bind_l; exact (Hub_b sigma)].
    + right; exists env_latch.
      split; [exact Henv_l | split; [exact Hfa_ev_b | split]].
      * intros r Hdom.
        pose proof (disjoint_raw_ids_spec _ _ r Edisj Hdom) as Hnin_loop.
        assert (Hnin_b : ~ In r (code_written_ids (blk_code b_body)))
          by (intros Hb; exact (Hnin_loop (proj2 (in_app_iff _ _ _) (or_intror Hb)))).
        rewrite (Hpres_b r Hnin_b); exact (Hpres_hc_dom r Hdom Hnin_b).
      * eapply pure_cfg_steps_to_tau_trans; [exact Hhdr_jump |].
        eapply denote_cfg_from_block_jump; [exact Hf_body |].
        unfold denote_block; rewrite Ep_body, Htm_body.
        eapply pure_cfg_steps_bind; [apply denote_empty_phis_ret |].
        eapply pure_cfg_steps_bind; [exact Hst_b | apply PCS_Ret; reflexivity].
Qed.

Local Lemma reify_natural_loop_exit_step {Pa : Params} :
  forall (bmap : rmap (block dtyp)) bid_hdr br_exit b_exit
         lmap_hdr_c evals_exit lmap_exit ti_x w_ret op_ret md_x ce_ret
         (varargs : option (@ptr _ (@PTR Pa))) (penv_cut : param_env Pa)
         bid_prev (env_prev env_hdr_c : rmap (@dvalue Pa)),
    RM.find br_exit bmap = Some b_exit ->
    blk_phis b_exit = [] ->
    reify_pure_code lmap_hdr_c (blk_code b_exit) = Some (evals_exit, lmap_exit) ->
    blk_term b_exit = (ti_x, TERM_Ret (DTYPE_Base (DTYPE_I w_ret), op_ret), md_x) ->
    reify_pure_exp lmap_exit (Some (DTYPE_Base (DTYPE_I w_ret))) op_ret = Some (w_ret, ce_ret) ->
    lmap_matches_env penv_cut lmap_hdr_c env_hdr_c ->
    pure_cfg_steps_to_tau env_prev
      (denote_cfg_from bmap varargs (bid_prev, bid_hdr))
      env_hdr_c
      (denote_cfg_from bmap varargs (bid_hdr, br_exit)) ->
    ((forall sigma, cfg_steps_to_ub sigma env_prev (denote_cfg_from bmap varargs (bid_prev, bid_hdr))) /\
     exists ce msg, In ce (ce_ret :: evals_exit) /\
       eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ub msg) \/
    (exists env_exit dv_ret,
       Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
         evals_exit /\
       eval_closed_cert_expr penv_cut dummy_freeze_oracle ce_ret = raise_ret dv_ret /\
       wf_scalar_dvalue w_ret dv_ret /\
       pure_cfg_steps env_prev (denote_cfg_from bmap varargs (bid_prev, bid_hdr))
         env_exit dv_ret).
Proof.
  intros bmap bid_hdr br_exit b_exit lmap_hdr_c evals_exit lmap_exit
         ti_x w_ret op_ret md_x ce_ret varargs penv_cut bid_prev env_prev env_hdr_c
         Hf_exit Ep_exit Hr_exit Htm_exit Hr_ret Henv_hc Hhdr_jump.
  destruct (eval_reified_pure_code (blk_code b_exit) varargs penv_cut
              lmap_hdr_c env_hdr_c evals_exit lmap_exit Henv_hc Hr_exit)
    as [[Hub_x (ce_x & msg_x & Hin_x & Hev_x)] | (env_exit & Henv_x & Hfa_ev_x & _ & Hst_x)].
  - left; split.
    + intros sigma; eapply pure_cfg_steps_to_tau_then_ub; [exact Hhdr_jump |].
      eapply denote_cfg_from_block_ub; [exact Hf_exit |].
      unfold denote_block; rewrite Ep_exit, Htm_exit.
      eapply cfg_steps_to_ub_bind_r;
        [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ (denote_empty_phis_ret bid_hdr env_hdr_c))
        | apply cfg_steps_to_ub_bind_l; exact (Hub_x sigma)].
    + exists ce_x, msg_x; split; [right; exact Hin_x | exact Hev_x].
  - destruct (eval_reified_pure_exp op_ret penv_cut lmap_exit env_exit
                (Some (DTYPE_Base (DTYPE_I w_ret))) w_ret ce_ret Henv_x Hr_ret)
      as [[Hub_r [msg_r Hev_r]] | [dv_ret [Hev_r [Hsc_r Hst_r]]]].
    + left; split.
      * intros sigma; eapply pure_cfg_steps_to_tau_then_ub; [exact Hhdr_jump |].
        eapply denote_cfg_from_block_ub; [exact Hf_exit |].
        unfold denote_block; rewrite Ep_exit, Htm_exit.
        eapply cfg_steps_to_ub_bind_r;
          [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ (denote_empty_phis_ret bid_hdr env_hdr_c)) |].
        eapply cfg_steps_to_ub_bind_r;
          [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_x) |].
        cbn [denote_terminator]; unfold denote_exp'.
        apply cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub_r sigma).
      * exists ce_ret, msg_r; split; [left; reflexivity | exact Hev_r].
    + right; exists env_exit, dv_ret.
      split; [exact Hfa_ev_x | split; [exact Hev_r | split; [exact Hsc_r |]]].
      eapply pure_cfg_steps_to_tau_then_ret; [exact Hhdr_jump |].
      eapply denote_cfg_from_block_ret; [exact Hf_exit |].
      unfold denote_block; rewrite Ep_exit, Htm_exit.
      eapply pure_cfg_steps_bind; [apply denote_empty_phis_ret |].
      eapply pure_cfg_steps_bind; [exact Hst_x |].
      cbn [denote_terminator]; unfold denote_exp'.
      eapply pure_cfg_steps_bind;
        [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst_r) | apply PCS_Ret; reflexivity].
Qed.

Local Lemma reify_natural_loop_hdr_step {Pa : Params} :
  forall G b_entry b_hdr (hspecs : list (raw_id * positive))
         (lmap_entry : rmap (positive * cert_expr)) wrap_cut
         evals_hdr lmap_hdr_c ti_h op_cond br1 br2 md_h ce_cond
         pol br_latch br_exit bid_latch_from evals_body lmap_latch body_wr
         b_exit evals_exit lmap_exit ti_x w_ret op_ret md_x ce_ret bid_hdr
         (varargs : option (@ptr _ (@PTR Pa))) (penv_cut : param_env Pa)
         bid_prev (env_prev : rmap (@dvalue Pa)) (dvs : list (raw_id * @dvalue Pa)),
    let bmap := ocfg_map (blks G) in
    let dom_entry := args G ++ code_written_ids (blk_code b_entry) in
    RM.find bid_hdr bmap = Some b_hdr ->
    reify_pure_code (wrap_cut lmap_entry hspecs) (blk_code b_hdr) = Some (evals_hdr, lmap_hdr_c) ->
    blk_term b_hdr = (ti_h, TERM_Br (DTYPE_Base (DTYPE_I 1%positive), op_cond) br1 br2, md_h) ->
    reify_pure_exp lmap_hdr_c (Some (DTYPE_Base (DTYPE_I 1%positive))) op_cond = Some (1%positive, ce_cond) ->
    (forall b : bool, (if b then br1 else br2) = (if Bool.eqb b pol then br_latch else br_exit)) ->
    (if raw_id_eqb br_latch bid_hdr
     then Some (bid_hdr, @nil cert_expr, lmap_hdr_c, @nil raw_id)
     else
       match RM.find br_latch bmap with
       | Some b_body =>
           if list_empty_b (blk_phis b_body) then
             match blk_term b_body, reify_pure_code lmap_hdr_c (blk_code b_body) with
             | (_, TERM_Br_1 br_back, _), Some (evals_b, lmap_b) =>
                 if raw_id_eqb br_back bid_hdr
                 then Some (br_latch, evals_b, lmap_b, code_written_ids (blk_code b_body))
                 else None
             | _, _ => None
             end
           else None
       | None => None
       end) = Some (bid_latch_from, evals_body, lmap_latch, body_wr) ->
    disjoint_raw_ids dom_entry (List.map fst hspecs ++ code_written_ids (blk_code b_hdr) ++ body_wr) = true ->
    RM.find br_exit bmap = Some b_exit ->
    blk_phis b_exit = [] ->
    reify_pure_code lmap_hdr_c (blk_code b_exit) = Some (evals_exit, lmap_exit) ->
    blk_term b_exit = (ti_x, TERM_Ret (DTYPE_Base (DTYPE_I w_ret), op_ret), md_x) ->
    reify_pure_exp lmap_exit (Some (DTYPE_Base (DTYPE_I w_ret))) op_ret = Some (w_ret, ce_ret) ->
    List.map fst dvs = List.map fst hspecs ->
    pure_cfg_steps env_prev (denote_phis bid_prev (blk_phis b_hdr)) (apply_phi_env env_prev dvs) tt ->
    lmap_matches_env penv_cut (wrap_cut lmap_entry hspecs) (apply_phi_env env_prev dvs) ->
    ((forall sigma, cfg_steps_to_ub sigma env_prev (denote_cfg_from bmap varargs (bid_prev, bid_hdr))) /\
     ((exists ce msg, In ce (ce_cond :: evals_hdr) /\
         eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ub msg) \/
      eval_closed_cert_expr penv_cut dummy_freeze_oracle ce_cond =
        raise_ret (DVALUE_Base DVALUE_Poison))) \/
    (exists (cbit : @Integers.bit_int 1),
       Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
         evals_hdr /\
       eval_closed_cert_expr penv_cut dummy_freeze_oracle ce_cond =
         raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit)) /\
       (Bool.eqb (@Integers.unsigned 1 cbit =? 1)%Z pol = true ->
        ((forall sigma, cfg_steps_to_ub sigma env_prev (denote_cfg_from bmap varargs (bid_prev, bid_hdr))) /\
         exists ce msg, In ce evals_body /\
           eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ub msg) \/
        (exists env_latch,
           lmap_matches_env penv_cut lmap_latch env_latch /\
           Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
             evals_body /\
           (forall r, In r dom_entry -> RM.find r env_latch = RM.find r env_prev) /\
           pure_cfg_steps_to_tau env_prev (denote_cfg_from bmap varargs (bid_prev, bid_hdr))
             env_latch (denote_cfg_from bmap varargs (bid_latch_from, bid_hdr)))) /\
       (Bool.eqb (@Integers.unsigned 1 cbit =? 1)%Z pol = false ->
        ((forall sigma, cfg_steps_to_ub sigma env_prev (denote_cfg_from bmap varargs (bid_prev, bid_hdr))) /\
         exists ce msg, In ce (ce_ret :: evals_exit) /\
           eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ub msg) \/
        (exists env_exit dv_ret,
           Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
             evals_exit /\
           eval_closed_cert_expr penv_cut dummy_freeze_oracle ce_ret = raise_ret dv_ret /\
           wf_scalar_dvalue w_ret dv_ret /\
           pure_cfg_steps env_prev (denote_cfg_from bmap varargs (bid_prev, bid_hdr))
             env_exit dv_ret))).
Proof.
  intros G b_entry b_hdr hspecs lmap_entry wrap_cut evals_hdr lmap_hdr_c ti_h op_cond br1 br2 md_h ce_cond
         pol br_latch br_exit bid_latch_from evals_body lmap_latch body_wr b_exit evals_exit lmap_exit
         ti_x w_ret op_ret md_x ce_ret bid_hdr varargs penv_cut bid_prev env_prev dvs
         bmap dom_entry Hf_hdr Hr_hdr Htm_hdr Hr_cond Hpol_br Elatch Edisj
         Hf_exit Ep_exit Hr_exit Htm_exit Hr_ret Hmap_dvs Hst_phis Henv_hdr0.
  destruct (eval_reified_pure_code (blk_code b_hdr) varargs penv_cut
              (wrap_cut lmap_entry hspecs) (apply_phi_env env_prev dvs)
              evals_hdr lmap_hdr_c Henv_hdr0 Hr_hdr)
    as [[Hub_h (ce_h & msg_h & Hin_h & Hev_h)] | (env_hdr_c & Henv_hc & Hfa_ev_h & Hpres_h & Hst_h)].
  - left; split.
    + intros sigma; eapply denote_cfg_from_block_ub; [exact Hf_hdr |].
      unfold denote_block.
      eapply cfg_steps_to_ub_bind_r;
        [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_phis)
        | apply cfg_steps_to_ub_bind_l; exact (Hub_h sigma)].
    + left; exists ce_h, msg_h; split; [right; exact Hin_h | exact Hev_h].
  - destruct (eval_reified_pure_exp op_cond penv_cut lmap_hdr_c env_hdr_c
                (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive ce_cond Henv_hc Hr_cond)
      as [[Hub_c [msg_c Hev_c]] | [dv_c [Hev_c [Hsc_c Hst_c]]]].
    + left; split.
      * intros sigma; eapply denote_cfg_from_block_ub; [exact Hf_hdr |].
        unfold denote_block; rewrite Htm_hdr.
        eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_phis) |].
        eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_h) |].
        cbn [denote_terminator]; unfold denote_exp'.
        apply cfg_steps_to_ub_bind_l, mcfg_to_cfg_steps_ub; exact (Hub_c sigma).
      * left; exists ce_cond, msg_c; split; [left; reflexivity | exact Hev_c].
    + destruct Hsc_c as [-> | [cbit ->]].
      * left; split; [| right; exact Hev_c].
        intros sigma; eapply denote_cfg_from_block_ub; [exact Hf_hdr |].
        unfold denote_block; rewrite Htm_hdr.
        eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_phis) |].
        eapply cfg_steps_to_ub_bind_r; [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ Hst_h) |].
        cbn [denote_terminator]; unfold denote_exp'.
        eapply cfg_steps_to_ub_bind_r;
          [exact (mcfg_to_cfg_steps_ret _ _ _ _ _ _ (pure_mcfg_to_mcfg_ret sigma _ _ _ _ Hst_c))
          | apply cfg_steps_raiseUB].
      * right; exists cbit; split; [exact Hfa_ev_h | split; [exact Hev_c |]].
        set (br_tgt := if (@Integers.unsigned 1 cbit =? 1)%Z then br1 else br2).
        assert (Hhdr_jump :
          pure_cfg_steps_to_tau env_prev
            (denote_cfg_from bmap varargs (bid_prev, bid_hdr))
            env_hdr_c
            (denote_cfg_from bmap varargs (bid_hdr, br_tgt))).
        { eapply denote_cfg_from_block_jump; [exact Hf_hdr |].
          unfold denote_block; rewrite Htm_hdr.
          eapply pure_cfg_steps_bind; [exact Hst_phis |].
          eapply pure_cfg_steps_bind; [exact Hst_h |].
          cbn [denote_terminator]; unfold denote_exp'.
          eapply pure_cfg_steps_bind; [exact (pure_mcfg_to_pure_cfg _ _ _ _ Hst_c) |].
          cbn iota beta; rewrite bit_int_1_equ_one_eq_unsigned; unfold br_tgt.
          destruct (@Integers.unsigned 1 cbit =? 1)%Z; apply PCS_Ret; reflexivity. }
        assert (Hpres_hc_dom :
          forall r, In r dom_entry -> ~ In r body_wr -> RM.find r env_hdr_c = RM.find r env_prev).
        { intros r Hdom _.
          pose proof (disjoint_raw_ids_spec _ _ r Edisj Hdom) as Hnin_loop.
          rewrite (Hpres_h r
            (fun Hc => Hnin_loop (proj2 (in_app_iff _ _ _) (or_intror (proj2 (in_app_iff _ _ _) (or_introl Hc)))))).
          apply apply_phi_env_preserves_not_in.
          rewrite Hmap_dvs; intros Hp; exact (Hnin_loop (proj2 (in_app_iff _ _ _) (or_introl Hp))). }
        split.
        -- intros Econt.
           assert (Hbr_latch : br_tgt = br_latch)
             by (unfold br_tgt; rewrite (Hpol_br (@Integers.unsigned 1 cbit =? 1)%Z), Econt; reflexivity).
           rewrite Hbr_latch in Hhdr_jump.
           rewrite app_assoc in Edisj.
           exact (reify_natural_loop_latch_step bmap bid_hdr br_latch bid_latch_from
                    evals_body lmap_latch body_wr lmap_hdr_c dom_entry
                    (List.map fst hspecs ++ code_written_ids (blk_code b_hdr))
                    varargs penv_cut bid_prev env_prev env_hdr_c
                    Edisj Elatch Henv_hc Hpres_hc_dom Hhdr_jump).
        -- intros Eexit.
           assert (Hbr_exit : br_tgt = br_exit)
             by (unfold br_tgt; rewrite (Hpol_br (@Integers.unsigned 1 cbit =? 1)%Z), Eexit; reflexivity).
           rewrite Hbr_exit in Hhdr_jump.
           exact (reify_natural_loop_exit_step bmap bid_hdr br_exit b_exit
                    lmap_hdr_c evals_exit lmap_exit ti_x w_ret op_ret md_x ce_ret
                    varargs penv_cut bid_prev env_prev env_hdr_c
                    Hf_exit Ep_exit Hr_exit Htm_exit Hr_ret Henv_hc Hhdr_jump).
Qed.

Lemma reify_natural_loop_spec :

  forall G hdr_name allowed cut_allowed lmap0 wrap_cut hspecs s,
    wf_pure_lmap allowed lmap0 ->
    (forall r w ce, RM.find r lmap0 = Some (w, ce) -> In r (args G)) ->
    (forall lmap, wf_pure_lmap allowed lmap -> wf_pure_lmap cut_allowed (wrap_cut lmap hspecs)) ->
    reify_natural_loop G hdr_name lmap0 wrap_cut = Some (hspecs, s) ->
    exists b_entry b_hdr,
      let bmap := ocfg_map (blks G) in
      let dom_entry := args G ++ code_written_ids (blk_code b_entry) in
      RM.find (init G) bmap = Some b_entry /\
      RM.find (nls_bid_hdr s) bmap = Some b_hdr /\
      extract_hdr_phi_specs (blk_phis b_hdr) = Some hspecs /\
      reify_pure_phis (init G) (nls_lmap_entry s) (blk_phis b_hdr) = Some (nls_init_pevals s) /\
      reify_pure_phis (nls_bid_latch_from s) (nls_lmap_latch s) (blk_phis b_hdr) = Some (nls_next_pevals s) /\
      wf_pure_lmap allowed (nls_lmap_entry s) /\
      (forall r w ce, RM.find r (nls_lmap_entry s) = Some (w, ce) -> In r dom_entry) /\
      Forall (wf_pure_eval_entry allowed) (nls_evals_entry s) /\
      Forall (fun '(_, w, ce) =>
        is_supported_bit_width w = true /\ cert_expr_bit_width ce = w /\ wf_pure_eval_entry allowed ce)
        (nls_init_pevals s) /\
      Forall (wf_pure_eval_entry cut_allowed) (nls_evals_hdr s) /\
      wf_pure_eval_entry cut_allowed (nls_ce_cond s) /\
      cert_expr_bit_width (nls_ce_cond s) = 1%positive /\
      Forall (wf_pure_eval_entry cut_allowed) (nls_evals_body s) /\
      Forall (fun '(_, w, ce) =>
        is_supported_bit_width w = true /\ cert_expr_bit_width ce = w /\ wf_pure_eval_entry cut_allowed ce)
        (nls_next_pevals s) /\
      Forall (wf_pure_eval_entry cut_allowed) (nls_evals_exit s) /\
      wf_pure_eval_entry cut_allowed (nls_ce_ret s) /\
      cert_expr_bit_width (nls_ce_ret s) = nls_w_ret s /\
      is_supported_bit_width (nls_w_ret s) = true /\
      (forall (Pa : Params) (varargs : option (@ptr _ (@PTR Pa)))
              (penv : param_env Pa) (env0 : rmap (@dvalue Pa)),
         lmap_matches_env penv lmap0 env0 ->
         ((forall sigma, cfg_steps_to_ub sigma env0 (denote_cfg_from bmap varargs (init G, init G))) /\
          exists ce msg, In ce (nls_evals_entry s) /\
            eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ub msg) \/
         (exists env_entry,
            lmap_matches_env penv (nls_lmap_entry s) env_entry /\
            Forall (fun ce => exists dv, eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv)
              (nls_evals_entry s) /\
            pure_cfg_steps_to_tau env0 (denote_cfg_from bmap varargs (init G, init G))
              env_entry (denote_cfg_from bmap varargs (init G, nls_bid_hdr s)))) /\
      (forall (Pa : Params) (varargs : option (@ptr _ (@PTR Pa)))
              (penv_cut : param_env Pa) bid_prev (env_prev : rmap (@dvalue Pa))
              (dvs : list (raw_id * @dvalue Pa)),
         List.map fst dvs = List.map fst hspecs ->
         pure_cfg_steps env_prev (denote_phis bid_prev (blk_phis b_hdr)) (apply_phi_env env_prev dvs) tt ->
         lmap_matches_env penv_cut (wrap_cut (nls_lmap_entry s) hspecs) (apply_phi_env env_prev dvs) ->
         ((forall sigma, cfg_steps_to_ub sigma env_prev (denote_cfg_from bmap varargs (bid_prev, nls_bid_hdr s))) /\
          ((exists ce msg, In ce (nls_ce_cond s :: nls_evals_hdr s) /\
              eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ub msg) \/
           eval_closed_cert_expr penv_cut dummy_freeze_oracle (nls_ce_cond s) =
             raise_ret (DVALUE_Base DVALUE_Poison))) \/
         (exists (cbit : @Integers.bit_int 1),
            Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
              (nls_evals_hdr s) /\
            eval_closed_cert_expr penv_cut dummy_freeze_oracle (nls_ce_cond s) =
              raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit)) /\
            (Bool.eqb (@Integers.unsigned 1 cbit =? 1)%Z (nls_latch_on_true s) = true ->
             ((forall sigma, cfg_steps_to_ub sigma env_prev (denote_cfg_from bmap varargs (bid_prev, nls_bid_hdr s))) /\
              exists ce msg, In ce (nls_evals_body s) /\
                eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ub msg) \/
             (exists env_latch,
                lmap_matches_env penv_cut (nls_lmap_latch s) env_latch /\
                Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
                  (nls_evals_body s) /\
                (forall r, In r dom_entry -> RM.find r env_latch = RM.find r env_prev) /\
                pure_cfg_steps_to_tau env_prev (denote_cfg_from bmap varargs (bid_prev, nls_bid_hdr s))
                  env_latch (denote_cfg_from bmap varargs (nls_bid_latch_from s, nls_bid_hdr s)))) /\
            (Bool.eqb (@Integers.unsigned 1 cbit =? 1)%Z (nls_latch_on_true s) = false ->
             ((forall sigma, cfg_steps_to_ub sigma env_prev (denote_cfg_from bmap varargs (bid_prev, nls_bid_hdr s))) /\
              exists ce msg, In ce (nls_ce_ret s :: nls_evals_exit s) /\
                eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ub msg) \/
             (exists env_exit dv_ret,
                Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
                  (nls_evals_exit s) /\
                eval_closed_cert_expr penv_cut dummy_freeze_oracle (nls_ce_ret s) = raise_ret dv_ret /\
                wf_scalar_dvalue (nls_w_ret s) dv_ret /\
                pure_cfg_steps env_prev (denote_cfg_from bmap varargs (bid_prev, nls_bid_hdr s))
                  env_exit dv_ret)))).
Proof.
  intros G hdr_name allowed cut_allowed lmap0 wrap_cut hspecs s Hlmap0 Hdom0 Hwrap Hr.
  unfold reify_natural_loop in Hr; cbn zeta in Hr.
  set (bmap := ocfg_map (blks G)) in *.
  destruct (RM.find (init G) bmap) as [b_entry |] eqn:Hf_ent; [| discriminate Hr].
  destruct (negb (list_empty_b (blk_phis b_entry))) eqn:Ep_ent; [discriminate Hr |].
  apply negb_false_iff, list_empty_b_nil in Ep_ent.
  destruct (blk_term b_entry) as [[ti_e tm_e] md_e] eqn:Htm_ent.
  destruct tm_e as [| | | bid_hdr | | | | |]; try discriminate Hr.
  destruct (negb (cert_block_matches_id hdr_name bid_hdr) || raw_id_eqb bid_hdr (init G)); [discriminate Hr |].
  destruct (RM.find bid_hdr bmap) as [b_hdr |] eqn:Hf_hdr; [| discriminate Hr].
  destruct (reify_pure_code lmap0 (blk_code b_entry)) as [[evals_entry lmap_entry] |] eqn:Hr_ent; [| discriminate Hr].
  destruct (extract_hdr_phi_specs (blk_phis b_hdr)) as [hspecs' |] eqn:Ehspecs; [| discriminate Hr].
  destruct (reify_pure_phis (init G) lmap_entry (blk_phis b_hdr)) as [init_pevals |] eqn:Hr_init; [| discriminate Hr].
  destruct (reify_pure_code (wrap_cut lmap_entry hspecs') (blk_code b_hdr))
    as [[evals_hdr lmap_hdr_c] |] eqn:Hr_hdr; [| discriminate Hr].
  destruct (blk_term b_hdr) as [[ti_h tm_h] md_h] eqn:Htm_hdr.
  destruct tm_h as [| | [dt_c op_cond] br1 br2 | | | | | |]; try discriminate Hr.
  destruct dt_c as [tb_c | |]; try discriminate Hr;
    destruct tb_c as [wc | | | | | | | | | |]; try discriminate Hr;
    destruct wc as [| |]; try discriminate Hr.
  destruct (reify_pure_exp lmap_hdr_c (Some (DTYPE_Base (DTYPE_I 1%positive))) op_cond)
    as [[wc' ce_cond] |] eqn:Hr_cond; [| discriminate Hr].
  pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr_cond)) as ->.
  set (opt_pol :=
    if is_latch_edge_b bmap bid_hdr br1 && negb (is_latch_edge_b bmap bid_hdr br2)
    then Some (true, br1, br2)
    else if is_latch_edge_b bmap bid_hdr br2 && negb (is_latch_edge_b bmap bid_hdr br1)
    then Some (false, br2, br1)
    else None) in *.
  destruct opt_pol as [[[pol br_latch] br_exit] |] eqn:Epol; [| discriminate Hr].
  assert (Hpol_br :
    forall b : bool,
      (if b then br1 else br2) =
      (if Bool.eqb b pol then br_latch else br_exit)).
  { unfold opt_pol in Epol.
    destruct (is_latch_edge_b bmap bid_hdr br1 && negb (is_latch_edge_b bmap bid_hdr br2)).
    - inversion Epol; subst pol br_latch br_exit; intros []; reflexivity.
    - destruct (is_latch_edge_b bmap bid_hdr br2 && negb (is_latch_edge_b bmap bid_hdr br1)); [| discriminate Epol].
      inversion Epol; subst pol br_latch br_exit; intros []; reflexivity. }
  match type of Hr with
  | match ?ol with Some _ => _ | None => _ end = Some _ =>
      destruct ol as [[[[bid_latch_from evals_body] lmap_latch] body_wr] |] eqn:Elatch; [| discriminate Hr]
  end.
  destruct (negb (disjoint_raw_ids (args G ++ code_written_ids (blk_code b_entry))
                    (List.map fst hspecs' ++ code_written_ids (blk_code b_hdr) ++ body_wr)) ||
            raw_id_eqb br_exit bid_hdr) eqn:Edisj_bad; [discriminate Hr |].
  apply orb_false_iff in Edisj_bad as [Edisj _]; apply negb_false_iff in Edisj.
  destruct (reify_pure_phis bid_latch_from lmap_latch (blk_phis b_hdr))
    as [next_pevals |] eqn:Hr_next; [| discriminate Hr].
  destruct (RM.find br_exit bmap) as [b_exit |] eqn:Hf_exit; [| discriminate Hr].
  destruct (negb (list_empty_b (blk_phis b_exit))) eqn:Ep_exit; [discriminate Hr |].
  apply negb_false_iff, list_empty_b_nil in Ep_exit.
  destruct (reify_pure_code lmap_hdr_c (blk_code b_exit))
    as [[evals_exit lmap_exit] |] eqn:Hr_exit; [| discriminate Hr].
  destruct (blk_term b_exit) as [[ti_x tm_x] md_x] eqn:Htm_exit.
  destruct tm_x as [[dt_r op_ret] | | | | | | | |]; try discriminate Hr.
  destruct dt_r as [tb_r | |]; try discriminate Hr;
    destruct tb_r as [w_ret | | | | | | | | | |]; try discriminate Hr.
  destruct (is_supported_bit_width w_ret) eqn:Hsup_ret; [| discriminate Hr].
  destruct (reify_pure_exp lmap_exit (Some (DTYPE_Base (DTYPE_I w_ret))) op_ret)
    as [[wr' ce_ret] |] eqn:Hr_ret; [| discriminate Hr].
  pose proof (check_opt_int_width_some_inv _ _ (reify_pure_exp_top_width _ _ _ _ _ Hr_ret)) as ->.
  inversion Hr; subst hspecs' s; clear Hr; cbn [
    nls_bid_hdr nls_bid_latch_entry nls_bid_latch_from nls_bid_exit nls_latch_on_true
    nls_evals_entry nls_lmap_entry nls_init_pevals nls_evals_hdr nls_lmap_hdr_c nls_ce_cond
    nls_evals_body nls_lmap_latch nls_next_pevals nls_evals_exit nls_w_ret nls_ce_ret ].
  destruct (reify_pure_code_typing _ allowed lmap0 evals_entry lmap_entry Hlmap0 Hr_ent)
    as [Hfa_ent Hlmap_ent].
  pose proof (lmap_dom_code _ lmap0 evals_entry lmap_entry (args G) Hdom0 Hr_ent) as Hdom_ent.
  pose proof (reify_pure_phis_typing _ allowed (init G) lmap_entry init_pevals Hlmap_ent Hr_init) as Hfa_init.
  pose proof (Hwrap lmap_entry Hlmap_ent) as Hlmap_hdr0.
  destruct (reify_pure_code_typing _ cut_allowed _ evals_hdr lmap_hdr_c Hlmap_hdr0 Hr_hdr)
    as [Hfa_hdr Hlmap_hdrc].
  destruct (reify_pure_exp_typing op_cond cut_allowed lmap_hdr_c
              (Some (DTYPE_Base (DTYPE_I 1%positive))) 1%positive ce_cond Hlmap_hdrc Hr_cond)
    as (_ & Hwt_cond & Hbw_cond & Hlf_cond & Hfv_cond).
  assert (Hlatch_ty :
    Forall (wf_pure_eval_entry cut_allowed) evals_body /\
    wf_pure_lmap cut_allowed lmap_latch).
  { destruct (raw_id_eqb br_latch bid_hdr) eqn:Eself.
    - inversion Elatch; subst; split; [constructor | exact Hlmap_hdrc].
    - destruct (RM.find br_latch bmap) as [b_body |]; [| discriminate Elatch].
      destruct (list_empty_b (blk_phis b_body)); [| discriminate Elatch].
      destruct (blk_term b_body) as [[_ tm_b] _]; destruct tm_b; try discriminate Elatch.
      destruct (reify_pure_code lmap_hdr_c (blk_code b_body)) as [[eb ll] |] eqn:Hrb; [| discriminate Elatch].
      destruct (raw_id_eqb br bid_hdr); [| discriminate Elatch].
      inversion Elatch; subst.
      exact (reify_pure_code_typing _ cut_allowed lmap_hdr_c evals_body lmap_latch Hlmap_hdrc Hrb). }
  destruct Hlatch_ty as [Hfa_body Hlmap_latch].
  pose proof (reify_pure_phis_typing _ cut_allowed bid_latch_from lmap_latch next_pevals Hlmap_latch Hr_next)
    as Hfa_next.
  destruct (reify_pure_code_typing _ cut_allowed lmap_hdr_c evals_exit lmap_exit Hlmap_hdrc Hr_exit)
    as [Hfa_exit Hlmap_exit].
  destruct (reify_pure_exp_typing op_ret cut_allowed lmap_exit
              (Some (DTYPE_Base (DTYPE_I w_ret))) w_ret ce_ret Hlmap_exit Hr_ret)
    as (_ & Hwt_ret & Hbw_ret & Hlf_ret & Hfv_ret).
  exists b_entry, b_hdr.
  split; [exact Hf_ent |].
  split; [exact Hf_hdr |].
  split; [exact Ehspecs |].
  split; [exact Hr_init |].
  split; [exact Hr_next |].
  split; [exact Hlmap_ent |].
  split; [exact Hdom_ent |].
  split; [exact Hfa_ent |].
  split; [exact Hfa_init |].
  split; [exact Hfa_hdr |].
  split; [repeat split; assumption |].
  split; [exact Hbw_cond |].
  split; [exact Hfa_body |].
  split; [exact Hfa_next |].
  split; [exact Hfa_exit |].
  split; [repeat split; assumption |].
  split; [exact Hbw_ret |].
  split; [exact Hsup_ret |].
  split.
  - (* Entry block step *)
    intros Pa varargs penv env0 Henv0.
    destruct (eval_reified_pure_code (blk_code b_entry) varargs penv lmap0 env0 evals_entry lmap_entry Henv0 Hr_ent)
      as [[Hub_e Hce_e] | (env_entry & Henv_e & Hfa_ev_e & _ & Hst_e)].
    + left; split; [| exact Hce_e].
      intros sigma; eapply denote_cfg_from_block_ub; [exact Hf_ent |].
      unfold denote_block; rewrite Ep_ent, Htm_ent.
      eapply cfg_steps_to_ub_bind_r;
        [exact (pure_cfg_to_cfg_ret sigma _ _ _ _ (denote_empty_phis_ret (init G) env0))
        | apply cfg_steps_to_ub_bind_l; exact (Hub_e sigma)].
    + right; exists env_entry; split; [exact Henv_e | split; [exact Hfa_ev_e |]].
      eapply denote_cfg_from_block_jump; [exact Hf_ent |].
      unfold denote_block; rewrite Ep_ent, Htm_ent.
      eapply pure_cfg_steps_bind; [apply denote_empty_phis_ret |].
      eapply pure_cfg_steps_bind; [exact Hst_e | apply PCS_Ret; reflexivity].
  - (* Header + Latch/Exit step *)
    intros Pa varargs penv_cut bid_prev env_prev dvs Hmap_dvs Hst_phis Henv_hdr0.
    exact (reify_natural_loop_hdr_step G b_entry b_hdr hspecs lmap_entry wrap_cut
             evals_hdr lmap_hdr_c ti_h op_cond br1 br2 md_h ce_cond
             pol br_latch br_exit bid_latch_from evals_body lmap_latch body_wr
             b_exit evals_exit lmap_exit ti_x w_ret op_ret md_x ce_ret bid_hdr
             varargs penv_cut bid_prev env_prev dvs
             Hf_hdr Hr_hdr Htm_hdr Hr_cond Hpol_br Elatch Edisj
             Hf_exit Ep_exit Hr_exit Htm_exit Hr_ret Hmap_dvs Hst_phis Henv_hdr0).
Qed.

Lemma wf_pure_lmap_mono :
  forall allowed1 allowed2 lmap,
    incl allowed1 allowed2 ->
    wf_pure_lmap allowed1 lmap ->
    wf_pure_lmap allowed2 lmap.
Proof.
  intros allowed1 allowed2 lmap Hinc H r w ce Hf.
  destruct (H r w ce Hf) as (Hwt & Hbw & Hlf & Hfv).
  repeat split; try assumption; intros u Hu; exact (Hinc u (Hfv u Hu)).
Qed.

Lemma NoDup_app_r {A : Type} :
  forall (xs ys : list A), NoDup (xs ++ ys) -> NoDup ys.
Proof.
  induction xs as [| x rx IH]; intros ys Hnd; cbn in Hnd; [exact Hnd |].
  inversion Hnd as [| ? ? _ Hndr]; exact (IH ys Hndr).
Qed.

Lemma NoDup_app_disj {A : Type} :
  forall (xs ys : list A) x, NoDup (xs ++ ys) -> In x xs -> ~ In x ys.
Proof.
  induction xs as [| x0 rx IH]; intros ys x Hnd Hin; cbn in *; [contradiction |].
  inversion Hnd as [| ? ? Hnin Hndr]; subst.
  destruct Hin as [-> | Hrx].
  - intros Hy; apply Hnin, in_app_iff; right; exact Hy.
  - exact (IH ys x Hndr Hrx).
Qed.

Lemma bool_eqb_swap_inv :
  forall x p b : bool, Bool.eqb x p = b -> x = Bool.eqb b p.
Proof.
  intros [] [] [] H; try discriminate H; reflexivity.
Qed.

Lemma eff_loop_cond_typing :
  forall allowed pol ce,
    wf_pure_eval_entry allowed ce ->
    cert_expr_bit_width ce = 1%positive ->
    wf_pure_eval_entry allowed (eff_loop_cond pol ce) /\
    cert_expr_bit_width (eff_loop_cond pol ce) = 1%positive.
Proof.
  intros allowed [|] ce (Hwt & Hlf & Hfv) Hbw; cbn [eff_loop_cond].
  - split; [repeat split; assumption | exact Hbw].
  - split; [| reflexivity].
    repeat split.
    + cbn [wt_cert_expr]; rewrite Hwt, Hbw; reflexivity.
    + cbn [is_let_free_expr]; rewrite Hlf, !Bool.andb_true_r; reflexivity.
    + cbn [collect_free_vars]; rewrite !app_nil_r; exact Hfv.
Qed.

Lemma eff_loop_cond_poison {Pa : Params} :
  forall (penv : param_env Pa) pol ce,
    eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret (DVALUE_Base DVALUE_Poison) ->
    eval_closed_cert_expr penv dummy_freeze_oracle (eff_loop_cond pol ce) =
    raise_ret (DVALUE_Base DVALUE_Poison).
Proof.
  intros penv [|] ce Hev; [exact Hev |].
  unfold eval_closed_cert_expr in *; cbn [eff_loop_cond eval_cert_expr]; rewrite Hev; reflexivity.
Qed.

Fixpoint filter_param_ub_ctx (src_pnames : list string) (ctx : ub_ctx)
  {struct ctx} : ub_ctx :=
  match ctx with
  | [] => []
  | UBA_ParamNoUndef nm w :: rest =>
      if string_in_list nm src_pnames
      then UBA_ParamNoUndef nm w :: filter_param_ub_ctx src_pnames rest
      else filter_param_ub_ctx src_pnames rest
  | UBA_PtrNonNull nm :: rest =>
      if string_in_list nm src_pnames
      then UBA_PtrNonNull nm :: filter_param_ub_ctx src_pnames rest
      else filter_param_ub_ctx src_pnames rest
  | UBA_PtrDereferenceable nm n :: rest =>
      if string_in_list nm src_pnames
      then UBA_PtrDereferenceable nm n :: filter_param_ub_ctx src_pnames rest
      else filter_param_ub_ctx src_pnames rest
  | UBA_PtrAligned nm al :: rest =>
      if string_in_list nm src_pnames
      then UBA_PtrAligned nm al :: filter_param_ub_ctx src_pnames rest
      else filter_param_ub_ctx src_pnames rest
  | _ :: rest => filter_param_ub_ctx src_pnames rest
  end.

Lemma filter_param_ub_ctx_holds {Pa : Params} :
  forall src_pnames ctx (bs : list (string * @dvalue Pa)) (penv : param_env Pa) foracle,
    (forall x, In x src_pnames -> ~ In x (List.map fst bs)) ->
    ub_ctx_holds penv foracle ctx ->
    ub_ctx_holds (extend_penv bs penv) foracle (filter_param_ub_ctx src_pnames ctx).
Proof.
  intros src_pnames ctx bs penv foracle Hdisj Hctx.
  induction Hctx as [| ua rest Hua _ IH]; cbn [filter_param_ub_ctx]; [constructor |].
  destruct ua as [nm w | nm | nm al | nm n | | | | |]; try exact IH;
    (destruct (string_in_list nm src_pnames) eqn:Ein; [| exact IH]);
    apply string_in_list_spec in Ein;
    (constructor; [| exact IH]);
    cbn [ub_assumption_holds] in *; intros dv Hpm;
    rewrite (extend_penv_not_in bs penv nm (Hdisj nm Ein)) in Hpm;
    exact (Hua dv Hpm).
Qed.

Fixpoint fold_ub_assumptions
  (allowed : list (string * positive))
  (prior_evals prior_brs : list cert_expr)
  (ctx : ub_ctx)
  (uas : list ub_assumption)
  {struct uas} : option ub_ctx :=
  match uas with
  | [] => Some ctx
  | ua :: rest =>
      if check_ub_assumption_justified allowed prior_evals prior_brs CD_RetVoid ctx ua
      then fold_ub_assumptions allowed prior_evals prior_brs (ua :: ctx) rest
      else None
  end.

Lemma fold_ub_assumptions_sound {Pa : Params} :
  forall uas allowed prior_evals prior_brs ctx ctx_out (penv : param_env Pa) foracle,
    wf_param_env_for allowed penv ->
    (forall big, In big prior_evals ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed) ->
    (forall big, In big prior_evals ->
      exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv) ->
    (forall c, In c prior_brs ->
      exists cbit : @Integers.bit_int 1,
        eval_closed_cert_expr penv foracle c = raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))) ->
    ub_ctx_holds penv foracle ctx ->
    fold_ub_assumptions allowed prior_evals prior_brs ctx uas = Some ctx_out ->
    ub_ctx_holds penv foracle ctx_out.
Proof.
  induction uas as [| ua rest IH];
    intros allowed prior_evals prior_brs ctx ctx_out penv foracle Hpenv Hpwf Hpret Hpbr Hctx Hf;
    cbn [fold_ub_assumptions] in Hf.
  - inversion Hf; subst; exact Hctx.
  - destruct (check_ub_assumption_justified allowed prior_evals prior_brs CD_RetVoid ctx ua) eqn:Ej;
      [| discriminate Hf].
    pose proof (check_ub_assumption_justified_sound allowed prior_evals prior_brs CD_RetVoid ctx ua
                  penv foracle NONE eq_refl Hpenv Hpwf Hpret Hpbr eq_refl Hctx Ej) as Hua.
    exact (IH allowed prior_evals prior_brs (ua :: ctx) ctx_out penv foracle
             Hpenv Hpwf Hpret Hpbr (Forall_cons _ Hua Hctx) Hf).
Qed.

Lemma extend_penv_wf_param_union {Pa : Params} :
  forall allowed pspecs (dvs_s dvs_t : list (raw_id * @dvalue Pa)) (penv : param_env Pa),
    wf_param_env_for allowed penv ->
    cut_phi_rel pspecs dvs_s dvs_t ->
    NoDup (cut_names_from 0%nat pspecs) ->
    (forall nm w, In (nm, w) allowed -> ~ In nm (cut_names_from 0%nat pspecs)) ->
    wf_param_env_for (allowed ++ cut_vars_from 0%nat pspecs)
      (extend_penv (cut_bindings_from 0%nat pspecs dvs_s dvs_t) penv).
Proof.
  intros allowed pspecs dvs_s dvs_t penv Hpenv Hrel Hnd Hdisj nm w Hin.
  set (bs := cut_bindings_from 0%nat pspecs dvs_s dvs_t).
  pose proof (cut_bindings_fst pspecs dvs_s dvs_t 0%nat Hrel) as Hfst; fold bs in Hfst.
  apply in_app_iff in Hin as [Hina | Hinc].
  - destruct (Hpenv nm w Hina) as [dv [Hpm Hsc]].
    exists dv; split; [| exact Hsc].
    rewrite extend_penv_not_in; [exact Hpm | rewrite Hfst; exact (Hdisj nm w Hina)].
  - assert (Hnd_bs : NoDup (List.map fst bs)) by (rewrite Hfst; exact Hnd).
    exact (cut_bindings_wf_param pspecs dvs_s dvs_t 0%nat bs penv Hrel Hnd_bs (incl_refl bs) nm w Hinc).
Qed.

Definition check_loop_cutpoint_cfg
  (allowed : list (string * positive))
  (init_ctx : ub_ctx)
  (src_cfg tgt_cfg : CFG.cfg dtyp)
  (cert : proof_certificate)
  (lci : loop_cutpoint_invariant)
  (opt_pf : option (list lrat_step)) : bool :=
  let src_pnames := List.map cert_reg_name (args src_cfg) in
  let src_uses := param_idx_uses_cfg src_cfg in
  let tgt_uses := param_idx_uses_cfg tgt_cfg in
  forallb (fun '(nm, _) => string_in_list nm src_pnames) allowed &&
  let lmap0_s := init_param_lmap (args src_cfg) src_pnames src_uses in
  let lmap0_t := init_param_lmap (args tgt_cfg) src_pnames tgt_uses in
  match reify_natural_loop src_cfg (lci_src_header lci) lmap0_s (overlay_hspecs_s 0%nat),
        reify_natural_loop tgt_cfg (lci_tgt_header lci) lmap0_t (overlay_hspecs_t 0%nat) with
  | Some (hspecs_s, s_s), Some (hspecs_t, s_t) =>
      match pair_phi_specs hspecs_s hspecs_t with
      | None => false
      | Some pspecs =>
          let cut_allowed := allowed ++ cut_vars_from 0%nat pspecs in
          no_dup_strings (src_pnames ++ cut_names_from 0%nat pspecs) &&
          match fold_ub_assumptions allowed (nls_evals_entry s_s) [] init_ctx
                  (block_uas_for (init src_cfg) (pc_blocks cert) (init src_cfg)) with
          | None => false
          | Some ctx_ent =>
              forallb (expr_safe_under_src ctx_ent (nls_evals_entry s_s)) (nls_evals_entry s_t) &&
              forallb (expr_safe_under_src ctx_ent
                         (nls_evals_entry s_s ++ peval_exprs (nls_init_pevals s_s)))
                      (peval_exprs (nls_init_pevals s_t)) &&
              check_pevals_refine ctx_ent opt_pf pspecs
                (nls_init_pevals s_s) (nls_init_pevals s_t) &&
              let base_loop_ctx := filter_param_ub_ctx src_pnames ctx_ent in
              match fold_ub_assumptions cut_allowed (nls_evals_hdr s_s) [nls_ce_cond s_s]
                      base_loop_ctx (block_uas_for (init src_cfg) (pc_blocks cert) (nls_bid_hdr s_s)) with
              | None => false
              | Some ctx_hdr =>
                  let eff_s := eff_loop_cond (nls_latch_on_true s_s) (nls_ce_cond s_s) in
                  let eff_t := eff_loop_cond (nls_latch_on_true s_t) (nls_ce_cond s_t) in
                  forallb (expr_safe_under_src ctx_hdr (nls_evals_hdr s_s))
                    (nls_ce_cond s_t :: nls_evals_hdr s_t) &&
                  check_expr_refines_with_lrat ctx_hdr eff_s eff_t opt_pf &&
                  let ctx_cont_0 :=
                    extract_branch_cond_assumptions (nls_latch_on_true s_s) (nls_ce_cond s_s) ++ ctx_hdr in
                  let latch_uas :=
                    if raw_id_eqb (nls_bid_latch_entry s_s) (nls_bid_hdr s_s) then []
                    else block_uas_for (init src_cfg) (pc_blocks cert) (nls_bid_latch_entry s_s) in
                  match fold_ub_assumptions cut_allowed
                          (nls_evals_hdr s_s ++ nls_evals_body s_s) [nls_ce_cond s_s]
                          ctx_cont_0 latch_uas with
                  | None => false
                  | Some ctx_cont =>
                      forallb (expr_safe_under_src ctx_cont
                                 (nls_evals_hdr s_s ++ nls_evals_body s_s))
                              (nls_evals_body s_t) &&
                      forallb (expr_safe_under_src ctx_cont
                                 ((nls_evals_hdr s_s ++ nls_evals_body s_s) ++
                                  peval_exprs (nls_next_pevals s_s)))
                              (peval_exprs (nls_next_pevals s_t)) &&
                      check_pevals_refine ctx_cont opt_pf pspecs
                        (nls_next_pevals s_s) (nls_next_pevals s_t) &&
                      let ctx_exit_0 :=
                        extract_branch_cond_assumptions
                          (negb (nls_latch_on_true s_s)) (nls_ce_cond s_s) ++ ctx_hdr in
                      match fold_ub_assumptions cut_allowed
                              (nls_evals_hdr s_s ++ nls_evals_exit s_s) [nls_ce_cond s_s]
                              ctx_exit_0 (block_uas_for (init src_cfg) (pc_blocks cert) (nls_bid_exit s_s)) with
                      | None => false
                      | Some ctx_exit =>
                          match pc_return_obligation cert with
                          | RO_VoidEquiv => false
                          | RO_ScalarRefines w _ _ _ =>
                              Pos.eqb w (nls_w_ret s_s) &&
                              Pos.eqb w (nls_w_ret s_t) &&
                              forallb (expr_safe_under_src ctx_exit
                                         (nls_evals_hdr s_s ++ nls_evals_exit s_s))
                                      (nls_ce_ret s_t :: nls_evals_exit s_t) &&
                              check_expr_refines_with_lrat ctx_exit
                                (nls_ce_ret s_s) (nls_ce_ret s_t) opt_pf
                          end
                      end
                  end
              end
          end
      end
  | _, _ => false
  end.

Lemma forall_ret_in {Pa : Params} :
  forall (es : list cert_expr) (penv : param_env Pa) foracle,
    Forall (fun ce => exists dv, eval_closed_cert_expr penv foracle ce = raise_ret dv) es ->
    forall big, In big es -> exists dv, eval_closed_cert_expr penv foracle big = raise_ret dv.
Proof.
  intros es penv foracle Hfa; rewrite Forall_forall in Hfa; exact Hfa.
Qed.

Lemma forall_wf_pure_in :
  forall allowed es,
    Forall (wf_pure_eval_entry allowed) es ->
    forall big, In big es ->
      wt_cert_expr [] big = true /\ is_let_free_expr big = true /\ incl (collect_free_vars [] big) allowed.
Proof.
  intros allowed es Hfa; rewrite Forall_forall in Hfa; exact Hfa.
Qed.

Local Lemma check_loop_cutpoint_continue_step {Pa : Params} :
  forall cut_allowed opt_pf pspecs
         (src_cfg tgt_cfg : CFG.cfg dtyp)
         s_s s_t b_ent_s b_ent_t b_hdr_s b_hdr_t
         ctx_cont_0 ctx_cont latch_uas
         (penv_cut : param_env Pa)
         bid_prev_s bid_prev_t
         (env_prev_s env_prev_t : rmap (@dvalue Pa))
         (cbit_s cbit_t : @Integers.bit_int 1),
    let bmap_s := ocfg_map (blks src_cfg) in
    let bmap_t := ocfg_map (blks tgt_cfg) in
    let dom_entry_s := args src_cfg ++ code_written_ids (blk_code b_ent_s) in
    let dom_entry_t := args tgt_cfg ++ code_written_ids (blk_code b_ent_t) in
    wf_param_env_for cut_allowed penv_cut ->
    ub_ctx_holds penv_cut dummy_freeze_oracle ctx_cont_0 ->
    (forall c, In c [nls_ce_cond s_s] ->
       exists cbit : @Integers.bit_int 1,
         eval_closed_cert_expr penv_cut dummy_freeze_oracle c =
         raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))) ->
    Forall (wf_pure_eval_entry cut_allowed) (nls_evals_hdr s_s) ->
    Forall (wf_pure_eval_entry cut_allowed) (nls_evals_body s_s) ->
    Forall (fun '(_, w, ce) =>
      is_supported_bit_width w = true /\ cert_expr_bit_width ce = w /\ wf_pure_eval_entry cut_allowed ce)
      (nls_next_pevals s_s) ->
    Forall (fun '(_, w, ce) =>
      is_supported_bit_width w = true /\ cert_expr_bit_width ce = w /\ wf_pure_eval_entry cut_allowed ce)
      (nls_next_pevals s_t) ->
    Forall (wf_pure_eval_entry cut_allowed) (nls_evals_body s_t) ->
    Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
      (nls_evals_hdr s_s) ->
    Bool.eqb (@Integers.unsigned 1 cbit_t =? 1)%Z (nls_latch_on_true s_t) =
    Bool.eqb (@Integers.unsigned 1 cbit_s =? 1)%Z (nls_latch_on_true s_s) ->
    Bool.eqb (@Integers.unsigned 1 cbit_s =? 1)%Z (nls_latch_on_true s_s) = true ->
    fold_ub_assumptions cut_allowed (nls_evals_hdr s_s ++ nls_evals_body s_s)
      [nls_ce_cond s_s] ctx_cont_0 latch_uas = Some ctx_cont ->
    forallb (expr_safe_under_src ctx_cont (nls_evals_hdr s_s ++ nls_evals_body s_s))
      (nls_evals_body s_t) = true ->
    forallb (expr_safe_under_src ctx_cont
               ((nls_evals_hdr s_s ++ nls_evals_body s_s) ++ peval_exprs (nls_next_pevals s_s)))
      (peval_exprs (nls_next_pevals s_t)) = true ->
    check_pevals_refine ctx_cont opt_pf pspecs (nls_next_pevals s_s) (nls_next_pevals s_t) = true ->
    reify_pure_phis (nls_bid_latch_from s_s) (nls_lmap_latch s_s) (blk_phis b_hdr_s) = Some (nls_next_pevals s_s) ->
    reify_pure_phis (nls_bid_latch_from s_t) (nls_lmap_latch s_t) (blk_phis b_hdr_t) = Some (nls_next_pevals s_t) ->
    RM.find (nls_bid_hdr s_s) bmap_s = Some b_hdr_s ->
    (Bool.eqb (@Integers.unsigned 1 cbit_s =? 1)%Z (nls_latch_on_true s_s) = true ->
     ((forall sigma, cfg_steps_to_ub sigma env_prev_s (denote_cfg_from bmap_s None (bid_prev_s, nls_bid_hdr s_s))) /\
      exists ce msg, In ce (nls_evals_body s_s) /\
        eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ub msg) \/
     (exists env_latch_s,
        lmap_matches_env penv_cut (nls_lmap_latch s_s) env_latch_s /\
        Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
          (nls_evals_body s_s) /\
        (forall r, In r dom_entry_s -> RM.find r env_latch_s = RM.find r env_prev_s) /\
        pure_cfg_steps_to_tau env_prev_s (denote_cfg_from bmap_s None (bid_prev_s, nls_bid_hdr s_s))
          env_latch_s (denote_cfg_from bmap_s None (nls_bid_latch_from s_s, nls_bid_hdr s_s)))) ->
    (Bool.eqb (@Integers.unsigned 1 cbit_t =? 1)%Z (nls_latch_on_true s_t) = true ->
     ((forall sigma, cfg_steps_to_ub sigma env_prev_t (denote_cfg_from bmap_t None (bid_prev_t, nls_bid_hdr s_t))) /\
      exists ce msg, In ce (nls_evals_body s_t) /\
        eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ub msg) \/
     (exists env_latch_t,
        lmap_matches_env penv_cut (nls_lmap_latch s_t) env_latch_t /\
        Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
          (nls_evals_body s_t) /\
        (forall r, In r dom_entry_t -> RM.find r env_latch_t = RM.find r env_prev_t) /\
        pure_cfg_steps_to_tau env_prev_t (denote_cfg_from bmap_t None (bid_prev_t, nls_bid_hdr s_t))
          env_latch_t (denote_cfg_from bmap_t None (nls_bid_latch_from s_t, nls_bid_hdr s_t)))) ->
    (forall sigma, cfg_steps_to_ub sigma env_prev_s (denote_cfg_from bmap_s None (bid_prev_s, nls_bid_hdr s_s))) \/
    (exists env_latch_s env_latch_t dvs_next_s dvs_next_t,
       (forall r0, In r0 dom_entry_s -> RM.find r0 env_latch_s = RM.find r0 env_prev_s) /\
       (forall r0, In r0 dom_entry_t -> RM.find r0 env_latch_t = RM.find r0 env_prev_t) /\
       pure_cfg_steps_to_tau env_prev_s (denote_cfg_from bmap_s None (bid_prev_s, nls_bid_hdr s_s))
         env_latch_s (denote_cfg_from bmap_s None (nls_bid_latch_from s_s, nls_bid_hdr s_s)) /\
       pure_cfg_steps_to_tau env_prev_t (denote_cfg_from bmap_t None (bid_prev_t, nls_bid_hdr s_t))
         env_latch_t (denote_cfg_from bmap_t None (nls_bid_latch_from s_t, nls_bid_hdr s_t)) /\
       pure_cfg_steps env_latch_s (denote_phis (nls_bid_latch_from s_s) (blk_phis b_hdr_s))
         (apply_phi_env env_latch_s dvs_next_s) tt /\
       pure_cfg_steps env_latch_t (denote_phis (nls_bid_latch_from s_t) (blk_phis b_hdr_t))
         (apply_phi_env env_latch_t dvs_next_t) tt /\
       cut_phi_rel pspecs dvs_next_s dvs_next_t).
Proof.
  intros cut_allowed opt_pf pspecs src_cfg tgt_cfg s_s s_t b_ent_s b_ent_t b_hdr_s b_hdr_t
         ctx_cont_0 ctx_cont latch_uas penv_cut bid_prev_s bid_prev_t env_prev_s env_prev_t
         cbit_s cbit_t bmap_s bmap_t dom_entry_s dom_entry_t
         Hpenv_cut Hctx_cont0 Hbr_hdr_s Hfa_hdr_s Hfa_body_s Hfa_next_s Hfa_next_t Hfa_body_t
         Hret_hdr_s Epol_eq Econt Ef_cont Hsafe_body_t Hsafe_next_t Href_next
         Hr_next_s Hr_next_t Hf_hdr_s Hcont_s Hcont_t.
  destruct (Hcont_s Econt)
    as [[Hub_bs _] | (env_latch_s & Hlm_latch_s & Hret_body_s & Hpres_ls & Htau_s)].
  - left; exact Hub_bs.
  - assert (Hret_hb_s :
      Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
        (nls_evals_hdr s_s ++ nls_evals_body s_s))
      by (apply Forall_app; split; assumption).
    assert (Hwf_hb_s : Forall (wf_pure_eval_entry cut_allowed) (nls_evals_hdr s_s ++ nls_evals_body s_s))
      by (apply Forall_app; split; assumption).
    pose proof (fold_ub_assumptions_sound _ cut_allowed
                  (nls_evals_hdr s_s ++ nls_evals_body s_s) [nls_ce_cond s_s]
                  ctx_cont_0 ctx_cont penv_cut dummy_freeze_oracle Hpenv_cut
                  (forall_wf_pure_in _ _ Hwf_hb_s)
                  (forall_ret_in _ _ _ Hret_hb_s)
                  Hbr_hdr_s Hctx_cont0 Ef_cont) as Hctx_cont.
    destruct (pure_phis_denote_step (blk_phis b_hdr_s) penv_cut (nls_bid_latch_from s_s)
                (nls_lmap_latch s_s) env_latch_s (nls_next_pevals s_s) Hlm_latch_s Hr_next_s)
      as [[Hub_np_s _] | [dvs_next_s [Hpm_next_s Hst_np_s]]].
    + left; intros sigma; eapply pure_cfg_steps_to_tau_then_ub; [exact Htau_s |].
      eapply denote_cfg_from_block_ub; [exact Hf_hdr_s |].
      unfold denote_block; apply cfg_steps_to_ub_bind_l; exact (Hub_np_s sigma).
    + rewrite Econt in Epol_eq.
      destruct (Hcont_t Epol_eq)
        as [[_ (ce_bt & msg_bt & Hin_bt & Hev_bt)]
           | (env_latch_t & Hlm_latch_t & _ & Hpres_lt & Htau_t)].
      * exfalso; exact (exprs_safe_under_src_sound (nls_evals_body s_t) cut_allowed ctx_cont
                          (nls_evals_hdr s_s ++ nls_evals_body s_s) penv_cut Hpenv_cut Hctx_cont
                          (forall_ret_in _ _ _ Hret_hb_s) Hfa_body_t Hsafe_body_t
                          ce_bt msg_bt Hin_bt Hev_bt).
      * assert (Hret_hbn_s :
          Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
            ((nls_evals_hdr s_s ++ nls_evals_body s_s) ++ peval_exprs (nls_next_pevals s_s)))
          by (apply Forall_app; split; [exact Hret_hb_s | exact (peval_exprs_ret _ _ _ Hpm_next_s)]).
        destruct (pure_phis_denote_step (blk_phis b_hdr_t) penv_cut (nls_bid_latch_from s_t)
                    (nls_lmap_latch s_t) env_latch_t (nls_next_pevals s_t) Hlm_latch_t Hr_next_t)
          as [[_ (ce_npt & msg_npt & Hin_npt & Hev_npt)] | [dvs_next_t [Hpm_next_t Hst_np_t]]].
        -- exfalso; exact (exprs_safe_under_src_sound (peval_exprs (nls_next_pevals s_t))
                              cut_allowed ctx_cont
                              ((nls_evals_hdr s_s ++ nls_evals_body s_s) ++
                               peval_exprs (nls_next_pevals s_s))
                              penv_cut Hpenv_cut Hctx_cont
                              (forall_ret_in _ _ _ Hret_hbn_s)
                              (peval_exprs_typing _ _ Hfa_next_t) Hsafe_next_t
                              ce_npt msg_npt Hin_npt Hev_npt).
        -- destruct (check_pevals_refine_sound pspecs (nls_next_pevals s_s) (nls_next_pevals s_t)
                        dvs_next_s dvs_next_t cut_allowed ctx_cont opt_pf penv_cut
                        Hpenv_cut Hctx_cont Hfa_next_s Hfa_next_t Hpm_next_s Hpm_next_t Href_next)
              as (Hrel_next & _ & _).
           right; exists env_latch_s, env_latch_t, dvs_next_s, dvs_next_t.
           repeat split; assumption.
Qed.

Local Lemma check_loop_cutpoint_exit_step {Pa : Params} :
  forall cut_allowed opt_pf (src_cfg tgt_cfg : CFG.cfg dtyp)
         s_s s_t ctx_exit_0 ctx_exit b_exit_uas
         (sigma_tgt : @draw_strat Pa) (penv_cut : param_env Pa)
         bid_prev_s bid_prev_t (env_prev_s env_prev_t : rmap (@dvalue Pa))
         (cbit_s cbit_t : @Integers.bit_int 1),
    let bmap_s := ocfg_map (blks src_cfg) in
    let bmap_t := ocfg_map (blks tgt_cfg) in
    wf_param_env_for cut_allowed penv_cut ->
    ub_ctx_holds penv_cut dummy_freeze_oracle ctx_exit_0 ->
    (forall c, In c [nls_ce_cond s_s] ->
       exists cbit : @Integers.bit_int 1,
         eval_closed_cert_expr penv_cut dummy_freeze_oracle c =
         raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))) ->
    Forall (wf_pure_eval_entry cut_allowed) (nls_evals_hdr s_s) ->
    Forall (wf_pure_eval_entry cut_allowed) (nls_evals_exit s_s) ->
    Forall (wf_pure_eval_entry cut_allowed) (nls_evals_exit s_t) ->
    wf_pure_eval_entry cut_allowed (nls_ce_ret s_s) ->
    wf_pure_eval_entry cut_allowed (nls_ce_ret s_t) ->
    Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
      (nls_evals_hdr s_s) ->
    Bool.eqb (@Integers.unsigned 1 cbit_t =? 1)%Z (nls_latch_on_true s_t) =
    Bool.eqb (@Integers.unsigned 1 cbit_s =? 1)%Z (nls_latch_on_true s_s) ->
    Bool.eqb (@Integers.unsigned 1 cbit_s =? 1)%Z (nls_latch_on_true s_s) = false ->
    fold_ub_assumptions cut_allowed (nls_evals_hdr s_s ++ nls_evals_exit s_s)
      [nls_ce_cond s_s] ctx_exit_0 b_exit_uas = Some ctx_exit ->
    forallb (expr_safe_under_src ctx_exit (nls_evals_hdr s_s ++ nls_evals_exit s_s))
      (nls_ce_ret s_t :: nls_evals_exit s_t) = true ->
    check_expr_refines_with_lrat ctx_exit (nls_ce_ret s_s) (nls_ce_ret s_t) opt_pf = true ->
    (Bool.eqb (@Integers.unsigned 1 cbit_s =? 1)%Z (nls_latch_on_true s_s) = false ->
     ((forall sigma, cfg_steps_to_ub sigma env_prev_s (denote_cfg_from bmap_s None (bid_prev_s, nls_bid_hdr s_s))) /\
      exists ce msg, In ce (nls_ce_ret s_s :: nls_evals_exit s_s) /\
        eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ub msg) \/
     (exists env_exit_s dv_ret_s,
        Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
          (nls_evals_exit s_s) /\
        eval_closed_cert_expr penv_cut dummy_freeze_oracle (nls_ce_ret s_s) = raise_ret dv_ret_s /\
        wf_scalar_dvalue (nls_w_ret s_s) dv_ret_s /\
        pure_cfg_steps env_prev_s (denote_cfg_from bmap_s None (bid_prev_s, nls_bid_hdr s_s))
          env_exit_s dv_ret_s)) ->
    (Bool.eqb (@Integers.unsigned 1 cbit_t =? 1)%Z (nls_latch_on_true s_t) = false ->
     ((forall sigma, cfg_steps_to_ub sigma env_prev_t (denote_cfg_from bmap_t None (bid_prev_t, nls_bid_hdr s_t))) /\
      exists ce msg, In ce (nls_ce_ret s_t :: nls_evals_exit s_t) /\
        eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ub msg) \/
     (exists env_exit_t dv_ret_t,
        Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
          (nls_evals_exit s_t) /\
        eval_closed_cert_expr penv_cut dummy_freeze_oracle (nls_ce_ret s_t) = raise_ret dv_ret_t /\
        wf_scalar_dvalue (nls_w_ret s_t) dv_ret_t /\
        pure_cfg_steps env_prev_t (denote_cfg_from bmap_t None (bid_prev_t, nls_bid_hdr s_t))
          env_exit_t dv_ret_t)) ->
    det_ref dvalue_refines
      (run_draws sigma_tgt (run_cfg_locals env_prev_s (denote_cfg_from bmap_s None (bid_prev_s, nls_bid_hdr s_s))))
      (run_draws sigma_tgt (run_cfg_locals env_prev_t (denote_cfg_from bmap_t None (bid_prev_t, nls_bid_hdr s_t)))).
Proof.
  intros cut_allowed opt_pf src_cfg tgt_cfg s_s s_t ctx_exit_0 ctx_exit b_exit_uas
         sigma_tgt penv_cut bid_prev_s bid_prev_t env_prev_s env_prev_t cbit_s cbit_t
         bmap_s bmap_t Hpenv_cut Hctx_exit0 Hbr_hdr_s Hfa_hdr_s Hfa_exit_s Hfa_exit_t
         Hwf_ret_s Hwf_ret_t Hret_hdr_s Epol_eq Econt Ef_exit Hsafe_exit_t Href_ret Hexit_s Hexit_t.
  destruct (Hexit_s Econt)
    as [[Hub_xs _] | (env_exit_s & dv_ret_s & Hret_exit_s & Hev_ret_s & _ & Hret_st_s)].
  - exact (cfg_steps_ub_det_ref dvalue_refines sigma_tgt _ _ _ (Hub_xs sigma_tgt)).
  - assert (Hret_hx_s :
      Forall (fun ce => exists dv, eval_closed_cert_expr penv_cut dummy_freeze_oracle ce = raise_ret dv)
        (nls_evals_hdr s_s ++ nls_evals_exit s_s))
      by (apply Forall_app; split; assumption).
    assert (Hwf_hx_s : Forall (wf_pure_eval_entry cut_allowed) (nls_evals_hdr s_s ++ nls_evals_exit s_s))
      by (apply Forall_app; split; assumption).
    pose proof (fold_ub_assumptions_sound _ cut_allowed
                  (nls_evals_hdr s_s ++ nls_evals_exit s_s) [nls_ce_cond s_s]
                  ctx_exit_0 ctx_exit penv_cut dummy_freeze_oracle Hpenv_cut
                  (forall_wf_pure_in _ _ Hwf_hx_s)
                  (forall_ret_in _ _ _ Hret_hx_s)
                  Hbr_hdr_s Hctx_exit0 Ef_exit) as Hctx_exit.
    rewrite Econt in Epol_eq.
    destruct (Hexit_t Epol_eq)
      as [[_ (ce_xt & msg_xt & Hin_xt & Hev_xt)]
         | (env_exit_t & dv_ret_t & _ & Hev_ret_t & _ & Hret_st_t)].
    + exfalso; exact (exprs_safe_under_src_sound (nls_ce_ret s_t :: nls_evals_exit s_t)
                        cut_allowed ctx_exit (nls_evals_hdr s_s ++ nls_evals_exit s_s)
                        penv_cut Hpenv_cut Hctx_exit
                        (forall_ret_in _ _ _ Hret_hx_s)
                        (Forall_cons _ Hwf_ret_t Hfa_exit_t) Hsafe_exit_t
                        ce_xt msg_xt Hin_xt Hev_xt).
    + destruct Hwf_ret_s as (_ & _ & Hfv_ret_s).
      destruct Hwf_ret_t as (_ & _ & Hfv_ret_t).
      pose proof (check_expr_refines_with_lrat_sound ctx_exit (nls_ce_ret s_s) (nls_ce_ret s_t)
                    opt_pf penv_cut dummy_freeze_oracle Href_ret
                    (fun n w0 H => Hpenv_cut n w0 (Hfv_ret_s (n, w0) H))
                    (fun n w0 H => Hpenv_cut n w0 (Hfv_ret_t (n, w0) H))
                    Hctx_exit) as Hdv_ret.
      rewrite Hev_ret_s, Hev_ret_t in Hdv_ret; cbn [refine_eou_dvalue] in Hdv_ret.
      exact (cfg_steps_ret_det_ref dvalue_refines
               sigma_tgt env_prev_s _ sigma_tgt env_exit_s dv_ret_s
               sigma_tgt env_prev_t _ sigma_tgt env_exit_t dv_ret_t
               (pure_cfg_to_cfg_ret sigma_tgt _ _ _ _ Hret_st_s)
               (pure_cfg_to_cfg_ret sigma_tgt _ _ _ _ Hret_st_t)
               Hdv_ret).
Qed.

Local Lemma check_loop_cutpoint_cfg_loop_bisim {Pa : Params} :
  forall allowed cut_allowed opt_pf pspecs
         (src_cfg tgt_cfg : CFG.cfg dtyp) src_hdr tgt_hdr
         hspecs_s hspecs_t s_s s_t b_ent_s b_ent_t b_hdr_s b_hdr_t
         ctx_ent ctx_hdr ctx_cont ctx_exit
         (src_pnames : list string) hdr_uas latch_uas b_exit_uas
         (sigma_tgt : @draw_strat Pa) (penv : param_env Pa)
         (env_entry_s env_entry_t : rmap (@dvalue Pa)),
    let bmap_s := ocfg_map (blks src_cfg) in
    let bmap_t := ocfg_map (blks tgt_cfg) in
    let base_loop_ctx := filter_param_ub_ctx src_pnames ctx_ent in
    let eff_s := eff_loop_cond (nls_latch_on_true s_s) (nls_ce_cond s_s) in
    let eff_t := eff_loop_cond (nls_latch_on_true s_t) (nls_ce_cond s_t) in
    let ctx_cont_0 :=
      extract_branch_cond_assumptions (nls_latch_on_true s_s) (nls_ce_cond s_s) ++ ctx_hdr in
    let ctx_exit_0 :=
      extract_branch_cond_assumptions (negb (nls_latch_on_true s_s)) (nls_ce_cond s_s) ++ ctx_hdr in
    cut_allowed = allowed ++ cut_vars_from 0%nat pspecs ->
    NoDup (cut_names_from 0%nat pspecs) ->
    (forall x, In x src_pnames -> ~ In x (cut_names_from 0%nat pspecs)) ->
    (forall nm w, In (nm, w) allowed -> ~ In nm (cut_names_from 0%nat pspecs)) ->
    pair_phi_specs hspecs_s hspecs_t = Some pspecs ->
    wf_param_env_for allowed penv ->
    ub_ctx_holds penv dummy_freeze_oracle ctx_ent ->
    fold_ub_assumptions cut_allowed (nls_evals_hdr s_s) [nls_ce_cond s_s]
      base_loop_ctx hdr_uas = Some ctx_hdr ->
    fold_ub_assumptions cut_allowed (nls_evals_hdr s_s ++ nls_evals_body s_s)
      [nls_ce_cond s_s] ctx_cont_0 latch_uas = Some ctx_cont ->
    fold_ub_assumptions cut_allowed (nls_evals_hdr s_s ++ nls_evals_exit s_s)
      [nls_ce_cond s_s] ctx_exit_0 b_exit_uas = Some ctx_exit ->
    forallb (expr_safe_under_src ctx_hdr (nls_evals_hdr s_s))
      (nls_ce_cond s_t :: nls_evals_hdr s_t) = true ->
    check_expr_refines_with_lrat ctx_hdr eff_s eff_t opt_pf = true ->
    forallb (expr_safe_under_src ctx_cont (nls_evals_hdr s_s ++ nls_evals_body s_s))
      (nls_evals_body s_t) = true ->
    forallb (expr_safe_under_src ctx_cont
               ((nls_evals_hdr s_s ++ nls_evals_body s_s) ++ peval_exprs (nls_next_pevals s_s)))
      (peval_exprs (nls_next_pevals s_t)) = true ->
    check_pevals_refine ctx_cont opt_pf pspecs (nls_next_pevals s_s) (nls_next_pevals s_t) = true ->
    forallb (expr_safe_under_src ctx_exit (nls_evals_hdr s_s ++ nls_evals_exit s_s))
      (nls_ce_ret s_t :: nls_evals_exit s_t) = true ->
    check_expr_refines_with_lrat ctx_exit (nls_ce_ret s_s) (nls_ce_ret s_t) opt_pf = true ->
    (forall idx w0 pnm,
       In (idx, DTYPE_Base (DTYPE_I w0)) (param_idx_uses_cfg src_cfg) ->
       nth_error src_pnames idx = Some pnm -> In (pnm, w0) allowed) ->
    (forall idx w0 pnm,
       In (idx, DTYPE_Base (DTYPE_I w0)) (param_idx_uses_cfg tgt_cfg) ->
       nth_error src_pnames idx = Some pnm -> In (pnm, w0) allowed) ->
    (forall lmap, wf_pure_lmap allowed lmap ->
       wf_pure_lmap cut_allowed (overlay_hspecs_s 0%nat lmap hspecs_s)) ->
    (forall lmap, wf_pure_lmap allowed lmap ->
       wf_pure_lmap cut_allowed (overlay_hspecs_t 0%nat lmap hspecs_t)) ->
    reify_natural_loop src_cfg src_hdr
      (init_param_lmap (args src_cfg) src_pnames (param_idx_uses_cfg src_cfg))
      (overlay_hspecs_s 0%nat) = Some (hspecs_s, s_s) ->
    reify_natural_loop tgt_cfg tgt_hdr
      (init_param_lmap (args tgt_cfg) src_pnames (param_idx_uses_cfg tgt_cfg))
      (overlay_hspecs_t 0%nat) = Some (hspecs_t, s_t) ->
    RM.find (init src_cfg) bmap_s = Some b_ent_s ->
    RM.find (init tgt_cfg) bmap_t = Some b_ent_t ->
    RM.find (nls_bid_hdr s_s) bmap_s = Some b_hdr_s ->
    RM.find (nls_bid_hdr s_t) bmap_t = Some b_hdr_t ->
    lmap_matches_env penv (nls_lmap_entry s_s) env_entry_s ->
    lmap_matches_env penv (nls_lmap_entry s_t) env_entry_t ->
    forall bid_prev_s bid_prev_t env_prev_s env_prev_t dvs_s dvs_t,
      (forall r0, In r0 (args src_cfg ++ code_written_ids (blk_code b_ent_s)) ->
         RM.find r0 env_prev_s = RM.find r0 env_entry_s) ->
      (forall r0, In r0 (args tgt_cfg ++ code_written_ids (blk_code b_ent_t)) ->
         RM.find r0 env_prev_t = RM.find r0 env_entry_t) ->
      pure_cfg_steps env_prev_s (denote_phis bid_prev_s (blk_phis b_hdr_s))
        (apply_phi_env env_prev_s dvs_s) tt ->
      pure_cfg_steps env_prev_t (denote_phis bid_prev_t (blk_phis b_hdr_t))
        (apply_phi_env env_prev_t dvs_t) tt ->
      cut_phi_rel pspecs dvs_s dvs_t ->
      det_ref dvalue_refines
        (run_draws sigma_tgt (run_cfg_locals env_prev_s
           (denote_cfg_from bmap_s None (bid_prev_s, nls_bid_hdr s_s))))
        (run_draws sigma_tgt (run_cfg_locals env_prev_t
           (denote_cfg_from bmap_t None (bid_prev_t, nls_bid_hdr s_t)))).
Proof.
  intros allowed cut_allowed opt_pf pspecs src_cfg tgt_cfg src_hdr tgt_hdr
         hspecs_s hspecs_t s_s s_t b_ent_s b_ent_t b_hdr_s b_hdr_t
         ctx_ent ctx_hdr ctx_cont ctx_exit src_pnames hdr_uas latch_uas b_exit_uas
         sigma_tgt penv env_entry_s env_entry_t
         bmap_s bmap_t base_loop_ctx eff_s eff_t ctx_cont_0 ctx_exit_0
         Hcut_eq Hnd_cut Hdisj_sp_cut Hall_not_cut Epair Hpenv0 Hctx_ent
         Ef_hdr Ef_cont Ef_exit Hsafe_hdr_t Href_eff Hsafe_body_t Hsafe_next_t Href_next
         Hsafe_exit_t Href_ret Hpu_s Hpu_t Hwrap_s Hwrap_t Er_s Er_t
         Hf_ent_s Hf_ent_t Hf_hdr_s Hf_hdr_t Henv_ent_s Henv_ent_t.
  destruct (reify_natural_loop_spec src_cfg src_hdr allowed cut_allowed
              (init_param_lmap (args src_cfg) src_pnames (param_idx_uses_cfg src_cfg))
              (overlay_hspecs_s 0%nat) hspecs_s s_s
              (init_param_lmap_typing (param_idx_uses_cfg src_cfg) (args src_cfg) src_pnames allowed Hpu_s)
              (init_param_lmap_dom (param_idx_uses_cfg src_cfg) (args src_cfg) src_pnames)
              Hwrap_s Er_s)
    as (b_ent_s' & b_hdr_s' & Hf_ent_s' & Hf_hdr_s' & _ & _ & Hr_next_s &
        Hlmap_ent_s & Hdom_ent_s & _ & _ & Hfa_hdr_s &
        Hwf_cond_s & Hbw_cond_s & Hfa_body_s & Hfa_next_s & Hfa_exit_s &
        Hwf_ret_s & _ & _ & _ & Hstep_hdr_s).
  destruct (reify_natural_loop_spec tgt_cfg tgt_hdr allowed cut_allowed
              (init_param_lmap (args tgt_cfg) src_pnames (param_idx_uses_cfg tgt_cfg))
              (overlay_hspecs_t 0%nat) hspecs_t s_t
              (init_param_lmap_typing (param_idx_uses_cfg tgt_cfg) (args tgt_cfg) src_pnames allowed Hpu_t)
              (init_param_lmap_dom (param_idx_uses_cfg tgt_cfg) (args tgt_cfg) src_pnames)
              Hwrap_t Er_t)
    as (b_ent_t' & b_hdr_t' & Hf_ent_t' & Hf_hdr_t' & _ & _ & Hr_next_t &
        Hlmap_ent_t & Hdom_ent_t & _ & _ & Hfa_hdr_t &
        Hwf_cond_t & Hbw_cond_t & Hfa_body_t & Hfa_next_t & Hfa_exit_t &
        Hwf_ret_t & _ & _ & _ & Hstep_hdr_t).
  fold bmap_s in Hf_ent_s', Hf_hdr_s'; fold bmap_t in Hf_ent_t', Hf_hdr_t'.
  rewrite Hf_ent_s in Hf_ent_s'; injection Hf_ent_s' as <-.
  rewrite Hf_hdr_s in Hf_hdr_s'; injection Hf_hdr_s' as <-.
  rewrite Hf_ent_t in Hf_ent_t'; injection Hf_ent_t' as <-.
  rewrite Hf_hdr_t in Hf_hdr_t'; injection Hf_hdr_t' as <-.
  pcofix CIH.
  intros bid_prev_s bid_prev_t env_prev_s env_prev_t dvs_s dvs_t Hag_s Hag_t Hphis_s Hphis_t Hrel.
  set (bs := cut_bindings_from 0%nat pspecs dvs_s dvs_t).
  set (penv_cut := extend_penv bs penv).
  pose proof (cut_bindings_fst pspecs dvs_s dvs_t 0%nat Hrel) as Hbs_fst; fold bs in Hbs_fst.
  assert (Hnd_bs : NoDup (List.map fst bs)) by (rewrite Hbs_fst; exact Hnd_cut).
  assert (Hp_agree : forall nm w, In (nm, w) allowed -> penv nm = penv_cut nm).
  { intros nm w Hin; symmetry; unfold penv_cut; apply extend_penv_not_in.
    rewrite Hbs_fst; exact (Hall_not_cut nm w Hin). }
  pose proof (lmap_matches_env_transfer allowed _ penv penv_cut
                (nls_lmap_entry s_s) env_entry_s env_prev_s
                Hlmap_ent_s Hdom_ent_s Hp_agree Hag_s Henv_ent_s) as Hlm_prev_s.
  pose proof (lmap_matches_env_transfer allowed _ penv penv_cut
                (nls_lmap_entry s_t) env_entry_t env_prev_t
                Hlmap_ent_t Hdom_ent_t Hp_agree Hag_t Henv_ent_t) as Hlm_prev_t.
  destruct (overlay_cut_lmap_matches pspecs dvs_s dvs_t 0%nat bs penv
              (nls_lmap_entry s_s) (nls_lmap_entry s_t) env_prev_s env_prev_t
              Hrel Hnd_bs (incl_refl bs) Hlm_prev_s Hlm_prev_t)
    as [Hlm_hdr0_s Hlm_hdr0_t].
  destruct (pair_phi_specs_overlay hspecs_s hspecs_t pspecs 0%nat
              (nls_lmap_entry s_s) (nls_lmap_entry s_t) Epair)
    as (Hos_eq & Hot_eq & Hms_eq & Hmt_eq).
  rewrite <- Hos_eq in Hlm_hdr0_s; rewrite <- Hot_eq in Hlm_hdr0_t.
  assert (Hmap_dvs :
    List.map fst dvs_s = List.map fst hspecs_s /\
    List.map fst dvs_t = List.map fst hspecs_t).
  { rewrite Hms_eq, Hmt_eq; clear -Hrel.
    induction Hrel; cbn.
    - split; reflexivity.
    - destruct IHHrel as [Hs Ht]; split; f_equal; assumption. }
  destruct Hmap_dvs as [Hmap_dvs_s Hmap_dvs_t].
  pose proof (extend_penv_wf_param_union allowed pspecs dvs_s dvs_t penv
                Hpenv0 Hrel Hnd_cut Hall_not_cut) as Hpenv_cut;
    fold bs penv_cut in Hpenv_cut; rewrite <- Hcut_eq in Hpenv_cut.
  destruct (Hstep_hdr_s Pa None penv_cut bid_prev_s env_prev_s dvs_s Hmap_dvs_s Hphis_s Hlm_hdr0_s)
    as [[Hub_hs _] | (cbit_s & Hret_hdr_s & Hev_cond_s & Hcont_s & Hexit_s)].
  - eapply paco2_mon;
      [exact (cfg_steps_ub_det_ref dvalue_refines sigma_tgt _ _ _ (Hub_hs sigma_tgt))
      | intros ? ? []].
  - assert (Hdisj_bs : forall x, In x src_pnames -> ~ In x (List.map fst bs))
      by (rewrite Hbs_fst; exact Hdisj_sp_cut).
    pose proof (filter_param_ub_ctx_holds src_pnames ctx_ent bs penv dummy_freeze_oracle
                  Hdisj_bs Hctx_ent) as Hbase_ctx;
      fold penv_cut base_loop_ctx in Hbase_ctx.
    assert (Hbr_hdr_s : forall c, In c [nls_ce_cond s_s] ->
      exists cbit : @Integers.bit_int 1,
        eval_closed_cert_expr penv_cut dummy_freeze_oracle c =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1 cbit))).
    { intros c [<- | []]; exists cbit_s; exact Hev_cond_s. }
    pose proof (fold_ub_assumptions_sound _ cut_allowed (nls_evals_hdr s_s) [nls_ce_cond s_s]
                  base_loop_ctx ctx_hdr penv_cut dummy_freeze_oracle Hpenv_cut
                  (forall_wf_pure_in _ _ Hfa_hdr_s)
                  (forall_ret_in _ _ _ Hret_hdr_s)
                  Hbr_hdr_s Hbase_ctx Ef_hdr) as Hctx_hdr.
    destruct (eff_loop_cond_typing cut_allowed (nls_latch_on_true s_s) (nls_ce_cond s_s)
                Hwf_cond_s Hbw_cond_s) as [(_ & _ & Hfv_eff_s) _].
    destruct (eff_loop_cond_typing cut_allowed (nls_latch_on_true s_t) (nls_ce_cond s_t)
                Hwf_cond_t Hbw_cond_t) as [(_ & _ & Hfv_eff_t) _].
    fold eff_s in Hfv_eff_s; fold eff_t in Hfv_eff_t.
    destruct (eval_eff_loop_cond penv_cut (nls_latch_on_true s_s) (nls_ce_cond s_s)
                cbit_s Hev_cond_s) as [ebit_s [Hev_eff_s Eebit_s]]; fold eff_s in Hev_eff_s.
    pose proof (check_expr_refines_with_lrat_sound ctx_hdr eff_s eff_t opt_pf
                  penv_cut dummy_freeze_oracle Href_eff
                  (fun n w0 H => Hpenv_cut n w0 (Hfv_eff_s (n, w0) H))
                  (fun n w0 H => Hpenv_cut n w0 (Hfv_eff_t (n, w0) H))
                  Hctx_hdr) as Href_eff_ev.
    rewrite Hev_eff_s in Href_eff_ev.
    destruct (Hstep_hdr_t Pa None penv_cut bid_prev_t env_prev_t dvs_t Hmap_dvs_t Hphis_t Hlm_hdr0_t)
      as [[_ [(ce_ht & msg_ht & Hin_ht & Hev_ht) | Hev_ct_ps]]
         | (cbit_t & _ & Hev_cond_t & Hcont_t & Hexit_t)].
    + exfalso; exact (exprs_safe_under_src_sound (nls_ce_cond s_t :: nls_evals_hdr s_t)
                        cut_allowed ctx_hdr (nls_evals_hdr s_s) penv_cut Hpenv_cut Hctx_hdr
                        (forall_ret_in _ _ _ Hret_hdr_s)
                        (Forall_cons _ Hwf_cond_t Hfa_hdr_t) Hsafe_hdr_t
                        ce_ht msg_ht Hin_ht Hev_ht).
    + exfalso.
      pose proof (eff_loop_cond_poison penv_cut (nls_latch_on_true s_t) (nls_ce_cond s_t) Hev_ct_ps)
        as Hev_eff_t_ps; fold eff_t in Hev_eff_t_ps.
      rewrite Hev_eff_t_ps in Href_eff_ev; cbn [refine_eou_dvalue] in Href_eff_ev.
      destruct Href_eff_ev as [Habs | Habs]; discriminate Habs.
    + destruct (eval_eff_loop_cond penv_cut (nls_latch_on_true s_t) (nls_ce_cond s_t)
                  cbit_t Hev_cond_t) as [ebit_t [Hev_eff_t Eebit_t]]; fold eff_t in Hev_eff_t.
      rewrite Hev_eff_t in Href_eff_ev; cbn [refine_eou_dvalue] in Href_eff_ev.
      assert (Heb_eq : ebit_s = ebit_t).
      { destruct Href_eff_ev as [Habs | Heq_dv]; [discriminate Habs |].
        exact (eq_sym (dvalue_base_I_same_sz_inj 1 ebit_t ebit_s Heq_dv)). }
      subst ebit_t.
      assert (Epol_eq :
        Bool.eqb (@Integers.unsigned 1 cbit_t =? 1)%Z (nls_latch_on_true s_t) =
        Bool.eqb (@Integers.unsigned 1 cbit_s =? 1)%Z (nls_latch_on_true s_s))
        by congruence.
      destruct Hwf_cond_s as (Hwt_cs & Hlf_cs & _).
      case_eq (Bool.eqb (@Integers.unsigned 1 cbit_s =? 1)%Z (nls_latch_on_true s_s));
        intro Econt.
      * (* Loop continues *)
        pose proof (bool_eqb_swap_inv _ _ true Econt) as Ecbit_cont.
        replace (Bool.eqb true (nls_latch_on_true s_s)) with (nls_latch_on_true s_s) in Ecbit_cont
          by (destruct (nls_latch_on_true s_s); reflexivity).
        pose proof (extract_branch_cond_assumptions_sound penv_cut dummy_freeze_oracle
                      (nls_latch_on_true s_s) (nls_ce_cond s_s) cbit_s ctx_hdr
                      Hwt_cs Hlf_cs Hev_cond_s Ecbit_cont Hctx_hdr) as Hctx_cont0;
          fold ctx_cont_0 in Hctx_cont0.
        destruct (check_loop_cutpoint_continue_step cut_allowed opt_pf pspecs src_cfg tgt_cfg
                    s_s s_t b_ent_s b_ent_t b_hdr_s b_hdr_t ctx_cont_0 ctx_cont latch_uas
                    penv_cut bid_prev_s bid_prev_t env_prev_s env_prev_t cbit_s cbit_t
                    Hpenv_cut Hctx_cont0 Hbr_hdr_s Hfa_hdr_s Hfa_body_s Hfa_next_s Hfa_next_t
                    Hfa_body_t Hret_hdr_s Epol_eq Econt Ef_cont Hsafe_body_t Hsafe_next_t
                    Href_next Hr_next_s Hr_next_t Hf_hdr_s Hcont_s Hcont_t)
          as [Hub_cont
             | (env_latch_s & env_latch_t & dvs_next_s & dvs_next_t &
                Hpres_ls & Hpres_lt & Htau_s & Htau_t & Hst_np_s & Hst_np_t & Hrel_next)].
        -- eapply paco2_mon;
             [exact (cfg_steps_ub_det_ref dvalue_refines sigma_tgt _ _ _ (Hub_cont sigma_tgt))
             | intros ? ? []].
        -- pstep; eapply pure_cfg_steps_to_tau_sync; [exact Htau_s | exact Htau_t | right].
           exact (CIH (nls_bid_latch_from s_s) (nls_bid_latch_from s_t)
                      env_latch_s env_latch_t dvs_next_s dvs_next_t
                      (fun r0 Hr0 => eq_trans (Hpres_ls r0 Hr0) (Hag_s r0 Hr0))
                      (fun r0 Hr0 => eq_trans (Hpres_lt r0 Hr0) (Hag_t r0 Hr0))
                      Hst_np_s Hst_np_t Hrel_next).
      * (* Loop exits *)
        pose proof (bool_eqb_swap_inv _ _ false Econt) as Ecbit_exit.
        replace (Bool.eqb false (nls_latch_on_true s_s)) with (negb (nls_latch_on_true s_s)) in Ecbit_exit
          by (destruct (nls_latch_on_true s_s); reflexivity).
        pose proof (extract_branch_cond_assumptions_sound penv_cut dummy_freeze_oracle
                      (negb (nls_latch_on_true s_s)) (nls_ce_cond s_s) cbit_s ctx_hdr
                      Hwt_cs Hlf_cs Hev_cond_s Ecbit_exit Hctx_hdr) as Hctx_exit0;
          fold ctx_exit_0 in Hctx_exit0.
        eapply paco2_mon;
          [exact (check_loop_cutpoint_exit_step cut_allowed opt_pf src_cfg tgt_cfg
                    s_s s_t ctx_exit_0 ctx_exit b_exit_uas sigma_tgt penv_cut
                    bid_prev_s bid_prev_t env_prev_s env_prev_t cbit_s cbit_t
                    Hpenv_cut Hctx_exit0 Hbr_hdr_s Hfa_hdr_s Hfa_exit_s Hfa_exit_t
                    Hwf_ret_s Hwf_ret_t Hret_hdr_s Epol_eq Econt Ef_exit
                    Hsafe_exit_t Href_ret Hexit_s Hexit_t)
          | intros ? ? []].
Qed.

Lemma check_loop_cutpoint_cfg_open_sound {Pa : Params} :

  forall allowed init_ctx (src_cfg tgt_cfg : CFG.cfg dtyp)
         cert lci opt_pf arg_dtys (vs : list (@dvalue Pa)),
    NoDup (args src_cfg) ->
    NoDup (args tgt_cfg) ->
    NoDup (List.map cert_reg_name (args src_cfg)) ->
    List.length (args src_cfg) = List.length (args tgt_cfg) ->
    List.length arg_dtys = List.length (args src_cfg) ->
    cfg_param_dtyp_compatible src_cfg arg_dtys = true ->
    cfg_param_dtyp_compatible tgt_cfg arg_dtys = true ->
    Forall2 dvalue_has_dtyp vs arg_dtys ->
    (forall idx w0 pnm,
       In (idx, DTYPE_Base (DTYPE_I w0)) (param_idx_uses_cfg src_cfg) ->
       nth_error (List.map cert_reg_name (args src_cfg)) idx = Some pnm ->
       In (pnm, w0) allowed) ->
    (forall idx w0 pnm,
       In (idx, DTYPE_Base (DTYPE_I w0)) (param_idx_uses_cfg tgt_cfg) ->
       nth_error (List.map cert_reg_name (args src_cfg)) idx = Some pnm ->
       In (pnm, w0) allowed) ->
    wf_param_env_for allowed (build_param_env (List.map cert_reg_name (args src_cfg)) vs) ->
    ub_ctx_holds (build_param_env (List.map cert_reg_name (args src_cfg)) vs)
      dummy_freeze_oracle init_ctx ->
    check_loop_cutpoint_cfg allowed init_ctx src_cfg tgt_cfg cert lci opt_pf = true ->
    ow_itree_refines dvalue_refines
      (eval_cfg_open src_cfg vs)
      (eval_cfg_open tgt_cfg vs).
Proof.
  intros allowed init_ctx src_cfg tgt_cfg cert lci opt_pf arg_dtys vs
         Hnd_sa Hnd_ta Hnd_sp Hlen_st Hlen_da Hcomp_s Hcomp_t Hvs
         Hpu_s Hpu_t Hpenv0 Hinit_ctx Hchk.
  unfold check_loop_cutpoint_cfg in Hchk; cbn zeta in Hchk.
  set (src_pnames := List.map cert_reg_name (args src_cfg)) in *.
  set (src_uses := param_idx_uses_cfg src_cfg) in *.
  set (tgt_uses := param_idx_uses_cfg tgt_cfg) in *.
  set (lmap0_s := init_param_lmap (args src_cfg) src_pnames src_uses) in *.
  set (lmap0_t := init_param_lmap (args tgt_cfg) src_pnames tgt_uses) in *.
  apply andb_true_iff in Hchk as [Hall_in Hchk].
  destruct (reify_natural_loop src_cfg (lci_src_header lci) lmap0_s (overlay_hspecs_s 0%nat))
    as [[hspecs_s s_s] |] eqn:Er_s; [| discriminate Hchk].
  destruct (reify_natural_loop tgt_cfg (lci_tgt_header lci) lmap0_t (overlay_hspecs_t 0%nat))
    as [[hspecs_t s_t] |] eqn:Er_t; [| discriminate Hchk].
  destruct (pair_phi_specs hspecs_s hspecs_t) as [pspecs |] eqn:Epair; [| discriminate Hchk].
  set (cut_allowed := allowed ++ cut_vars_from 0%nat pspecs) in *.
  apply andb_true_iff in Hchk as [Hnd_all Hchk].
  apply no_dup_strings_spec in Hnd_all.
  pose proof (NoDup_app_r _ _ Hnd_all) as Hnd_cut.
  assert (Hdisj_sp_cut : forall x, In x src_pnames -> ~ In x (cut_names_from 0%nat pspecs))
    by (intros x Hx; exact (NoDup_app_disj _ _ x Hnd_all Hx)).
  assert (Hall_not_cut : forall nm w, In (nm, w) allowed -> ~ In nm (cut_names_from 0%nat pspecs)).
  { intros nm w Hin; rewrite forallb_forall in Hall_in.
    pose proof (Hall_in (nm, w) Hin) as Hsin; cbn in Hsin.
    apply string_in_list_spec in Hsin; exact (Hdisj_sp_cut nm Hsin). }
  destruct (fold_ub_assumptions allowed (nls_evals_entry s_s) [] init_ctx
              (block_uas_for (init src_cfg) (pc_blocks cert) (init src_cfg))) as [ctx_ent |] eqn:Ef_ent;
    [| discriminate Hchk].
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as (((Hsafe_ent_t & Hsafe_init_t) & Href_init) & Hchk).
  set (base_loop_ctx := filter_param_ub_ctx src_pnames ctx_ent) in *.
  destruct (fold_ub_assumptions cut_allowed (nls_evals_hdr s_s) [nls_ce_cond s_s]
              base_loop_ctx (block_uas_for (init src_cfg) (pc_blocks cert) (nls_bid_hdr s_s)))
    as [ctx_hdr |] eqn:Ef_hdr; [| discriminate Hchk].
  set (eff_s := eff_loop_cond (nls_latch_on_true s_s) (nls_ce_cond s_s)) in *.
  set (eff_t := eff_loop_cond (nls_latch_on_true s_t) (nls_ce_cond s_t)) in *.
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as ((Hsafe_hdr_t & Href_eff) & Hchk).
  set (ctx_cont_0 := extract_branch_cond_assumptions (nls_latch_on_true s_s) (nls_ce_cond s_s) ++ ctx_hdr) in *.
  set (latch_uas := if raw_id_eqb (nls_bid_latch_entry s_s) (nls_bid_hdr s_s) then []
                    else block_uas_for (init src_cfg) (pc_blocks cert) (nls_bid_latch_entry s_s)) in *.
  destruct (fold_ub_assumptions cut_allowed (nls_evals_hdr s_s ++ nls_evals_body s_s)
              [nls_ce_cond s_s] ctx_cont_0 latch_uas) as [ctx_cont |] eqn:Ef_cont;
    [| discriminate Hchk].
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as (((Hsafe_body_t & Hsafe_next_t) & Href_next) & Hchk).
  set (ctx_exit_0 := extract_branch_cond_assumptions (negb (nls_latch_on_true s_s)) (nls_ce_cond s_s) ++ ctx_hdr) in *.
  destruct (fold_ub_assumptions cut_allowed (nls_evals_hdr s_s ++ nls_evals_exit s_s)
              [nls_ce_cond s_s] ctx_exit_0 (block_uas_for (init src_cfg) (pc_blocks cert) (nls_bid_exit s_s)))
    as [ctx_exit |] eqn:Ef_exit; [| discriminate Hchk].
  destruct (pc_return_obligation cert) as [| w_ro ? ? ?]; [discriminate Hchk |].
  rewrite !andb_true_iff in Hchk.
  destruct Hchk as (((Hws_ro & Hwt_ro) & Hsafe_exit_t) & Href_ret).
  apply Pos.eqb_eq in Hws_ro; apply Pos.eqb_eq in Hwt_ro.
  pose proof (pair_phi_specs_supported _ _ _ Epair) as Hsup_ps.
  assert (Hinc_cut_vars : incl (cut_vars_from 0%nat pspecs) cut_allowed)
    by (intros u Hu; apply in_app_iff; right; exact Hu).
  assert (Hinc_all_cut : incl allowed cut_allowed)
    by (intros u Hu; apply in_app_iff; left; exact Hu).
  assert (Hwrap_s : forall lmap, wf_pure_lmap allowed lmap ->
    wf_pure_lmap cut_allowed (overlay_hspecs_s 0%nat lmap hspecs_s)).
  { intros lmap Hl; destruct (pair_phi_specs_overlay _ _ _ 0%nat lmap lmap Epair) as (Hos & _).
    rewrite Hos; pose proof (wf_pure_lmap_mono _ _ lmap Hinc_all_cut Hl) as Hlc.
    exact (proj1 (overlay_cut_lmap_typing pspecs 0%nat cut_allowed lmap lmap Hsup_ps Hinc_cut_vars Hlc Hlc)). }
  assert (Hwrap_t : forall lmap, wf_pure_lmap allowed lmap ->
    wf_pure_lmap cut_allowed (overlay_hspecs_t 0%nat lmap hspecs_t)).
  { intros lmap Hl; destruct (pair_phi_specs_overlay _ _ _ 0%nat lmap lmap Epair) as (_ & Hot & _).
    rewrite Hot; pose proof (wf_pure_lmap_mono _ _ lmap Hinc_all_cut Hl) as Hlc.
    exact (proj2 (overlay_cut_lmap_typing pspecs 0%nat cut_allowed lmap lmap Hsup_ps Hinc_cut_vars Hlc Hlc)). }
  destruct (reify_natural_loop_spec src_cfg (lci_src_header lci) allowed cut_allowed
              lmap0_s (overlay_hspecs_s 0%nat) hspecs_s s_s
              (init_param_lmap_typing src_uses (args src_cfg) src_pnames allowed Hpu_s)
              (init_param_lmap_dom src_uses (args src_cfg) src_pnames)
              Hwrap_s Er_s)
    as (b_ent_s & b_hdr_s & Hf_ent_s & Hf_hdr_s & _ & Hr_init_s & Hr_next_s &
        Hlmap_ent_s & Hdom_ent_s & Hfa_ent_s & Hfa_init_s & Hfa_hdr_s &
        Hwf_cond_s & Hbw_cond_s & Hfa_body_s & Hfa_next_s & Hfa_exit_s &
        Hwf_ret_s & Hbw_ret_s & _ & Hstep_ent_s & Hstep_hdr_s).
  destruct (reify_natural_loop_spec tgt_cfg (lci_tgt_header lci) allowed cut_allowed
              lmap0_t (overlay_hspecs_t 0%nat) hspecs_t s_t
              (init_param_lmap_typing tgt_uses (args tgt_cfg) src_pnames allowed Hpu_t)
              (init_param_lmap_dom tgt_uses (args tgt_cfg) src_pnames)
              Hwrap_t Er_t)
    as (b_ent_t & b_hdr_t & Hf_ent_t & Hf_hdr_t & _ & Hr_init_t & Hr_next_t &
        Hlmap_ent_t & Hdom_ent_t & Hfa_ent_t & Hfa_init_t & Hfa_hdr_t &
        Hwf_cond_t & Hbw_cond_t & Hfa_body_t & Hfa_next_t & Hfa_exit_t &
        Hwf_ret_t & Hbw_ret_t & _ & Hstep_ent_t & Hstep_hdr_t).
  intros sigma_tgt Hwfsig_t.
  exists sigma_tgt; split; [exact Hwfsig_t |].
  set (penv := build_param_env src_pnames vs) in *.
  set (bmap_s := ocfg_map (blks src_cfg)) in *.
  set (bmap_t := ocfg_map (blks tgt_cfg)) in *.
  pose proof (List.Forall2_length Hvs) as Hlen_vs.
  assert (Hlen_sp : List.length src_pnames = List.length (args src_cfg))
    by (unfold src_pnames; apply List.length_map).
  assert (Hlp_s : List.length (args src_cfg) = List.length vs) by lia.
  assert (Hlp_t : List.length (args tgt_cfg) = List.length vs) by lia.
  assert (Hls_v : List.length src_pnames = List.length vs) by lia.
  pose proof (init_param_lmap_matches src_uses (args src_cfg) src_pnames arg_dtys vs
                Hnd_sa Hnd_sp Hlp_s Hls_v Hvs
                (fun idx dt => cfg_param_dtyp_compatible_nth src_cfg arg_dtys idx dt Hcomp_s)) as Henv0_s.
  pose proof (init_param_lmap_matches tgt_uses (args tgt_cfg) src_pnames arg_dtys vs
                Hnd_ta Hnd_sp Hlp_t Hls_v Hvs
                (fun idx dt => cfg_param_dtyp_compatible_nth tgt_cfg arg_dtys idx dt Hcomp_t)) as Henv0_t.
  fold penv lmap0_s in Henv0_s; fold penv lmap0_t in Henv0_t.
  unfold eval_cfg_open.
  change (denote_cfg src_cfg None) with (denote_cfg_from bmap_s None (init src_cfg, init src_cfg)).
  change (denote_cfg tgt_cfg None) with (denote_cfg_from bmap_t None (init tgt_cfg, init tgt_cfg)).
  destruct (Hstep_ent_s Pa None penv (init_cfg_locals (args src_cfg) vs) Henv0_s)
    as [[Hub_ent_s _] | (env_entry_s & Henv_ent_s & Hret_ent_s & Htau_ent_s)].
  - exact (cfg_steps_ub_det_ref dvalue_refines sigma_tgt
             (init_cfg_locals (args src_cfg) vs)
             (denote_cfg_from bmap_s None (init src_cfg, init src_cfg))
             _ (Hub_ent_s sigma_tgt)).
  - pose proof (fold_ub_assumptions_sound _ allowed (nls_evals_entry s_s) [] init_ctx ctx_ent
                  penv dummy_freeze_oracle Hpenv0
                  (forall_wf_pure_in _ _ Hfa_ent_s)
                  (forall_ret_in _ _ _ Hret_ent_s)
                  (fun _ H => False_ind _ H)
                  Hinit_ctx Ef_ent) as Hctx_ent.
    destruct (Hstep_ent_t Pa None penv (init_cfg_locals (args tgt_cfg) vs) Henv0_t)
      as [[_ (ce_et & msg_et & Hin_et & Hev_et)] | (env_entry_t & Henv_ent_t & _ & Htau_ent_t)].
    + exfalso; exact (exprs_safe_under_src_sound (nls_evals_entry s_t) allowed ctx_ent
                        (nls_evals_entry s_s) penv Hpenv0 Hctx_ent
                        (forall_ret_in _ _ _ Hret_ent_s) Hfa_ent_t Hsafe_ent_t
                        ce_et msg_et Hin_et Hev_et).
    + destruct (pure_phis_denote_step (blk_phis b_hdr_s) penv (init src_cfg)
                  (nls_lmap_entry s_s) env_entry_s (nls_init_pevals s_s) Henv_ent_s Hr_init_s)
        as [[Hub_ip_s _] | [dvs0_s [Hpm0_s Hst_ip_s]]].
      * assert (Hub_from_ent : cfg_steps_to_ub sigma_tgt (init_cfg_locals (args src_cfg) vs)
                  (denote_cfg_from bmap_s None (init src_cfg, init src_cfg))).
        { eapply pure_cfg_steps_to_tau_then_ub; [exact Htau_ent_s |].
          eapply denote_cfg_from_block_ub; [exact Hf_hdr_s |].
          unfold denote_block; apply cfg_steps_to_ub_bind_l; exact (Hub_ip_s sigma_tgt). }
        exact (cfg_steps_ub_det_ref dvalue_refines sigma_tgt _ _ _ Hub_from_ent).
      * pose proof (Forall_app (wf_pure_eval_entry allowed)
                    (nls_evals_entry s_s) (peval_exprs (nls_init_pevals s_s))) as Hfa_app_ip.
        assert (Hret_ent_ip_s :
          Forall (fun ce => exists dv, eval_closed_cert_expr penv dummy_freeze_oracle ce = raise_ret dv)
            (nls_evals_entry s_s ++ peval_exprs (nls_init_pevals s_s)))
          by (apply Forall_app; split; [exact Hret_ent_s | exact (peval_exprs_ret penv _ _ Hpm0_s)]).
        destruct (pure_phis_denote_step (blk_phis b_hdr_t) penv (init tgt_cfg)
                    (nls_lmap_entry s_t) env_entry_t (nls_init_pevals s_t) Henv_ent_t Hr_init_t)
          as [[_ (ce_ipt & msg_ipt & Hin_ipt & Hev_ipt)] | [dvs0_t [Hpm0_t Hst_ip_t]]].
        -- exfalso; exact (exprs_safe_under_src_sound (peval_exprs (nls_init_pevals s_t)) allowed ctx_ent
                             (nls_evals_entry s_s ++ peval_exprs (nls_init_pevals s_s)) penv Hpenv0 Hctx_ent
                             (forall_ret_in _ _ _ Hret_ent_ip_s)
                             (peval_exprs_typing _ _ Hfa_init_t) Hsafe_init_t
                             ce_ipt msg_ipt Hin_ipt Hev_ipt).
        -- destruct (check_pevals_refine_sound pspecs (nls_init_pevals s_s) (nls_init_pevals s_t)
                       dvs0_s dvs0_t allowed ctx_ent opt_pf penv Hpenv0 Hctx_ent
                       Hfa_init_s Hfa_init_t Hpm0_s Hpm0_t Href_init)
             as (Hrel0 & _ & _).
           pstep; eapply pure_cfg_steps_to_tau_sync; [exact Htau_ent_s | exact Htau_ent_t | left].
           exact (check_loop_cutpoint_cfg_loop_bisim allowed cut_allowed opt_pf pspecs
                    src_cfg tgt_cfg (lci_src_header lci) (lci_tgt_header lci)
                    hspecs_s hspecs_t s_s s_t b_ent_s b_ent_t b_hdr_s b_hdr_t
                    ctx_ent ctx_hdr ctx_cont ctx_exit src_pnames
                    (block_uas_for (init src_cfg) (pc_blocks cert) (nls_bid_hdr s_s))
                    latch_uas
                    (block_uas_for (init src_cfg) (pc_blocks cert) (nls_bid_exit s_s))
                    sigma_tgt penv env_entry_s env_entry_t
                    eq_refl Hnd_cut Hdisj_sp_cut Hall_not_cut Epair Hpenv0 Hctx_ent
                    Ef_hdr Ef_cont Ef_exit Hsafe_hdr_t Href_eff Hsafe_body_t Hsafe_next_t
                    Href_next Hsafe_exit_t Href_ret Hpu_s Hpu_t Hwrap_s Hwrap_t Er_s Er_t
                    Hf_ent_s Hf_ent_t Hf_hdr_s Hf_hdr_t Henv_ent_s Henv_ent_t
                    (init src_cfg) (init tgt_cfg) env_entry_s env_entry_t dvs0_s dvs0_t
                    (fun _ _ => eq_refl) (fun _ _ => eq_refl) Hst_ip_s Hst_ip_t Hrel0).
Qed.

