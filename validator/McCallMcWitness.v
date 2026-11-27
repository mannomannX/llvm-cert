(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Machine-Code Call Execution Witnesses ([CertValidator.McCallMcWitness])

    Implements Sections 5.1-5.3 of Milestone M3c of Phase 8.3a: call-variable
    disjointness, incremental context invariance, and [RV64IM+RVC] / [AArch64]
    machine-code call-tree execution witnesses on top of
    [CertValidator.McCallSpec]. *)

From Stdlib Require Import
  ZArith
  NArith
  PArith
  Strings.Ascii
  Strings.String
  Numbers.DecimalString
  Numbers.DecimalZ
  List
  Bool
  Lia.
Import ListNotations.

From ITree Require Import
  ITree
  ITreeFacts
  Events.Exception.

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
  Syntax.DynamicTypes
  Syntax.TypToDtyp
  Syntax.RawIdMaps
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.Attributes
  Semantics.Denotation
  Semantics.LLVMEvents
  Semantics.IntrinsicsDefinitions.

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
  Diag
  McOblDischarger
  McCallSpec.

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

Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.


(** *** 5.1 Call Variable Disjointness & Incremental Context Invariance *)

Lemma string_append_eq_prefix : forall p s1 s2,
  (p ++ s1 = p ++ s2 -> s1 = s2)%string.
Proof.
  induction p as [| c rp IH]; intros s1 s2 H; cbn in H; [exact H |].
  inversion H; apply IH; assumption.
Qed.

Lemma mc_call_hi_var_inj : forall k1 k2,
  mc_call_hi_var k1 = mc_call_hi_var k2 -> k1 = k2.
Proof.
  intros k1 k2 Heq; unfold mc_call_hi_var in Heq.
  apply string_append_eq_prefix in Heq.
  apply show_Z_dec_pos_inj in Heq; lia.
Qed.

Lemma decimal_uint_no_underscore : forall d,
  ~ In "_"%char (list_ascii_of_string (DecimalString.NilEmpty.string_of_uint d)).
Proof.
  induction d; cbn [DecimalString.NilEmpty.string_of_uint list_ascii_of_string In];
    intro H; try exact H; (destruct H as [Hc | Hr]; [discriminate Hc | exact (IHd Hr)]).
Qed.

Lemma show_Z_dec_pos_no_underscore : forall n : Z,
  (0 <= n)%Z ->
  ~ In "_"%char (list_ascii_of_string (show_Z_dec n)).
Proof.
  intros n Hn Hin; unfold show_Z_dec in Hin.
  destruct n as [| p | p]; [| | lia]; cbn in Hin.
  - destruct Hin as [H | H]; [discriminate H | contradiction H].
  - exact (decimal_uint_no_underscore (Pos.to_uint p) Hin).
Qed.

Fixpoint take_before_underscore (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => if Ascii.eqb c "_"%char then EmptyString else String c (take_before_underscore rest)
  end.

Lemma take_before_underscore_app : forall a b,
  ~ In "_"%char (list_ascii_of_string a) ->
  take_before_underscore (a ++ "_" ++ b)%string = a.
Proof.
  induction a as [| c ra IH]; intros b Hnin.
  - cbn; reflexivity.
  - change ((String c ra ++ "_" ++ b)%string) with (String c (ra ++ "_" ++ b)%string).
    cbn [take_before_underscore]; destruct (Ascii.eqb c "_"%char) eqn:Ec.
    + apply Ascii.eqb_eq in Ec; subst c; exfalso; apply Hnin; left; reflexivity.
    + f_equal; apply IH; intro H; apply Hnin; right; exact H.
Qed.

Lemma mc_call_ret_var_k_inj : forall k1 k2 w1 w2,
  mc_call_ret_var k1 w1 = mc_call_ret_var k2 w2 -> k1 = k2.
Proof.
  intros k1 k2 w1 w2 Heq; unfold mc_call_ret_var in Heq.
  apply string_append_eq_prefix in Heq.
  apply (f_equal take_before_underscore) in Heq.
  rewrite !take_before_underscore_app in Heq
    by (apply show_Z_dec_pos_no_underscore; lia).
  apply show_Z_dec_pos_inj in Heq; lia.
Qed.

Lemma mc_call_ret_hi_disjoint : forall k1 w1 k2,
  mc_call_ret_var k1 w1 <> mc_call_hi_var k2.
Proof.
  intros k1 w1 k2 Heq; unfold mc_call_ret_var, mc_call_hi_var in Heq.
  change ("!call_hi_" ++ show_Z_dec (Z.of_nat k2))%string
    with ("!call_" ++ ("hi_" ++ show_Z_dec (Z.of_nat k2)))%string in Heq.
  apply string_append_eq_prefix in Heq.
  unfold show_Z_dec in Heq; destruct (Z.of_nat k1) as [| p1 |] eqn:Ez; try lia.
  - cbn in Heq; discriminate Heq.
  - cbn in Heq; destruct (Pos.to_uint p1); cbn in Heq; discriminate Heq.
Qed.

(** An environment invariant indexed by [cid]: all [!call_*] and [!call_hi_*]
    variables appearing inside expressions valid at step [cid] are not overwritten
    by binding calls at [cid' >= cid]. *)

Definition allowed_ge_cid_fresh (cid : nat) (allowed : list (string * positive)) : Prop :=
  (forall k w, In (mc_call_ret_var k w, w) allowed -> (k < cid)%nat) /\
  (forall k w, In (mc_call_ret_var k w, w) allowed -> False -> False) /\
  (forall nm w, In (nm, w) allowed ->
     forall k' w', (cid <= k')%nat -> nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k').

Lemma allowed0_fresh_all : forall (allowed0 : list (string * positive)),
  (forall nm w, In (nm, w) allowed0 -> mc_starts_with_bang nm = false) ->
  forall cid nm w, In (nm, w) allowed0 ->
    forall k' w', (cid <= k')%nat -> nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k'.
Proof.
  intros allowed0 Hnb cid nm w Hin k' w' _.
  pose proof (Hnb nm w Hin) as Hf; split; intro Heq; subst nm; discriminate Hf.
Qed.

(** *** 5.2 Concrete Path Execution Witnesses for RV64 & AArch64 *)

Lemma rv_sym_read_call_args_from_sound {Pa : Params} :
  forall pc cname (penv : param_env Pa) foracle rf0 sp0 vrf rf idx n aes,
    rv_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    rv_sym_read_call_args_from pc cname idx n vrf = inr aes ->
    Forall2 (fun e64 v64 =>
      eval_closed_cert_expr penv foracle e64 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)))
      aes
      (List.map (fun k => rv_read_reg (idx + N.of_nat k) rf) (seq 0 n)).
Proof.
  intros pc cname penv foracle rf0 sp0 vrf rf idx n; revert idx;
    induction n as [| n' IH]; intros idx aes Hag Hrd;
    cbn [rv_sym_read_call_args_from seq List.map] in *;
    [inversion Hrd; constructor |].
  destruct (rv_val_read idx vrf) as [| e64 | |] eqn:Er; try discriminate Hrd.
  destruct (rv_sym_read_call_args_from pc cname (N.succ idx) n' vrf) as [| rest] eqn:Hr; [discriminate Hrd |].
  inversion Hrd; subst aes; clear Hrd.
  constructor.
  - pose proof (Hag idx) as Hi; rewrite Er in Hi; cbn [mc_sym_val_agrees] in Hi.
    rewrite N.add_0_r; exact Hi.
  - rewrite <- seq_shift, !map_map.
    replace (List.map (fun x => rv_read_reg (idx + N.of_nat (S x)) rf) (seq 0 n'))
      with (List.map (fun k => rv_read_reg (N.succ idx + N.of_nat k) rf) (seq 0 n'))
      by (apply map_ext; intro k; f_equal; lia).
    exact (IH (N.succ idx) rest Hag Hr).
Qed.

Lemma a64_sym_read_call_args_from_sound {Pa : Params} :
  forall pc cname (penv : param_env Pa) foracle rf0 sp0 vrf rf idx n aes,
    a64_val_regs_agrees penv foracle rf0 sp0 vrf rf ->
    a64_sym_read_call_args_from pc cname idx n vrf = inr aes ->
    Forall2 (fun e64 v64 =>
      eval_closed_cert_expr penv foracle e64 =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)))
      aes
      (List.map (fun k => a64_read_reg (idx + N.of_nat k) rf) (seq 0 n)).
Proof.
  intros pc cname penv foracle rf0 sp0 vrf rf idx n; revert idx;
    induction n as [| n' IH]; intros idx aes Hag Hrd;
    cbn [a64_sym_read_call_args_from seq List.map] in *;
    [inversion Hrd; constructor |].
  destruct (a64_val_read idx vrf) as [| e64 | |] eqn:Er; try discriminate Hrd.
  destruct (a64_sym_read_call_args_from pc cname (N.succ idx) n' vrf) as [| rest] eqn:Hr; [discriminate Hrd |].
  inversion Hrd; subst aes; clear Hrd.
  constructor.
  - pose proof (Hag idx) as Hi; rewrite Er in Hi; cbn [mc_sym_val_agrees] in Hi.
    rewrite N.add_0_r; exact Hi.
  - rewrite <- seq_shift, !map_map.
    replace (List.map (fun x => a64_read_reg (idx + N.of_nat (S x)) rf) (seq 0 n'))
      with (List.map (fun k => a64_read_reg (N.succ idx + N.of_nat k) rf) (seq 0 n'))
      by (apply map_ext; intro k; f_equal; lia).
    exact (IH (N.succ idx) rest Hag Hr).
Qed.

Lemma eval_let_binds_ext {Pa : Params}
  (f1 f2 : let_val_env Pa -> cert_expr -> EOU (@dvalue Pa))
  (xs : list (string * cert_expr)) :
  Forall (fun p => forall lenv, f1 lenv (snd p) = f2 lenv (snd p)) xs ->
  forall lenv,
    eval_let_binds f1 lenv xs = eval_let_binds f2 lenv xs.
Proof.
  intros Hfa; induction Hfa as [| [nm be] rest Hhead _ IH]; intros lenv; cbn in *; [reflexivity |].
  rewrite Hhead; destruct (f2 lenv be); cbn; try reflexivity; apply IH.
Qed.

Lemma eval_cert_expr_extensional {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) foracle e lenv,
    (forall nm, penv1 nm = penv2 nm) ->
    eval_cert_expr penv1 lenv foracle e = eval_cert_expr penv2 lenv foracle e.
Proof.
  intros penv1 penv2 foracle e lenv Heq; revert lenv.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o IHo
    | bs body IHbs IHb ] using cert_expr_ind_nested;
    intro lenv; cbn [eval_cert_expr]; try reflexivity.
  - destruct (lookup_let_val lenv nm); [reflexivity | rewrite Heq; reflexivity].
  - rewrite IHl, IHr; reflexivity.
  - rewrite IHl, IHr; reflexivity.
  - rewrite IHo; reflexivity.
  - rewrite IHc, IHt, IHf; reflexivity.
  - rewrite IHo; reflexivity.
  - rewrite (@eval_let_binds_ext Pa
               (fun ce x => eval_cert_expr penv1 ce foracle x)
               (fun ce x => eval_cert_expr penv2 ce foracle x) bs IHbs lenv).
    destruct (eval_let_binds (fun ce x => eval_cert_expr penv2 ce foracle x) lenv bs);
      cbn; [| | | apply IHb]; reflexivity.
Qed.

Lemma mc_tree_path_ok_extensional {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) ret_w path t tr v,
    (forall nm, penv1 nm = penv2 nm) ->
    mc_tree_path_ok penv1 ret_w path t tr v ->
    mc_tree_path_ok penv2 ret_w path t tr v.
Proof.
  intros penv1 penv2 ret_w path t tr v Heq H.
  assert (Hce : forall e, eval_closed_cert_expr penv1 dummy_freeze_oracle e =
                          eval_closed_cert_expr penv2 dummy_freeze_oracle e)
    by (intro e; apply eval_cert_expr_extensional; exact Heq).
  induction H.
  - apply MTPO_Ret; rewrite <- Hce; exact H.
  - eapply MTPO_Branch; [rewrite <- Hce; exact H | exact IHmc_tree_path_ok].
  - eapply MTPO_Call; [| rewrite <- Heq; exact H0 | exact H1 | exact IHmc_tree_path_ok].
    clear -H Hce; induction H; [constructor | constructor; [rewrite <- Hce; exact H | exact IHForall2]].
Qed.

Lemma mc_tree_path_ok_app_r {Pa : Params} :
  forall (penv : param_env Pa) ret_w p1 p2 t tr_vals v_ret,
    mc_tree_path_ok penv ret_w p1 t tr_vals v_ret ->
    mc_tree_path_ok penv ret_w (p1 ++ p2) t tr_vals v_ret.
Proof.
  intros penv ret_w p1 p2 t tr_vals v_ret H; induction H.
  - apply MTPO_Ret; exact H.
  - eapply MTPO_Branch; [exact H | exact IHmc_tree_path_ok].
  - eapply MTPO_Call; eassumption.
Qed.

Definition binds_disjoint_from {Pa : Params}
  (allowed : list (string * positive)) (binds : list (string * @dvalue Pa)) : Prop :=
  forall nm w, In (nm, w) allowed -> ~ In nm (List.map fst binds).

Lemma binds_disjoint_app {Pa : Params} :
  forall allowed (b1 b2 : list (string * @dvalue Pa)),
    binds_disjoint_from allowed b1 ->
    binds_disjoint_from allowed b2 ->
    binds_disjoint_from allowed (b1 ++ b2).
Proof.
  intros allowed b1 b2 H1 H2 nm w Hin Hina; rewrite List.map_app in Hina;
    apply in_app_iff in Hina as [H | H]; [exact (H1 nm w Hin H) | exact (H2 nm w Hin H)].
Qed.

Lemma overlay_penv_app {Pa : Params} :
  forall (b1 b2 : list (string * @dvalue Pa)) (base : param_env Pa) nm,
    overlay_penv (b1 ++ b2) base nm = overlay_penv b1 (overlay_penv b2 base) nm.
Proof.
  induction b1 as [| [x dv] rest IH]; intros b2 base nm; cbn; [reflexivity |].
  destruct (String.eqb nm x); [reflexivity | exact (IH b2 base nm)].
Qed.

Lemma overlay_penv_disjoint_allowed {Pa : Params} :
  forall (binds : list (string * @dvalue Pa)) (base : param_env Pa) allowed,
    binds_disjoint_from allowed binds ->
    forall nm w, In (nm, w) allowed -> overlay_penv binds base nm = base nm.
Proof.
  intros binds base allowed Hdisj nm w Hin; apply overlay_penv_not_in; exact (Hdisj nm w Hin).
Qed.

Lemma summarize_rv64_call_at_exec {Pa : Params} :
  forall insts im
    (Him : forall pc, pt_get (N.succ_pos pc) im = lookup_rv_call_inst insts pc)
    fuel callees visited pc cid sp_off vrf astk ret_w allowed t_mc
    (O : rv_call_oracle) (penv0 : param_env Pa) rf0 rf mstk,
    rv_supported_arg_width ret_w = true ->
    (forall c, In c callees -> rv_supported_arg_width (mcs_ret_width c) = true) ->
    forallb rv_call_inst_no_word_mulh insts = true ->
    wf_rv_call_oracle callees O ->
    mc_valid_sp0_depth 2%nat (rv_read_reg 2%N rf0) ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    rv_val_read 2%N vrf = MSV_StackPtr sp_off ->
    rv_val_regs_wf allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (forall nm w, In (nm, w) allowed ->
       forall k' w', (cid <= k')%nat -> nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k') ->
    rv_val_regs_agrees penv0 dummy_freeze_oracle rf0 (rv_read_reg 2%N rf0) vrf rf ->
    mc_sym_stack_agrees penv0 dummy_freeze_oracle (fun r => rv_read_reg r rf0) (rv_read_reg 2%N rf0) astk mstk ->
    summarize_rv64_call_at fuel im callees visited pc cid sp_off vrf astk ret_w = inr t_mc ->
    exists tr_mc new_binds rf_end mstk_end,
      NoDup (List.map fst new_binds) /\
      binds_disjoint_from allowed new_binds /\
      (forall nm, In nm (List.map fst new_binds) ->
         exists k, (cid <= k)%nat /\
           ((exists w, nm = mc_call_ret_var k w) \/ nm = mc_call_hi_var k)) /\
      (forall nm dv, In (nm, dv) new_binds ->
         exists w, In (nm, w) (collect_mc_call_vars t_mc) /\
           exists v : @Integers.bit_int w, dv = DVALUE_Base (@DVALUE_I Pa w v)) /\
      rv_exec_with_calls fuel insts O pc (rv_read_reg 2%N rf0) rf mstk = Some (tr_mc, rf_end, mstk_end) /\
      rv_callee_saved_preserved rf0 rf_end /\
      rf_end 1%N = rf0 1%N /\
      forall extra_binds : list (string * @dvalue Pa),
        binds_disjoint_from allowed extra_binds ->
        (forall nm, In nm (List.map fst new_binds) -> ~ In nm (List.map fst extra_binds)) ->
        mc_tree_path_ok (overlay_penv (new_binds ++ extra_binds) penv0) ret_w [] t_mc
          (List.map (fun '(cn, rf_c, a0_r) =>
             let n := match find_callee_spec callees cn with
                      | Some sp => List.length (mcs_args sp)
                      | None => 0%nat end in
             (cn, List.map (fun j => rv_read_reg (10%N + N.of_nat j) rf_c) (seq 0 n), a0_r)) tr_mc)
          (rv_trunc_ret_val ret_w (rv_read_reg 10%N rf_end)).
Proof.
  intros insts im Him fuel; induction fuel as [| fuel' IH];
    intros callees visited pc cid sp_off vrf astk ret_w allowed t_mc
           O penv0 rf0 rf mstk Hrw Hcws Hmul HO Hsp0 Hrng Hsp2 Hvrf Hastk Hfresh Hag_rf Hag_stk Hsum;
    cbn [summarize_rv64_call_at] in Hsum;
    destruct (pt_has_n pc visited); try discriminate Hsum.
  destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Hlk; [| discriminate Hsum].
  rewrite Him in Hlk.
  assert (Hin_dec : In dec insts).
  { clear -Hlk; induction insts as [| d rest IHi]; cbn in Hlk; [discriminate |].
    destruct (N.eqb (drci_off d) pc); [inversion Hlk; left; reflexivity | right; exact (IHi Hlk)]. }
  destruct (drci_inst dec) as [i | cname] eqn:Edi.
  - assert (Hdec_nmul : inst_no_word_mulh (mk_decoded_rv (drci_off dec) (drci_len dec) i) = true).
    { rewrite forallb_forall in Hmul; pose proof (Hmul dec Hin_dec) as Hm;
        unfold rv_call_inst_no_word_mulh in Hm; rewrite Edi in Hm; exact Hm. }
    assert (Hsp0_1 : mc_valid_sp0 (rv_read_reg 2%N rf0))
      by (destruct Hsp0 as [H0 H1]; split; [unfold mc_frame_cap in *; lia | exact H1]).
    destruct (rv_sym_step_one (mk_decoded_rv (drci_off dec) (drci_len dec) i) pc sp_off vrf astk ret_w)
      as [res |] eqn:Est; [| discriminate Hsum].
    pose proof (rv_sym_step_one_wf allowed (mk_decoded_rv (drci_off dec) (drci_len dec) i)
                  pc sp_off vrf astk ret_w res Hrw Hdec_nmul Hrng Hsp2 Hvrf Hastk Est) as Hwf_step.
    pose proof (rv_sym_step_one_sound (mk_decoded_rv (drci_off dec) (drci_len dec) i)
                  pc sp_off vrf astk ret_w res penv0 dummy_freeze_oracle rf0 rf mstk
                  Hrw Hdec_nmul Hsp0_1 Hrng Hsp2 Hag_rf Hag_stk Est) as Hsd_step.
    destruct res as [npc sp' vrf' astk' | cond tpc npc | ret_e].
    + destruct Hwf_step as (Hrng' & Hsp2' & Hvrf' & Hastk').
      destruct Hsd_step as (rf' & mstk' & Hexec1 & _ & _ & Hag_rf' & Hag_stk').
      destruct (IH callees (pt_add_n pc visited) npc cid sp' vrf' astk' ret_w allowed t_mc
                   O penv0 rf0 rf' mstk' Hrw Hcws Hmul HO Hsp0 Hrng' Hsp2' Hvrf' Hastk' Hfresh
                   Hag_rf' Hag_stk' Hsum)
        as (tr_mc & nb & rf_end & mstk_end & Hnd & Hdisj & Hkge & Hcv & Hexec & Hpres & Hra & Hpath).
      exists tr_mc, nb, rf_end, mstk_end; repeat split; try assumption.
      cbn [rv_exec_with_calls]; rewrite Hlk, Edi.
      destruct i; cbn [rv_exec_one_nonret] in Hexec1; try discriminate Hexec1;
        rewrite ?Hexec1; exact Hexec.
    + destruct (summarize_rv64_call_at fuel' im callees (pt_add_n pc visited) tpc cid sp_off vrf astk ret_w)
        as [| dt] eqn:Hdt; [discriminate Hsum |].
      destruct (summarize_rv64_call_at fuel' im callees (pt_add_n pc visited) npc cid sp_off vrf astk ret_w)
        as [| df] eqn:Hdf; [discriminate Hsum |].
      inversion Hsum; subst t_mc; clear Hsum.
      destruct Hwf_step as (Hwt_c & Hbw_c & Hlf_c & Hsub_c).
      destruct Hsd_step as [b [Hevc Hexec1]].
      assert (Hnext_p : summarize_rv64_call_at fuel' im callees (pt_add_n pc visited)
                          (if b then tpc else npc) cid sp_off vrf astk ret_w = inr (if b then dt else df))
        by (destruct b; [exact Hdt | exact Hdf]).
      destruct (IH callees (pt_add_n pc visited) (if b then tpc else npc) cid sp_off vrf astk ret_w
                   allowed (if b then dt else df) O penv0 rf0 rf mstk
                   Hrw Hcws Hmul HO Hsp0 Hrng Hsp2 Hvrf Hastk Hfresh Hag_rf Hag_stk Hnext_p)
        as (tr_mc & nb & rf_end & mstk_end & Hnd & Hdisj & Hkge & Hcv & Hexec & Hpres & Hra & Hpath).
      exists tr_mc, nb, rf_end, mstk_end; repeat split; try assumption.
      * intros nm dv Hinn; destruct (Hcv nm dv Hinn) as (w & Hcm & Hv).
        exists w; split; [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_app_iff; destruct b; [right | left]; exact Hcm | exact Hv].
      * cbn [rv_exec_with_calls]; rewrite Hlk, Edi.
        destruct i; cbn [rv_exec_one_nonret] in Hexec1; try discriminate Hexec1;
          rewrite Hexec1; exact Hexec.
      * intros extra Hdx Hnx; specialize (Hpath extra Hdx Hnx).
        eapply MTPO_Branch.
        -- unfold eval_closed_cert_expr in *; erewrite mcc_eval_cert_expr_penv_agree; [exact Hevc | exact Hlf_c |].
           intros nm w Hnm; pose proof (vars_subset_b_incl _ _ Hsub_c _ Hnm) as Hal.
           apply (overlay_penv_disjoint_allowed (nb ++ extra) penv0 allowed (binds_disjoint_app _ _ _ Hdisj Hdx) nm w Hal).
        -- exact (mc_tree_path_ok_app_r _ _ [] [(b, cond)] _ _ _ Hpath).
    + inversion Hsum; subst t_mc; clear Hsum.
      destruct Hsd_step as (Edri & Hpres & Hra & Hevr).
      destruct Hwf_step as (_ & _ & Hlf_r & Hsub_r).
      exists [], [], rf, mstk.
      split; [constructor | split; [| split; [| split; [| split; [| split; [exact Hpres | split; [exact Hra |]]]]]]].
      * intros nm w _ H; contradiction H.
      * intros nm H; contradiction H.
      * intros nm dv H; contradiction H.
      * cbn [dri_inst] in Edri; cbn [rv_exec_with_calls]; rewrite Hlk, Edi, Edri; reflexivity.
      * intros extra Hdx _; apply MTPO_Ret.
        unfold eval_closed_cert_expr in *; erewrite mcc_eval_cert_expr_penv_agree; [exact Hevr | exact Hlf_r |].
        intros nm w Hnm; pose proof (vars_subset_b_incl _ _ Hsub_r _ Hnm) as Hal.
        cbn [app]; exact (overlay_penv_disjoint_allowed extra penv0 allowed Hdx nm w Hal).
  - destruct (mc_sp_aligned16 sp_off) eqn:Esp_al; cbn [negb] in Hsum; [| discriminate Hsum].
    destruct (find_callee_spec callees cname) as [c |] eqn:Efc; [| discriminate Hsum].
    destruct (rv_sym_read_call_args_from pc cname 10%N (List.length (mcs_args c)) vrf) as [| aes] eqn:Eargs;
      [discriminate Hsum |].
    destruct (mc_post_call_ret_expr cid (mcs_ret_width c) (mcs_ret_ext c)) as [ret_e64 opt_hi] eqn:Epc.
    destruct (summarize_rv64_call_at fuel' im callees (pt_add_n pc visited)
                (pc + drci_len dec)%N (S cid) sp_off (rv_post_call_vrf cid c vrf) astk ret_w)
      as [| cont] eqn:Ect; [discriminate Hsum |].
    inversion Hsum; subst t_mc; clear Hsum.
    pose proof (find_callee_spec_in _ _ _ Efc) as [Hc_in Hc_nm].
    pose proof (Hcws c Hc_in) as Hcrw.
    pose proof (Hag_rf 2%N) as Hag2; rewrite Hsp2 in Hag2; cbn [mc_sym_val_agrees] in Hag2.
    destruct Hag2 as [_ Hrf2_eq].
    assert (Hsp_eq_off : mc_addr_to_off (rv_read_reg 2%N rf0) (rv_read_reg 2%N rf) = sp_off).
    { rewrite Hrf2_eq; refine (mc_addr_to_off_add (rv_read_reg 2%N rf0) sp_off _ Hrng).
      destruct Hsp0 as [Hlo_sp _]; simpl Z.of_nat in Hlo_sp; unfold mc_frame_cap in *; lia. }
    assert (Hsp_call_valid : mc_valid_sp0 (rv_read_reg 2%N rf)).
    { rewrite Hrf2_eq; exact (mc_valid_sp0_depth_step _ _ Hsp0 Esp_al). }
    set (next_pc := (pc + drci_len dec)%N).
    set (rf_link := rv_write_reg 1%N (@Integers.repr 64%positive (Z.of_N next_pc)) rf).
    assert (Hrf_link2 : rv_read_reg 2%N rf_link = rv_read_reg 2%N rf)
      by (unfold rv_read_reg, rf_link, rv_write_reg; cbn [N.eqb]; reflexivity).
    assert (Hsp_call_valid_l : mc_valid_sp0 (rv_read_reg 2%N rf_link))
      by (rewrite Hrf_link2; exact Hsp_call_valid).
    destruct (HO c rf_link mstk Hc_in Hsp_call_valid_l) as (rf_ret & v_ret & HO_eq & Hpres_c & Habi_c).
    rewrite Hc_nm in HO_eq.
    set (step_binds :=
      (mc_call_ret_var cid (mcs_ret_width c), DVALUE_Base (@DVALUE_I Pa (mcs_ret_width c) v_ret)) ::
      match opt_hi with
      | None => []
      | Some hn => [(hn, DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg 10%N rf_ret)))]
      end).
    set (penv1 := overlay_penv step_binds penv0).
    set (ext := match opt_hi with None => [] | Some hn => [(hn, 64%positive)] end).
    set (allowed' := (mc_call_ret_var cid (mcs_ret_width c), mcs_ret_width c) :: ext ++ allowed).
    assert (Hinc : incl allowed allowed') by (intros x Hx; right; apply in_or_app; right; exact Hx).
    assert (Hopt_hi_nm : forall hn, opt_hi = Some hn -> hn = mc_call_hi_var cid).
    { intros hn Hhn; unfold mc_post_call_ret_expr in Epc.
      destruct (Pos.eqb (mcs_ret_width c) 64%positive); [inversion Epc; rewrite Hhn in *; discriminate |].
      destruct (mcs_ret_ext c); inversion Epc; subst; try discriminate; congruence. }
    assert (Hnd_step : NoDup (List.map fst step_binds)).
    { unfold step_binds; destruct opt_hi as [hn |] eqn:Ehi; cbn [List.map].
      - constructor; [| constructor; [intro H; contradiction H | constructor]].
        intro Hin; destruct Hin as [Heq | []]; pose proof (Hopt_hi_nm hn eq_refl) as ->.
        cbn [fst] in Heq; exfalso; apply (mc_call_ret_hi_disjoint cid (mcs_ret_width c) cid); symmetry; exact Heq.
      - constructor; [intro H; contradiction H | constructor]. }
    assert (Hdisj_step : binds_disjoint_from allowed step_binds).
    { intros nm w Hin Hina; unfold step_binds in Hina; destruct opt_hi as [hn |]; cbn [List.map fst] in Hina.
      - destruct Hina as [Heq | [Heq | []]].
        + exfalso; apply (proj1 (Hfresh nm w Hin cid (mcs_ret_width c) (Nat.le_refl _))); symmetry; exact Heq.
        + pose proof (Hopt_hi_nm hn eq_refl) as ->.
          exfalso; apply (proj2 (Hfresh nm w Hin cid (mcs_ret_width c) (Nat.le_refl _))); symmetry; exact Heq.
      - destruct Hina as [Heq | []].
        exfalso; apply (proj1 (Hfresh nm w Hin cid (mcs_ret_width c) (Nat.le_refl _))); symmetry; exact Heq. }
    assert (Hp1_al : forall nm w, In (nm, w) allowed -> penv1 nm = penv0 nm)
      by (intros nm w Hin; unfold penv1; exact (overlay_penv_disjoint_allowed step_binds penv0 allowed Hdisj_step nm w Hin)).
    assert (Hvrf' : rv_val_regs_wf allowed' (rv_post_call_vrf cid c vrf)).
    { pose proof (rv_post_call_vrf_wf allowed cid c vrf Hvrf Hcrw) as Hpv; rewrite Epc in Hpv; exact Hpv. }
    assert (Hsp2' : rv_val_read 2%N (rv_post_call_vrf cid c vrf) = MSV_StackPtr sp_off).
    { unfold rv_val_read, rv_post_call_vrf; rewrite Epc; cbn [N.eqb]; unfold rv_val_read in Hsp2; exact Hsp2. }
    assert (Hastk' : mc_sym_stack_wf allowed' sp_off astk)
      by (exact (mc_sym_stack_wf_mono _ _ _ _ Hinc Hastk)).
    assert (Hfresh' : forall nm w, In (nm, w) allowed' ->
      forall k' w', (S cid <= k')%nat -> nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k').
    { intros nm w Hin k' w' Hge; destruct Hin as [Heq | Hin].
      - inversion Heq; subst nm w; split;
          [intro H; apply mc_call_ret_var_k_inj in H; lia | apply mc_call_ret_hi_disjoint].
      - apply in_app_iff in Hin as [Hext | Hal].
        + unfold ext in Hext; destruct opt_hi as [hn |]; [| contradiction Hext].
          destruct Hext as [Heq | []]; inversion Heq; subst nm w; pose proof (Hopt_hi_nm hn eq_refl) as ->.
          split; [intro H; symmetry in H; apply (mc_call_ret_hi_disjoint _ _ _ H)
                 | intro H; apply mc_call_hi_var_inj in H; lia].
        + exact (Hfresh nm w Hal k' w' ltac:(lia)). }
    assert (Hag_rf_ret : rv_val_regs_agrees penv1 dummy_freeze_oracle rf0 (rv_read_reg 2%N rf0)
                           (rv_post_call_vrf cid c vrf) rf_ret).
    { intro r; unfold rv_val_read, rv_post_call_vrf; rewrite Epc.
      destruct (N.eqb r 0%N) eqn:Er0.
      - apply N.eqb_eq in Er0; subst r; unfold rv_read_reg; cbn [N.eqb mc_sym_val_agrees].
        rewrite eval_ce_const, repr_zero_N; reflexivity.
      - destruct (N.eqb r 2%N) eqn:Er2.
        + apply N.eqb_eq in Er2; subst r; pose proof (Hag_rf 2%N) as H2; unfold rv_val_read in H2, Hsp2; cbn [N.eqb] in H2, Hsp2.
          rewrite Hsp2 in H2 |- *; cbn [mc_sym_val_agrees] in H2 |- *.
          assert (Hrf_eq2 : rf_ret 2%N = rf_link 2%N) by (apply Hpres_c; reflexivity).
          unfold rv_read_reg in *; cbn [N.eqb] in *; rewrite Hrf_eq2, Hrf_link2; exact H2.
        + destruct (N.eqb r 10%N) eqn:Er10.
          * apply N.eqb_eq in Er10; subst r; cbn [mc_sym_val_agrees].
            unfold rv_read_reg; cbn [N.eqb].
            eapply mc_post_call_ret_expr_sound; [exact Hcrw | exact Epc | exact Habi_c | |].
            -- unfold penv1; apply overlay_penv_lookup_in; [exact Hnd_step | left; reflexivity].
            -- destruct opt_hi as [hn |] eqn:Ehi; [| exact I].
               unfold penv1; apply overlay_penv_lookup_in; [exact Hnd_step | right; left; reflexivity].
          * destruct (rv_is_callee_saved r) eqn:Ecs; [| exact I].
            pose proof (Hag_rf r) as Hr; unfold rv_val_read in Hr; rewrite Er0 in Hr.
            assert (Hr_ne1 : r <> 1%N) by (intro C; subst r; discriminate Ecs).
            assert (Hrf_eqr : rv_read_reg r rf_ret = rv_read_reg r rf).
            { unfold rv_read_reg; rewrite Er0; rewrite (Hpres_c r Ecs).
              unfold rf_link, rv_write_reg; cbn [N.eqb]; destruct (N.eqb r 1%N) eqn:E1;
                [apply N.eqb_eq in E1; contradiction | reflexivity]. }
            rewrite Hrf_eqr.
            destruct (vrf r) as [| e | |] eqn:Evr; try exact Hr.
            pose proof (Hvrf r) as Hwr; unfold rv_val_read in Hwr; rewrite Er0, Evr in Hwr.
            destruct Hwr as (_ & _ & Hlf_e & Hsub_e); cbn [mc_sym_val_agrees] in Hr |- *.
            unfold eval_closed_cert_expr in *; erewrite mcc_eval_cert_expr_penv_agree; [exact Hr | exact Hlf_e |].
            intros nm0 w0 Hnm0; exact (Hp1_al nm0 w0 (vars_subset_b_incl _ _ Hsub_e _ Hnm0)). }
    assert (Hag_stk1 : mc_sym_stack_agrees penv1 dummy_freeze_oracle (fun r => rv_read_reg r rf0) (rv_read_reg 2%N rf0) astk mstk)
      by (eapply (mc_sym_stack_agrees_penv_agree penv0 penv1); [exact Hastk | intros nm w H; symmetry; exact (Hp1_al nm w H) | exact Hag_stk]).
    destruct (IH callees (pt_add_n pc visited) next_pc (S cid) sp_off
                 (rv_post_call_vrf cid c vrf) astk ret_w allowed' cont
                 O penv1 rf0 rf_ret mstk Hrw Hcws Hmul HO Hsp0 Hrng Hsp2' Hvrf' Hastk' Hfresh' Hag_rf_ret Hag_stk1 Ect)
      as (tr_r & nb_r & rf_end & mstk_end & Hnd_r & Hdisj_r & Hkge_r & Hcv_r & Hexec_r & Hpres_r & Hra_r & Hpath_r).
    exists ((cname, rf_link, rv_read_reg 10%N rf_ret) :: tr_r), (step_binds ++ nb_r), rf_end, mstk_end.
    assert (Hdisj_sr : forall nm, In nm (List.map fst step_binds) -> ~ In nm (List.map fst nb_r)).
    { intros nm Hst Hin_r; destruct (Hkge_r nm Hin_r) as [k' [Hk' Hnm']].
      assert (Hex : exists w', In (nm, w') allowed').
      { unfold step_binds in Hst; destruct opt_hi as [hn |] eqn:Ehi; cbn [List.map fst] in Hst.
        - destruct Hst as [<- | [<- | []]].
          + exists (mcs_ret_width c); left; reflexivity.
          + exists 64%positive; right; left; reflexivity.
        - destruct Hst as [<- | []]; exists (mcs_ret_width c); left; reflexivity. }
      destruct Hex as [w' Hw'].
      destruct Hnm' as [[w'' Heq] | Heq];
        [pose proof (Hfresh' nm w' Hw' k' w'' Hk') as [Hne _]; exact (Hne Heq)
        | pose proof (Hfresh' nm w' Hw' k' 1%positive Hk') as [_ Hne]; exact (Hne Heq)]. }
    repeat split.
    + rewrite List.map_app; apply NoDup_app_intro; assumption.
    + apply binds_disjoint_app; [exact Hdisj_step |].
      intros nm w Hin; exact (Hdisj_r nm w (Hinc _ Hin)).
    + intros nm Hin; rewrite List.map_app in Hin; apply in_app_iff in Hin as [Hst | Hr].
      * unfold step_binds in Hst; destruct opt_hi as [hn |]; cbn [List.map fst] in Hst.
        -- destruct Hst as [<- | [<- | []]].
           ++ exists cid; split; [lia | left; exists (mcs_ret_width c); reflexivity].
           ++ pose proof (Hopt_hi_nm hn eq_refl) as ->; exists cid; split; [lia | right; reflexivity].
        -- destruct Hst as [<- | []]; exists cid; split; [lia | left; exists (mcs_ret_width c); reflexivity].
      * destruct (Hkge_r nm Hr) as [k [Hk Hnm]]; exists k; split; [lia | exact Hnm].
    + intros nm dv Hin; apply in_app_iff in Hin as [Hst | Hr].
      * unfold step_binds in Hst; destruct opt_hi as [hn |] eqn:Ehi.
        -- destruct Hst as [Heq | [Heq | []]]; inversion Heq; subst nm dv.
           ++ exists (mcs_ret_width c); split;
                [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; right; left; reflexivity
                | exists v_ret; reflexivity].
           ++ exists 64%positive; split;
                [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; right; right; left; reflexivity
                | exists (rv_read_reg 10%N rf_ret); reflexivity].
        -- destruct Hst as [Heq | []]; inversion Heq; subst nm dv.
           exists (mcs_ret_width c); split;
             [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; right; left; reflexivity
             | exists v_ret; reflexivity].
      * destruct (Hcv_r nm dv Hr) as (w & Hcm & Hv); exists w; split;
          [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; left; exact Hcm
          | exact Hv].
    + cbn [rv_exec_with_calls]; rewrite Hlk, Edi, Hsp_eq_off, Esp_al.
      fold next_pc rf_link; rewrite HO_eq; cbn [fst snd]; rewrite Hexec_r; reflexivity.
    + exact Hpres_r.
    + exact Hra_r.
    + intros extra Hdx Hnx.
      cbn [List.map] in *.
      assert (Hfc : find_callee_spec callees cname = Some c) by exact Efc.
      rewrite Hfc.
      assert (Hargs_eval : Forall2 (fun e64 v64 =>
        eval_closed_cert_expr (overlay_penv ((step_binds ++ nb_r) ++ extra) penv0) dummy_freeze_oracle e64 =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)))
        aes
        (List.map (fun j => rv_read_reg (10%N + N.of_nat j) rf_link) (seq 0 (List.length (mcs_args c))))).
      { assert (Hrf_arg_eq : List.map (fun j => rv_read_reg (10%N + N.of_nat j) rf_link) (seq 0 (List.length (mcs_args c))) =
                             List.map (fun j => rv_read_reg (10%N + N.of_nat j) rf) (seq 0 (List.length (mcs_args c)))).
        { apply map_ext; intro j; unfold rf_link, rv_read_reg, rv_write_reg; cbn [N.eqb].
          destruct (N.eqb (10%N + N.of_nat j) 0%N) eqn:E0; [reflexivity |].
          destruct (N.eqb (10%N + N.of_nat j) 1%N) eqn:E1; [apply N.eqb_eq in E1; lia | reflexivity]. }
        rewrite Hrf_arg_eq.
        pose proof (rv_sym_read_call_args_from_sound pc cname penv0 dummy_freeze_oracle rf0 (rv_read_reg 2%N rf0) vrf rf 10%N
                      (List.length (mcs_args c)) aes Hag_rf Eargs) as Hs_args.
        pose proof (rv_sym_read_call_args_from_wf pc cname allowed 10%N (List.length (mcs_args c)) vrf aes Hvrf Eargs) as Hwf_args.
        assert (Hfa_ev : forall e64 v64,
          wf_sym_expr allowed 64%positive e64 ->
          eval_closed_cert_expr penv0 dummy_freeze_oracle e64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) ->
          eval_closed_cert_expr (overlay_penv ((step_binds ++ nb_r) ++ extra) penv0) dummy_freeze_oracle e64 =
          raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64))).
        { intros e64 v64 (_ & _ & Hlf & Hsub) Hev; unfold eval_closed_cert_expr in *.
          assert (Hdisj_all : binds_disjoint_from allowed ((step_binds ++ nb_r) ++ extra))
            by (apply binds_disjoint_app; [apply binds_disjoint_app; [exact Hdisj_step | intros x wx Hx; exact (Hdisj_r x wx (Hinc _ Hx))] | exact Hdx]).
          erewrite mcc_eval_cert_expr_penv_agree; [exact Hev | exact Hlf |].
          intros nm w Hnm; exact (overlay_penv_disjoint_allowed _ penv0 allowed Hdisj_all nm w (vars_subset_b_incl _ _ Hsub _ Hnm)). }
        clear -Hwf_args Hs_args Hfa_ev; induction Hs_args; [constructor |].
        inversion Hwf_args as [| ? ? Hw0 Hwr]; subst; constructor; [exact (Hfa_ev _ _ Hw0 H) | exact (IHHs_args Hwr)]. }
      eapply MTPO_Call; [exact Hargs_eval | | symmetry; exact (proj1 Habi_c) |].
      * unfold penv1; rewrite <- app_assoc, overlay_penv_app;
          unfold step_binds; cbn [overlay_penv]; rewrite String.eqb_refl; reflexivity.
      * assert (Hdx_r : binds_disjoint_from allowed' extra).
        { intros nm w Hin Hina; destruct Hin as [Heq | Hin].
          - inversion Heq; subst nm w; apply (Hnx (mc_call_ret_var cid (mcs_ret_width c)));
              [rewrite List.map_app; apply in_or_app; left; left; reflexivity | exact Hina].
          - apply in_app_iff in Hin as [Hext | Hal].
            + unfold ext in Hext; destruct opt_hi as [hn |]; [| contradiction Hext].
              destruct Hext as [Heq | []]; inversion Heq; subst nm w; apply (Hnx hn);
                [rewrite List.map_app; apply in_or_app; left; right; left; reflexivity | exact Hina].
            + exact (Hdx nm w Hal Hina). }
        assert (Hnx_r : forall nm, In nm (List.map fst nb_r) -> ~ In nm (List.map fst extra)).
        { intros nm Hin; apply Hnx; rewrite List.map_app; apply in_or_app; right; exact Hin. }
        specialize (Hpath_r extra Hdx_r Hnx_r).
        assert (Henv_eq : forall nm,
          overlay_penv (nb_r ++ extra) penv1 nm =
          overlay_penv ((step_binds ++ nb_r) ++ extra) penv0 nm).
        { intro nm; unfold penv1; rewrite <- app_assoc; repeat rewrite overlay_penv_app.
          destruct (in_dec string_dec nm (List.map fst nb_r)) as [Hin_r | Hnin_r].
          - rewrite (overlay_penv_not_in step_binds _ nm).
            + clear -Hin_r; induction nb_r as [| [x dv] rest IHnb]; cbn in *; [contradiction |].
              destruct (String.eqb nm x) eqn:Ex; [reflexivity |].
              apply IHnb; destruct Hin_r as [-> | Hr]; [rewrite String.eqb_refl in Ex; discriminate Ex | exact Hr].
            + intro Hs; exact (Hdisj_sr nm Hs Hin_r).
          - rewrite !overlay_penv_not_in by exact Hnin_r.
            destruct (in_dec string_dec nm (List.map fst step_binds)) as [Hin_s | Hnin_s].
            + rewrite (overlay_penv_not_in extra _ nm) by (apply Hnx; rewrite List.map_app; apply in_or_app; left; exact Hin_s).
              clear -Hin_s; induction step_binds as [| [x dv] rest IHst]; cbn in *;
                [exfalso; exact Hin_s |].
              destruct (String.eqb nm x) eqn:Ex; [reflexivity |].
              apply IHst; destruct Hin_s as [<- | Hs]; [rewrite String.eqb_refl in Ex; discriminate Ex | exact Hs].
            + rewrite (overlay_penv_not_in step_binds _ nm Hnin_s).
              rewrite overlay_penv_app, (overlay_penv_not_in nb_r _ nm Hnin_r).
              clear -Hnin_s; induction extra as [| [x dv] rest IHe]; cbn [overlay_penv];
                [exact (overlay_penv_not_in step_binds penv0 nm Hnin_s)
                | destruct (String.eqb nm x); [reflexivity | exact IHe]]. }
        exact (mc_tree_path_ok_extensional _ _ _ _ _ _ _ Henv_eq Hpath_r).
Qed.



(** *** 5.3 AArch64 Call-Tree Execution Witness *)

Lemma summarize_a64_call_at_exec {Pa : Params} :
  forall insts im
    (Him : forall pc, pt_get (N.succ_pos pc) im = lookup_a64_call_inst insts pc)
    fuel callees visited pc cid sp_off vrf astk sfl fl_def ret_w allowed t_mc
    (O : a64_call_oracle) (penv0 : param_env Pa) rf0 sp0 rf sp fl mstk,
    rv_supported_arg_width ret_w = true ->
    (forall c, In c callees ->
       rv_supported_arg_width (mcs_ret_width c) = true /\
       (List.length (mcs_args c) <= 8)%nat) ->
    forallb a64_call_inst_valid insts = true ->
    wf_a64_call_oracle callees O ->
    mc_valid_sp0_depth 2%nat sp0 ->
    (- mc_frame_cap <= sp_off <= 0)%Z ->
    sp = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off) ->
    wf_a64_val_regs allowed vrf ->
    mc_sym_stack_wf allowed sp_off astk ->
    (fl_def = true -> wf_sym_flags allowed sfl) ->
    (forall nm w, In (nm, w) allowed ->
       forall k' w', (cid <= k')%nat -> nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k') ->
    a64_val_regs_agrees penv0 dummy_freeze_oracle rf0 sp0 vrf rf ->
    mc_sym_stack_agrees penv0 dummy_freeze_oracle (fun r0 => a64_read_reg r0 rf0) sp0 astk mstk ->
    (fl_def = true -> sym_flags_agree penv0 dummy_freeze_oracle sfl fl) ->
    summarize_a64_call_at fuel im callees visited pc cid sp_off vrf astk sfl fl_def ret_w = inr t_mc ->
    exists tr_mc new_binds rf_end fl_end mstk_end,
      NoDup (List.map fst new_binds) /\
      binds_disjoint_from allowed new_binds /\
      (forall nm, In nm (List.map fst new_binds) ->
         exists k, (cid <= k)%nat /\ ((exists w, nm = mc_call_ret_var k w) \/ nm = mc_call_hi_var k)) /\
      (forall nm dv, In (nm, dv) new_binds ->
         exists w, In (nm, w) (collect_mc_call_vars t_mc) /\
                   exists v : @Integers.bit_int w, dv = DVALUE_Base (@DVALUE_I Pa w v)) /\
      a64_exec_with_calls fuel insts O pc sp0 rf sp fl mstk =
        Some (tr_mc, rf_end, sp0, fl_end, mstk_end) /\
      a64_callee_saved_preserved rf0 rf_end /\
      forall extra_binds,
        binds_disjoint_from allowed extra_binds ->
        (forall nm, In nm (List.map fst new_binds) -> ~ In nm (List.map fst extra_binds)) ->
        mc_tree_path_ok (overlay_penv (new_binds ++ extra_binds) penv0) ret_w [] t_mc
          (List.map (fun '(cn, rf_c, a0_r) =>
            let n := match find_callee_spec callees cn with
                     | Some spc => List.length (mcs_args spc)
                     | None => 0%nat
                     end in
            (cn, List.map (fun j => a64_read_reg (N.of_nat j) rf_c) (seq 0 n), a0_r)) tr_mc)
          (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end)).
Proof.
  intros insts im Him fuel; induction fuel as [| fuel' IH];
    intros callees visited pc cid sp_off vrf astk sfl fl_def ret_w allowed t_mc
           O penv0 rf0 sp0 rf sp fl mstk
           Hrw Hcws Hval HO Hsp0 Hrng Hsp Hvrf Hastk Hflwf Hfresh Hag_rf Hag_stk Hfl Hsum;
    cbn [summarize_a64_call_at] in Hsum;
    destruct (pt_has_n pc visited); try discriminate Hsum.
  destruct (pt_get (N.succ_pos pc) im) as [dec |] eqn:Hlk; [| discriminate Hsum].
  rewrite Him in Hlk.
  assert (Hin_dec : In dec insts).
  { clear -Hlk; induction insts as [| d rest IHi]; cbn in Hlk; [discriminate |].
    destruct (N.eqb (daci_off d) pc); [inversion Hlk; left; reflexivity | right; exact (IHi Hlk)]. }
  assert (Hsp0_1 : mc_valid_sp0 sp0)
    by (destruct Hsp0 as [H0 H1]; split; [unfold mc_frame_cap in *; lia | exact H1]).
  destruct (daci_inst dec) as [i | cname] eqn:Edi.
  - assert (Hdec_val : a64_inst_valid (mk_decoded_a64_inst (daci_off dec) i) = true).
    { rewrite forallb_forall in Hval; pose proof (Hval dec Hin_dec) as Hv;
        unfold a64_call_inst_valid in Hv; rewrite Edi in Hv; exact Hv. }
    destruct (a64_sym_step_one (mk_decoded_a64_inst (daci_off dec) i) pc sp_off vrf astk sfl fl_def ret_w)
      as [res |] eqn:Est; [| discriminate Hsum].
    pose proof (a64_sym_step_one_wf allowed (mk_decoded_a64_inst (daci_off dec) i)
                  pc sp_off vrf astk sfl fl_def ret_w res Hrw Hrng Hvrf Hastk Hflwf Est) as Hwf_step.
    pose proof (a64_sym_step_one_sound (mk_decoded_a64_inst (daci_off dec) i)
                  pc sp_off vrf astk sfl fl_def ret_w res penv0 dummy_freeze_oracle rf0 sp0 rf sp fl mstk
                  Hrw Hdec_val Hsp0_1 Hrng Hsp Hag_rf Hag_stk Hfl Est) as Hsd_step.
    destruct res as [npc sp_off' vrf' astk' sfl' fl_def' | cond tpc npc fl_def' | ret_e].
    + destruct Hwf_step as (Hrng' & Hvrf' & Hastk' & Hflwf').
      destruct Hsd_step as (rf' & sp' & fl' & mstk' & Hexec1 & _ & Hsp' & Hag_rf' & Hag_stk' & Hfl').
      destruct (IH callees (pt_add_n pc visited) npc cid sp_off' vrf' astk' sfl' fl_def' ret_w
                   allowed t_mc O penv0 rf0 sp0 rf' sp' fl' mstk'
                   Hrw Hcws Hval HO Hsp0 Hrng' Hsp' Hvrf' Hastk' Hflwf' Hfresh Hag_rf' Hag_stk' Hfl' Hsum)
        as (tr_mc & nb & rf_end & fl_end & mstk_end & Hnd & Hdisj & Hkge & Hcv & Hexec & Hpres & Hpath).
      exists tr_mc, nb, rf_end, fl_end, mstk_end; split; [exact Hnd | split; [exact Hdisj | split; [exact Hkge | split; [exact Hcv | split; [| split; [exact Hpres | exact Hpath]]]]]].
      cbn [a64_exec_with_calls]; rewrite Hlk, Edi.
      destruct i; cbn [a64_exec_one_nonret] in Hexec1; try discriminate Hexec1;
        rewrite Hexec1; exact Hexec.
    + destruct Hwf_step as [Hcw Himp].
      destruct Hcw as (_ & _ & Hlf_c & Hsub_c).
      destruct Hsd_step as (b & Hevc & Hexec1 & _).
      destruct (summarize_a64_call_at fuel' im callees (pt_add_n pc visited) tpc cid sp_off vrf astk sfl fl_def' ret_w)
        as [| dt] eqn:Hdt; [discriminate Hsum |].
      destruct (summarize_a64_call_at fuel' im callees (pt_add_n pc visited) npc cid sp_off vrf astk sfl fl_def' ret_w)
        as [| df] eqn:Hdf; [discriminate Hsum |].
      inversion Hsum; subst t_mc; clear Hsum.
      assert (Hnext_p : summarize_a64_call_at fuel' im callees (pt_add_n pc visited)
                          (if b then tpc else npc) cid sp_off vrf astk sfl fl_def' ret_w =
                        inr (if b then dt else df))
        by (destruct b; [exact Hdt | exact Hdf]).
      destruct (IH callees (pt_add_n pc visited) (if b then tpc else npc) cid sp_off vrf astk sfl fl_def' ret_w
                   allowed (if b then dt else df) O penv0 rf0 sp0 rf sp fl mstk
                   Hrw Hcws Hval HO Hsp0 Hrng Hsp Hvrf Hastk (fun h => Hflwf (Himp h)) Hfresh Hag_rf Hag_stk (fun h => Hfl (Himp h)) Hnext_p)
        as (tr_mc & nb & rf_end & fl_end & mstk_end & Hnd & Hdisj & Hkge & Hcv & Hexec & Hpres & Hpath).
      exists tr_mc, nb, rf_end, fl_end, mstk_end; repeat split; try assumption.
      * intros nm dv Hinn; destruct (Hcv nm dv Hinn) as (w & Hcm & Hv).
        exists w; split; [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_app_iff; destruct b; [right | left]; exact Hcm | exact Hv].
      * cbn [a64_exec_with_calls]; rewrite Hlk, Edi.
        destruct i; cbn [a64_exec_one_nonret] in Hexec1; try discriminate Hexec1;
          rewrite Hexec1; exact Hexec.
      * intros extra Hdx Hnx; specialize (Hpath extra Hdx Hnx).
        eapply MTPO_Branch.
        -- unfold eval_closed_cert_expr in *; erewrite mcc_eval_cert_expr_penv_agree; [exact Hevc | exact Hlf_c |].
           intros nm w Hnm; pose proof (vars_subset_b_incl _ _ Hsub_c _ Hnm) as Hal.
           apply (overlay_penv_disjoint_allowed (nb ++ extra) penv0 allowed (binds_disjoint_app _ _ _ Hdisj Hdx) nm w Hal).
        -- exact (mc_tree_path_ok_app_r _ _ [] [(b, cond)] _ _ _ Hpath).
    + inversion Hsum; subst t_mc; clear Hsum.
      destruct Hsd_step as (Edai & Esp_eq & Hpres & Hevr).
      destruct Hwf_step as (_ & _ & Hlf_r & Hsub_r).
      exists [], [], rf, fl, mstk.
      split; [constructor | split; [| split; [| split; [| split; [| split; [exact Hpres |]]]]]].
      * intros nm w _ H; contradiction H.
      * intros nm H; contradiction H.
      * intros nm dv H; contradiction H.
      * cbn [dai_inst] in Edai; cbn [a64_exec_with_calls]; rewrite Hlk, Edi, Edai, Esp_eq; reflexivity.
      * intros extra Hdx _; apply MTPO_Ret.
        unfold eval_closed_cert_expr in *; erewrite mcc_eval_cert_expr_penv_agree; [exact Hevr | exact Hlf_r |].
        intros nm w Hnm; pose proof (vars_subset_b_incl _ _ Hsub_r _ Hnm) as Hal.
        cbn [app]; exact (overlay_penv_disjoint_allowed extra penv0 allowed Hdx nm w Hal).
  - destruct (mc_sp_aligned16 sp_off) eqn:Esp_al; cbn [negb] in Hsum; [| discriminate Hsum].
    destruct (find_callee_spec callees cname) as [c |] eqn:Efc; [| discriminate Hsum].
    destruct (a64_sym_read_call_args_from pc cname 0%N (List.length (mcs_args c)) vrf) as [| aes] eqn:Eargs;
      [discriminate Hsum |].
    destruct (mc_post_call_ret_expr cid (mcs_ret_width c) (mcs_ret_ext c)) as [ret_e64 opt_hi] eqn:Epc.
    destruct (summarize_a64_call_at fuel' im callees (pt_add_n pc visited)
                (pc + 4%N)%N (S cid) sp_off (a64_post_call_vrf cid c vrf) astk sfl false ret_w)
      as [| cont] eqn:Ect; [discriminate Hsum |].
    inversion Hsum; subst t_mc; clear Hsum.
    pose proof (find_callee_spec_in _ _ _ Efc) as [Hc_in Hc_nm].
    destruct (Hcws c Hc_in) as [Hcrw Hclen].
    assert (Hsp_eq_off : mc_addr_to_off sp0 sp = sp_off).
    { rewrite Hsp; refine (mc_addr_to_off_add sp0 sp_off _ Hrng).
      destruct Hsp0 as [Hlo_sp _]; simpl Z.of_nat in Hlo_sp; unfold mc_frame_cap in *; lia. }
    assert (Hsp_call_valid : mc_valid_sp0 sp)
      by (rewrite Hsp; exact (mc_valid_sp0_depth_step sp0 sp_off Hsp0 Esp_al)).
    set (next_pc := (pc + 4%N)%N).
    set (rf_link := a64_write_reg 30%N (@Integers.repr 64%positive (Z.of_N next_pc)) rf).
    destruct (HO c rf_link sp fl mstk Hc_in Hsp_call_valid)
      as (rf_ret & fl_ret & v_ret & HO_eq & Hpres_c & Habi_c).
    rewrite Hc_nm in HO_eq.
    set (step_binds :=
      (mc_call_ret_var cid (mcs_ret_width c), DVALUE_Base (@DVALUE_I Pa (mcs_ret_width c) v_ret)) ::
      match opt_hi with
      | None => []
      | Some hn => [(hn, DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg 0%N rf_ret)))]
      end).
    set (penv1 := overlay_penv step_binds penv0).
    set (ext := match opt_hi with None => [] | Some hn => [(hn, 64%positive)] end).
    set (allowed' := (mc_call_ret_var cid (mcs_ret_width c), mcs_ret_width c) :: ext ++ allowed).
    assert (Hinc : incl allowed allowed') by (intros x Hx; right; apply in_or_app; right; exact Hx).
    assert (Hopt_hi_nm : forall hn, opt_hi = Some hn -> hn = mc_call_hi_var cid).
    { intros hn Hhn; unfold mc_post_call_ret_expr in Epc.
      destruct (Pos.eqb (mcs_ret_width c) 64%positive); [inversion Epc; rewrite Hhn in *; discriminate |].
      destruct (mcs_ret_ext c); inversion Epc; subst; try discriminate; congruence. }
    assert (Hnd_step : NoDup (List.map fst step_binds)).
    { unfold step_binds; destruct opt_hi as [hn |] eqn:Ehi; cbn [List.map].
      - constructor; [| constructor; [intro H; contradiction H | constructor]].
        intro Hin; destruct Hin as [Heq | []]; pose proof (Hopt_hi_nm hn eq_refl) as ->.
        cbn [fst] in Heq; exfalso; apply (mc_call_ret_hi_disjoint cid (mcs_ret_width c) cid); symmetry; exact Heq.
      - constructor; [intro H; contradiction H | constructor]. }
    assert (Hdisj_step : binds_disjoint_from allowed step_binds).
    { intros nm w Hin Hina; unfold step_binds in Hina; destruct opt_hi as [hn |]; cbn [List.map fst] in Hina.
      - destruct Hina as [Heq | [Heq | []]].
        + exfalso; apply (proj1 (Hfresh nm w Hin cid (mcs_ret_width c) (Nat.le_refl _))); symmetry; exact Heq.
        + pose proof (Hopt_hi_nm hn eq_refl) as ->.
          exfalso; apply (proj2 (Hfresh nm w Hin cid (mcs_ret_width c) (Nat.le_refl _))); symmetry; exact Heq.
      - destruct Hina as [Heq | []].
        exfalso; apply (proj1 (Hfresh nm w Hin cid (mcs_ret_width c) (Nat.le_refl _))); symmetry; exact Heq. }
    assert (Hp1_al : forall nm w, In (nm, w) allowed -> penv1 nm = penv0 nm)
      by (intros nm w Hin; unfold penv1; exact (overlay_penv_disjoint_allowed step_binds penv0 allowed Hdisj_step nm w Hin)).
    assert (Hvrf' : wf_a64_val_regs allowed' (a64_post_call_vrf cid c vrf)).
    { pose proof (a64_post_call_vrf_wf allowed cid c vrf Hvrf Hcrw) as Hpv; rewrite Epc in Hpv; exact Hpv. }
    assert (Hastk' : mc_sym_stack_wf allowed' sp_off astk)
      by (exact (mc_sym_stack_wf_mono _ _ _ _ Hinc Hastk)).
    assert (Hfresh' : forall nm w, In (nm, w) allowed' ->
      forall k' w', (S cid <= k')%nat -> nm <> mc_call_ret_var k' w' /\ nm <> mc_call_hi_var k').
    { intros nm w Hin k' w' Hge; destruct Hin as [Heq | Hin].
      - inversion Heq; subst nm w; split;
          [intro H; apply mc_call_ret_var_k_inj in H; lia | apply mc_call_ret_hi_disjoint].
      - apply in_app_iff in Hin as [Hext | Hal].
        + unfold ext in Hext; destruct opt_hi as [hn |]; [| contradiction Hext].
          destruct Hext as [Heq | []]; inversion Heq; subst nm w; pose proof (Hopt_hi_nm hn eq_refl) as ->.
          split; [intro H; symmetry in H; apply (mc_call_ret_hi_disjoint _ _ _ H)
                 | intro H; apply mc_call_hi_var_inj in H; lia].
        + exact (Hfresh nm w Hal k' w' ltac:(lia)). }
    assert (Hag_rf_ret : a64_val_regs_agrees penv1 dummy_freeze_oracle rf0 sp0
                           (a64_post_call_vrf cid c vrf) rf_ret).
    { intro r; unfold a64_val_read, a64_post_call_vrf; rewrite Epc.
      destruct (N.leb 31%N r) eqn:E31.
      - unfold a64_read_reg; rewrite E31; cbn [mc_sym_val_agrees].
        rewrite eval_ce_const, repr_zero_N; reflexivity.
      - destruct (N.eqb r 0%N) eqn:Er0.
        + apply N.eqb_eq in Er0; subst r; cbn [mc_sym_val_agrees].
          unfold a64_read_reg; cbn [N.leb].
          eapply mc_post_call_ret_expr_sound; [exact Hcrw | exact Epc | exact Habi_c | |].
          * unfold penv1; apply overlay_penv_lookup_in; [exact Hnd_step | left; reflexivity].
          * destruct opt_hi as [hn |] eqn:Ehi; [| exact I].
            unfold penv1; apply overlay_penv_lookup_in; [exact Hnd_step | right; left; reflexivity].
        + destruct (N.leb 19%N r && N.leb r 29%N) eqn:E19; [| exact I].
          apply andb_true_iff in E19 as [H19 H29].
          assert (Hcs : a64_is_callee_saved r = true).
          { unfold a64_is_callee_saved; rewrite H19; apply N.leb_le in H29; apply N.leb_le; lia. }
          assert (Hr_ne30 : r <> 30%N) by (apply N.leb_le in H29; lia).
          pose proof (Hag_rf r) as Hr; unfold a64_val_read in Hr; rewrite E31 in Hr.
          assert (Hrf_eqr : a64_read_reg r rf_ret = a64_read_reg r rf).
          { unfold a64_read_reg; rewrite E31; rewrite (Hpres_c r Hcs).
            unfold rf_link, a64_write_reg; change (N.leb 31%N 30%N) with false; cbn [N.eqb]; destruct (N.eqb r 30%N) eqn:E30;
              [apply N.eqb_eq in E30; contradiction | reflexivity]. }
          rewrite Hrf_eqr.
          destruct (vrf r) as [| e | |] eqn:Evr; try exact Hr.
          pose proof (Hvrf r) as Hwr; unfold a64_val_read in Hwr; rewrite E31, Evr in Hwr.
          destruct Hwr as (_ & _ & Hlf_e & Hsub_e); cbn [mc_sym_val_agrees] in Hr |- *.
          unfold eval_closed_cert_expr in *; erewrite mcc_eval_cert_expr_penv_agree; [exact Hr | exact Hlf_e |].
          intros nm0 w0 Hnm0; exact (Hp1_al nm0 w0 (vars_subset_b_incl _ _ Hsub_e _ Hnm0)). }
    assert (Hag_stk1 : mc_sym_stack_agrees penv1 dummy_freeze_oracle (fun r => a64_read_reg r rf0) sp0 astk mstk)
      by (eapply (mc_sym_stack_agrees_penv_agree penv0 penv1); [exact Hastk | intros nm w H; symmetry; exact (Hp1_al nm w H) | exact Hag_stk]).
    destruct (IH callees (pt_add_n pc visited) next_pc (S cid) sp_off
                 (a64_post_call_vrf cid c vrf) astk sfl false ret_w allowed' cont
                 O penv1 rf0 sp0 rf_ret sp fl_ret mstk
                 Hrw Hcws Hval HO Hsp0 Hrng Hsp Hvrf' Hastk' (fun C : false = true => ltac:(discriminate C))
                 Hfresh' Hag_rf_ret Hag_stk1 (fun C : false = true => ltac:(discriminate C)) Ect)
      as (tr_r & nb_r & rf_end & fl_end & mstk_end & Hnd_r & Hdisj_r & Hkge_r & Hcv_r & Hexec_r & Hpres_r & Hpath_r).
    exists ((cname, rf_link, a64_read_reg 0%N rf_ret) :: tr_r), (step_binds ++ nb_r), rf_end, fl_end, mstk_end.
    assert (Hdisj_sr : forall nm, In nm (List.map fst step_binds) -> ~ In nm (List.map fst nb_r)).
    { intros nm Hst Hin_r; destruct (Hkge_r nm Hin_r) as [k' [Hk' Hnm']].
      assert (Hex : exists w', In (nm, w') allowed').
      { unfold step_binds in Hst; destruct opt_hi as [hn |] eqn:Ehi; cbn [List.map fst] in Hst.
        - destruct Hst as [<- | [<- | []]].
          + exists (mcs_ret_width c); left; reflexivity.
          + exists 64%positive; right; left; reflexivity.
        - destruct Hst as [<- | []]; exists (mcs_ret_width c); left; reflexivity. }
      destruct Hex as [w' Hw'].
      destruct Hnm' as [[w'' Heq] | Heq];
        [pose proof (Hfresh' nm w' Hw' k' w'' Hk') as [Hne _]; exact (Hne Heq)
        | pose proof (Hfresh' nm w' Hw' k' 1%positive Hk') as [_ Hne]; exact (Hne Heq)]. }
    repeat split.
    + rewrite List.map_app; apply NoDup_app_intro; assumption.
    + apply binds_disjoint_app; [exact Hdisj_step |].
      intros nm w Hin; exact (Hdisj_r nm w (Hinc _ Hin)).
    + intros nm Hin; rewrite List.map_app in Hin; apply in_app_iff in Hin as [Hst | Hr].
      * unfold step_binds in Hst; destruct opt_hi as [hn |]; cbn [List.map fst] in Hst.
        -- destruct Hst as [<- | [<- | []]].
           ++ exists cid; split; [lia | left; exists (mcs_ret_width c); reflexivity].
           ++ pose proof (Hopt_hi_nm hn eq_refl) as ->; exists cid; split; [lia | right; reflexivity].
        -- destruct Hst as [<- | []]; exists cid; split; [lia | left; exists (mcs_ret_width c); reflexivity].
      * destruct (Hkge_r nm Hr) as [k [Hk Hnm]]; exists k; split; [lia | exact Hnm].
    + intros nm dv Hin; apply in_app_iff in Hin as [Hst | Hr].
      * unfold step_binds in Hst; destruct opt_hi as [hn |] eqn:Ehi.
        -- destruct Hst as [Heq | [Heq | []]]; inversion Heq; subst nm dv.
           ++ exists (mcs_ret_width c); split;
                [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; right; left; reflexivity
                | exists v_ret; reflexivity].
           ++ exists 64%positive; split;
                [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; right; right; left; reflexivity
                | exists (a64_read_reg 0%N rf_ret); reflexivity].
        -- destruct Hst as [Heq | []]; inversion Heq; subst nm dv.
           exists (mcs_ret_width c); split;
             [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; right; left; reflexivity
             | exists v_ret; reflexivity].
      * destruct (Hcv_r nm dv Hr) as (w & Hcm & Hv); exists w; split;
          [unfold collect_mc_call_vars; cbn [collect_mc_call_vars_acc]; rewrite collect_mc_call_vars_acc_shift; apply in_or_app; left; exact Hcm
          | exact Hv].
    + cbn [a64_exec_with_calls]; rewrite Hlk, Edi, Hsp_eq_off, Esp_al.
      fold next_pc rf_link; rewrite HO_eq; cbn [fst snd]; rewrite Hexec_r; reflexivity.
    + exact Hpres_r.
    + intros extra Hdx Hnx.
      cbn [List.map] in *.
      assert (Hfc : find_callee_spec callees cname = Some c) by exact Efc.
      rewrite Hfc.
      assert (Hargs_eval : Forall2 (fun e64 v64 =>
        eval_closed_cert_expr (overlay_penv ((step_binds ++ nb_r) ++ extra) penv0) dummy_freeze_oracle e64 =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)))
        aes
        (List.map (fun j => a64_read_reg (N.of_nat j) rf_link) (seq 0 (List.length (mcs_args c))))).
      { assert (Hrf_arg_eq : List.map (fun j => a64_read_reg (N.of_nat j) rf_link) (seq 0 (List.length (mcs_args c))) =
                             List.map (fun j => a64_read_reg (N.of_nat j) rf) (seq 0 (List.length (mcs_args c)))).
        { apply map_ext_in; intros j Hj; apply in_seq in Hj as [_ Hj].
          unfold rf_link, a64_read_reg, a64_write_reg; change (N.leb 31%N 30%N) with false.
          destruct (N.leb 31%N (N.of_nat j)) eqn:E31; [reflexivity |].
          destruct (N.eqb (N.of_nat j) 30%N) eqn:E30; [apply N.eqb_eq in E30; lia | reflexivity]. }
        rewrite Hrf_arg_eq.
        pose proof (a64_sym_read_call_args_from_sound pc cname penv0 dummy_freeze_oracle rf0 sp0 vrf rf 0%N
                      (List.length (mcs_args c)) aes Hag_rf Eargs) as Hs_args.
        replace (List.map (fun k => a64_read_reg (0%N + N.of_nat k) rf) (seq 0 (List.length (mcs_args c))))
          with (List.map (fun k => a64_read_reg (N.of_nat k) rf) (seq 0 (List.length (mcs_args c)))) in Hs_args
          by (apply map_ext; intro k; reflexivity).
        pose proof (a64_sym_read_call_args_from_wf pc cname allowed 0%N (List.length (mcs_args c)) vrf aes Hvrf Eargs) as Hwf_args.
        assert (Hfa_ev : forall e64 v64,
          wf_sym_expr allowed 64%positive e64 ->
          eval_closed_cert_expr penv0 dummy_freeze_oracle e64 = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) ->
          eval_closed_cert_expr (overlay_penv ((step_binds ++ nb_r) ++ extra) penv0) dummy_freeze_oracle e64 =
          raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64))).
        { intros e64 v64 (_ & _ & Hlf_a & Hsub_a) Hev; unfold eval_closed_cert_expr in *.
          assert (Hdisj_all : binds_disjoint_from allowed ((step_binds ++ nb_r) ++ extra))
            by (apply binds_disjoint_app; [apply binds_disjoint_app; [exact Hdisj_step | intros x wx Hx; exact (Hdisj_r x wx (Hinc _ Hx))] | exact Hdx]).
          erewrite mcc_eval_cert_expr_penv_agree; [exact Hev | exact Hlf_a |].
          intros nm w Hnm; exact (overlay_penv_disjoint_allowed _ penv0 allowed Hdisj_all nm w (vars_subset_b_incl _ _ Hsub_a _ Hnm)). }
        clear -Hwf_args Hs_args Hfa_ev; induction Hs_args; [constructor |].
        inversion Hwf_args as [| ? ? Hw0 Hwr]; subst; constructor; [exact (Hfa_ev _ _ Hw0 H) | exact (IHHs_args Hwr)]. }
      eapply MTPO_Call; [exact Hargs_eval | | symmetry; exact (proj1 Habi_c) |].
      * unfold penv1; rewrite <- app_assoc, overlay_penv_app;
          unfold step_binds; cbn [overlay_penv]; rewrite String.eqb_refl; reflexivity.
      * assert (Hdx_r : binds_disjoint_from allowed' extra).
        { intros nm w Hin Hina; destruct Hin as [Heq | Hin].
          - inversion Heq; subst nm w; apply (Hnx (mc_call_ret_var cid (mcs_ret_width c)));
              [rewrite List.map_app; apply in_or_app; left; left; reflexivity | exact Hina].
          - apply in_app_iff in Hin as [Hext | Hal].
            + unfold ext in Hext; destruct opt_hi as [hn |]; [| contradiction Hext].
              destruct Hext as [Heq | []]; inversion Heq; subst nm w; apply (Hnx hn);
                [rewrite List.map_app; apply in_or_app; left; right; left; reflexivity | exact Hina].
            + exact (Hdx nm w Hal Hina). }
        assert (Hnx_r : forall nm, In nm (List.map fst nb_r) -> ~ In nm (List.map fst extra)).
        { intros nm Hin; apply Hnx; rewrite List.map_app; apply in_or_app; right; exact Hin. }
        specialize (Hpath_r extra Hdx_r Hnx_r).
        assert (Henv_eq : forall nm,
          overlay_penv (nb_r ++ extra) penv1 nm =
          overlay_penv ((step_binds ++ nb_r) ++ extra) penv0 nm).
        { intro nm; unfold penv1; rewrite <- app_assoc; repeat rewrite overlay_penv_app.
          destruct (in_dec string_dec nm (List.map fst nb_r)) as [Hin_r | Hnin_r].
          - rewrite (overlay_penv_not_in step_binds _ nm).
            + clear -Hin_r; induction nb_r as [| [x dv] rest IHnb]; cbn in *; [contradiction |].
              destruct (String.eqb nm x) eqn:Ex; [reflexivity |].
              apply IHnb; destruct Hin_r as [-> | Hr]; [rewrite String.eqb_refl in Ex; discriminate Ex | exact Hr].
            + intro Hs; exact (Hdisj_sr nm Hs Hin_r).
          - rewrite !overlay_penv_not_in by exact Hnin_r.
            destruct (in_dec string_dec nm (List.map fst step_binds)) as [Hin_s | Hnin_s].
            + rewrite (overlay_penv_not_in extra _ nm) by (apply Hnx; rewrite List.map_app; apply in_or_app; left; exact Hin_s).
              clear -Hin_s; induction step_binds as [| [x dv] rest IHst]; cbn in *;
                [exfalso; exact Hin_s |].
              destruct (String.eqb nm x) eqn:Ex; [reflexivity |].
              apply IHst; destruct Hin_s as [<- | Hs]; [rewrite String.eqb_refl in Ex; discriminate Ex | exact Hs].
            + rewrite (overlay_penv_not_in step_binds _ nm Hnin_s).
              rewrite overlay_penv_app, (overlay_penv_not_in nb_r _ nm Hnin_r).
              clear -Hnin_s; induction extra as [| [x dv] rest IHe]; cbn [overlay_penv];
                [exact (overlay_penv_not_in step_binds penv0 nm Hnin_s)
                | destruct (String.eqb nm x); [reflexivity | exact IHe]]. }
        exact (mc_tree_path_ok_extensional _ _ _ _ _ _ _ Henv_eq Hpath_r).
Qed.

