(* Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
   Licensed under the LLVMCert Non-Commercial Evaluation & Research License
   or a separate LLVMCert Commercial Software License Agreement.
   See /LICENSE in the repository root for details. *)

(** * Loop Cutpoint MC Tree, Validators & CNF Emitters ([CertValidator.McLoopCheck])

    Purpose:
      Implements shared MC loop trees ([mc_seg_tree]), cutpoint/skeleton state builders,
      leaf-pair obligation collection ([collect_mc_ir_obls]), and end-to-end loop validators
      and CNF emitters ([validate_mc_loop_rv64], [validate_mc_loop_a64], [emit_mc_loop_cnf_*]).

    Trust Contract & Fail-Closed Boundary:
      Proof-only helper module (re-exported by [McLoop]). [validate_mc_loop_rv64] and
      [validate_mc_loop_a64] fail closed ([inl err]) on ill-formed loop specs, freeze or
      skeleton violations, IR/MC reification errors, or failed LRAT obligation discharge.

    Assumptions:
      [Stdlib], [Vellvm], [CertValidator.common.Diag], and [CertValidator] core, RV64/A64
      loop-seg, [McFormat], [McOblDischarger], and [McLoopIrSpec] modules; zero custom axioms.

    Section Outline:
      4. Shared [mc_seg_tree], cutpoint/skeleton states & [collect_mc_ir_obls_sound]; 5. Loop
      validators & CNF emitters ([validate_mc_loop_*], [emit_mc_loop_cnf_*]). *)

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
  Syntax.RawIdMaps
  Semantics.Interfaces.Params
  Semantics.EOU
  Semantics.VellvmIntegers
  Semantics.DynamicValues
  Semantics.Attributes
  Semantics.Denotation
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
  McLoopIrSpec.

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

(** ** 4. Shared MC Tree, Cutpoint/Skeleton States & Obligation Collection *)

Definition ir_seg_exprs_freeze_free_cut (phis : list (positive * cert_expr)) : bool :=
  forallb (fun '(_, ce) => negb (expr_has_freeze ce)) phis.

Fixpoint ir_seg_freeze_free (t : ir_seg_tree) : bool :=
  match t with
  | IST_Cut _ phis => ir_seg_exprs_freeze_free_cut phis
  | IST_Ret _ ret_e => negb (expr_has_freeze ret_e)
  | IST_UB => true
  | IST_Branch cond dt df =>
      negb (expr_has_freeze cond) && ir_seg_freeze_free dt && ir_seg_freeze_free df
  end.

Lemma binop_flags_weaken_refl : forall fl,
  binop_flags_weaken fl fl = true.
Proof.
  intros [nuw nsw ex disj]; unfold binop_flags_weaken; cbn.
  destruct nuw, nsw, ex, disj; reflexivity.
Qed.

Lemma cast_flags_weaken_refl : forall fl,
  cast_flags_weaken fl fl = true.
Proof.
  intros [nn nu ns]; unfold cast_flags_weaken; cbn.
  destruct nn, nu, ns; reflexivity.
Qed.

Lemma eval_cert_expr_refine_mono {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) foracle e,
    wt_cert_expr [] e = true ->
    is_let_free_expr e = true ->
    ub_free_expr e = true ->
    expr_has_freeze e = false ->
    (forall nm w, In (nm, w) (collect_free_vars [] e) ->
       exists d1 d2 : @dvalue Pa,
         penv1 nm = Some d1 /\
         penv2 nm = Some d2 /\
         wf_scalar_dvalue w d1 /\
         wf_scalar_dvalue w d2 /\
         dvalue_refines d1 d2) ->
    exists v1 v2 : @dvalue Pa,
      eval_closed_cert_expr penv1 foracle e = raise_ret v1 /\
      eval_closed_cert_expr penv2 foracle e = raise_ret v2 /\
      wf_scalar_dvalue (cert_expr_bit_width e) v1 /\
      wf_scalar_dvalue (cert_expr_bit_width e) v2 /\
      dvalue_refines v1 v2.
Proof.
  intros penv1 penv2 foracle e.
  induction e as
    [ w val | w | nm w
    | op w fl l IHl r IHr
    | pr ss w l IHl r IHr
    | k fw tw fl o IHo
    | w c IHc t IHt f IHf
    | w o _
    | bs body _ _ ] using cert_expr_ind_nested;
    intros Hwt Hlf Hub Hnfrz Hvars;
    unfold eval_closed_cert_expr in *;
    cbn [wt_cert_expr cert_expr_bit_width is_let_free_expr ub_free_expr expr_has_freeze collect_free_vars eval_cert_expr lookup_let_val] in *.
  - eexists _, _; repeat split; try reflexivity;
      [right; eexists; reflexivity | right; eexists; reflexivity | apply dvalue_refines_refl].
  - eexists _, _; repeat split; try reflexivity;
      [left; reflexivity | left; reflexivity | apply dvalue_refines_refl].
  - destruct (Hvars nm w (or_introl eq_refl)) as (d1 & d2 & Hp1 & Hp2 & Hwf1 & Hwf2 & Href).
    rewrite Hp1, Hp2.
    assert (Hck1 : check_scalar_width w d1 = raise_ret d1)
      by (destruct Hwf1 as [-> | [i1 ->]]; cbn; rewrite ?Pos.eqb_refl; reflexivity).
    assert (Hck2 : check_scalar_width w d2 = raise_ret d2)
      by (destruct Hwf2 as [-> | [i2 ->]]; cbn; rewrite ?Pos.eqb_refl; reflexivity).
    rewrite Hck1, Hck2; eexists _, _; repeat split; assumption.
  - rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf; rewrite !andb_true_iff in Hub.
    apply orb_false_iff in Hnfrz as [Hnf_l Hnf_r].
    destruct Hwt as ((((Hsh & Hwtl) & Hwtr) & Hbw1) & Hbw2); apply Pos.eqb_eq in Hbw1; apply Pos.eqb_eq in Hbw2.
    destruct Hlf as [Hlfl Hlfr]; destruct Hub as [[Hnop Hubl] Hubr].
    destruct (IHl Hwtl Hlfl Hubl Hnf_l (fun x wx Hx => Hvars x wx (in_or_app _ _ _ (or_introl Hx))))
      as (vl1 & vl2 & El1 & El2 & Wl1 & Wl2 & Rl).
    destruct (IHr Hwtr Hlfr Hubr Hnf_r (fun x wx Hx => Hvars x wx (in_or_app _ _ _ (or_intror Hx))))
      as (vr1 & vr2 & Er1 & Er2 & Wr1 & Wr2 & Rr).
    rewrite Hbw1 in Wl1, Wl2; rewrite Hbw2 in Wr1, Wr2; apply negb_true_iff in Hnop.
    destruct (eval_iop_non_div_rem_no_ub op fl w vl1 vr1 Hnop Wl1 Wr1) as [v1 [Ev1 W1]].
    destruct (eval_iop_non_div_rem_no_ub op fl w vl2 vr2 Hnop Wl2 Wr2) as [v2 [Ev2 W2]].
    pose proof (eval_iop_non_div_rem_monotone op fl fl w vl1 vl2 vr1 vr2 Hnop (binop_flags_weaken_refl fl) Wl1 Wl2 Wr1 Wr2 Rl Rr) as Hm.
    rewrite El1, El2, Er1, Er2; cbn [eou_bind]; rewrite Ev1, Ev2 in Hm |- *; cbn [refine_eou_dvalue] in Hm.
    eexists _, _; repeat split; assumption.
  - rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf; rewrite !andb_true_iff in Hub.
    apply orb_false_iff in Hnfrz as [Hnf_l Hnf_r].
    destruct Hwt as (((Hwtl & Hwtr) & Hbw1) & Hbw2); apply Pos.eqb_eq in Hbw1; apply Pos.eqb_eq in Hbw2.
    destruct Hlf as [Hlfl Hlfr]; destruct Hub as [Hubl Hubr].
    destruct (IHl Hwtl Hlfl Hubl Hnf_l (fun x wx Hx => Hvars x wx (in_or_app _ _ _ (or_introl Hx))))
      as (vl1 & vl2 & El1 & El2 & Wl1 & Wl2 & Rl).
    destruct (IHr Hwtr Hlfr Hubr Hnf_r (fun x wx Hx => Hvars x wx (in_or_app _ _ _ (or_intror Hx))))
      as (vr1 & vr2 & Er1 & Er2 & Wr1 & Wr2 & Rr).
    rewrite Hbw1 in Wl1, Wl2; rewrite Hbw2 in Wr1, Wr2.
    destruct (eval_icmp_wf_scalar ss pr w vl1 vr1 Wl1 Wr1) as [v1 [Ev1 W1]].
    destruct (eval_icmp_wf_scalar ss pr w vl2 vr2 Wl2 Wr2) as [v2 [Ev2 W2]].
    assert (Himp : implb ss ss = true) by (destruct ss; reflexivity).
    pose proof (eval_icmp_monotone ss ss pr w vl1 vl2 vr1 vr2 Himp Wl1 Wl2 Wr1 Wr2 Rl Rr) as Hm.
    rewrite El1, El2, Er1, Er2; cbn [eou_bind]; rewrite Ev1, Ev2 in Hm |- *; cbn [refine_eou_dvalue] in Hm.
    eexists _, _; repeat split; assumption.
  - rewrite !andb_true_iff in Hwt; destruct Hwt as [[Hck Hwto] Hbwo]; apply Pos.eqb_eq in Hbwo.
    destruct (IHo Hwto Hlf Hub Hnfrz Hvars) as (vo1 & vo2 & Eo1 & Eo2 & Wo1 & Wo2 & Ro).
    rewrite Hbwo in Wo1, Wo2.
    destruct (eval_cast_wf_scalar k fw tw fl vo1 Hck Wo1) as [v1 [Ev1 W1]].
    destruct (eval_cast_wf_scalar k fw tw fl vo2 Hck Wo2) as [v2 [Ev2 W2]].
    pose proof (eval_cast_monotone k fw tw fl fl vo1 vo2 Hck Hck (cast_flags_weaken_refl fl) Wo1 Wo2 Ro) as Hm.
    rewrite Eo1, Eo2; cbn [eou_bind]; rewrite Ev1, Ev2 in Hm |- *; cbn [refine_eou_dvalue] in Hm.
    eexists _, _; repeat split; assumption.
  - rewrite !andb_true_iff in Hwt; rewrite !andb_true_iff in Hlf; rewrite !andb_true_iff in Hub.
    apply orb_false_iff in Hnfrz as [Hnf_ct Hnf_f]; apply orb_false_iff in Hnf_ct as [Hnf_c Hnf_t].
    destruct Hwt as (((((Hwtc & Hwtt) & Hwtf) & Hbwc) & Hbwt) & Hbwf).
    apply Pos.eqb_eq in Hbwc; apply Pos.eqb_eq in Hbwt; apply Pos.eqb_eq in Hbwf.
    destruct Hlf as [[Hlfc Hlft] Hlff]; destruct Hub as [[Hubc Hubt] Hubf].
    destruct (IHc Hwtc Hlfc Hubc Hnf_c (fun x wx Hx => Hvars x wx (in_or_app _ _ _ (or_introl Hx))))
      as (vc1 & vc2 & Ec1 & Ec2 & Wc1 & Wc2 & Rc).
    destruct (IHt Hwtt Hlft Hubt Hnf_t (fun x wx Hx => Hvars x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hx))))))
      as (vt1 & vt2 & Et1 & Et2 & Wt1 & Wt2 & Rt).
    destruct (IHf Hwtf Hlff Hubf Hnf_f (fun x wx Hx => Hvars x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hx))))))
      as (vf1 & vf2 & Ef1 & Ef2 & Wf1 & Wf2 & Rf).
    rewrite Hbwc in Wc1, Wc2; rewrite Hbwt in Wt1, Wt2; rewrite Hbwf in Wf1, Wf2.
    destruct (eval_select_wf_scalar w vc1 vt1 vf1 Wc1 Wt1 Wf1) as [v1 [Ev1 W1]].
    destruct (eval_select_wf_scalar w vc2 vt2 vf2 Wc2 Wt2 Wf2) as [v2 [Ev2 W2]].
    pose proof (eval_select_monotone w vc1 vc2 vt1 vt2 vf1 vf2 Wc1 Wc2 Wt1 Wt2 Wf1 Wf2 Rc Rt Rf) as Hm.
    rewrite Ec1, Ec2, Et1, Et2, Ef1, Ef2; cbn [eou_bind]; rewrite Ev1, Ev2 in Hm |- *; cbn [refine_eou_dvalue] in Hm.
    eexists _, _; repeat split; assumption.
  - discriminate Hnfrz.
  - discriminate Hlf.
Qed.

Inductive mc_seg_tree : Type :=
| MST_Cut (sp_off : Z) (rr : N -> mc_sym_val) (astk : mc_sym_stack)
| MST_Ret (ret_e : cert_expr)
| MST_Branch (cond : cert_expr) (dt df : mc_seg_tree).

Fixpoint rv_seg_to_mc_seg (t : rv_seg_tree) : mc_seg_tree :=
  match t with
  | RST_Cut sp vrf stk => MST_Cut sp (fun r => rv_val_read r vrf) stk
  | RST_Ret ret_e => MST_Ret ret_e
  | RST_Branch cond dt df => MST_Branch cond (rv_seg_to_mc_seg dt) (rv_seg_to_mc_seg df)
  end.

Fixpoint a64_seg_to_mc_seg (t : a64_seg_tree) : mc_seg_tree :=
  match t with
  | AST_Cut sp vrf stk => MST_Cut sp (fun r => a64_val_read r vrf) stk
  | AST_Ret ret_e => MST_Ret ret_e
  | AST_Branch cond dt df => MST_Branch cond (a64_seg_to_mc_seg dt) (a64_seg_to_mc_seg df)
  end.

Fixpoint mc_seg_holds {Pa : Params}
  (penv : param_env Pa) (foracle : freeze_oracle)
  (P_cut : Z -> (N -> mc_sym_val) -> mc_sym_stack -> Prop)
  (P_ret : cert_expr -> Prop)
  (t : mc_seg_tree) {struct t} : Prop :=
  match t with
  | MST_Cut sp rr astk => P_cut sp rr astk
  | MST_Ret ret_e => P_ret ret_e
  | MST_Branch cond dt df =>
      exists b : bool,
        eval_closed_cert_expr penv foracle cond =
          raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive
            (if b then @Integers.one 1%positive else @Integers.zero 1%positive))) /\
        mc_seg_holds penv foracle P_cut P_ret (if b then dt else df)
  end.

Lemma rv_seg_exec_to_mc {Pa : Params} :
  forall penv foracle insts cut_pc req_step pc rf0 rf mstk ret_w (t : rv_seg_tree),
    @rv_seg_exec_spec Pa penv foracle insts cut_pc req_step pc rf0 rf mstk ret_w t ->
    mc_seg_holds penv foracle
      (fun sp_off' rr' astk' =>
         exists n rf' mstk',
           (req_step = true -> (1 <= n)%nat) /\
           rv_exec_steps n insts (rv_read_reg 2%N rf0) pc rf mstk = Some (cut_pc, rf', mstk') /\
           (- mc_frame_cap <= sp_off' <= 0)%Z /\
           rr' 2%N = MSV_StackPtr sp_off' /\
           (forall r, mc_sym_val_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0) (rr' r) (rv_read_reg r rf')) /\
           mc_sym_stack_agrees penv foracle (fun r0 => rv_read_reg r0 rf0) (rv_read_reg 2%N rf0) astk' mstk')
      (fun ret_e =>
         exists fuel_end rf_end mstk_end,
           rv_exec_mem fuel_end insts pc (rv_read_reg 2%N rf0) rf mstk = Some (rf_end, mstk_end) /\
           rv_callee_saved_preserved rf0 rf_end /\
           rf_end 1%N = rf0 1%N /\
           eval_closed_cert_expr penv foracle ret_e =
             raise_ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (rf_end 10%N)))))
      (rv_seg_to_mc_seg t).
Proof.
  intros penv foracle insts cut_pc req_step pc rf0 rf mstk ret_w t.
  induction t as [sp' vrf' astk' | ret_e | cond dt IHt df IHf];
    intro Hspec; cbn [rv_seg_exec_spec rv_seg_to_mc_seg mc_seg_holds] in *.
  - exact Hspec.
  - exact Hspec.
  - destruct Hspec as [b [Hbc Hsub]]; exists b; split; [exact Hbc |].
    destruct b; [exact (IHt Hsub) | exact (IHf Hsub)].
Qed.

Lemma a64_seg_exec_to_mc {Pa : Params} :
  forall penv foracle insts cut_pc req_step pc rf0 sp0 rf sp fl mstk ret_w (t : a64_seg_tree),
    @a64_seg_exec_spec Pa penv foracle insts cut_pc req_step pc rf0 sp0 rf sp fl mstk ret_w t ->
    mc_seg_holds penv foracle
      (fun sp_off' rr' astk' =>
         exists n rf' sp' fl' mstk',
           (req_step = true -> (1 <= n)%nat) /\
           a64_exec_steps n insts sp0 pc rf sp fl mstk = Some (cut_pc, rf', sp', fl', mstk') /\
           (- mc_frame_cap <= sp_off' <= 0)%Z /\
           sp' = @Integers.add 64%positive sp0 (@Integers.repr 64%positive sp_off') /\
           (forall r, mc_sym_val_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 (rr' r) (a64_read_reg r rf')) /\
           mc_sym_stack_agrees penv foracle (fun r0 => a64_read_reg r0 rf0) sp0 astk' mstk')
      (fun ret_e =>
         exists fuel_end rf_end fl_end mstk_end,
           a64_exec_mem fuel_end insts pc sp0 rf sp fl mstk = Some (rf_end, sp0, fl_end, mstk_end) /\
           a64_callee_saved_preserved rf0 rf_end /\
           eval_closed_cert_expr penv foracle ret_e =
             raise_ret (DVALUE_Base (@DVALUE_I Pa ret_w (rv_trunc_ret_val ret_w (a64_read_reg 0%N rf_end)))))
      (a64_seg_to_mc_seg t).
Proof.
  intros penv foracle insts cut_pc req_step pc rf0 sp0 rf sp fl mstk ret_w t.
  induction t as [sp' vrf' astk' | ret_e | cond dt IHt df IHf];
    intro Hspec; cbn [a64_seg_exec_spec a64_seg_to_mc_seg mc_seg_holds] in *.
  - exact Hspec.
  - exact Hspec.
  - destruct Hspec as [b [Hbc Hsub]]; exists b; split; [exact Hbc |].
    destruct b; [exact (IHt Hsub) | exact (IHf Hsub)].
Qed.

Fixpoint extract_hdr_phis (phis : list (raw_id * phi dtyp * list (metadata dtyp)))
  : string + list (raw_id * positive) :=
  match phis with
  | [] => inr []
  | (id, Phi _ (DTYPE_Base (DTYPE_I w)) _, _) :: rest =>
      if is_supported_bit_width w then
        match extract_hdr_phis rest with
        | inr rs => inr ((id, w) :: rs)
        | inl err => inl err
        end
      else
        inl (diag "mc-loop-ir"
          ("header phi '" ++ mc_raw_id_name id ++ "' has unsupported bit width i" ++
           diag_pos_dec w))
  | (id, _, _) :: _ =>
      inl (diag "mc-loop-ir"
        ("header phi '" ++ mc_raw_id_name id ++ "' is not a supported scalar integer phi"))
  end.

Definition hi32_vars (ls : mc_loop_spec) : list (string * positive) :=
  List.flat_map (fun rb =>
    if Pos.eqb (mlr_width rb) 32%positive then [(mc_hi_var_name (mlr_reg rb), 64%positive)] else [])
    (ml_regs ls).

Definition cut_reg_expr (rb : mc_loop_reg_bind) : cert_expr :=
  if Pos.eqb (mlr_width rb) 64%positive then mlr_expr rb
  else combine_hi32_expr (CE_Var (mc_hi_var_name (mlr_reg rb)) 64%positive) (mlr_expr rb).

Definition cut_slot_expr (sz : mc_mem_size) (e : cert_expr) : cert_expr :=
  match sz with
  | MS_8 => e
  | _ => CE_Cast CCK_ZExt (mc_mem_bits sz) 64%positive no_cast_flags e
  end.

Definition slot_has_saved_reg (slots : list mc_loop_slot_bind) (r : N) : bool :=
  existsb (fun sb => match sb with MLS_SavedReg _ r0 => N.eqb r0 r | _ => false end) slots.

Definition build_cut_astk (slots : list mc_loop_slot_bind) : mc_sym_stack :=
  List.map (fun sb =>
    match sb with
    | MLS_Expr off sz e => (off, sz, MSV_Expr (cut_slot_expr sz e))
    | MLS_SavedReg off r => (off, MS_8, MSV_SavedReg r)
    end) slots.

Fixpoint build_skel_astk (idx : nat) (slots : list mc_loop_slot_bind) {struct slots} : mc_sym_stack :=
  match slots with
  | [] => []
  | MLS_Expr off sz _ :: rest =>
      (off, sz, MSV_Expr (CE_Var (mc_skel_slot_name idx) 64%positive)) :: build_skel_astk (S idx) rest
  | MLS_SavedReg off r :: rest =>
      (off, MS_8, MSV_SavedReg r) :: build_skel_astk (S idx) rest
  end.

Definition rv_cut_base_vrf (ls : mc_loop_spec) : rv_val_regs :=
  fun r =>
    if N.eqb r 0%N then MSV_Expr (CE_BvConst 64%positive 0%N)
    else if N.eqb r 2%N then MSV_StackPtr (ml_sp_off ls)
    else if n_in_list r rv_preserved_non_sp_regs && negb (slot_has_saved_reg (ml_slots ls) r) then MSV_SavedReg r
    else MSV_Undef.

Definition rv_cut_vrf (ls : mc_loop_spec) : rv_val_regs :=
  List.fold_left (fun vrf rb => rv_val_write (mlr_reg rb) (MSV_Expr (cut_reg_expr rb)) vrf)
    (ml_regs ls) (rv_cut_base_vrf ls).

Definition rv_skel_vrf (ls : mc_loop_spec) : rv_val_regs :=
  List.fold_left (fun vrf rb => rv_val_write (mlr_reg rb) (MSV_Expr (CE_Var (mc_skel_reg_name (mlr_reg rb)) 64%positive)) vrf)
    (ml_regs ls) (rv_cut_base_vrf ls).

Definition a64_cut_base_vrf (ls : mc_loop_spec) : a64_val_regs :=
  fun r =>
    if N.leb 31%N r then MSV_Expr (CE_BvConst 64%positive 0%N)
    else if a64_is_callee_saved r && negb (slot_has_saved_reg (ml_slots ls) r) then MSV_SavedReg r
    else MSV_Undef.

Definition a64_cut_vrf (ls : mc_loop_spec) : a64_val_regs :=
  List.fold_left (fun vrf rb => a64_val_write (mlr_reg rb) (MSV_Expr (cut_reg_expr rb)) vrf)
    (ml_regs ls) (a64_cut_base_vrf ls).

Definition a64_skel_vrf (ls : mc_loop_spec) : a64_val_regs :=
  List.fold_left (fun vrf rb => a64_val_write (mlr_reg rb) (MSV_Expr (CE_Var (mc_skel_reg_name (mlr_reg rb)) 64%positive)) vrf)
    (ml_regs ls) (a64_cut_base_vrf ls).

Definition mc_preserved_regs (arch : elf_arch) : list N :=
  match arch with
  | EA_Riscv64 => rv_preserved_non_sp_regs
  | EA_AArch64 => a64_callee_saved_list
  end.

Definition mc_unspilled_preserved (arch : elf_arch) (ls : mc_loop_spec) : list N :=
  List.filter (fun r =>
    negb (existsb (fun rb => N.eqb (mlr_reg rb) r) (ml_regs ls)) &&
    negb (slot_has_saved_reg (ml_slots ls) r))
    (mc_preserved_regs arch).

Definition mc_sym_val_kind (v : mc_sym_val) : string :=
  match v with
  | MSV_Undef => "undef"
  | MSV_Expr _ => "expr"
  | MSV_SavedReg r => ("saved-reg(x" ++ diag_N_dec r ++ ")")%string
  | MSV_StackPtr off => ("sp-ptr(" ++ diag_Z_dec off ++ ")")%string
  end.

Fixpoint mc_skel_tree_ok (arch : elf_arch) (ls : mc_loop_spec) (t : mc_seg_tree) {struct t} : bool :=
  match t with
  | MST_Cut sp' rr' astk' =>
      Z.eqb sp' (ml_sp_off ls) &&
      forallb (fun r => match rr' r with MSV_SavedReg r0 => N.eqb r0 r | _ => false end)
        (mc_unspilled_preserved arch ls) &&
      forallb (fun sb =>
        match sb with
        | MLS_Expr _ _ _ => true
        | MLS_SavedReg off r =>
            match mc_sym_stk_load off MS_8 false astk' with
            | Some (MSV_SavedReg r0) => N.eqb r0 r
            | _ => false
            end
        end) (ml_slots ls)
  | MST_Ret _ => true
  | MST_Branch _ dt df => mc_skel_tree_ok arch ls dt && mc_skel_tree_ok arch ls df
  end.

Fixpoint check_unspilled_preserved_diag
  (phase : string) (rr' : N -> mc_sym_val) (rs : list N) {struct rs} : string + unit :=
  match rs with
  | [] => inr tt
  | r :: rest =>
      match rr' r with
      | MSV_SavedReg r0 =>
          if N.eqb r0 r then check_unspilled_preserved_diag phase rr' rest
          else
            inl (diag "mc-loop-mc"
              (phase ++ " segment clobbered callee-saved reg x" ++ diag_N_dec r ++
               " (holds saved-reg x" ++ diag_N_dec r0 ++ ")"))
      | v =>
          inl (diag "mc-loop-mc"
            (phase ++ " segment clobbered callee-saved reg x" ++ diag_N_dec r ++
             " (" ++ mc_sym_val_kind v ++ ")"))
      end
  end.

Lemma check_unspilled_preserved_diag_sound : forall phase rr' rs,
  check_unspilled_preserved_diag phase rr' rs = inr tt ->
  forallb (fun r => match rr' r with MSV_SavedReg r0 => N.eqb r0 r | _ => false end) rs = true.
Proof.
  intros phase rr' rs; induction rs as [| r rest IH]; intro H; cbn in *; [reflexivity |].
  destruct (rr' r) as [| | r0 |]; try discriminate H.
  destruct (N.eqb r0 r) eqn:Er; [| discriminate H].
  cbn; exact (IH H).
Qed.

Fixpoint check_saved_slots_diag
  (phase : string) (astk' : mc_sym_stack) (sbs : list mc_loop_slot_bind)
  {struct sbs} : string + unit :=
  match sbs with
  | [] => inr tt
  | MLS_Expr _ _ _ :: rest => check_saved_slots_diag phase astk' rest
  | MLS_SavedReg off r :: rest =>
      match mc_sym_stk_load off MS_8 false astk' with
      | Some (MSV_SavedReg r0) =>
          if N.eqb r0 r then check_saved_slots_diag phase astk' rest
          else
            inl (diag "mc-loop-mc"
              (phase ++ " segment saved-reg stack slot at sp+" ++ diag_Z_dec off ++
               " holds saved x" ++ diag_N_dec r0 ++ ", expected x" ++ diag_N_dec r))
      | Some v =>
          inl (diag "mc-loop-mc"
            (phase ++ " segment saved-reg stack slot at sp+" ++ diag_Z_dec off ++
             " corrupted (" ++ mc_sym_val_kind v ++ ", expected saved x" ++ diag_N_dec r ++ ")"))
      | None =>
          inl (diag "mc-loop-mc"
            (phase ++ " segment saved-reg stack slot at sp+" ++ diag_Z_dec off ++
             " is unmapped (expected saved x" ++ diag_N_dec r ++ ")"))
      end
  end.

Lemma check_saved_slots_diag_sound : forall phase astk' sbs,
  check_saved_slots_diag phase astk' sbs = inr tt ->
  forallb (fun sb =>
    match sb with
    | MLS_Expr _ _ _ => true
    | MLS_SavedReg off r =>
        match mc_sym_stk_load off MS_8 false astk' with
        | Some (MSV_SavedReg r0) => N.eqb r0 r
        | _ => false
        end
    end) sbs = true.
Proof.
  intros phase astk' sbs; induction sbs as [| [off sz e | off r] rest IH]; intro H; cbn in *;
    [reflexivity | exact (IH H) |].
  destruct (mc_sym_stk_load off MS_8 false astk') as [[| | r0 |] |]; try discriminate H.
  destruct (N.eqb r0 r); [cbn; exact (IH H) | discriminate H].
Qed.

Fixpoint check_mc_skel_tree_diag
  (phase : string) (arch : elf_arch) (ls : mc_loop_spec) (t : mc_seg_tree) {struct t} : string + unit :=
  match t with
  | MST_Cut sp' rr' astk' =>
      if negb (Z.eqb sp' (ml_sp_off ls)) then
        inl (diag "mc-loop-mc"
          (phase ++ " segment reached cutpoint with sp-off=" ++ diag_Z_dec sp' ++
           ", expected " ++ diag_Z_dec (ml_sp_off ls)))
      else
        bind_err (check_unspilled_preserved_diag phase rr' (mc_unspilled_preserved arch ls)) (fun _ =>
        check_saved_slots_diag phase astk' (ml_slots ls))
  | MST_Ret _ => inr tt
  | MST_Branch _ dt df =>
      bind_err (check_mc_skel_tree_diag phase arch ls dt) (fun _ =>
      check_mc_skel_tree_diag phase arch ls df)
  end.

Lemma check_mc_skel_tree_diag_sound : forall phase arch ls t,
  check_mc_skel_tree_diag phase arch ls t = inr tt ->
  mc_skel_tree_ok arch ls t = true.
Proof.
  intros phase arch ls t; induction t as [sp' rr' astk' | ret_e | cond dt IHt df IHf];
    intro H; cbn in *.
  - destruct (Z.eqb sp' (ml_sp_off ls)) eqn:Hsp; cbn [negb] in H; [| discriminate H].
    destruct (check_unspilled_preserved_diag phase rr' (mc_unspilled_preserved arch ls))
      as [| []] eqn:Hu; cbn [bind_err] in H; [discriminate H |].
    rewrite (check_unspilled_preserved_diag_sound _ _ _ Hu),
            (check_saved_slots_diag_sound _ _ _ H); reflexivity.
  - reflexivity.
  - destruct (check_mc_skel_tree_diag phase arch ls dt) as [| []] eqn:Ht;
      cbn [bind_err] in H; [discriminate H |].
    rewrite (IHt eq_refl), (IHf H); reflexivity.
Qed.

Definition expr_has_var (nm : string) (e : cert_expr) : bool :=
  existsb (fun '(x, _) => String.eqb x nm) (collect_free_vars [] e).

Definition is_exact_cut_var (k : nat) (w : positive) (e : cert_expr) : bool :=
  match e with
  | CE_Var nm w' => String.eqb nm (mc_cut_var_name k) && Pos.eqb w w'
  | _ => false
  end.

Definition reg_slot_uses_cut_var_ok (k : nat) (w : positive) (e : cert_expr) : bool :=
  negb (expr_has_var (mc_cut_var_name k) e) || is_exact_cut_var k w e.

Fixpoint mc_count_tr_acc {A : Type} (p : A -> bool) (acc : nat) (xs : list A) {struct xs} : nat :=
  match xs with
  | [] => acc
  | x :: rest => mc_count_tr_acc p (if p x then S acc else acc) rest
  end.

Definition mc_count_tr {A : Type} (p : A -> bool) (xs : list A) : nat :=
  mc_count_tr_acc p 0%nat xs.

Lemma mc_count_tr_acc_eq : forall {A : Type} (p : A -> bool) (acc : nat) (xs : list A),
  mc_count_tr_acc p acc xs = (acc + List.length (List.filter p xs))%nat.
Proof.
  intros A p acc xs; revert acc; induction xs as [| x rest IH]; intro acc;
    cbn [mc_count_tr_acc List.filter List.length].
  - lia.
  - destruct (p x); rewrite IH; cbn [List.length]; lia.
Qed.

Lemma mc_count_tr_eq : forall {A : Type} (p : A -> bool) (xs : list A),
  mc_count_tr p xs = List.length (List.filter p xs).
Proof.
  intros A p xs; unfold mc_count_tr; exact (mc_count_tr_acc_eq p 0%nat xs).
Qed.

Definition cut_var_bind_count (k : nat) (rbs : list mc_loop_reg_bind) (sbs : list mc_loop_slot_bind) : nat :=
  mc_count_tr (fun rb => expr_has_var (mc_cut_var_name k) (mlr_expr rb)) rbs +
  mc_count_tr (fun sb => match sb with MLS_Expr _ _ e => expr_has_var (mc_cut_var_name k) e | MLS_SavedReg _ _ => false end) sbs.

Fixpoint check_cut_var_regs_acc
  (k : nat) (w : positive) (seen : bool) (rbs : list mc_loop_reg_bind)
  {struct rbs} : option bool :=
  match rbs with
  | [] => Some seen
  | rb :: rest =>
      let e := mlr_expr rb in
      if is_exact_cut_var k w e then
        if seen then None else check_cut_var_regs_acc k w true rest
      else if expr_has_var (mc_cut_var_name k) e then None
      else check_cut_var_regs_acc k w seen rest
  end.

Fixpoint check_cut_var_slots_acc
  (k : nat) (w : positive) (seen : bool) (sbs : list mc_loop_slot_bind)
  {struct sbs} : option bool :=
  match sbs with
  | [] => Some seen
  | MLS_SavedReg _ _ :: rest => check_cut_var_slots_acc k w seen rest
  | MLS_Expr _ _ e :: rest =>
      if is_exact_cut_var k w e then
        if seen then None else check_cut_var_slots_acc k w true rest
      else if expr_has_var (mc_cut_var_name k) e then None
      else check_cut_var_slots_acc k w seen rest
  end.

Definition cut_var_ptol (ls : mc_loop_spec) (k : nat) (w : positive) : bool :=
  match ml_inv ls with
  | None => true
  | Some inv_e => negb (expr_has_var (mc_cut_var_name k) inv_e)
  end &&
  match check_cut_var_regs_acc k w false (ml_regs ls) with
  | None => false
  | Some seen1 =>
      match check_cut_var_slots_acc k w seen1 (ml_slots ls) with
      | None => false
      | Some _ => true
      end
  end.

Lemma is_exact_cut_var_has_var : forall k w e,
  is_exact_cut_var k w e = true ->
  expr_has_var (mc_cut_var_name k) e = true.
Proof.
  intros k w [] H; cbn in H; try discriminate H.
  apply andb_true_iff in H as [Hs _]; cbn; rewrite Hs; reflexivity.
Qed.

Lemma check_cut_var_regs_acc_spec : forall k w seen rbs,
  check_cut_var_regs_acc k w seen rbs =
  let cnt := List.length (List.filter (fun rb => expr_has_var (mc_cut_var_name k) (mlr_expr rb)) rbs) in
  if forallb (fun rb => reg_slot_uses_cut_var_ok k w (mlr_expr rb)) rbs &&
     Nat.leb ((if seen then 1%nat else 0%nat) + cnt) 1%nat
  then Some (seen || Nat.eqb cnt 1%nat)
  else None.
Proof.
  intros k w seen rbs; revert seen; induction rbs as [| rb rest IH]; intro seen;
    cbn [check_cut_var_regs_acc List.filter List.length forallb].
  - destruct seen; reflexivity.
  - destruct (is_exact_cut_var k w (mlr_expr rb)) eqn:Eex.
    + pose proof (is_exact_cut_var_has_var k w (mlr_expr rb) Eex) as Hhv.
      unfold reg_slot_uses_cut_var_ok; rewrite Hhv, Eex; cbn [orb andb List.length].
      destruct seen.
      * cbn [Nat.add Nat.leb]; rewrite andb_false_r; reflexivity.
      * rewrite IH; cbn [Nat.add].
        set (c := Datatypes.length (List.filter (fun rb0 => expr_has_var (mc_cut_var_name k) (mlr_expr rb0)) rest)).
        destruct (forallb _ rest); [| reflexivity].
        destruct c as [| c']; reflexivity.
    + unfold reg_slot_uses_cut_var_ok; rewrite Eex.
      destruct (expr_has_var (mc_cut_var_name k) (mlr_expr rb)) eqn:Hhv; cbn [negb orb andb List.length].
      * reflexivity.
      * exact (IH seen).
Qed.

Lemma check_cut_var_slots_acc_spec : forall k w seen sbs,
  check_cut_var_slots_acc k w seen sbs =
  let cnt := List.length (List.filter (fun sb => match sb with MLS_Expr _ _ e => expr_has_var (mc_cut_var_name k) e | MLS_SavedReg _ _ => false end) sbs) in
  if forallb (fun sb => match sb with MLS_Expr _ _ e => reg_slot_uses_cut_var_ok k w e | MLS_SavedReg _ _ => true end) sbs &&
     Nat.leb ((if seen then 1%nat else 0%nat) + cnt) 1%nat
  then Some (seen || Nat.eqb cnt 1%nat)
  else None.
Proof.
  intros k w seen sbs; revert seen; induction sbs as [| [off sz e | off r] rest IH]; intro seen;
    cbn [check_cut_var_slots_acc List.filter List.length forallb].
  - destruct seen; reflexivity.
  - destruct (is_exact_cut_var k w e) eqn:Eex.
    + pose proof (is_exact_cut_var_has_var k w e Eex) as Hhv.
      unfold reg_slot_uses_cut_var_ok; rewrite Hhv, Eex; cbn [orb andb List.length].
      destruct seen.
      * cbn [Nat.add Nat.leb]; rewrite andb_false_r; reflexivity.
      * rewrite IH; cbn [Nat.add].
        set (c := Datatypes.length (List.filter _ rest)).
        destruct (forallb _ rest); [| reflexivity].
        destruct c as [| c']; reflexivity.
    + unfold reg_slot_uses_cut_var_ok; rewrite Eex.
      destruct (expr_has_var (mc_cut_var_name k) e) eqn:Hhv; cbn [negb orb andb List.length].
      * reflexivity.
      * exact (IH seen).
  - exact (IH seen).
Qed.

Lemma cut_var_ptol_spec : forall ls k w,
  cut_var_ptol ls k w =
  match ml_inv ls with
  | None => true
  | Some inv_e => negb (expr_has_var (mc_cut_var_name k) inv_e)
  end &&
  Nat.leb (cut_var_bind_count k (ml_regs ls) (ml_slots ls)) 1 &&
  forallb (fun rb => reg_slot_uses_cut_var_ok k w (mlr_expr rb)) (ml_regs ls) &&
  forallb (fun sb => match sb with MLS_Expr _ _ e => reg_slot_uses_cut_var_ok k w e | MLS_SavedReg _ _ => true end) (ml_slots ls).
Proof.
  intros ls k w; unfold cut_var_ptol, cut_var_bind_count; rewrite !mc_count_tr_eq.
  rewrite check_cut_var_regs_acc_spec.
  set (cr := Datatypes.length (List.filter (fun rb => expr_has_var (mc_cut_var_name k) (mlr_expr rb)) (ml_regs ls))).
  set (cs := Datatypes.length (List.filter (fun sb => match sb with MLS_Expr _ _ e => expr_has_var (mc_cut_var_name k) e | MLS_SavedReg _ _ => false end) (ml_slots ls))).
  set (okr := forallb (fun rb => reg_slot_uses_cut_var_ok k w (mlr_expr rb)) (ml_regs ls)).
  set (oks := forallb (fun sb => match sb with MLS_Expr _ _ e => reg_slot_uses_cut_var_ok k w e | MLS_SavedReg _ _ => true end) (ml_slots ls)).
  destruct (match ml_inv ls with None => true | Some inv_e => negb (expr_has_var (mc_cut_var_name k) inv_e) end);
    cbn [andb]; [| reflexivity].
  destruct okr; cbn [andb Nat.add]; [| rewrite andb_false_r; reflexivity].
  destruct (cr <=? 1)%nat eqn:Ecr.
  - rewrite check_cut_var_slots_acc_spec.
    change (forallb (fun sb => match sb with MLS_Expr _ _ e => reg_slot_uses_cut_var_ok k w e | MLS_SavedReg _ _ => true end) (ml_slots ls)) with oks.
    change (Datatypes.length (List.filter (fun sb => match sb with MLS_Expr _ _ e => expr_has_var (mc_cut_var_name k) e | MLS_SavedReg _ _ => false end) (ml_slots ls))) with cs.
    destruct oks; cbn [andb]; [| rewrite andb_false_r; reflexivity].
    destruct cr as [| [| cr']]; cbn [Nat.leb Nat.eqb] in Ecr |- *; try discriminate Ecr;
      rewrite ?andb_true_r; destruct cs as [| [| cs']]; reflexivity.
  - apply Nat.leb_gt in Ecr; assert (Hgt : (cr + cs <=? 1)%nat = false) by (apply Nat.leb_gt; lia);
      rewrite Hgt; cbn [andb]; reflexivity.
Qed.

Fixpoint expr_is_ptol_var_at (ls : mc_loop_spec) (idx : nat) (hdr_ws : list positive) (e : cert_expr) {struct hdr_ws} : bool :=
  match hdr_ws with
  | [] => false
  | w :: rest =>
      (is_exact_cut_var idx w e && cut_var_ptol ls idx w) ||
      expr_is_ptol_var_at ls (S idx) rest e
  end.

Definition expr_is_ptol_var (ls : mc_loop_spec) (hdr_ws : list positive) (e : cert_expr) : bool :=
  expr_is_ptol_var_at ls 0%nat hdr_ws e.

Fixpoint build_phi_subst (idx : nat) (phis : list (positive * cert_expr)) {struct phis}
  : list (string * positive * cert_expr) :=
  match phis with
  | [] => []
  | (w, ce) :: rest => (mc_cut_var_name idx, w, ce) :: build_phi_subst (S idx) rest
  end.

Fixpoint collect_phi_def_obls_acc
  (ls : mc_loop_spec) (is_body : bool) (path : list (bool * cert_expr))
  (idx : nat) (phis : list (positive * cert_expr)) (acc : list mc_loop_obl)
  {struct phis} : list mc_loop_obl :=
  match phis with
  | [] => acc
  | (w, ce) :: rest =>
      let acc' := if cut_var_ptol ls idx w then acc else MLO_Defined is_body path w ce :: acc in
      collect_phi_def_obls_acc ls is_body path (S idx) rest acc'
  end.

Definition trunc_mc_expr_to (w : positive) (e64 : cert_expr) : cert_expr :=
  if Pos.eqb w 64%positive then e64
  else CE_Cast CCK_Trunc 64%positive w no_cast_flags e64.

Definition trunc_mc_slot_expr (sz : mc_mem_size) (e64 : cert_expr) : cert_expr :=
  match sz with
  | MS_8 => e64
  | _ => CE_Cast CCK_Trunc 64%positive (mc_mem_bits sz) no_cast_flags e64
  end.

Fixpoint collect_reg_cut_obls_acc
  (ls : mc_loop_spec) (hdr_ws : list positive) (is_body : bool) (path : list (bool * cert_expr))
  (sub : list (string * positive * cert_expr)) (rr' : N -> mc_sym_val)
  (rbs : list mc_loop_reg_bind) (acc : list mc_loop_obl)
  {struct rbs} : string + list mc_loop_obl :=
  let phase : string := if is_body then "body" else "entry" in
  match rbs with
  | [] => inr acc
  | rb :: rest =>
      match rr' (mlr_reg rb) with
      | MSV_Expr e_mc64 =>
          let e_src := subst_cert_expr sub (mlr_expr rb) in
          let e_tgt := trunc_mc_expr_to (mlr_width rb) e_mc64 in
          let o_ref := MLO_Refine is_body path (mlr_width rb) e_src e_tgt in
          let acc' :=
            if expr_is_ptol_var ls hdr_ws (mlr_expr rb) then o_ref :: acc
            else MLO_Defined is_body path (mlr_width rb) e_src :: o_ref :: acc
          in
          collect_reg_cut_obls_acc ls hdr_ws is_body path sub rr' rest acc'
      | v =>
          inl (diag "mc-loop-obl"
            (phase ++ " cutpoint reg x" ++ diag_N_dec (mlr_reg rb) ++
             " has non-expression value (" ++ mc_sym_val_kind v ++ ")"))
      end
  end.

Fixpoint collect_slot_cut_obls_acc
  (ls : mc_loop_spec) (hdr_ws : list positive) (is_body : bool) (path : list (bool * cert_expr))
  (sub : list (string * positive * cert_expr)) (astk' : mc_sym_stack)
  (sbs : list mc_loop_slot_bind) (acc : list mc_loop_obl)
  {struct sbs} : string + list mc_loop_obl :=
  let phase : string := if is_body then "body" else "entry" in
  match sbs with
  | [] => inr acc
  | MLS_SavedReg off r :: rest =>
      match mc_sym_stk_load off MS_8 false astk' with
      | Some (MSV_SavedReg r0) =>
          if N.eqb r0 r then collect_slot_cut_obls_acc ls hdr_ws is_body path sub astk' rest acc
          else
            inl (diag "mc-loop-obl"
              (phase ++ " cutpoint saved-reg at sp+" ++ diag_Z_dec off ++
               " holds saved x" ++ diag_N_dec r0 ++ ", expected x" ++ diag_N_dec r))
      | Some v =>
          inl (diag "mc-loop-obl"
            (phase ++ " cutpoint saved-reg at sp+" ++ diag_Z_dec off ++
             " holds " ++ mc_sym_val_kind v ++ ", expected saved x" ++ diag_N_dec r))
      | None =>
          inl (diag "mc-loop-obl"
            (phase ++ " cutpoint saved-reg at sp+" ++ diag_Z_dec off ++
             " is unmapped (expected saved x" ++ diag_N_dec r ++ ")"))
      end
  | MLS_Expr off sz e_s :: rest =>
      match mc_sym_stk_load off sz false astk' with
      | Some (MSV_Expr e_mc64) =>
          let w := mc_mem_bits sz in
          let e_src := subst_cert_expr sub e_s in
          let e_tgt := trunc_mc_slot_expr sz e_mc64 in
          let o_ref := MLO_Refine is_body path w e_src e_tgt in
          let acc' :=
            if expr_is_ptol_var ls hdr_ws e_s then o_ref :: acc
            else MLO_Defined is_body path w e_src :: o_ref :: acc
          in
          collect_slot_cut_obls_acc ls hdr_ws is_body path sub astk' rest acc'
      | Some v =>
          inl (diag "mc-loop-obl"
            (phase ++ " cutpoint slot at sp+" ++ diag_Z_dec off ++
             " (size " ++ diag_Z_dec (mc_mem_bytes_Z sz) ++ ") has non-expression value (" ++
             mc_sym_val_kind v ++ ")"))
      | None =>
          inl (diag "mc-loop-obl"
            (phase ++ " cutpoint slot at sp+" ++ diag_Z_dec off ++
             " (size " ++ diag_Z_dec (mc_mem_bytes_Z sz) ++ ") is unmapped in MC stack"))
      end
  end.

Definition mc_path_unconditional (ls : mc_loop_spec) (is_body : bool) (p : list (bool * cert_expr)) : bool :=
  match p with
  | [] => negb is_body || match ml_inv ls with None => true | Some _ => false end
  | _ :: _ => false
  end.

Fixpoint check_widths_match (ws : list positive) (phis : list (positive * cert_expr)) {struct ws} : bool :=
  match ws, phis with
  | [], [] => true
  | w :: rw, (wp, _) :: rp => Pos.eqb w wp && check_widths_match rw rp
  | _, _ => false
  end.

Fixpoint collect_mc_ir_obls_acc
  (arch : elf_arch) (ls : mc_loop_spec) (ret_w : positive) (hdr_ws : list positive)
  (is_body : bool) (path : list (bool * cert_expr)) (t_ir : ir_seg_tree) (t_mc : mc_seg_tree)
  (acc : list mc_loop_obl)
  {struct t_ir} : string + list mc_loop_obl :=
  let phase : string := if is_body then "body" else "entry" in
  match t_ir with
  | IST_UB => inr acc
  | IST_Branch cond dt_ir df_ir =>
      match collect_mc_ir_obls_acc arch ls ret_w hdr_ws is_body ((false, cond) :: path) df_ir t_mc acc with
      | inl err => inl err
      | inr acc_f =>
          collect_mc_ir_obls_acc arch ls ret_w hdr_ws is_body ((true, cond) :: path) dt_ir t_mc acc_f
      end
  | IST_Ret rw ret_ir =>
      (fix go_mc (u : mc_seg_tree) (p : list (bool * cert_expr)) (a : list mc_loop_obl) {struct u}
          : string + list mc_loop_obl :=
        match u with
        | MST_Branch cond_mc dt_mc df_mc =>
            match go_mc df_mc ((false, cond_mc) :: p) a with
            | inl err => inl err
            | inr af => go_mc dt_mc ((true, cond_mc) :: p) af
            end
        | MST_Ret ret_mc =>
            if Pos.eqb rw ret_w then inr (MLO_Refine is_body p rw ret_ir ret_mc :: a)
            else
              inl (diag "mc-loop-obl"
                (phase ++ " IR return width i" ++ diag_pos_dec rw ++
                 " does not match declared ret-width i" ++ diag_pos_dec ret_w))
        | MST_Cut _ _ _ =>
            if mc_path_unconditional ls is_body p then
              inl (diag "mc-loop-obl"
                (phase ++ " control-flow mismatch: IR returned while MC reached loop cutpoint unconditionally"))
            else inr (imposs_obl_cons is_body p a)
        end) t_mc path acc
  | IST_Cut _ phis_ir =>
      (fix go_mc (u : mc_seg_tree) (p : list (bool * cert_expr)) (a : list mc_loop_obl) {struct u}
          : string + list mc_loop_obl :=
        match u with
        | MST_Branch cond_mc dt_mc df_mc =>
            match go_mc df_mc ((false, cond_mc) :: p) a with
            | inl err => inl err
            | inr af => go_mc dt_mc ((true, cond_mc) :: p) af
            end
        | MST_Ret _ =>
            if mc_path_unconditional ls is_body p then
              inl (diag "mc-loop-obl"
                (phase ++ " control-flow mismatch: IR reached loop cutpoint while MC returned unconditionally"))
            else inr (imposs_obl_cons is_body p a)
        | MST_Cut sp' rr' astk' =>
            if negb (Z.eqb sp' (ml_sp_off ls)) then
              inl (diag "mc-loop-obl"
                (phase ++ " cutpoint sp-off mismatch: got " ++ diag_Z_dec sp' ++
                 ", expected " ++ diag_Z_dec (ml_sp_off ls)))
            else
              match check_unspilled_preserved_diag phase rr' (mc_unspilled_preserved arch ls) with
              | inl err => inl err
              | inr tt =>
                  if negb (check_widths_match hdr_ws phis_ir) then
                    inl (diag "mc-loop-obl"
                      (phase ++ " header phi count/width mismatch at cutpoint"))
                  else
                    let sub := build_phi_subst 0%nat phis_ir in
                    let a_inv :=
                      match ml_inv ls with
                      | None => a
                      | Some inv_e =>
                          MLO_Refine is_body p 1%positive (CE_BvConst 1%positive 1%N) (subst_cert_expr sub inv_e) :: a
                      end in
                    let a_phi := collect_phi_def_obls_acc ls is_body p 0%nat phis_ir a_inv in
                    match collect_reg_cut_obls_acc ls hdr_ws is_body p sub rr' (ml_regs ls) a_phi with
                    | inl err => inl err
                    | inr a_reg =>
                        collect_slot_cut_obls_acc ls hdr_ws is_body p sub astk' (ml_slots ls) a_reg
                    end
              end
        end) t_mc path acc
  end.

Definition collect_mc_ir_obls
  (arch : elf_arch) (ls : mc_loop_spec) (ret_w : positive) (hdr_ws : list positive)
  (is_body : bool) (path : list (bool * cert_expr)) (t_ir : ir_seg_tree) (t_mc : mc_seg_tree)
  : string + list mc_loop_obl :=
  collect_mc_ir_obls_acc arch ls ret_w hdr_ws is_body path t_ir t_mc [].

Lemma collect_mc_ir_obls_acc_sub :
  forall (P : mc_loop_obl -> Prop) arch ls ret_w hdr_ws is_body path t_ir t_mc acc res,
    collect_mc_ir_obls_acc arch ls ret_w hdr_ws is_body path t_ir t_mc acc = inr res ->
    Forall P res ->
    Forall P acc.
Proof.
  intros P arch ls ret_w hdr_ws is_body path t_ir;
    revert path; induction t_ir as [lm ph | rw0 re | | c0 d0 IH0 d1 IH1];
    intros path t_mc acc res Hcol Hfa; cbn [collect_mc_ir_obls_acc] in Hcol.
  - clear -Hcol Hfa.
    induction t_mc as [sp' rr' astk' | ret_mc | cm dl IHl dr IHr] in path, acc, res, Hcol, Hfa |- *;
      cbn in Hcol.
    + destruct (Z.eqb sp' (ml_sp_off ls)); cbn [negb] in Hcol; [| discriminate Hcol].
      destruct (check_unspilled_preserved_diag _ rr' (mc_unspilled_preserved arch ls)) as [| []];
        [discriminate Hcol |].
      destruct (check_widths_match hdr_ws ph); cbn [negb] in Hcol; [| discriminate Hcol].
      set (ai := match ml_inv ls with None => acc | Some _ => _ :: acc end) in *.
      set (ap := collect_phi_def_obls_acc ls is_body path 0%nat ph ai) in *.
      destruct (collect_reg_cut_obls_acc ls hdr_ws is_body path _ rr' (ml_regs ls) ap)
        as [| ar] eqn:Ero; [discriminate Hcol |].
      assert (Hsr : Forall P ar).
      { clear -Hcol Hfa; revert ar res Hcol Hfa; induction (ml_slots ls) as [| [o s e | o r0] r IHs];
          intros ar0 res0 Eso0 Hfa0; cbn in Eso0;
          [inversion Eso0; subst; exact Hfa0
          | destruct (mc_sym_stk_load o s false astk') as [[| em | |] |]; try discriminate Eso0;
            pose proof (IHs _ _ Eso0 Hfa0) as Hsub; destruct (expr_is_ptol_var ls hdr_ws e);
            [inversion Hsub; assumption | inversion Hsub as [| ? ? ? Hs1]; inversion Hs1; assumption]
          | destruct (mc_sym_stk_load o MS_8 false astk') as [[| | r1 |] |]; try discriminate Eso0;
            destruct (N.eqb r1 r0); [| discriminate Eso0]; exact (IHs _ _ Eso0 Hfa0)]. }
      assert (Hsp : Forall P ap).
      { clear -Ero Hsr; clearbody ap; revert ap ar Ero Hsr; induction (ml_regs ls) as [| rb r IHr];
          intros ap0 ar0 Ero0 Hsr0; cbn in Ero0;
          [inversion Ero0; subst; exact Hsr0
          | destruct (rr' (mlr_reg rb)) as [| em | |]; try discriminate Ero0;
            pose proof (IHr _ _ Ero0 Hsr0) as Hsub; destruct (expr_is_ptol_var ls hdr_ws (mlr_expr rb));
            [inversion Hsub; assumption | inversion Hsub as [| ? ? ? Hs1]; inversion Hs1; assumption]]. }
      assert (Hsa : Forall P ai).
      { clear -Hsp; unfold ap in Hsp; clear ap; clearbody ai; revert ai Hsp; generalize 0%nat as idx;
          induction ph as [| [w0 ce0] rp IHp]; intros idx a0 H0; cbn in H0; [exact H0 |].
        destruct (cut_var_ptol ls idx w0); [exact (IHp (S idx) a0 H0) |].
        pose proof (IHp (S idx) _ H0) as Hsub0; inversion Hsub0; assumption. }
      unfold ai in Hsa; destruct (ml_inv ls); [inversion Hsa; assumption | exact Hsa].
    + destruct (mc_path_unconditional ls is_body path); [discriminate Hcol |].
      inversion Hcol; subst res; inversion Hfa; assumption.
    + match type of Hcol with
      | match ?f with inl _ => _ | inr _ => _ end = _ => destruct f as [| af] eqn:Eaf
      end; [discriminate Hcol |].
      exact (IHr _ _ _ Eaf (IHl _ _ _ Hcol Hfa)).
  - clear -Hcol Hfa.
    induction t_mc as [| ret_mc | cm dl IHl dr IHr] in path, acc, res, Hcol, Hfa |- *; cbn in Hcol.
    + destruct (mc_path_unconditional ls is_body path); [discriminate Hcol |].
      inversion Hcol; subst res; inversion Hfa; assumption.
    + destruct (Pos.eqb rw0 ret_w); [inversion Hcol; subst res; inversion Hfa; assumption | discriminate Hcol].
    + match type of Hcol with
      | match ?f with inl _ => _ | inr _ => _ end = _ => destruct f as [| af] eqn:Eaf
      end; [discriminate Hcol |].
      exact (IHr _ _ _ Eaf (IHl _ _ _ Hcol Hfa)).
  - inversion Hcol; subst res; exact Hfa.
  - destruct (collect_mc_ir_obls_acc arch ls ret_w hdr_ws is_body ((false, c0) :: path) d1 t_mc acc)
      as [| acc_f] eqn:Edf; [discriminate Hcol |].
    exact (IH1 _ _ _ _ Edf (IH0 _ _ _ _ Hcol Hfa)).
Qed.

Lemma cut_slot_expr_wf : forall allowed off sz e,
  mc_slot_in_frame 0%Z off sz = true ->
  wt_cert_expr [] e = true ->
  cert_expr_bit_width e = mc_mem_bits sz ->
  is_let_free_expr e = true ->
  vars_subset_b (collect_free_vars [] e) allowed = true ->
  mc_sym_val_wf allowed (MSV_Expr (cut_slot_expr sz e)).
Proof.
  intros allowed off sz e _ Hwt Hbw Hlf Hsub.
  destruct sz; unfold cut_slot_expr, mc_sym_val_wf;
    [apply wf_sym_cast; [reflexivity |]
    | apply wf_sym_cast; [reflexivity |]
    | apply wf_sym_cast; [reflexivity |]
    |];
    unfold wf_sym_expr; cbn [mc_mem_bits]; rewrite Hwt, Hbw, Hlf; repeat split; try reflexivity; exact Hsub.
Qed.

Lemma mc_stk_load_expr_agrees {Pa : Params} :
  forall penv foracle off sz (mstk : mc_stack_mem) (e : cert_expr),
    eval_closed_cert_expr penv foracle e = raise_ret (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz)
      (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false))))) ->
    exists v64 : @Integers.bit_int 64%positive,
      eval_closed_cert_expr penv foracle (cut_slot_expr sz e) = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive v64)) /\
      mc_stk_load mstk off sz false =
        (match sz with
         | MS_8 => v64
         | _ =>
             let w := mc_mem_bits sz in
             @Integers.repr 64%positive (@Integers.unsigned w (@Integers.repr w (@Integers.unsigned 64%positive v64)))
         end) /\
      mc_stk_load mstk off sz true =
        (match sz with
         | MS_8 => v64
         | _ =>
             let w := mc_mem_bits sz in
             @Integers.repr 64%positive (@Integers.signed w (@Integers.repr w (@Integers.unsigned 64%positive v64)))
         end).
Proof.
  intros penv foracle off sz mstk e He.
  destruct sz; unfold cut_slot_expr.
  - (* MS_1: 8-bit *)
    pose proof (eval_ce_zext penv foracle 8%positive 64%positive _ _ eq_refl He) as Hz.
    eexists; split; [exact Hz |].
    unfold mc_stk_load, mc_mem_bits, mc_mem_bytes in *; cbv zeta iota beta in *; change (N.to_nat 1%N) with 1%nat in *.
    pose proof (mc_stk_read_bytes_bound mstk off 1%nat) as Hb.
    change (N.pow 256%N (N.of_nat 1%nat)) with 256%N in Hb; rewrite N2Z.inj_lt in Hb; change (Z.of_N 256%N) with 256%Z in Hb.
    pose proof (N2Z.is_nonneg (mc_stk_read_bytes mstk off 1%nat)) as Hnn.
    assert (Hu8 : @Integers.unsigned 8%positive (@Integers.repr 8%positive (Z.of_N (mc_stk_read_bytes mstk off 1%nat))) = Z.of_N (mc_stk_read_bytes mstk off 1%nat))
      by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 8%positive) with 255%Z; lia).
    assert (Hu64 : @Integers.unsigned 64%positive (@Integers.repr 64%positive (Z.of_N (mc_stk_read_bytes mstk off 1%nat))) = Z.of_N (mc_stk_read_bytes mstk off 1%nat))
      by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 64%positive) with 18446744073709551615%Z; lia).
    repeat (first [rewrite Hu8 | rewrite Hu64]); split; reflexivity.
  - (* MS_2: 16-bit *)
    pose proof (eval_ce_zext penv foracle 16%positive 64%positive _ _ eq_refl He) as Hz.
    eexists; split; [exact Hz |].
    unfold mc_stk_load, mc_mem_bits, mc_mem_bytes in *; cbv zeta iota beta in *; change (N.to_nat 2%N) with 2%nat in *.
    pose proof (mc_stk_read_bytes_bound mstk off 2%nat) as Hb.
    change (N.pow 256%N (N.of_nat 2%nat)) with 65536%N in Hb; rewrite N2Z.inj_lt in Hb; change (Z.of_N 65536%N) with 65536%Z in Hb.
    pose proof (N2Z.is_nonneg (mc_stk_read_bytes mstk off 2%nat)) as Hnn.
    assert (Hu16 : @Integers.unsigned 16%positive (@Integers.repr 16%positive (Z.of_N (mc_stk_read_bytes mstk off 2%nat))) = Z.of_N (mc_stk_read_bytes mstk off 2%nat))
      by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 16%positive) with 65535%Z; lia).
    assert (Hu64 : @Integers.unsigned 64%positive (@Integers.repr 64%positive (Z.of_N (mc_stk_read_bytes mstk off 2%nat))) = Z.of_N (mc_stk_read_bytes mstk off 2%nat))
      by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 64%positive) with 18446744073709551615%Z; lia).
    repeat (first [rewrite Hu16 | rewrite Hu64]); split; reflexivity.
  - (* MS_4: 32-bit *)
    pose proof (eval_ce_zext penv foracle 32%positive 64%positive _ _ eq_refl He) as Hz.
    eexists; split; [exact Hz |].
    unfold mc_stk_load, mc_mem_bits, mc_mem_bytes in *; cbv zeta iota beta in *; change (N.to_nat 4%N) with 4%nat in *.
    pose proof (mc_stk_read_bytes_bound mstk off 4%nat) as Hb.
    change (N.pow 256%N (N.of_nat 4%nat)) with 4294967296%N in Hb; rewrite N2Z.inj_lt in Hb; change (Z.of_N 4294967296%N) with 4294967296%Z in Hb.
    pose proof (N2Z.is_nonneg (mc_stk_read_bytes mstk off 4%nat)) as Hnn.
    assert (Hu32 : @Integers.unsigned 32%positive (@Integers.repr 32%positive (Z.of_N (mc_stk_read_bytes mstk off 4%nat))) = Z.of_N (mc_stk_read_bytes mstk off 4%nat))
      by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 32%positive) with 4294967295%Z; lia).
    assert (Hu64 : @Integers.unsigned 64%positive (@Integers.repr 64%positive (Z.of_N (mc_stk_read_bytes mstk off 4%nat))) = Z.of_N (mc_stk_read_bytes mstk off 4%nat))
      by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 64%positive) with 18446744073709551615%Z; lia).
    repeat (first [rewrite Hu32 | rewrite Hu64]); split; reflexivity.
  - (* MS_8: 64-bit *)
    cbn [mc_mem_bits] in He; rewrite (@Integers.repr_unsigned 64%positive) in He.
    exists (mc_stk_load mstk off MS_8 false); split; [exact He |].
    unfold mc_stk_load; cbn; split; reflexivity.
Qed.

Lemma build_cut_astk_agrees {Pa : Params} :
  forall penv foracle read_init sp0 slots mstk,
    (forall off sz e, In (MLS_Expr off sz e) slots ->
       eval_closed_cert_expr penv foracle e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mc_mem_bits sz)
           (@Integers.repr (mc_mem_bits sz) (@Integers.unsigned 64%positive (mc_stk_load mstk off sz false)))))) ->
    (forall off r, In (MLS_SavedReg off r) slots ->
       mc_stk_load mstk off MS_8 false = read_init r) ->
    mc_sym_stack_agrees penv foracle read_init sp0 (build_cut_astk slots) mstk.
Proof.
  intros penv foracle read_init sp0 slots mstk Hexpr Hsav.
  unfold build_cut_astk, mc_sym_stack_agrees; apply Forall_forall.
  intros [[off sz] sv] Hin; apply in_map_iff in Hin as [sb [Heq Hsb]].
  destruct sb as [o s e | o r]; inversion Heq; subst; clear Heq.
  - exact (mc_stk_load_expr_agrees penv foracle off sz mstk e (Hexpr off sz e Hsb)).
  - split; [reflexivity | exact (Hsav off r Hsb)].
Qed.

Lemma build_skel_astk_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle read_init sp0 idx slots mstk,
    (forall i o s e, nth_error slots i = Some (MLS_Expr o s e) ->
       penv (mc_skel_slot_name (idx + i)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk o s false)))) ->
    (forall o r, In (MLS_SavedReg o r) slots -> mc_stk_load mstk o MS_8 false = read_init r) ->
    mc_sym_stack_agrees penv foracle read_init sp0 (build_skel_astk idx slots) mstk.
Proof.
  intros penv foracle read_init sp0 idx slots; revert idx;
    induction slots as [| sb rest IH]; intros idx mstk Hp Hsav;
    cbn [build_skel_astk]; [constructor |].
  assert (Hp_rest : forall i o s e, nth_error rest i = Some (MLS_Expr o s e) ->
    penv (mc_skel_slot_name (S idx + i)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (mc_stk_load mstk o s false)))).
  { intros i o s e Hnth; replace (S idx + i)%nat with (idx + S i)%nat by lia; exact (Hp (S i) o s e Hnth). }
  destruct sb as [o s e | o r]; constructor.
  - pose proof (Hp 0%nat o s e eq_refl) as H0; rewrite Nat.add_0_r in H0.
    exists (mc_stk_load mstk o s false); split.
    + unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite H0; cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
    + destruct s; unfold mc_stk_load, mc_mem_bits, mc_mem_bytes in *; cbv zeta iota beta in *.
      * change (N.to_nat 1%N) with 1%nat in *; pose proof (mc_stk_read_bytes_bound mstk o 1%nat) as Hb;
          change (N.pow 256%N (N.of_nat 1%nat)) with 256%N in Hb; rewrite N2Z.inj_lt in Hb; change (Z.of_N 256%N) with 256%Z in Hb;
          pose proof (N2Z.is_nonneg (mc_stk_read_bytes mstk o 1%nat)) as Hnn;
          assert (Hu8 : @Integers.unsigned 8%positive (@Integers.repr 8%positive (Z.of_N (mc_stk_read_bytes mstk o 1%nat))) = Z.of_N (mc_stk_read_bytes mstk o 1%nat)) by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 8%positive) with 255%Z; lia);
          assert (Hu64 : @Integers.unsigned 64%positive (@Integers.repr 64%positive (Z.of_N (mc_stk_read_bytes mstk o 1%nat))) = Z.of_N (mc_stk_read_bytes mstk o 1%nat)) by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 64%positive) with 18446744073709551615%Z; lia);
          repeat (first [rewrite Hu8 | rewrite Hu64]); split; reflexivity.
      * change (N.to_nat 2%N) with 2%nat in *; pose proof (mc_stk_read_bytes_bound mstk o 2%nat) as Hb;
          change (N.pow 256%N (N.of_nat 2%nat)) with 65536%N in Hb; rewrite N2Z.inj_lt in Hb; change (Z.of_N 65536%N) with 65536%Z in Hb;
          pose proof (N2Z.is_nonneg (mc_stk_read_bytes mstk o 2%nat)) as Hnn;
          assert (Hu16 : @Integers.unsigned 16%positive (@Integers.repr 16%positive (Z.of_N (mc_stk_read_bytes mstk o 2%nat))) = Z.of_N (mc_stk_read_bytes mstk o 2%nat)) by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 16%positive) with 65535%Z; lia);
          assert (Hu64 : @Integers.unsigned 64%positive (@Integers.repr 64%positive (Z.of_N (mc_stk_read_bytes mstk o 2%nat))) = Z.of_N (mc_stk_read_bytes mstk o 2%nat)) by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 64%positive) with 18446744073709551615%Z; lia);
          repeat (first [rewrite Hu16 | rewrite Hu64]); split; reflexivity.
      * change (N.to_nat 4%N) with 4%nat in *; pose proof (mc_stk_read_bytes_bound mstk o 4%nat) as Hb;
          change (N.pow 256%N (N.of_nat 4%nat)) with 4294967296%N in Hb; rewrite N2Z.inj_lt in Hb; change (Z.of_N 4294967296%N) with 4294967296%Z in Hb;
          pose proof (N2Z.is_nonneg (mc_stk_read_bytes mstk o 4%nat)) as Hnn;
          assert (Hu32 : @Integers.unsigned 32%positive (@Integers.repr 32%positive (Z.of_N (mc_stk_read_bytes mstk o 4%nat))) = Z.of_N (mc_stk_read_bytes mstk o 4%nat)) by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 32%positive) with 4294967295%Z; lia);
          assert (Hu64 : @Integers.unsigned 64%positive (@Integers.repr 64%positive (Z.of_N (mc_stk_read_bytes mstk o 4%nat))) = Z.of_N (mc_stk_read_bytes mstk o 4%nat)) by (apply Integers.unsigned_repr; change (@Integers.max_unsigned 64%positive) with 18446744073709551615%Z; lia);
          repeat (first [rewrite Hu32 | rewrite Hu64]); split; reflexivity.
      * split; reflexivity.
  - exact (IH (S idx) mstk Hp_rest (fun o0 r0 H => Hsav o0 r0 (or_intror H))).
  - split; [reflexivity | exact (Hsav o r (or_introl eq_refl))].
  - exact (IH (S idx) mstk Hp_rest (fun o0 r0 H => Hsav o0 r0 (or_intror H))).
Qed.

Lemma rv_val_write_eq : forall r sv vrf,
  r <> 0%N -> rv_val_read r (rv_val_write r sv vrf) = sv.
Proof.
  intros r sv vrf Hne; unfold rv_val_read, rv_val_write.
  destruct (N.eqb r 0%N) eqn:Er0; [apply N.eqb_eq in Er0; contradiction |].
  rewrite N.eqb_refl; reflexivity.
Qed.

Lemma rv_val_write_neq : forall r r' sv vrf,
  r' <> r -> rv_val_read r' (rv_val_write r sv vrf) = rv_val_read r' vrf.
Proof.
  intros r r' sv vrf Hne; unfold rv_val_read, rv_val_write.
  destruct (N.eqb r' 0%N) eqn:Er0'; [reflexivity |].
  destruct (N.eqb r 0%N); [reflexivity |].
  destruct (N.eqb r' r) eqn:Eeq; [apply N.eqb_eq in Eeq; contradiction | reflexivity].
Qed.

Lemma a64_val_write_eq : forall r sv vrf,
  (r < 31)%N -> a64_val_read r (a64_val_write r sv vrf) = sv.
Proof.
  intros r sv vrf Hlt; unfold a64_val_read, a64_val_write.
  destruct (N.leb 31%N r) eqn:Er31; [apply N.leb_le in Er31; lia |].
  rewrite N.eqb_refl; reflexivity.
Qed.

Lemma a64_val_write_neq : forall r r' sv vrf,
  r' <> r -> a64_val_read r' (a64_val_write r sv vrf) = a64_val_read r' vrf.
Proof.
  intros r r' sv vrf Hne; unfold a64_val_read, a64_val_write.
  destruct (N.leb 31%N r') eqn:Er31'; [reflexivity |].
  destruct (N.leb 31%N r); [reflexivity |].
  destruct (N.eqb r' r) eqn:Eeq; [apply N.eqb_eq in Eeq; contradiction | reflexivity].
Qed.

Lemma no_dup_N_to_NoDup : forall xs,
  no_dup_N xs = true -> NoDup xs.
Proof.
  induction xs as [| x rest IH]; intro H; cbn [no_dup_N] in H; [constructor |].
  apply andb_true_iff in H as [Hnin Hrest]; constructor; [| exact (IH Hrest)].
  intro Hin; apply negb_true_iff in Hnin.
  assert (Hex : n_in_list_bool x rest = true)
    by (unfold n_in_list_bool; apply existsb_exists; exists x; split; [exact Hin | apply N.eqb_refl]).
  rewrite Hex in Hnin; discriminate Hnin.
Qed.

Lemma n_in_list_In : forall x xs,
  n_in_list x xs = true -> In x xs.
Proof.
  intros x; induction xs as [| y ys IH]; intro H; cbn in H; [discriminate |].
  apply orb_true_iff in H as [Heq | Hr]; [apply N.eqb_eq in Heq; left; congruence | right; exact (IH Hr)].
Qed.

Lemma rv_cut_base_vrf_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle ls rf0 rf r,
    rf 2%N = @Integers.add 64%positive (rv_read_reg 2%N rf0) (@Integers.repr 64%positive (ml_sp_off ls)) ->
    (- mc_frame_cap <= ml_sp_off ls <= 0)%Z ->
    ~ In r (List.map mlr_reg (ml_regs ls)) ->
    (forall r0, In r0 (mc_unspilled_preserved EA_Riscv64 ls) -> rf r0 = rf0 r0) ->
    mc_sym_val_agrees penv foracle (fun k => rv_read_reg k rf0) (rv_read_reg 2%N rf0)
      (rv_val_read r (rv_cut_base_vrf ls)) (rv_read_reg r rf).
Proof.
  intros penv foracle ls rf0 rf r Hsp Hrng Hnin Hunsp.
  unfold rv_val_read, rv_cut_base_vrf.
  destruct (N.eqb r 0%N) eqn:E0.
  - cbn [mc_sym_val_agrees]; unfold rv_read_reg; rewrite E0, eval_ce_const, repr_zero_N; reflexivity.
  - destruct (N.eqb r 2%N) eqn:E2.
    + apply N.eqb_eq in E2; subst r; cbn [mc_sym_val_agrees]; unfold rv_read_reg; cbn [N.eqb]; split; assumption.
    + destruct (n_in_list r rv_preserved_non_sp_regs && negb (slot_has_saved_reg (ml_slots ls) r)) eqn:Ep.
      * apply andb_true_iff in Ep as [Hpres Hnsav].
        cbn [mc_sym_val_agrees]; unfold rv_read_reg; rewrite E0; apply Hunsp.
        unfold mc_unspilled_preserved; apply filter_In; split; [exact (n_in_list_In r rv_preserved_non_sp_regs Hpres) |].
        apply andb_true_iff; split; [| exact Hnsav].
        apply negb_true_iff; destruct (existsb (fun rb => N.eqb (mlr_reg rb) r) (ml_regs ls)) eqn:Ex; [| reflexivity].
        apply existsb_exists in Ex as [rb [Hrb Heqr]]; apply N.eqb_eq in Heqr; subst r.
        exfalso; apply Hnin, in_map_iff; exists rb; split; [reflexivity | exact Hrb].
      * cbn [mc_sym_val_agrees]; trivial.
Qed.

Lemma rv_fold_write_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle (f_expr : mc_loop_reg_bind -> cert_expr) rf0 rf rbs base r,
    NoDup (List.map mlr_reg rbs) ->
    forallb (wf_mc_loop_reg_bind EA_Riscv64) rbs = true ->
    (~ In r (List.map mlr_reg rbs) ->
       mc_sym_val_agrees penv foracle (fun k => rv_read_reg k rf0) (rv_read_reg 2%N rf0) (rv_val_read r base) (rv_read_reg r rf)) ->
    (forall rb, In rb rbs ->
       eval_closed_cert_expr penv foracle (f_expr rb) = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg (mlr_reg rb) rf)))) ->
    mc_sym_val_agrees penv foracle (fun k => rv_read_reg k rf0) (rv_read_reg 2%N rf0)
      (rv_val_read r (List.fold_left (fun vrf rb => rv_val_write (mlr_reg rb) (MSV_Expr (f_expr rb)) vrf) rbs base))
      (rv_read_reg r rf).
Proof.
  intros penv foracle f_expr rf0 rf rbs; induction rbs as [| rb rest IH];
    intros base r Hnd Hall Hbase Hfe; cbn [List.fold_left List.map] in *.
  - apply Hbase; intros [].
  - inversion Hnd as [| ? ? Hnin Hnd']; subst; cbn [forallb] in Hall; apply andb_true_iff in Hall as [Hrb Hall'].
    apply IH; try assumption; [| intros rb0 H0; apply Hfe; right; exact H0].
    intro Hninr; destruct (N.eq_dec r (mlr_reg rb)) as [-> | Hneq].
    + unfold wf_mc_loop_reg_bind in Hrb; rewrite !andb_true_iff in Hrb; destruct Hrb as (((((Hv & _) & _) & _) & _) & _).
      cbn [mc_loop_reg_valid] in Hv; rewrite !andb_true_iff in Hv; destruct Hv as [[H1 _] _].
      rewrite rv_val_write_eq by (apply N.leb_le in H1; lia).
      exact (Hfe rb (or_introl eq_refl)).
    + rewrite rv_val_write_neq by exact Hneq; apply Hbase; intros [Heq | Hin]; [apply Hneq; symmetry; exact Heq | exact (Hninr Hin)].
Qed.

Lemma rv_cut_vrf_sp : forall ls,
  forallb (wf_mc_loop_reg_bind EA_Riscv64) (ml_regs ls) = true ->
  rv_val_read 2%N (rv_cut_vrf ls) = MSV_StackPtr (ml_sp_off ls).
Proof.
  intros ls Hwf; unfold rv_cut_vrf.
  assert (Hgen : forall rbs base,
    forallb (wf_mc_loop_reg_bind EA_Riscv64) rbs = true ->
    rv_val_read 2%N base = MSV_StackPtr (ml_sp_off ls) ->
    rv_val_read 2%N (List.fold_left (fun vrf rb => rv_val_write (mlr_reg rb) (MSV_Expr (cut_reg_expr rb)) vrf) rbs base) =
      MSV_StackPtr (ml_sp_off ls)).
  { intros rbs; induction rbs as [| rb rest IH]; intros base Hall Hb; cbn [List.fold_left]; [exact Hb |].
    cbn [forallb] in Hall; apply andb_true_iff in Hall as [Hrb Hall'].
    apply IH; [exact Hall' |].
    unfold wf_mc_loop_reg_bind in Hrb; rewrite !andb_true_iff in Hrb; destruct Hrb as (((((Hv & _) & _) & _) & _) & _).
    cbn [mc_loop_reg_valid] in Hv; rewrite !andb_true_iff in Hv; destruct Hv as [_ Hn2]; apply negb_true_iff, N.eqb_neq in Hn2.
    rewrite rv_val_write_neq; [exact Hb | intro Heq; apply Hn2; symmetry; exact Heq]. }
  apply Hgen; [exact Hwf | reflexivity].
Qed.

Lemma rv_skel_vrf_sp : forall ls,
  forallb (wf_mc_loop_reg_bind EA_Riscv64) (ml_regs ls) = true ->
  rv_val_read 2%N (rv_skel_vrf ls) = MSV_StackPtr (ml_sp_off ls).
Proof.
  intros ls Hwf; unfold rv_skel_vrf.
  assert (Hgen : forall rbs base,
    forallb (wf_mc_loop_reg_bind EA_Riscv64) rbs = true ->
    rv_val_read 2%N base = MSV_StackPtr (ml_sp_off ls) ->
    rv_val_read 2%N (List.fold_left (fun vrf rb => rv_val_write (mlr_reg rb) (MSV_Expr (CE_Var (mc_skel_reg_name (mlr_reg rb)) 64%positive)) vrf) rbs base) =
      MSV_StackPtr (ml_sp_off ls)).
  { intros rbs; induction rbs as [| rb rest IH]; intros base Hall Hb; cbn [List.fold_left]; [exact Hb |].
    cbn [forallb] in Hall; apply andb_true_iff in Hall as [Hrb Hall'].
    apply IH; [exact Hall' |].
    unfold wf_mc_loop_reg_bind in Hrb; rewrite !andb_true_iff in Hrb; destruct Hrb as (((((Hv & _) & _) & _) & _) & _).
    cbn [mc_loop_reg_valid] in Hv; rewrite !andb_true_iff in Hv; destruct Hv as [_ Hn2]; apply negb_true_iff, N.eqb_neq in Hn2.
    rewrite rv_val_write_neq; [exact Hb | intro Heq; apply Hn2; symmetry; exact Heq]. }
  apply Hgen; [exact Hwf | reflexivity].
Qed.

Lemma rv_cut_vrf_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle ls rf0 rf,
    wf_mc_loop_spec EA_Riscv64 ls = true ->
    rf 2%N = @Integers.add 64%positive (rv_read_reg 2%N rf0) (@Integers.repr 64%positive (ml_sp_off ls)) ->
    (- mc_frame_cap <= ml_sp_off ls <= 0)%Z ->
    (forall r, In r (mc_unspilled_preserved EA_Riscv64 ls) -> rf r = rf0 r) ->
    (forall rb, In rb (ml_regs ls) ->
       eval_closed_cert_expr penv foracle (mlr_expr rb) =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mlr_width rb) (@Integers.repr (mlr_width rb) (@Integers.unsigned 64%positive (rv_read_reg (mlr_reg rb) rf))))) /\
       (mlr_width rb = 32%positive ->
          penv (mc_hi_var_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg (mlr_reg rb) rf))))) ->
    rv_val_regs_agrees penv foracle rf0 (rv_read_reg 2%N rf0) (rv_cut_vrf ls) rf.
Proof.
  intros penv foracle ls rf0 rf Hwf Hsp Hrng Hunsp Hregs r.
  unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
  destruct Hwf as (((((((_ & _) & _) & Hnd) & Hwbr) & _) & _) & _); rewrite mc_map_tr_eq in Hnd.
  apply rv_fold_write_agrees; try assumption; [apply no_dup_N_to_NoDup; exact Hnd | |].
  - intro Hnin; exact (rv_cut_base_vrf_agrees penv foracle ls rf0 rf r Hsp Hrng Hnin Hunsp).
  - intros rb Hrb; destruct (Hregs rb Hrb) as [Hev Hhi].
    rewrite forallb_forall in Hwbr; pose proof (Hwbr rb Hrb) as Hwrb.
    unfold wf_mc_loop_reg_bind in Hwrb; rewrite !andb_true_iff in Hwrb; destruct Hwrb as (((((_ & Hw) & _) & _) & _) & _).
    unfold cut_reg_expr; apply orb_true_iff in Hw as [Hw32 | Hw64].
    + apply Pos.eqb_eq in Hw32; rewrite Hw32 in *; cbn [Pos.eqb].
      eapply combine_hi32_expr_sound; [| exact Hev | reflexivity].
      unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite (Hhi eq_refl); cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
    + apply Pos.eqb_eq in Hw64; rewrite Hw64 in *; rewrite Pos.eqb_refl; rewrite (@Integers.repr_unsigned 64%positive) in Hev; exact Hev.
Qed.

Lemma rv_skel_vrf_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle ls rf0 rf,
    wf_mc_loop_spec EA_Riscv64 ls = true ->
    rf 2%N = @Integers.add 64%positive (rv_read_reg 2%N rf0) (@Integers.repr 64%positive (ml_sp_off ls)) ->
    (- mc_frame_cap <= ml_sp_off ls <= 0)%Z ->
    (forall r, In r (mc_unspilled_preserved EA_Riscv64 ls) -> rf r = rf0 r) ->
    (forall rb, In rb (ml_regs ls) ->
       penv (mc_skel_reg_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (rv_read_reg (mlr_reg rb) rf)))) ->
    rv_val_regs_agrees penv foracle rf0 (rv_read_reg 2%N rf0) (rv_skel_vrf ls) rf.
Proof.
  intros penv foracle ls rf0 rf Hwf Hsp Hrng Hunsp Hregs r.
  unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
  destruct Hwf as (((((((_ & _) & _) & Hnd) & Hwbr) & _) & _) & _); rewrite mc_map_tr_eq in Hnd.
  apply rv_fold_write_agrees; try assumption; [apply no_dup_N_to_NoDup; exact Hnd | |].
  - intro Hnin; exact (rv_cut_base_vrf_agrees penv foracle ls rf0 rf r Hsp Hrng Hnin Hunsp).
  - intros rb Hrb; unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite (Hregs rb Hrb); cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
Qed.

Lemma a64_cut_base_vrf_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle ls rf0 sp0 rf r,
    ~ In r (List.map mlr_reg (ml_regs ls)) ->
    (forall r0, In r0 (mc_unspilled_preserved EA_AArch64 ls) -> a64_read_reg r0 rf = a64_read_reg r0 rf0) ->
    mc_sym_val_agrees penv foracle (fun k => a64_read_reg k rf0) sp0
      (a64_val_read r (a64_cut_base_vrf ls)) (a64_read_reg r rf).
Proof.
  intros penv foracle ls rf0 sp0 rf r Hnin Hunsp.
  unfold a64_val_read, a64_cut_base_vrf.
  destruct (N.leb 31%N r) eqn:E31.
  - cbn [mc_sym_val_agrees]; unfold a64_read_reg; rewrite E31, eval_ce_const, repr_zero_N; reflexivity.
  - destruct (a64_is_callee_saved r && negb (slot_has_saved_reg (ml_slots ls) r)) eqn:Ep.
    + apply andb_true_iff in Ep as [Hcs Hnsav].
      cbn [mc_sym_val_agrees]; apply Hunsp.
      unfold mc_unspilled_preserved; apply filter_In; split.
      * unfold a64_is_callee_saved in Hcs; apply andb_true_iff in Hcs as [H19 H30]; apply N.leb_le in H19; apply N.leb_le in H30.
        cbn [mc_preserved_regs]; unfold a64_callee_saved_list.
        assert (Hr_eq : r = 19%N \/ r = 20%N \/ r = 21%N \/ r = 22%N \/ r = 23%N \/ r = 24%N \/ r = 25%N \/ r = 26%N \/ r = 27%N \/ r = 28%N \/ r = 29%N \/ r = 30%N) by lia.
        repeat destruct Hr_eq as [-> | Hr_eq]; cbn; auto 15.
      * apply andb_true_iff; split; [| exact Hnsav].
        apply negb_true_iff; destruct (existsb (fun rb => N.eqb (mlr_reg rb) r) (ml_regs ls)) eqn:Ex; [| reflexivity].
        apply existsb_exists in Ex as [rb [Hrb Heqr]]; apply N.eqb_eq in Heqr; subst r.
        exfalso; apply Hnin, in_map_iff; exists rb; split; [reflexivity | exact Hrb].
    + cbn [mc_sym_val_agrees]; trivial.
Qed.

Lemma a64_fold_write_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle (f_expr : mc_loop_reg_bind -> cert_expr) rf0 sp0 rf rbs base r,
    NoDup (List.map mlr_reg rbs) ->
    forallb (wf_mc_loop_reg_bind EA_AArch64) rbs = true ->
    (~ In r (List.map mlr_reg rbs) ->
       mc_sym_val_agrees penv foracle (fun k => a64_read_reg k rf0) sp0 (a64_val_read r base) (a64_read_reg r rf)) ->
    (forall rb, In rb rbs ->
       eval_closed_cert_expr penv foracle (f_expr rb) = raise_ret (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (mlr_reg rb) rf)))) ->
    mc_sym_val_agrees penv foracle (fun k => a64_read_reg k rf0) sp0
      (a64_val_read r (List.fold_left (fun vrf rb => a64_val_write (mlr_reg rb) (MSV_Expr (f_expr rb)) vrf) rbs base))
      (a64_read_reg r rf).
Proof.
  intros penv foracle f_expr rf0 sp0 rf rbs; induction rbs as [| rb rest IH];
    intros base r Hnd Hall Hbase Hfe; cbn [List.fold_left List.map] in *.
  - apply Hbase; intros [].
  - inversion Hnd as [| ? ? Hnin Hnd']; subst; cbn [forallb] in Hall; apply andb_true_iff in Hall as [Hrb Hall'].
    apply IH; try assumption; [| intros rb0 H0; apply Hfe; right; exact H0].
    intro Hninr; destruct (N.eq_dec r (mlr_reg rb)) as [-> | Hneq].
    + unfold wf_mc_loop_reg_bind in Hrb; rewrite !andb_true_iff in Hrb; destruct Hrb as (((((Hv & _) & _) & _) & _) & _).
      cbn [mc_loop_reg_valid] in Hv; apply N.leb_le in Hv.
      rewrite a64_val_write_eq by lia.
      exact (Hfe rb (or_introl eq_refl)).
    + rewrite a64_val_write_neq by exact Hneq; apply Hbase; intros [Heq | Hin]; [apply Hneq; symmetry; exact Heq | exact (Hninr Hin)].
Qed.

Lemma a64_cut_vrf_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle ls rf0 sp0 rf,
    wf_mc_loop_spec EA_AArch64 ls = true ->
    (forall r, In r (mc_unspilled_preserved EA_AArch64 ls) -> a64_read_reg r rf = a64_read_reg r rf0) ->
    (forall rb, In rb (ml_regs ls) ->
       eval_closed_cert_expr penv foracle (mlr_expr rb) =
         raise_ret (DVALUE_Base (@DVALUE_I Pa (mlr_width rb) (@Integers.repr (mlr_width rb) (@Integers.unsigned 64%positive (a64_read_reg (mlr_reg rb) rf))))) /\
       (mlr_width rb = 32%positive ->
          penv (mc_hi_var_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (mlr_reg rb) rf))))) ->
    a64_val_regs_agrees penv foracle rf0 sp0 (a64_cut_vrf ls) rf.
Proof.
  intros penv foracle ls rf0 sp0 rf Hwf Hunsp Hregs r.
  unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
  destruct Hwf as (((((((_ & _) & _) & Hnd) & Hwbr) & _) & _) & _); rewrite mc_map_tr_eq in Hnd.
  apply a64_fold_write_agrees; try assumption; [apply no_dup_N_to_NoDup; exact Hnd | |].
  - intro Hnin; exact (a64_cut_base_vrf_agrees penv foracle ls rf0 sp0 rf r Hnin Hunsp).
  - intros rb Hrb; destruct (Hregs rb Hrb) as [Hev Hhi].
    rewrite forallb_forall in Hwbr; pose proof (Hwbr rb Hrb) as Hwrb.
    unfold wf_mc_loop_reg_bind in Hwrb; rewrite !andb_true_iff in Hwrb; destruct Hwrb as (((((_ & Hw) & _) & _) & _) & _).
    unfold cut_reg_expr; apply orb_true_iff in Hw as [Hw32 | Hw64].
    + apply Pos.eqb_eq in Hw32; rewrite Hw32 in *; cbn [Pos.eqb].
      eapply combine_hi32_expr_sound; [| exact Hev | reflexivity].
      unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite (Hhi eq_refl); cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
    + apply Pos.eqb_eq in Hw64; rewrite Hw64 in *; rewrite Pos.eqb_refl; rewrite (@Integers.repr_unsigned 64%positive) in Hev; exact Hev.
Qed.

Lemma a64_skel_vrf_agrees {Pa : Params} :
  forall (penv : param_env Pa) foracle ls rf0 sp0 rf,
    wf_mc_loop_spec EA_AArch64 ls = true ->
    (forall r, In r (mc_unspilled_preserved EA_AArch64 ls) -> a64_read_reg r rf = a64_read_reg r rf0) ->
    (forall rb, In rb (ml_regs ls) ->
       penv (mc_skel_reg_name (mlr_reg rb)) = Some (DVALUE_Base (@DVALUE_I Pa 64%positive (a64_read_reg (mlr_reg rb) rf)))) ->
    a64_val_regs_agrees penv foracle rf0 sp0 (a64_skel_vrf ls) rf.
Proof.
  intros penv foracle ls rf0 sp0 rf Hwf Hunsp Hregs r.
  unfold wf_mc_loop_spec in Hwf; rewrite !andb_true_iff in Hwf.
  destruct Hwf as (((((((_ & _) & _) & Hnd) & Hwbr) & _) & _) & _); rewrite mc_map_tr_eq in Hnd.
  apply a64_fold_write_agrees; try assumption; [apply no_dup_N_to_NoDup; exact Hnd | |].
  - intro Hnin; exact (a64_cut_base_vrf_agrees penv foracle ls rf0 sp0 rf r Hnin Hunsp).
  - intros rb Hrb; unfold eval_closed_cert_expr; cbn [eval_cert_expr lookup_let_val]; rewrite (Hregs rb Hrb); cbn [check_scalar_width]; rewrite Pos.eqb_refl; reflexivity.
Qed.

Lemma mc_skel_tree_ok_extract {Pa : Params} :
  forall arch ls (penv : param_env Pa) foracle P_cut P_ret t,
    mc_skel_tree_ok arch ls t = true ->
    mc_seg_holds penv foracle P_cut P_ret t ->
    (exists sp' rr' astk',
       sp' = ml_sp_off ls /\
       (forall r, In r (mc_unspilled_preserved arch ls) -> rr' r = MSV_SavedReg r) /\
       (forall off r, In (MLS_SavedReg off r) (ml_slots ls) ->
          mc_sym_stk_load off MS_8 false astk' = Some (MSV_SavedReg r)) /\
       P_cut sp' rr' astk') \/
    (exists ret_e, P_ret ret_e).
Proof.
  intros arch ls penv foracle P_cut P_ret t.
  induction t as [sp' rr' astk' | ret_e | cond dt IHt df IHf];
    intros Hok Hh; cbn [mc_skel_tree_ok mc_seg_holds] in *.
  - rewrite !andb_true_iff in Hok; destruct Hok as [[Hsp Hunsp] Hsav].
    apply Z.eqb_eq in Hsp.
    left; exists sp', rr', astk'; repeat split; try assumption.
    + intros r Hr; rewrite forallb_forall in Hunsp; pose proof (Hunsp r Hr) as Hr0.
      destruct (rr' r) as [| | r0 |]; try discriminate Hr0; apply N.eqb_eq in Hr0; subst r0; reflexivity.
    + intros off r Hr; rewrite forallb_forall in Hsav; pose proof (Hsav (MLS_SavedReg off r) Hr) as Hr0.
      cbn in Hr0; destruct (mc_sym_stk_load off MS_8 false astk') as [sv |] eqn:Eld;
        [destruct sv as [| | r0 |] |]; try discriminate Hr0;
        apply N.eqb_eq in Hr0; subst r0; reflexivity.
  - right; exists ret_e; exact Hh.
  - apply andb_true_iff in Hok as [Ht Hf]; destruct Hh as [b [_ Hsub]].
    destruct b; [exact (IHt Ht Hsub) | exact (IHf Hf Hsub)].
Qed.

Definition mc_cut_obl_inv_holds {Pa : Params}
  (ls : mc_loop_spec) (penv : param_env Pa) (foracle : freeze_oracle) : Prop :=
  match ml_inv ls with
  | None => True
  | Some inv_e =>
      eval_closed_cert_expr penv foracle inv_e =
      raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
  end.

Definition expr_cut_vars_ok (ls : mc_loop_spec) (e : cert_expr) : Prop :=
  forall nm w, In (nm, w) (collect_free_vars [] e) -> mc_starts_with_bang nm = false \/ exists k, nm = mc_cut_var_name k.

Lemma expr_has_var_false_not_in : forall nm e,
  expr_has_var nm e = false -> forall w, ~ In (nm, w) (collect_free_vars [] e).
Proof.
  intros nm e Hfv w Hin; unfold expr_has_var in Hfv.
  assert (Htru : existsb (fun '(x, _) => String.eqb x nm) (collect_free_vars [] e) = true)
    by (apply existsb_exists; exists (nm, w); split; [exact Hin | apply String.eqb_refl]).
  rewrite Htru in Hfv; discriminate Hfv.
Qed.

Lemma eval_cert_expr_penv_eq_if_vars {Pa : Params} :
  forall (penv1 penv2 : param_env Pa) foracle e,
    is_let_free_expr e = true ->
    (forall nm w, In (nm, w) (collect_free_vars [] e) -> penv1 nm = penv2 nm) ->
    eval_closed_cert_expr penv1 foracle e = eval_closed_cert_expr penv2 foracle e.
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
    intros Hlf Hag; unfold eval_closed_cert_expr in *;
    cbn [is_let_free_expr collect_free_vars eval_cert_expr lookup_let_val] in *;
    try reflexivity; try discriminate Hlf.
  - rewrite (Hag nm w (or_introl eq_refl)); reflexivity.
  - apply andb_true_iff in Hlf as [Hl Hr];
      rewrite (IHl Hl (fun x wx H => Hag x wx (in_or_app _ _ _ (or_introl H)))),
              (IHr Hr (fun x wx H => Hag x wx (in_or_app _ _ _ (or_intror H)))); reflexivity.
  - apply andb_true_iff in Hlf as [Hl Hr];
      rewrite (IHl Hl (fun x wx H => Hag x wx (in_or_app _ _ _ (or_introl H)))),
              (IHr Hr (fun x wx H => Hag x wx (in_or_app _ _ _ (or_intror H)))); reflexivity.
  - rewrite (IHo Hlf Hag); reflexivity.
  - rewrite !andb_true_iff in Hlf; destruct Hlf as [[Hc Ht] Hf];
      rewrite (IHc Hc (fun x wx H => Hag x wx (in_or_app _ _ _ (or_introl H)))),
              (IHt Ht (fun x wx H => Hag x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl H)))))),
              (IHf Hf (fun x wx H => Hag x wx (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror H)))))); reflexivity.
  - rewrite (IHo Hlf Hag); reflexivity.
Qed.

Lemma check_widths_match_spec : forall ws phis,
  check_widths_match ws phis = true ->
  Forall2 (fun w '(wp, _) => w = wp) ws phis.
Proof.
  induction ws as [| w rw IH]; intros [| [wp ce] rp] H; cbn in H; try discriminate H; [constructor |].
  apply andb_true_iff in H as [Hw Hr]; apply Pos.eqb_eq in Hw; constructor; [exact Hw | exact (IH rp Hr)].
Qed.

Definition is_ptol_for_spec (ls : mc_loop_spec) (hdr_ws : list positive) (idx : nat) (w : positive) : bool :=
  match nth_error hdr_ws idx with
  | Some w' => Pos.eqb w w' && cut_var_ptol ls idx w
  | None => false
  end.

Lemma expr_is_ptol_var_at_spec : forall ls hdr_ws idx e,
  expr_is_ptol_var_at ls idx hdr_ws e = true ->
  exists k w,
    (idx <= k)%nat /\
    nth_error hdr_ws (k - idx)%nat = Some w /\
    e = CE_Var (mc_cut_var_name k) w /\
    cut_var_ptol ls k w = true.
Proof.
  intros ls hdr_ws; induction hdr_ws as [| w_h rest IH]; intros idx e H; cbn in H; [discriminate H |].
  apply orb_true_iff in H as [Hhere | Hlater].
  - apply andb_true_iff in Hhere as [He Hpt].
    destruct e as [| | nm bw | | | | | |]; try discriminate He; cbn in He; apply andb_true_iff in He as [Hnm Hw].
    apply String.eqb_eq in Hnm; apply Pos.eqb_eq in Hw; rewrite Hnm, <- Hw.
    exists idx, w_h; rewrite Nat.sub_diag; repeat split; try lia; try reflexivity; exact Hpt.
  - destruct (IH (S idx) e Hlater) as (k & wk & Hle & Hnth & He & Hpt).
    exists k, wk; repeat split; try lia; try assumption.
    replace (k - idx)%nat with (S (k - S idx))%nat by lia; exact Hnth.
Qed.

Lemma expr_not_ptol_var_avoids_ptol : forall ls hdr_ws e k w,
  expr_is_ptol_var ls hdr_ws e = false ->
  nth_error hdr_ws k = Some w ->
  cut_var_ptol ls k w = true ->
  reg_slot_uses_cut_var_ok k w e = true ->
  forall w0, ~ In (mc_cut_var_name k, w0) (collect_free_vars [] e).
Proof.
  intros ls hdr_ws e k w Hno Hnth Hpt Hok w0 Hin.
  unfold reg_slot_uses_cut_var_ok in Hok; apply orb_true_iff in Hok as [Hneg | His].
  - apply negb_true_iff in Hneg; exact (expr_has_var_false_not_in _ _ Hneg w0 Hin).
  - destruct e as [| | nm bw | | | | | |]; try discriminate His; cbn in His; apply andb_true_iff in His as [Hnm Hw].
    apply String.eqb_eq in Hnm; apply Pos.eqb_eq in Hw; subst nm bw.
    assert (Hyes : expr_is_ptol_var ls hdr_ws (CE_Var (mc_cut_var_name k) w) = true).
    { unfold expr_is_ptol_var; clear -Hnth Hpt.
      assert (Hgen : forall idx xs, nth_error xs (k - idx)%nat = Some w -> (idx <= k)%nat ->
        expr_is_ptol_var_at ls idx xs (CE_Var (mc_cut_var_name k) w) = true).
      { intros idx xs; revert idx; induction xs as [| x rx IH]; intros idx Hn Hle; cbn in *.
        - destruct (k - idx)%nat; discriminate Hn.
        - destruct (Nat.eq_dec idx k) as [-> | Hneq].
          + rewrite Nat.sub_diag in Hn; inversion Hn; subst x.
            rewrite String.eqb_refl, Pos.eqb_refl, Hpt; reflexivity.
          + replace (k - idx)%nat with (S (k - S idx))%nat in Hn by lia.
            rewrite (IH (S idx) Hn ltac:(lia)), orb_true_r; reflexivity. }
      exact (Hgen 0%nat hdr_ws ltac:(rewrite Nat.sub_0_r; exact Hnth) ltac:(lia)). }
    rewrite Hyes in Hno; discriminate Hno.
Qed.

Lemma build_phi_subst_in : forall idx phis nm w ce,
  In (nm, w, ce) (build_phi_subst idx phis) ->
  exists j, nm = mc_cut_var_name (idx + j) /\ nth_error phis j = Some (w, ce).
Proof.
  intros idx phis; revert idx; induction phis as [| [w0 ce0] rest IH];
    intros idx nm w ce Hin; cbn [build_phi_subst] in Hin; [contradiction |].
  destruct Hin as [Heq | Hinr].
  - inversion Heq; subst; exists 0%nat; rewrite Nat.add_0_r; split; reflexivity.
  - destruct (IH (S idx) nm w ce Hinr) as [j [Hnm Hnth]].
    exists (S j); split; [rewrite Hnm; f_equal; lia | exact Hnth].
Qed.

Lemma build_phi_subst_nodup : forall idx phis,
  NoDup (List.map (fun '(x, _, _) => x) (build_phi_subst idx phis)).
Proof.
  intros idx phis; revert idx; induction phis as [| [w ce] rest IH];
    intro idx; cbn [build_phi_subst List.map]; constructor; [| exact (IH (S idx))].
  intro Hin; apply in_map_iff in Hin as [[[nm w0] ce0] [Hnm Hrest]].
  subst nm; destruct (build_phi_subst_in _ _ _ _ _ Hrest) as [j [Heq _]].
  apply mc_cut_var_name_inj in Heq; lia.
Qed.

Lemma lookup_phi_subst_some : forall idx phis j w ce,
  nth_error phis j = Some (w, ce) ->
  lookup_subst (mc_cut_var_name (idx + j)) (build_phi_subst idx phis) = Some (w, ce).
Proof.
  intros idx phis; revert idx; induction phis as [| [w0 ce0] rest IH];
    intros idx j w ce Hnth; cbn [build_phi_subst lookup_subst]; [destruct j; discriminate Hnth |].
  destruct j as [| j']; cbn in Hnth.
  - inversion Hnth; subst w0 ce0; rewrite Nat.add_0_r, String.eqb_refl; reflexivity.
  - destruct (String.eqb (mc_cut_var_name (idx + S j')) (mc_cut_var_name idx)) eqn:Eeq.
    + apply String.eqb_eq, mc_cut_var_name_inj in Eeq; lia.
    + replace (idx + S j')%nat with (S idx + j')%nat by lia; exact (IH (S idx) j' w ce Hnth).
Qed.

Lemma lookup_phi_subst_none_non_bang : forall idx phis nm,
  mc_starts_with_bang nm = false ->
  lookup_subst nm (build_phi_subst idx phis) = None.
Proof.
  intros idx phis; revert idx; induction phis as [| [w ce] rest IH];
    intros idx nm Hnb; cbn [build_phi_subst lookup_subst]; [reflexivity |].
  destruct (String.eqb nm (mc_cut_var_name idx)) eqn:Eeq.
  - apply String.eqb_eq in Eeq; subst nm; cbn in Hnb; discriminate Hnb.
  - exact (IH (S idx) nm Hnb).
Qed.

Lemma build_phi_subst_wf : forall allowed_ir idx phis,
  Forall (fun '(wp, ce) =>
    wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
    is_let_free_expr ce = true /\ ub_free_expr ce = true /\ incl (collect_free_vars [] ce) allowed_ir) phis ->
  Forall (subst_entry_wf allowed_ir) (build_phi_subst idx phis).
Proof.
  intros allowed_ir idx phis; revert idx; induction phis as [| [w ce] rest IH];
    intros idx Hfa; cbn [build_phi_subst]; [constructor |].
  inversion Hfa as [| ? ? Hw Hrest]; subst; constructor; [exact Hw | exact (IH (S idx) Hrest)].
Qed.

Lemma collect_phi_def_obls_acc_sound {Pa : Params} :
  forall ls (penv_mc : param_env Pa) opt_inv is_body path idx phis acc,
    (is_body = true ->
     match opt_inv with
     | None => True
     | Some inv_e =>
         eval_closed_cert_expr penv_mc dummy_freeze_oracle inv_e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
     end) ->
    (forall (b : bool) (c : cert_expr), In (b, c) path ->
       eval_closed_cert_expr penv_mc dummy_freeze_oracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body)
      (collect_phi_def_obls_acc ls is_body path idx phis acc) ->
    Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) acc /\
    (forall j w ce,
       nth_error phis j = Some (w, ce) ->
       cut_var_ptol ls (idx + j) w = false ->
       exists vi,
         eval_closed_cert_expr penv_mc dummy_freeze_oracle ce =
         raise_ret (DVALUE_Base (@DVALUE_I Pa w vi))).
Proof.
  intros ls penv_mc opt_inv is_body path idx phis;
    revert idx; induction phis as [| [w0 ce0] rest IH];
    intros idx acc Hinv Hpath Hfa; cbn [collect_phi_def_obls_acc] in *.
  - split; [exact Hfa | intros [| j'] ? ? Hn; discriminate Hn].
  - destruct (cut_var_ptol ls idx w0) eqn:Ept.
    + destruct (IH (S idx) acc Hinv Hpath Hfa) as [Hacc Hrest].
      split; [exact Hacc | intros [| j'] w ce Hn Hpt].
      * inversion Hn; subst w0 ce0; rewrite Nat.add_0_r, Ept in Hpt; discriminate Hpt.
      * replace (idx + S j')%nat with (S idx + j')%nat in Hpt by lia; exact (Hrest j' w ce Hn Hpt).
    + destruct (IH (S idx) (MLO_Defined is_body path w0 ce0 :: acc) Hinv Hpath Hfa) as [Hacc Hrest].
      inversion Hacc as [| ? ? Hd Hacc0]; subst.
      split; [exact Hacc0 | intros [| j'] w ce Hn Hpt].
      * inversion Hn; subst w0 ce0; exact (Hd eq_refl Hinv Hpath).
      * replace (idx + S j')%nat with (S idx + j')%nat in Hpt by lia; exact (Hrest j' w ce Hn Hpt).
Qed.

Lemma collect_reg_cut_obls_acc_sound {Pa : Params} :
  forall ls hdr_ws (penv_mc : param_env Pa) opt_inv is_body path sub rr' rbs acc res,
    collect_reg_cut_obls_acc ls hdr_ws is_body path sub rr' rbs acc = inr res ->
    Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) res ->
    Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) acc /\
    (forall rb, In rb rbs ->
       exists e_mc64,
         rr' (mlr_reg rb) = MSV_Expr e_mc64 /\
         mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
           (MLO_Refine is_body path (mlr_width rb) (subst_cert_expr sub (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
         (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false ->
          mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
            (MLO_Defined is_body path (mlr_width rb) (subst_cert_expr sub (mlr_expr rb))))).
Proof.
  intros ls hdr_ws penv_mc opt_inv is_body path sub rr' rbs;
    induction rbs as [| rb0 rest IH]; intros acc res Hrec Hfa; cbn [collect_reg_cut_obls_acc] in Hrec.
  - inversion Hrec; subst res; split; [exact Hfa | intros rb []].
  - destruct (rr' (mlr_reg rb0)) as [| e_mc64 | |] eqn:Err; try discriminate Hrec.
    destruct (expr_is_ptol_var ls hdr_ws (mlr_expr rb0)) eqn:Ept.
    + destruct (IH _ res Hrec Hfa) as [Hacc Hrest].
      inversion Hacc as [| ? ? Ho_r Hacc0]; subst.
      split; [exact Hacc0 | intros rb [<- | Hinr]].
      * exists e_mc64; split; [exact Err | split; [exact Ho_r | intro C; congruence]].
      * exact (Hrest rb Hinr).
    + destruct (IH _ res Hrec Hfa) as [Hacc Hrest].
      inversion Hacc as [| ? ? Ho_d Hacc1]; subst; inversion Hacc1 as [| ? ? Ho_r Hacc0]; subst.
      split; [exact Hacc0 | intros rb [<- | Hinr]].
      * exists e_mc64; split; [exact Err | split; [exact Ho_r | intros _; exact Ho_d]].
      * exact (Hrest rb Hinr).
Qed.

Lemma collect_slot_cut_obls_acc_sound {Pa : Params} :
  forall ls hdr_ws (penv_mc : param_env Pa) opt_inv is_body path sub astk' sbs acc res,
    collect_slot_cut_obls_acc ls hdr_ws is_body path sub astk' sbs acc = inr res ->
    Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) res ->
    Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) acc /\
    (forall off r, In (MLS_SavedReg off r) sbs ->
       mc_sym_stk_load off MS_8 false astk' = Some (MSV_SavedReg r)) /\
    (forall off sz e_s, In (MLS_Expr off sz e_s) sbs ->
       exists e_mc64,
         mc_sym_stk_load off sz false astk' = Some (MSV_Expr e_mc64) /\
         mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
           (MLO_Refine is_body path (mc_mem_bits sz) (subst_cert_expr sub e_s) (trunc_mc_slot_expr sz e_mc64)) /\
         (expr_is_ptol_var ls hdr_ws e_s = false ->
          mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
            (MLO_Defined is_body path (mc_mem_bits sz) (subst_cert_expr sub e_s)))).
Proof.
  intros ls hdr_ws penv_mc opt_inv is_body path sub astk' sbs;
    induction sbs as [| [o s e | o r0] rest IH]; intros acc res Hrec Hfa; cbn [collect_slot_cut_obls_acc] in Hrec.
  - inversion Hrec; subst res; split; [exact Hfa | split; intros; contradiction].
  - destruct (mc_sym_stk_load o s false astk') as [[| em | |] |] eqn:Eld; try discriminate Hrec.
    destruct (expr_is_ptol_var ls hdr_ws e) eqn:Ept.
    + destruct (IH _ res Hrec Hfa) as (Hacc & Hsav & Hexp).
      inversion Hacc as [| ? ? Ho_r Hacc0]; subst.
      split; [exact Hacc0 | split].
      * intros off r [Hc | Hr]; [discriminate Hc | exact (Hsav off r Hr)].
      * intros off sz e_s [Heq | Hr].
        -- inversion Heq; subst; exists em; split; [exact Eld | split; [exact Ho_r | intro C; congruence]].
        -- exact (Hexp off sz e_s Hr).
    + destruct (IH _ res Hrec Hfa) as (Hacc & Hsav & Hexp).
      inversion Hacc as [| ? ? Ho_d Hacc1]; subst; inversion Hacc1 as [| ? ? Ho_r Hacc0]; subst.
      split; [exact Hacc0 | split].
      * intros off r [Hc | Hr]; [discriminate Hc | exact (Hsav off r Hr)].
      * intros off sz e_s [Heq | Hr].
        -- inversion Heq; subst; exists em; split; [exact Eld | split; [exact Ho_r | intros _; exact Ho_d]].
        -- exact (Hexp off sz e_s Hr).
  - destruct (mc_sym_stk_load o MS_8 false astk') as [[| | r1 |] |] eqn:Eld; try discriminate Hrec.
    destruct (N.eqb r1 r0) eqn:Er; [| discriminate Hrec]; apply N.eqb_eq in Er; subst r1.
    destruct (IH acc res Hrec Hfa) as (Hacc & Hsav & Hexp).
    split; [exact Hacc | split].
    + intros off r [Heq | Hr]; [inversion Heq; subst; exact Eld | exact (Hsav off r Hr)].
    + intros off sz e_s [Hc | Hr]; [discriminate Hc | exact (Hexp off sz e_s Hr)].
Qed.

(** Leaf-pair soundness for [collect_mc_ir_obls_acc] against generic
    [ir_seg_eval_spec] and [mc_seg_holds]. *)
Theorem collect_mc_ir_obls_acc_sound {Pa : Params} :
  forall arch ls ret_w hdr_ws allowed_ir (is_body : bool)
         (penv_ir penv_mc : param_env Pa)
         bmap hdr_id hdr_phis wr_keep env0 bid_from cur_bid t_ir
         P_cut P_ret t_mc opt_inv (path : list (bool * cert_expr)) acc res,
    extract_hdr_phi_widths hdr_phis = hdr_ws ->
    ir_seg_wf allowed_ir hdr_ws t_ir ->
    ir_seg_freeze_free t_ir = true ->
    (forall nm w, In (nm, w) allowed_ir ->
       exists d1 d2 : @dvalue Pa,
         penv_ir nm = Some d1 /\ penv_mc nm = Some d2 /\
         wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2) ->
    ir_seg_eval_spec bmap hdr_id hdr_phis wr_keep penv_ir env0 bid_from cur_bid t_ir ->
    mc_seg_holds penv_mc dummy_freeze_oracle P_cut P_ret t_mc ->
    (is_body = true ->
     match opt_inv with
     | None => True
     | Some inv_e =>
         eval_closed_cert_expr penv_mc dummy_freeze_oracle inv_e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
     end) ->
    (forall (b : bool) (c : cert_expr), In (b, c) path ->
       eval_closed_cert_expr penv_mc dummy_freeze_oracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    collect_mc_ir_obls_acc arch ls ret_w hdr_ws is_body path t_ir t_mc acc = inr res ->
    Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) res ->
    Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) acc /\
    ((forall sigma, cfg_steps_to_ub sigma env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))) \/
     (exists env_out dv_ir ret_mc dv_mc,
        pure_cfg_steps env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid)) env_out dv_ir /\
        P_ret ret_mc /\
        eval_closed_cert_expr penv_mc dummy_freeze_oracle ret_mc = raise_ret dv_mc /\
        dvalue_refines dv_ir dv_mc) \/
     (exists env_c bid_c b_hdr dvs lmap_cut phis_ir sp' rr' astk',
        ((env_c = env0 /\ bid_c = bid_from /\ cur_bid = hdr_id) \/
         pure_cfg_steps_to_tau env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))
           env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id))) /\
        RM.find hdr_id bmap = Some b_hdr /\
        In lmap_cut (collect_entry_cut_lmaps t_ir) /\
        lmap_matches_env penv_ir lmap_cut env_c /\
        (forall r, In r wr_keep -> RM.find r env_c = RM.find r env0) /\
        pure_cfg_steps env_c (denote_phis bid_c (blk_phis b_hdr)) (apply_phi_env env_c dvs) tt /\
        Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs /\
        Forall2 (fun w '(wp, _) => w = wp) hdr_ws phis_ir /\
        Forall (fun '(wp, ce) =>
          wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
          is_let_free_expr ce = true /\ ub_free_expr ce = true /\
          expr_has_freeze ce = false /\ incl (collect_free_vars [] ce) allowed_ir) phis_ir /\
        Forall2 (fun '(wp, ce) '(_, dv) =>
          eval_closed_cert_expr penv_ir dummy_freeze_oracle ce = raise_ret dv /\
          wf_scalar_dvalue wp dv) phis_ir dvs /\
        sp' = ml_sp_off ls /\
        P_cut sp' rr' astk' /\
        (forall r, In r (mc_unspilled_preserved arch ls) -> rr' r = MSV_SavedReg r) /\
        (forall k w ce,
           nth_error phis_ir k = Some (w, ce) ->
           cut_var_ptol ls k w = false ->
           exists vi,
             eval_closed_cert_expr penv_mc dummy_freeze_oracle ce =
             raise_ret (DVALUE_Base (@DVALUE_I Pa w vi))) /\
        (forall rb, In rb (ml_regs ls) ->
           exists e_mc64,
             rr' (mlr_reg rb) = MSV_Expr e_mc64 /\
             mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
               (MLO_Refine is_body path (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
             (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false ->
              mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
                (MLO_Defined is_body path (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb))))) /\
        (forall off r, In (MLS_SavedReg off r) (ml_slots ls) ->
           mc_sym_stk_load off MS_8 false astk' = Some (MSV_SavedReg r)) /\
        (forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) ->
           exists e_mc64,
             mc_sym_stk_load off sz false astk' = Some (MSV_Expr e_mc64) /\
             mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
               (MLO_Refine is_body path (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
             (expr_is_ptol_var ls hdr_ws e_s = false ->
              mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
                (MLO_Defined is_body path (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s)))) /\
        match ml_inv ls with
        | None => True
        | Some inv_e =>
            mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
              (MLO_Refine is_body path 1%positive (CE_BvConst 1%positive 1%N) (subst_cert_expr (build_phi_subst 0%nat phis_ir) inv_e))
        end)).
Proof.
  intros arch ls ret_w hdr_ws allowed_ir is_body penv_ir penv_mc bmap hdr_id hdr_phis wr_keep.
  intros env0 bid_from cur_bid t_ir P_cut P_ret t_mc opt_inv path acc res Hhdr Hwf_ir Hfrz_ir Href.
  revert env0 bid_from cur_bid path acc res Hwf_ir Hfrz_ir.
  induction t_ir as [lmap_cut phis_ir | rw ret_ir | | cond dt_ir IHt df_ir IHf];
    intros env0 bid_from cur_bid path acc res Hwf_ir Hfrz_ir Hir Hmc Hinv Hpath Hcol Hobls.
  - (* IST_Cut *)
    destruct Hwf_ir as [_ Hwf_phis]; cbn [ir_seg_freeze_free ir_seg_exprs_freeze_free_cut] in Hfrz_ir.
    assert (Hphis_wf : Forall (fun '(wp, ce) =>
      wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
      is_let_free_expr ce = true /\ ub_free_expr ce = true /\
      expr_has_freeze ce = false /\ incl (collect_free_vars [] ce) allowed_ir) phis_ir).
    { clear -Hwf_phis Hfrz_ir.
      induction Hwf_phis as [| w [wp ce] rw rp (_ & Hwt & Hbw & Hlf & Hub & Hfv) _ IH];
        cbn [forallb] in *; [constructor |].
      apply andb_true_iff in Hfrz_ir as [Hnfrz Hfrz_r]; apply negb_true_iff in Hnfrz.
      constructor; [repeat split; assumption | exact (IH Hfrz_r)]. }
    clear Hhdr; induction t_mc as [sp' rr' astk' | ret_mc | cond_mc dt_mc IHtm df_mc IHfm] in path, acc, res, Hmc, Hpath, Hcol, Hobls |- *;
      cbn [collect_mc_ir_obls_acc mc_seg_holds] in Hcol, Hobls, Hmc.
    + destruct (Z.eqb sp' (ml_sp_off ls)) eqn:Hsp; cbn [negb] in Hcol; [| discriminate Hcol].
      destruct (check_unspilled_preserved_diag _ rr' (mc_unspilled_preserved arch ls)) as [| []] eqn:Hunsp_d;
        [discriminate Hcol |].
      pose proof (check_unspilled_preserved_diag_sound _ _ _ Hunsp_d) as Hunsp.
      destruct (check_widths_match hdr_ws phis_ir) eqn:Hwm; cbn [negb] in Hcol; [| discriminate Hcol].
      set (a_inv := match ml_inv ls with None => acc | Some inv_e => MLO_Refine is_body path 1%positive (CE_BvConst 1%positive 1%N) (subst_cert_expr (build_phi_subst 0%nat phis_ir) inv_e) :: acc end) in *.
      set (a_phi := collect_phi_def_obls_acc ls is_body path 0%nat phis_ir a_inv) in *.
      destruct (collect_reg_cut_obls_acc ls hdr_ws is_body path (build_phi_subst 0%nat phis_ir) rr' (ml_regs ls) a_phi) as [| a_reg] eqn:Ero;
        [discriminate Hcol |].
      destruct (collect_slot_cut_obls_acc_sound ls hdr_ws penv_mc opt_inv is_body path (build_phi_subst 0%nat phis_ir) astk' (ml_slots ls) a_reg res Hcol Hobls)
        as (Hfa_reg & Hsav & Hslts_o).
      destruct (collect_reg_cut_obls_acc_sound ls hdr_ws penv_mc opt_inv is_body path (build_phi_subst 0%nat phis_ir) rr' (ml_regs ls) a_phi a_reg Ero Hfa_reg)
        as (Hfa_phi & Hregs_o).
      destruct (collect_phi_def_obls_acc_sound ls penv_mc opt_inv is_body path 0%nat phis_ir a_inv Hinv Hpath Hfa_phi)
        as (Hfa_inv & Hphi_d).
      assert (Hacc_ok : Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) acc).
      { unfold a_inv in Hfa_inv; destruct (ml_inv ls); [inversion Hfa_inv; assumption | exact Hfa_inv]. }
      split; [exact Hacc_ok |].
      destruct Hir as [Hub | (env_c & bid_c & b_hdr & dvs & Htau & Ebh & Hlm & Hkp & Hph & Hids & Hstp)]; [left; exact Hub |].
      right; right; exists env_c, bid_c, b_hdr, dvs, lmap_cut, phis_ir, sp', rr', astk'.
      apply Z.eqb_eq in Hsp.
      cbn [collect_entry_cut_lmaps].
      repeat split; try assumption.
      * left; reflexivity.
      * exact (check_widths_match_spec _ _ Hwm).
      * intros r Hr; rewrite forallb_forall in Hunsp; pose proof (Hunsp r Hr) as Hrr.
        destruct (rr' r) as [| | r0 |]; try discriminate Hrr; apply N.eqb_eq in Hrr; subst r0; reflexivity.
      * unfold a_inv in Hfa_inv; destruct (ml_inv ls); [inversion Hfa_inv; assumption | exact I].
    + destruct (mc_path_unconditional ls is_body path); [discriminate Hcol |].
      inversion Hcol; subst res; exfalso; exact (imposs_obl_absurd penv_mc dummy_freeze_oracle opt_inv is_body path Hinv Hpath ltac:(constructor; [exact (Forall_inv Hobls) | constructor])).
    + destruct Hmc as [b [Hbc Hsub]].
      assert (Hpath' : forall (b0 : bool) (c0 : cert_expr), In (b0, c0) ((b, cond_mc) :: path) ->
        eval_closed_cert_expr penv_mc dummy_freeze_oracle c0 =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b0 then @Integers.one 1%positive else @Integers.zero 1%positive)))).
      { intros b0 c0 [Heq | Hin]; [inversion Heq; subst; exact Hbc | exact (Hpath b0 c0 Hin)]. }
      match type of Hcol with
      | match ?f with inl _ => _ | inr _ => _ end = _ => destruct f as [| af] eqn:Haf_eq
      end; [discriminate Hcol |].
      assert (Haf : Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) af) by
        exact (collect_mc_ir_obls_acc_sub _ arch ls ret_w hdr_ws is_body ((true, cond_mc) :: path) (IST_Cut lmap_cut phis_ir) dt_mc af res Hcol Hobls).
      assert (Hacc_or_sub :
        Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) acc /\
        ((forall sigma, cfg_steps_to_ub sigma env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))) \/
         (exists env_out dv_ir ret_mc dv_mc,
            pure_cfg_steps env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid)) env_out dv_ir /\
            P_ret ret_mc /\
            eval_closed_cert_expr penv_mc dummy_freeze_oracle ret_mc = raise_ret dv_mc /\
            dvalue_refines dv_ir dv_mc) \/
         (exists env_c bid_c b_hdr dvs lmap_cut0 phis_ir0 sp' rr' astk',
            ((env_c = env0 /\ bid_c = bid_from /\ cur_bid = hdr_id) \/
             pure_cfg_steps_to_tau env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))
               env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id))) /\
            RM.find hdr_id bmap = Some b_hdr /\
            In lmap_cut0 (collect_entry_cut_lmaps (IST_Cut lmap_cut phis_ir)) /\
            lmap_matches_env penv_ir lmap_cut0 env_c /\
            (forall r, In r wr_keep -> RM.find r env_c = RM.find r env0) /\
            pure_cfg_steps env_c (denote_phis bid_c (blk_phis b_hdr)) (apply_phi_env env_c dvs) tt /\
            Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs /\
            Forall2 (fun w '(wp, _) => w = wp) hdr_ws phis_ir0 /\
            Forall (fun '(wp, ce) =>
              wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
              is_let_free_expr ce = true /\ ub_free_expr ce = true /\
              expr_has_freeze ce = false /\ incl (collect_free_vars [] ce) allowed_ir) phis_ir0 /\
            Forall2 (fun '(wp, ce) '(_, dv) =>
              eval_closed_cert_expr penv_ir dummy_freeze_oracle ce = raise_ret dv /\
              wf_scalar_dvalue wp dv) phis_ir0 dvs /\
            sp' = ml_sp_off ls /\ P_cut sp' rr' astk' /\
            (forall r, In r (mc_unspilled_preserved arch ls) -> rr' r = MSV_SavedReg r) /\
            (forall k w ce, nth_error phis_ir0 k = Some (w, ce) -> cut_var_ptol ls k w = false ->
               exists vi, eval_closed_cert_expr penv_mc dummy_freeze_oracle ce = raise_ret (DVALUE_Base (@DVALUE_I Pa w vi))) /\
            (forall rb, In rb (ml_regs ls) -> exists e_mc64, rr' (mlr_reg rb) = MSV_Expr e_mc64 /\
               mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body ((b, cond_mc) :: path) (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
               (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false -> mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Defined is_body ((b, cond_mc) :: path) (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) (mlr_expr rb))))) /\
            (forall off r, In (MLS_SavedReg off r) (ml_slots ls) -> mc_sym_stk_load off MS_8 false astk' = Some (MSV_SavedReg r)) /\
            (forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) -> exists e_mc64, mc_sym_stk_load off sz false astk' = Some (MSV_Expr e_mc64) /\
               mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body ((b, cond_mc) :: path) (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
               (expr_is_ptol_var ls hdr_ws e_s = false -> mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Defined is_body ((b, cond_mc) :: path) (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) e_s)))) /\
            match ml_inv ls with None => True | Some inv_e => mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body ((b, cond_mc) :: path) 1%positive (CE_BvConst 1%positive 1%N) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) inv_e)) end))).
      { destruct b.
        -- destruct (IHtm ((true, cond_mc) :: path) af res Hsub Hpath' Hcol Hobls) as [_ Hres]; split.
           ++ exact (collect_mc_ir_obls_acc_sub _ arch ls ret_w hdr_ws is_body ((false, cond_mc) :: path) (IST_Cut lmap_cut phis_ir) df_mc acc af Haf_eq Haf).
           ++ exact Hres.
        -- exact (IHfm ((false, cond_mc) :: path) acc af Hsub Hpath' Haf_eq Haf). }
      destruct Hacc_or_sub as [Hacc_ok [Hub_m | [Hret_m | (env_c & bid_c & b_hdr & dvs & lmap_cut0 & phis_ir0 & sp' & rr' & astk' & Htau_m & Ebh_m & Hin_m & Hlm_m & Hkp_m & Hstp_m & Hids_m & Hws_m & Hpwf_m & Hph_m & Hsp_m & Hpc_m & Hunsp_m & Hphi_m & Hregs_m & Hsav_m & Hslts_m & Hmi_m)]]];
        split; try assumption.
      * left; exact Hub_m.
      * right; left; exact Hret_m.
      * right; right; exists env_c, bid_c, b_hdr, dvs, lmap_cut0, phis_ir0, sp', rr', astk'.
        repeat split; try assumption.
        -- intros rb Hrb; destruct (Hregs_m rb Hrb) as (e_mc64 & Err & Ho_r & Ho_d); exists e_mc64; split; [exact Err | split].
           ++ intros Hbm Hinv0 Hpath0; exact (Ho_r Hbm Hinv0 Hpath').
           ++ intros Hnpt Hbm Hinv0 Hpath0; exact (Ho_d Hnpt Hbm Hinv0 Hpath').
        -- intros off sz e_s Hsl; destruct (Hslts_m off sz e_s Hsl) as (e_mc64 & Eld & Ho_r & Ho_d); exists e_mc64; split; [exact Eld | split].
           ++ intros Hbm Hinv0 Hpath0; exact (Ho_r Hbm Hinv0 Hpath').
           ++ intros Hnpt Hbm Hinv0 Hpath0; exact (Ho_d Hnpt Hbm Hinv0 Hpath').
        -- destruct (ml_inv ls); [| exact I]; intros Hbm Hinv0 Hpath0; exact (Hmi_m Hbm Hinv0 Hpath').
  - (* IST_Ret *)
    destruct Hwf_ir as (_ & Hsup & Hwt_r & Hbw_r & Hlf_r & Hub_r & Hfv_r).
    cbn [ir_seg_freeze_free] in Hfrz_ir; apply negb_true_iff in Hfrz_ir.
    induction t_mc as [sp' rr' astk' | ret_mc | cond_mc dt_mc IHtm df_mc IHfm] in path, acc, res, Hmc, Hpath, Hcol, Hobls |- *;
      cbn [collect_mc_ir_obls_acc mc_seg_holds] in Hcol, Hobls, Hmc.
    + destruct (mc_path_unconditional ls is_body path); [discriminate Hcol |].
      inversion Hcol; subst res; exfalso; exact (imposs_obl_absurd penv_mc dummy_freeze_oracle opt_inv is_body path Hinv Hpath ltac:(constructor; [exact (Forall_inv Hobls) | constructor])).
    + destruct (Pos.eqb rw ret_w) eqn:Erw; [| discriminate Hcol].
      inversion Hcol; subst res; clear Hcol.
      inversion Hobls as [| ? ? Ho_r Hacc_ok]; subst; clear Hobls.
      split; [exact Hacc_ok |].
      destruct Hir as [Hub | (env_out & dv_ir & Hst & Hev_ir)]; [left; exact Hub |].
      pose proof (Ho_r eq_refl Hinv Hpath) as Href_e.
      destruct (eval_cert_expr_refine_mono penv_ir penv_mc dummy_freeze_oracle ret_ir Hwt_r Hlf_r Hub_r Hfrz_ir
                  (fun x wx Hx => Href x wx (Hfv_r (x, wx) Hx)))
        as (v1 & v2 & Ev1 & Ev2 & _ & _ & R12).
      rewrite Hev_ir in Ev1; inversion Ev1; subst v1.
      cbn [refine_eou_dvalue] in Href_e; rewrite Ev2 in Href_e; destruct (eval_closed_cert_expr penv_mc dummy_freeze_oracle ret_mc) as [| | | dv_mc] eqn:Evmc;
        try contradiction.
      right; left; exists env_out, dv_ir, ret_mc, dv_mc; repeat split; try assumption.
      exact (dvalue_refines_trans _ _ _ R12 Href_e).
    + destruct Hmc as [b [Hbc Hsub]].
      assert (Hpath' : forall (b0 : bool) (c0 : cert_expr), In (b0, c0) ((b, cond_mc) :: path) ->
        eval_closed_cert_expr penv_mc dummy_freeze_oracle c0 =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b0 then @Integers.one 1%positive else @Integers.zero 1%positive)))).
      { intros b0 c0 [Heq | Hin]; [inversion Heq; subst; exact Hbc | exact (Hpath b0 c0 Hin)]. }
      match type of Hcol with
      | match ?f with inl _ => _ | inr _ => _ end = _ => destruct f as [| af] eqn:Haf_eq
      end; [discriminate Hcol |].
      assert (Haf : Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) af) by
        exact (collect_mc_ir_obls_acc_sub _ arch ls ret_w hdr_ws is_body ((true, cond_mc) :: path) (IST_Ret rw ret_ir) dt_mc af res Hcol Hobls).
      assert (Hacc_or_sub :
        Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) acc /\
        ((forall sigma, cfg_steps_to_ub sigma env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))) \/
         (exists env_out dv_ir ret_mc dv_mc,
            pure_cfg_steps env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid)) env_out dv_ir /\
            P_ret ret_mc /\
            eval_closed_cert_expr penv_mc dummy_freeze_oracle ret_mc = raise_ret dv_mc /\
            dvalue_refines dv_ir dv_mc) \/
         (exists env_c bid_c b_hdr dvs lmap_cut0 phis_ir0 sp' rr' astk',
            ((env_c = env0 /\ bid_c = bid_from /\ cur_bid = hdr_id) \/
             pure_cfg_steps_to_tau env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))
               env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id))) /\
            RM.find hdr_id bmap = Some b_hdr /\
            In lmap_cut0 (collect_entry_cut_lmaps (IST_Ret rw ret_ir)) /\
            lmap_matches_env penv_ir lmap_cut0 env_c /\
            (forall r, In r wr_keep -> RM.find r env_c = RM.find r env0) /\
            pure_cfg_steps env_c (denote_phis bid_c (blk_phis b_hdr)) (apply_phi_env env_c dvs) tt /\
            Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs /\
            Forall2 (fun w '(wp, _) => w = wp) hdr_ws phis_ir0 /\
            Forall (fun '(wp, ce) =>
              wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
              is_let_free_expr ce = true /\ ub_free_expr ce = true /\
              expr_has_freeze ce = false /\ incl (collect_free_vars [] ce) allowed_ir) phis_ir0 /\
            Forall2 (fun '(wp, ce) '(_, dv) =>
              eval_closed_cert_expr penv_ir dummy_freeze_oracle ce = raise_ret dv /\
              wf_scalar_dvalue wp dv) phis_ir0 dvs /\
            sp' = ml_sp_off ls /\ P_cut sp' rr' astk' /\
            (forall r, In r (mc_unspilled_preserved arch ls) -> rr' r = MSV_SavedReg r) /\
            (forall k w ce, nth_error phis_ir0 k = Some (w, ce) -> cut_var_ptol ls k w = false ->
               exists vi, eval_closed_cert_expr penv_mc dummy_freeze_oracle ce = raise_ret (DVALUE_Base (@DVALUE_I Pa w vi))) /\
            (forall rb, In rb (ml_regs ls) -> exists e_mc64, rr' (mlr_reg rb) = MSV_Expr e_mc64 /\
               mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body ((b, cond_mc) :: path) (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
               (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false -> mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Defined is_body ((b, cond_mc) :: path) (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) (mlr_expr rb))))) /\
            (forall off r, In (MLS_SavedReg off r) (ml_slots ls) -> mc_sym_stk_load off MS_8 false astk' = Some (MSV_SavedReg r)) /\
            (forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) -> exists e_mc64, mc_sym_stk_load off sz false astk' = Some (MSV_Expr e_mc64) /\
               mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body ((b, cond_mc) :: path) (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
               (expr_is_ptol_var ls hdr_ws e_s = false -> mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Defined is_body ((b, cond_mc) :: path) (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) e_s)))) /\
            match ml_inv ls with None => True | Some inv_e => mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body ((b, cond_mc) :: path) 1%positive (CE_BvConst 1%positive 1%N) (subst_cert_expr (build_phi_subst 0%nat phis_ir0) inv_e)) end))).
      { destruct b.
        -- destruct (IHtm ((true, cond_mc) :: path) af res Hsub Hpath' Hcol Hobls) as [_ Hres]; split.
           ++ exact (collect_mc_ir_obls_acc_sub _ arch ls ret_w hdr_ws is_body ((false, cond_mc) :: path) (IST_Ret rw ret_ir) df_mc acc af Haf_eq Haf).
           ++ exact Hres.
        -- exact (IHfm ((false, cond_mc) :: path) acc af Hsub Hpath' Haf_eq Haf). }
      destruct Hacc_or_sub as [Hacc_ok [Hub_m | [Hret_m | (? & ? & ? & ? & ? & ? & ? & ? & ? & _ & _ & Hin_m & _)]]];
        split; try assumption; [left; exact Hub_m | right; left; exact Hret_m | exfalso; exact Hin_m].
  - (* IST_UB *)
    inversion Hcol; subst res; split; [exact Hobls | left; exact Hir].
  - (* IST_Branch *)
    cbn [collect_mc_ir_obls_acc] in Hcol.
    destruct Hwf_ir as [Hlms (Hwt_c & Hbw_c & Hlf_c & Hub_c & Hfv_c & Hwf_t & Hwf_f)].
    assert (Hlms_t : forall lm, In lm (collect_entry_cut_lmaps dt_ir) -> wf_pure_lmap allowed_ir lm)
      by (intros lm Hin; exact (Hlms lm (in_or_app _ _ _ (or_introl Hin)))).
    assert (Hlms_f : forall lm, In lm (collect_entry_cut_lmaps df_ir) -> wf_pure_lmap allowed_ir lm)
      by (intros lm Hin; exact (Hlms lm (in_or_app _ _ _ (or_intror Hin)))).
    cbn [ir_seg_freeze_free] in Hfrz_ir; rewrite !andb_true_iff in Hfrz_ir; destruct Hfrz_ir as [[Hnfrz_c Hnf_t] Hnf_f].
    apply negb_true_iff in Hnfrz_c.
    destruct (collect_mc_ir_obls_acc arch ls ret_w hdr_ws is_body ((false, cond) :: path) df_ir t_mc acc)
      as [| af] eqn:Eaf; [discriminate Hcol |].
    assert (Haf : Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) af)
      by exact (collect_mc_ir_obls_acc_sub _ _ _ _ _ _ _ _ _ _ _ Hcol Hobls).
    cbn [ir_seg_eval_spec] in Hir; destruct Hir as [Hub | (env_mid & bid_step & br_t & br_f & b & Htau & Hev_c & Hk2 & Hsub)].
    + split; [exact (collect_mc_ir_obls_acc_sub _ _ _ _ _ _ _ _ _ _ _ Eaf Haf) | left; exact Hub].
    + destruct (eval_cert_expr_refine_mono penv_ir penv_mc dummy_freeze_oracle cond Hwt_c Hlf_c Hub_c Hnfrz_c
                  (fun x wx Hx => Href x wx (Hfv_c (x, wx) Hx)))
        as (vc1 & vc2 & Evc1 & Evc2 & _ & _ & Rc).
      rewrite Hev_c in Evc1; inversion Evc1; subst vc1.
      assert (Hvc2 : vc2 = DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive))).
      { destruct Rc as [Hbad | <-]; [discriminate Hbad | reflexivity]. }
      subst vc2.
      assert (Hpath' : forall b0 c0, In (b0, c0) ((b, cond) :: path) ->
        eval_closed_cert_expr penv_mc dummy_freeze_oracle c0 =
        raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b0 then @Integers.one 1%positive else @Integers.zero 1%positive)))).
      { intros b0 c0 [Heq | Hin]; [inversion Heq; subst; exact Evc2 | exact (Hpath b0 c0 Hin)]. }
      assert (Hacc_and_sub :
        Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) acc /\
        ((forall sigma, cfg_steps_to_ub sigma env_mid (@denote_cfg_from Pa bmap None (bid_step, if b then br_t else br_f))) \/
         (exists env_out dv_ir ret_mc dv_mc,
            pure_cfg_steps env_mid (@denote_cfg_from Pa bmap None (bid_step, if b then br_t else br_f)) env_out dv_ir /\
            P_ret ret_mc /\
            eval_closed_cert_expr penv_mc dummy_freeze_oracle ret_mc = raise_ret dv_mc /\
            dvalue_refines dv_ir dv_mc) \/
         (exists env_c bid_c b_hdr dvs lmap_cut phis_ir sp' rr' astk',
            ((env_c = env_mid /\ bid_c = bid_step /\ (if b then br_t else br_f) = hdr_id) \/
             pure_cfg_steps_to_tau env_mid (@denote_cfg_from Pa bmap None (bid_step, if b then br_t else br_f))
               env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id))) /\
            RM.find hdr_id bmap = Some b_hdr /\
            In lmap_cut (collect_entry_cut_lmaps (if b then dt_ir else df_ir)) /\
            lmap_matches_env penv_ir lmap_cut env_c /\
            (forall r, In r wr_keep -> RM.find r env_c = RM.find r env_mid) /\
            pure_cfg_steps env_c (denote_phis bid_c (blk_phis b_hdr)) (apply_phi_env env_c dvs) tt /\
            Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs /\
            Forall2 (fun w '(wp, _) => w = wp) hdr_ws phis_ir /\
            Forall (fun '(wp, ce) =>
              wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
              is_let_free_expr ce = true /\ ub_free_expr ce = true /\
              expr_has_freeze ce = false /\ incl (collect_free_vars [] ce) allowed_ir) phis_ir /\
            Forall2 (fun '(wp, ce) '(_, dv) =>
              eval_closed_cert_expr penv_ir dummy_freeze_oracle ce = raise_ret dv /\
              wf_scalar_dvalue wp dv) phis_ir dvs /\
            sp' = ml_sp_off ls /\ P_cut sp' rr' astk' /\
            (forall r, In r (mc_unspilled_preserved arch ls) -> rr' r = MSV_SavedReg r) /\
            (forall k w ce, nth_error phis_ir k = Some (w, ce) -> cut_var_ptol ls k w = false ->
               exists vi, eval_closed_cert_expr penv_mc dummy_freeze_oracle ce = raise_ret (DVALUE_Base (@DVALUE_I Pa w vi))) /\
            (forall rb, In rb (ml_regs ls) -> exists e_mc64, rr' (mlr_reg rb) = MSV_Expr e_mc64 /\
               mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body ((b, cond) :: path) (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
               (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false -> mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Defined is_body ((b, cond) :: path) (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb))))) /\
            (forall off r, In (MLS_SavedReg off r) (ml_slots ls) -> mc_sym_stk_load off MS_8 false astk' = Some (MSV_SavedReg r)) /\
            (forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) -> exists e_mc64, mc_sym_stk_load off sz false astk' = Some (MSV_Expr e_mc64) /\
               mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body ((b, cond) :: path) (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
               (expr_is_ptol_var ls hdr_ws e_s = false -> mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Defined is_body ((b, cond) :: path) (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s)))) /\
            match ml_inv ls with None => True | Some inv_e => mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body (MLO_Refine is_body ((b, cond) :: path) 1%positive (CE_BvConst 1%positive 1%N) (subst_cert_expr (build_phi_subst 0%nat phis_ir) inv_e)) end))).
      { destruct b.
        - destruct (IHt _ _ _ ((true, cond) :: path) _ _ (conj Hlms_t Hwf_t) Hnf_t Hsub Hmc Hinv Hpath' Hcol Hobls) as [_ Hres].
          split; [exact (collect_mc_ir_obls_acc_sub _ _ _ _ _ _ _ _ _ _ _ Eaf Haf) | exact Hres].
        - exact (IHf _ _ _ ((false, cond) :: path) acc af (conj Hlms_f Hwf_f) Hnf_f Hsub Hmc Hinv Hpath' Eaf Haf). }
      destruct Hacc_and_sub as [Hacc_ok [Hub_sub | [(env_out & dv_ir & ret_mc & dv_mc & Hst & Hpr & Hevmc & Href_d)
                                            | (env_c & bid_c & b_hdr & dvs & lmap_cut & phis_ir & sp' & rr' & astk' &
                                               Htau2 & Ebh & Hin_lm & Hlm_m & Hkp2 & Hstp & Hids & Hws & Hpwf & Hph & Hsp & Hpc & Hunsp & Hphi_d & Hregs & Hsav & Hslts & Hmi)]]];
        split; try assumption.
      * left; intro sigma; exact (pure_cfg_steps_to_tau_then_ub sigma _ _ _ _ Htau (Hub_sub sigma)).
      * right; left; exists env_out, dv_ir, ret_mc, dv_mc; repeat split; try assumption.
        exact (pure_cfg_steps_to_tau_then_ret _ _ _ _ _ _ Htau Hst).
      * right; right; exists env_c, bid_c, b_hdr, dvs, lmap_cut, phis_ir, sp', rr', astk'.
        cbn [collect_entry_cut_lmaps].
        repeat split; try assumption.
        -- right; destruct Htau2 as [[-> [-> Eeq]] | Htau2]; [rewrite <- Eeq; exact Htau | exact (pure_cfg_steps_to_tau_trans _ _ _ _ _ _ Htau Htau2)].
        -- apply in_app_iff; destruct b; [left | right]; exact Hin_lm.
        -- intros r Hr; rewrite (Hkp2 r Hr), (Hk2 r Hr); reflexivity.
        -- intros rb Hrb; destruct (Hregs rb Hrb) as (e_mc64 & Err & Ho_r & Ho_d); exists e_mc64; split; [exact Err | split].
           ++ intros Hbm Hinv0 Hpath0; apply Ho_r; try assumption; intros b0 c0 Hin; apply Hpath'; exact Hin.
           ++ intros Hnpt Hbm Hinv0 Hpath0; apply Ho_d; try assumption; intros b0 c0 Hin; apply Hpath'; exact Hin.
        -- intros off sz e_s Hsl; destruct (Hslts off sz e_s Hsl) as (e_mc64 & Eld & Ho_r & Ho_d); exists e_mc64; split; [exact Eld | split].
           ++ intros Hbm Hinv0 Hpath0; apply Ho_r; try assumption; intros b0 c0 Hin; apply Hpath'; exact Hin.
           ++ intros Hnpt Hbm Hinv0 Hpath0; apply Ho_d; try assumption; intros b0 c0 Hin; apply Hpath'; exact Hin.
        -- destruct (ml_inv ls); [| exact I]; intros Hbm Hinv0 Hpath0; apply Hmi; try assumption.
Qed.

Theorem collect_mc_ir_obls_sound {Pa : Params} :
  forall arch ls ret_w hdr_ws allowed_ir (is_body : bool)
         (penv_ir penv_mc : param_env Pa)
         bmap hdr_id hdr_phis wr_keep env0 bid_from cur_bid t_ir
         P_cut P_ret t_mc opt_inv (path : list (bool * cert_expr)) res,
    extract_hdr_phi_widths hdr_phis = hdr_ws ->
    ir_seg_wf allowed_ir hdr_ws t_ir ->
    ir_seg_freeze_free t_ir = true ->
    (forall nm w, In (nm, w) allowed_ir ->
       exists d1 d2 : @dvalue Pa,
         penv_ir nm = Some d1 /\ penv_mc nm = Some d2 /\
         wf_scalar_dvalue w d1 /\ wf_scalar_dvalue w d2 /\ dvalue_refines d1 d2) ->
    ir_seg_eval_spec bmap hdr_id hdr_phis wr_keep penv_ir env0 bid_from cur_bid t_ir ->
    mc_seg_holds penv_mc dummy_freeze_oracle P_cut P_ret t_mc ->
    (is_body = true ->
     match opt_inv with
     | None => True
     | Some inv_e =>
         eval_closed_cert_expr penv_mc dummy_freeze_oracle inv_e =
         raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (@Integers.one 1%positive)))
     end) ->
    (forall (b : bool) (c : cert_expr), In (b, c) path ->
       eval_closed_cert_expr penv_mc dummy_freeze_oracle c =
       raise_ret (DVALUE_Base (@DVALUE_I Pa 1%positive (if b then @Integers.one 1%positive else @Integers.zero 1%positive)))) ->
    collect_mc_ir_obls arch ls ret_w hdr_ws is_body path t_ir t_mc = inr res ->
    Forall (mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body) res ->
    (forall sigma, cfg_steps_to_ub sigma env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))) \/
    (exists env_out dv_ir ret_mc dv_mc,
       pure_cfg_steps env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid)) env_out dv_ir /\
       P_ret ret_mc /\
       eval_closed_cert_expr penv_mc dummy_freeze_oracle ret_mc = raise_ret dv_mc /\
       dvalue_refines dv_ir dv_mc) \/
    (exists env_c bid_c b_hdr dvs lmap_cut phis_ir sp' rr' astk',
       ((env_c = env0 /\ bid_c = bid_from /\ cur_bid = hdr_id) \/
        pure_cfg_steps_to_tau env0 (@denote_cfg_from Pa bmap None (bid_from, cur_bid))
          env_c (@denote_cfg_from Pa bmap None (bid_c, hdr_id))) /\
       RM.find hdr_id bmap = Some b_hdr /\
       In lmap_cut (collect_entry_cut_lmaps t_ir) /\
       lmap_matches_env penv_ir lmap_cut env_c /\
       (forall r, In r wr_keep -> RM.find r env_c = RM.find r env0) /\
       pure_cfg_steps env_c (denote_phis bid_c (blk_phis b_hdr)) (apply_phi_env env_c dvs) tt /\
       Forall2 (fun '(id, _) '(id', _) => id' = id) hdr_phis dvs /\
       Forall2 (fun w '(wp, _) => w = wp) hdr_ws phis_ir /\
       Forall (fun '(wp, ce) =>
         wt_cert_expr [] ce = true /\ cert_expr_bit_width ce = wp /\
         is_let_free_expr ce = true /\ ub_free_expr ce = true /\
         expr_has_freeze ce = false /\ incl (collect_free_vars [] ce) allowed_ir) phis_ir /\
       Forall2 (fun '(wp, ce) '(_, dv) =>
         eval_closed_cert_expr penv_ir dummy_freeze_oracle ce = raise_ret dv /\
         wf_scalar_dvalue wp dv) phis_ir dvs /\
       sp' = ml_sp_off ls /\
       P_cut sp' rr' astk' /\
       (forall r, In r (mc_unspilled_preserved arch ls) -> rr' r = MSV_SavedReg r) /\
       (forall k w ce,
          nth_error phis_ir k = Some (w, ce) ->
          cut_var_ptol ls k w = false ->
          exists vi,
            eval_closed_cert_expr penv_mc dummy_freeze_oracle ce =
            raise_ret (DVALUE_Base (@DVALUE_I Pa w vi))) /\
       (forall rb, In rb (ml_regs ls) ->
          exists e_mc64,
            rr' (mlr_reg rb) = MSV_Expr e_mc64 /\
            mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
              (MLO_Refine is_body path (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb)) (trunc_mc_expr_to (mlr_width rb) e_mc64)) /\
            (expr_is_ptol_var ls hdr_ws (mlr_expr rb) = false ->
             mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
               (MLO_Defined is_body path (mlr_width rb) (subst_cert_expr (build_phi_subst 0%nat phis_ir) (mlr_expr rb))))) /\
       (forall off r, In (MLS_SavedReg off r) (ml_slots ls) ->
          mc_sym_stk_load off MS_8 false astk' = Some (MSV_SavedReg r)) /\
       (forall off sz e_s, In (MLS_Expr off sz e_s) (ml_slots ls) ->
          exists e_mc64,
            mc_sym_stk_load off sz false astk' = Some (MSV_Expr e_mc64) /\
            mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
              (MLO_Refine is_body path (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s) (trunc_mc_slot_expr sz e_mc64)) /\
            (expr_is_ptol_var ls hdr_ws e_s = false ->
             mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
               (MLO_Defined is_body path (mc_mem_bits sz) (subst_cert_expr (build_phi_subst 0%nat phis_ir) e_s)))) /\
       match ml_inv ls with
       | None => True
       | Some inv_e =>
           mc_obl_holds penv_mc dummy_freeze_oracle opt_inv is_body
             (MLO_Refine is_body path 1%positive (CE_BvConst 1%positive 1%N) (subst_cert_expr (build_phi_subst 0%nat phis_ir) inv_e))
       end).
Proof.
  intros arch ls ret_w hdr_ws allowed_ir is_body penv_ir penv_mc bmap hdr_id hdr_phis wr_keep
         env0 bid_from cur_bid t_ir P_cut P_ret t_mc opt_inv path res Hhdr Hwf Hfrz Href Hir Hmc Hinv Hpath Hcol Hobls.
  exact (proj2 (collect_mc_ir_obls_acc_sound arch ls ret_w hdr_ws allowed_ir is_body penv_ir penv_mc
                  bmap hdr_id hdr_phis wr_keep env0 bid_from cur_bid t_ir P_cut P_ret t_mc opt_inv path [] res
                  Hhdr Hwf Hfrz Href Hir Hmc Hinv Hpath Hcol Hobls)).
Qed.

Lemma reify_ir_seg_req_step_bid_from_irrel :
  forall phase fuel bmap hdr_id hdr_phis visited bid1 bid2 cur_bid lmap t,
    reify_ir_seg phase fuel bmap hdr_id hdr_phis true visited bid1 cur_bid lmap = inr t ->
    reify_ir_seg phase fuel bmap hdr_id hdr_phis true visited bid2 cur_bid lmap = inr t.
Proof. destruct fuel; intros bmap hdr_id hdr_phis visited bid1 bid2 cur_bid lmap t H; exact H. Qed.

(** ** 5. End-to-End Loop Validators & CNF Emitters ([validate_mc_loop_rv64], [validate_mc_loop_a64]) *)

Record mc_loop_ir_prep : Type := mk_mc_loop_ir_prep {
  mlip_hdr_id : block_id;
  mlip_b_hdr : block dtyp;
  mlip_hdr_phis : list (raw_id * positive);
  mlip_lmap_base : rmap (positive * cert_expr);
  mlip_wr_entry : list raw_id;
  mlip_wr_body : list raw_id;
  mlip_t_ir_entry : ir_seg_tree;
  mlip_t_ir_body : ir_seg_tree
}.

Definition check_ls_exprs_vars (allowed : list (string * positive)) (ls : mc_loop_spec) : bool :=
  forallb (fun rb => vars_subset_b (collect_free_vars [] (mlr_expr rb)) allowed) (ml_regs ls) &&
  forallb (fun sb => match sb with MLS_Expr _ _ e => vars_subset_b (collect_free_vars [] e) allowed | MLS_SavedReg _ _ => true end) (ml_slots ls) &&
  match ml_inv ls with
  | None => true
  | Some inv => vars_subset_b (collect_free_vars [] inv) allowed
  end.

Fixpoint check_ls_reg_vars_diag
  (allowed : list (string * positive)) (rbs : list mc_loop_reg_bind) {struct rbs} : string + unit :=
  match rbs with
  | [] => inr tt
  | rb :: rest =>
      if vars_subset_b (collect_free_vars [] (mlr_expr rb)) allowed then
        check_ls_reg_vars_diag allowed rest
      else
        inl (diag "mc-loop-ir"
          ("loop reg x" ++ diag_N_dec (mlr_reg rb) ++
           " expression references out-of-scope variable " ++
           mc_format_missing_var allowed (mlr_expr rb)))
  end.

Lemma check_ls_reg_vars_diag_sound : forall allowed rbs,
  check_ls_reg_vars_diag allowed rbs = inr tt ->
  forallb (fun rb => vars_subset_b (collect_free_vars [] (mlr_expr rb)) allowed) rbs = true.
Proof.
  intros allowed rbs; induction rbs as [| rb rest IH]; intro H; cbn in *; [reflexivity |].
  destruct (vars_subset_b (collect_free_vars [] (mlr_expr rb)) allowed); [cbn; exact (IH H) | discriminate H].
Qed.

Fixpoint check_ls_slot_vars_diag
  (allowed : list (string * positive)) (sbs : list mc_loop_slot_bind) {struct sbs} : string + unit :=
  match sbs with
  | [] => inr tt
  | MLS_SavedReg _ _ :: rest => check_ls_slot_vars_diag allowed rest
  | MLS_Expr off _ e :: rest =>
      if vars_subset_b (collect_free_vars [] e) allowed then
        check_ls_slot_vars_diag allowed rest
      else
        inl (diag "mc-loop-ir"
          ("loop slot at sp+" ++ diag_Z_dec off ++
           " expression references out-of-scope variable " ++
           mc_format_missing_var allowed e))
  end.

Lemma check_ls_slot_vars_diag_sound : forall allowed sbs,
  check_ls_slot_vars_diag allowed sbs = inr tt ->
  forallb (fun sb => match sb with MLS_Expr _ _ e => vars_subset_b (collect_free_vars [] e) allowed | MLS_SavedReg _ _ => true end) sbs = true.
Proof.
  intros allowed sbs; induction sbs as [| [off sz e | off r] rest IH]; intro H; cbn in *;
    [reflexivity | | exact (IH H)].
  destruct (vars_subset_b (collect_free_vars [] e) allowed); [cbn; exact (IH H) | discriminate H].
Qed.

Definition check_ls_exprs_vars_diag (allowed : list (string * positive)) (ls : mc_loop_spec) : string + unit :=
  bind_err (check_ls_reg_vars_diag allowed (ml_regs ls)) (fun _ =>
  bind_err (check_ls_slot_vars_diag allowed (ml_slots ls)) (fun _ =>
  match ml_inv ls with
  | None => inr tt
  | Some inv =>
      guard_err (vars_subset_b (collect_free_vars [] inv) allowed)
        (fun _ => diag "mc-loop-ir"
          ("loop invariant references out-of-scope variable " ++ mc_format_missing_var allowed inv))
  end)).

Lemma check_ls_exprs_vars_diag_sound : forall allowed ls,
  check_ls_exprs_vars_diag allowed ls = inr tt ->
  check_ls_exprs_vars allowed ls = true.
Proof.
  intros allowed ls H; unfold check_ls_exprs_vars_diag in H; unfold check_ls_exprs_vars.
  destruct (check_ls_reg_vars_diag allowed (ml_regs ls)) as [| []] eqn:Hr; cbn [bind_err] in H; [discriminate H |].
  destruct (check_ls_slot_vars_diag allowed (ml_slots ls)) as [| []] eqn:Hs; cbn [bind_err] in H; [discriminate H |].
  rewrite (check_ls_reg_vars_diag_sound _ _ Hr), (check_ls_slot_vars_diag_sound _ _ Hs).
  destruct (ml_inv ls) as [inv |] eqn:Hi; [| reflexivity].
  destruct (vars_subset_b (collect_free_vars [] inv) allowed); [reflexivity | discriminate H].
Qed.

Definition find_hdr_block_id (hdr_name : string) (blks : list (block dtyp)) : option block_id :=
  match List.find (fun b => String.eqb (cert_raw_id_bare (blk_id b)) hdr_name) blks with
  | Some b => Some (blk_id b)
  | None => None
  end.

Definition prepare_mc_loop_ir
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (ls : mc_loop_spec)
  : string + mc_loop_ir_prep :=
  if negb (forallb (fun '(nm, _) => negb (mc_starts_with_bang nm)) allowed0) then
    inl (diag "mc-loop-ir"
      ("disallowed internal '!' parameter variable '" ++ mc_format_first_bang_var allowed0 ++ "'"))
  else
    let bmap := ocfg_map (blks ir_cfg) in
    match find_hdr_block_id (ml_ir_header ls) (blks ir_cfg) with
    | None =>
        inl (diag "mc-loop-ir"
          ("loop ir-header block '" ++ ml_ir_header ls ++ "' not found in IR CFG"))
    | Some hdr_id =>
    match RM.find hdr_id bmap with
    | None =>
        inl (diag "mc-loop-ir"
          ("loop ir-header block '" ++ ml_ir_header ls ++ "' missing from CFG block map"))
    | Some b_hdr =>
        match extract_hdr_phis (blk_phis b_hdr) with
        | inl err => inl err
        | inr hdr_phis =>
            if negb (no_dup_raw_ids (List.map fst hdr_phis)) then
              inl (diag "mc-loop-ir"
                ("duplicate header phi variable '" ++
                 mc_format_first_dup_raw_id (List.map fst hdr_phis) ++
                 "' in block '" ++ ml_ir_header ls ++ "'"))
            else
              let ir_pnames := List.map cert_reg_name (args ir_cfg) in
              let lmap_init := init_param_lmap (args ir_cfg) ir_pnames (param_idx_uses_cfg ir_cfg) in
              let ir_fuel := S (List.length (blks ir_cfg) + 1) in
              match ir_seg_written_ids "entry" ir_fuel bmap hdr_id false [] (init ir_cfg),
                    reify_ir_seg "entry" ir_fuel bmap hdr_id hdr_phis false [] (init ir_cfg) (init ir_cfg) lmap_init with
              | inr wr_entry, inr t_ir_entry =>
                  let lmap_base := common_cut_lmap lmap_init (collect_entry_cut_lmaps t_ir_entry) in
                  let lmap_cut := wrap_cut_mc lmap_base hdr_phis in
                  match ir_seg_written_ids "body" ir_fuel bmap hdr_id true [] hdr_id,
                        reify_ir_seg "body" ir_fuel bmap hdr_id hdr_phis true [] hdr_id hdr_id lmap_cut with
                  | inr wr_body, inr t_ir_body =>
                      let body_defs := List.map fst hdr_phis ++ wr_body in
                      if negb (disjoint_raw_ids (lmap_keys lmap_base) body_defs) then
                        inl (diag "mc-loop-ir"
                          ("loop-carried base SSA variable '" ++
                           mc_format_first_overlap_raw_id (lmap_keys lmap_base) body_defs ++
                           "' is redefined inside loop body"))
                      else if negb (ir_seg_freeze_free t_ir_entry) then
                        inl (diag "mc-loop-ir" "freeze expressions disallowed in loop entry segment")
                      else if negb (ir_seg_freeze_free t_ir_body) then
                        inl (diag "mc-loop-ir" "freeze expressions disallowed in loop body segment")
                      else
                        match check_ls_exprs_vars_diag (allowed0 ++ cut_vars_from 0%nat hdr_phis) ls with
                        | inl err => inl err
                        | inr tt =>
                            inr (mk_mc_loop_ir_prep hdr_id b_hdr hdr_phis lmap_base wr_entry wr_body t_ir_entry t_ir_body)
                        end
                  | inl err, _ => inl err
                  | _, inl err => inl err
                  end
              | inl err, _ => inl err
              | _, inl err => inl err
              end
        end
    end
    end.

Record mc_loop_cnf_bundle : Type := mk_mc_loop_cnf_bundle {
  mlcb_prep : mc_loop_ir_prep;
  mlcb_ctx : ub_ctx;
  mlcb_known : list (string * positive);
  mlcb_obls : list mc_loop_obl
}.

Definition build_mc_loop_bundle_rv64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_rv_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (ls : mc_loop_spec) : string + (mc_loop_cnf_bundle * rv_seg_tree * rv_seg_tree * rv_seg_tree) :=
  match check_mc_loop_spec_diag EA_Riscv64 ls with
  | inl err => inl err
  | inr tt =>
      if negb (rv_supported_arg_width ret_w) then
        inl (diag "mc-loop" ("unsupported return width i" ++ diag_pos_dec ret_w ++ " for RV64 loop"))
      else if negb (forallb inst_no_word_mulh insts) then
        inl (diag "mc-loop-mc" "unsupported RV64 mulhw instruction in loop function")
      else if negb (Nat.leb (List.length arg_specs) 8) || negb (forallb rv_valid_arg_spec arg_specs) then
        inl (diag "mc-loop" "invalid RV64 argument specs for loop function")
      else
        match prepare_mc_loop_ir ir_cfg allowed0 ls with
        | inl err => inl err
        | inr prep =>
            let mc_fuel := S (2 * elf_length_tr insts) in
            let hdr_ws := extract_hdr_phi_widths (mlip_hdr_phis prep) in
            match summarize_rv64_seg "entry" mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                    (rv_build_init_val_regs 10%N arg_specs) [] ret_w,
                  summarize_rv64_seg "body" mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                    (rv_cut_vrf ls) (build_cut_astk (ml_slots ls)) ret_w,
                  summarize_rv64_seg "skel" mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                    (rv_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) ret_w with
            | inr seg_ent, inr seg_body, inr seg_skel =>
                match bind_err
                        (check_mc_skel_tree_diag "entry" EA_Riscv64 ls (rv_seg_to_mc_seg seg_ent))
                        (fun _ => check_mc_skel_tree_diag "skel" EA_Riscv64 ls (rv_seg_to_mc_seg seg_skel)) with
                | inl err => inl err
                | inr tt =>
                    match collect_mc_ir_obls_acc EA_Riscv64 ls ret_w hdr_ws true [] (mlip_t_ir_body prep) (rv_seg_to_mc_seg seg_body) [] with
                    | inl err => inl err
                    | inr obls_body =>
                        match collect_mc_ir_obls_acc EA_Riscv64 ls ret_w hdr_ws false [] (mlip_t_ir_entry prep) (rv_seg_to_mc_seg seg_ent) obls_body with
                        | inl err => inl err
                        | inr obls =>
                            let ghost_vars := cut_vars_from 0%nat (mlip_hdr_phis prep) ++ hi32_vars ls in
                            let known_vars := allowed0 ++ ghost_vars in
                            let loop_ctx := mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) ghost_vars in
                            inr (mk_mc_loop_cnf_bundle prep loop_ctx known_vars obls, seg_ent, seg_body, seg_skel)
                        end
                    end
                end
            | inl err, _, _ => inl err
            | _, inl err, _ => inl err
            | _, _, inl err => inl err
            end
        end
  end.

Definition validate_mc_loop_rv64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_rv_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (ls : mc_loop_spec) (opt_pf : option (list lrat_step)) : string + unit :=
  match build_mc_loop_bundle_rv64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls with
  | inl err => inl err
  | inr (bnd, _, _, _) =>
      check_mc_loop_obls "mc-loop" (mlcb_ctx bnd) (mlcb_known bnd) (ml_inv ls) (mlcb_obls bnd) opt_pf
  end.

Definition emit_mc_loop_cnf_rv64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_rv_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (ls : mc_loop_spec) : string + option (positive * cnf) :=
  match build_mc_loop_bundle_rv64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls with
  | inl err => inl err
  | inr (bnd, _, _, _) =>
      emit_mc_loop_cnf "mc-loop" (mlcb_ctx bnd) (mlcb_known bnd) (ml_inv ls) (mlcb_obls bnd)
  end.

Definition build_mc_loop_bundle_a64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_a64_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (ls : mc_loop_spec) : string + (mc_loop_cnf_bundle * a64_seg_tree * a64_seg_tree * a64_seg_tree) :=
  match check_mc_loop_spec_diag EA_AArch64 ls with
  | inl err => inl err
  | inr tt =>
      if negb (rv_supported_arg_width ret_w) then
        inl (diag "mc-loop" ("unsupported return width i" ++ diag_pos_dec ret_w ++ " for AArch64 loop"))
      else if negb (forallb a64_inst_valid insts) then
        inl (diag "mc-loop-mc" "invalid AArch64 instruction in loop function")
      else if negb (Nat.leb (List.length arg_specs) 8) || negb (forallb a64_valid_arg_spec arg_specs) then
        inl (diag "mc-loop" "invalid AArch64 argument specs for loop function")
      else
        match prepare_mc_loop_ir ir_cfg allowed0 ls with
        | inl err => inl err
        | inr prep =>
            let mc_fuel := S (2 * elf_length_tr insts) in
            let hdr_ws := extract_hdr_phi_widths (mlip_hdr_phis prep) in
            match summarize_a64_seg "entry" mc_fuel insts (ml_mc_pc ls) false [] 0%N 0%Z
                    (a64_build_init_val_regs 0%N arg_specs) [] a64_init_sym_flags false ret_w,
                  summarize_a64_seg "body" mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                    (a64_cut_vrf ls) (build_cut_astk (ml_slots ls)) a64_init_sym_flags false ret_w,
                  summarize_a64_seg "skel" mc_fuel insts (ml_mc_pc ls) true [] (ml_mc_pc ls) (ml_sp_off ls)
                    (a64_skel_vrf ls) (build_skel_astk 0%nat (ml_slots ls)) a64_init_sym_flags false ret_w with
            | inr seg_ent, inr seg_body, inr seg_skel =>
                match bind_err
                        (check_mc_skel_tree_diag "entry" EA_AArch64 ls (a64_seg_to_mc_seg seg_ent))
                        (fun _ => check_mc_skel_tree_diag "skel" EA_AArch64 ls (a64_seg_to_mc_seg seg_skel)) with
                | inl err => inl err
                | inr tt =>
                    match collect_mc_ir_obls_acc EA_AArch64 ls ret_w hdr_ws true [] (mlip_t_ir_body prep) (a64_seg_to_mc_seg seg_body) [] with
                    | inl err => inl err
                    | inr obls_body =>
                        match collect_mc_ir_obls_acc EA_AArch64 ls ret_w hdr_ws false [] (mlip_t_ir_entry prep) (a64_seg_to_mc_seg seg_ent) obls_body with
                        | inl err => inl err
                        | inr obls =>
                            let ghost_vars := cut_vars_from 0%nat (mlip_hdr_phis prep) ++ hi32_vars ls in
                            let known_vars := allowed0 ++ ghost_vars in
                            let loop_ctx := mc_init_ctx ++ List.map (fun '(nm, w) => UBA_ParamNoUndef nm w) ghost_vars in
                            inr (mk_mc_loop_cnf_bundle prep loop_ctx known_vars obls, seg_ent, seg_body, seg_skel)
                        end
                    end
                end
            | inl err, _, _ => inl err
            | _, inl err, _ => inl err
            | _, _, inl err => inl err
            end
        end
  end.

Definition validate_mc_loop_a64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_a64_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (ls : mc_loop_spec) (opt_pf : option (list lrat_step)) : string + unit :=
  match build_mc_loop_bundle_a64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls with
  | inl err => inl err
  | inr (bnd, _, _, _) =>
      check_mc_loop_obls "mc-loop" (mlcb_ctx bnd) (mlcb_known bnd) (ml_inv ls) (mlcb_obls bnd) opt_pf
  end.

Definition emit_mc_loop_cnf_a64
  (ir_cfg : CFG.cfg dtyp) (allowed0 : list (string * positive)) (mc_init_ctx : ub_ctx)
  (insts : list decoded_a64_inst) (arg_specs : list rv_arg_spec) (ret_w : positive)
  (ls : mc_loop_spec) : string + option (positive * cnf) :=
  match build_mc_loop_bundle_a64 ir_cfg allowed0 mc_init_ctx insts arg_specs ret_w ls with
  | inl err => inl err
  | inr (bnd, _, _, _) =>
      emit_mc_loop_cnf "mc-loop" (mlcb_ctx bnd) (mlcb_known bnd) (ml_inv ls) (mlcb_obls bnd)
  end.




